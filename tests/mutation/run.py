#!/usr/bin/env python3
"""Mutation testing of the trusted contract (`RecursionFast/Contract/**/*.lean`).

  python3 -I tests/mutation/run.py [--only ID,ID,...] [--file Relation.lean] [--jobs 3]
                                   [--scratch DIR] [--harness] [--check] [--out DIR]

For each mutant of `tests/mutation/mutants.toml` it refreshes a scratch copy of this repository
(`--scratch`, default `$RF_MUTATION_SCRATCH` or `<this checkout>-mutation`; one slot per parallel
job, reused), applies the
textual replacement there (the original text must occur exactly once), and runs the killing
pipeline, cheapest first, stopping at the first kill:

  1. `lake build RecursionFast.Contract`: a failure is INVALID (the mutant is not a contract);
  2. `lake build RecursionFast` (library and controls): the first failing module KILLS it;
  3. with `--harness`, for a mutant that survived 2: the organiser tests that run compiled contract
     code (`.lake/build/bin/extract`, the Lean signer against the service, `accprobe`).

The repository itself is never changed: a slot is a copy of the working tree (without `.lake`
and `.git`), with `.lake/packages` a symlink to this checkout's package tree (read only: Mathlib is
never rebuilt) and `.lake/build` copied from this checkout, which must be up to date
(`lake build --no-build RecursionFast` is checked first). Every command runs under `timeout`, in a
`systemd-run --user --scope -p MemoryMax=16G` scope pinned by `taskset` to the slot's cores.

Results: `--out` (default `tests/mutation/`) gets `results.json` (merged with earlier results by
mutant id) and `results.md`; build logs go to `<scratch>/logs/<id>.<stage>.log`. `--check` only
checks that every mutant's original text occurs exactly once.
"""
import argparse
import json
import os
import re
import signal
import subprocess
import sys
import threading
import time
import tomllib
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
CONTRACT = os.path.join("RecursionFast", "Contract")
BUILD_TIMEOUT = 25 * 60

ERR = re.compile(r"error: (?:\./)*(\S+?\.lean):(\d+):(\d+): ?(.*)")
FAILED_JOB = re.compile(r"✖ \[\d+/\d+\] (?:Building|Compiling) (\S+)")


def load_mutants():
    with open(os.path.join(HERE, "mutants.toml"), "rb") as f:
        return tomllib.load(f)["mutant"]


def check_mutants(ms):
    """Each mutant's original text occurs exactly once in its file; ids are unique."""
    bad, seen = [], set()
    for m in ms:
        if m["id"] in seen:
            bad.append(f"{m['id']}: duplicate id")
        seen.add(m["id"])
        src = open(os.path.join(ROOT, CONTRACT, m["file"]), encoding="utf-8").read()
        n = src.count(m["original"])
        if n != 1:
            bad.append(f"{m['id']}: original text occurs {n} times in {m['file']}")
        if m["original"] == m["replacement"]:
            bad.append(f"{m['id']}: replacement equals the original")
    return bad


def scoped(cores, timeout_s, argv):
    return ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=16G", "taskset", "-c", cores,
            "timeout", "-k", "30", str(timeout_s)] + argv


def sync_slot(slot):
    """Make the slot a copy of the working tree and of its `.lake/build` (never deleting anything)."""
    os.makedirs(os.path.join(slot, ".lake"), exist_ok=True)
    tar = subprocess.Popen(["tar", "-C", ROOT, "--exclude=.lake", "--exclude=.git", "--exclude=./logs",
                            "--exclude=__pycache__", "--exclude=./service/target", "-cf", "-", "."], stdout=subprocess.PIPE)
    subprocess.run(["tar", "-C", slot, "-xf", "-"], stdin=tar.stdout, check=True, timeout=300)
    if tar.wait(timeout=300) != 0:
        raise RuntimeError("tar of the working tree failed")
    pk = os.path.join(slot, ".lake", "packages")
    if not os.path.lexists(pk):
        os.symlink(os.path.realpath(os.path.join(ROOT, ".lake", "packages")), pk)
    for d in ("build", "config"):
        os.makedirs(os.path.join(slot, ".lake", d), exist_ok=True)
        subprocess.run(["cp", "-a", os.path.join(ROOT, ".lake", d) + "/.", os.path.join(slot, ".lake", d) + "/"],
                       check=True, timeout=600)
    # the service's binaries for the harness stage, built once in this checkout
    tgt = os.path.join(slot, "service", "target")
    if not os.path.lexists(tgt) and os.path.isdir(os.path.join(ROOT, "service", "target")):
        os.symlink(os.path.join(ROOT, "service", "target"), tgt)


def apply_mutant(slot, m):
    path = os.path.join(slot, CONTRACT, m["file"])
    src = open(path, encoding="utf-8").read()
    if src.count(m["original"]) != 1:
        raise RuntimeError(f"original text occurs {src.count(m['original'])} times in {m['file']}")
    open(path, "w", encoding="utf-8").write(src.replace(m["original"], m["replacement"]))


def run_build(slot, cores, threads, argv, log_path, timeout_s=BUILD_TIMEOUT, stop_at_first=True):
    """Run a Lake build; return (exit code, the first error of each failing Lean file in order as
    [file, line, message], the first failed job, seconds). With `stop_at_first`, the build is
    stopped once the first error of a Lean file is reported."""
    env = dict(os.environ, LEAN_NUM_THREADS=str(threads))
    t0 = time.time()
    errors, job, cur, lines_after = [], None, None, 0
    with open(log_path, "w", encoding="utf-8") as log:
        log.write("$ " + " ".join(argv) + "\n")
        p = subprocess.Popen(scoped(cores, timeout_s, argv), cwd=slot, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True, errors="replace", env=env,
                             start_new_session=True)
        timer = None
        for line in p.stdout:
            log.write(line)
            log.flush()
            if job is None and (mj := FAILED_JOB.search(line)):
                job = mj.group(1)
            if (me := ERR.search(line)):
                if all(e[0] != me.group(1) for e in errors):
                    cur = [me.group(1), int(me.group(2)), me.group(4).strip()]
                    errors.append(cur)
                    lines_after = 0
                    if stop_at_first and timer is None:  # let Lake print the message, then stop
                        timer = threading.Timer(5, stop_group, (p,))
                        timer.start()
                else:
                    cur = None
            elif cur is not None and lines_after < 6 and line.strip() \
                    and not line.startswith(("✖", "✔", "⚠", "trace:", "error:", "info:", "warning:", "Some required")):
                cur[2] += " " + line.strip()
                lines_after += 1
            elif line.startswith(("✖", "✔", "⚠")):
                cur = None
        rc = p.wait()
        if timer is not None:
            timer.cancel()
    return rc, errors, job, round(time.time() - t0, 1)


def stop_group(p):
    try:
        os.killpg(p.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    def later():
        time.sleep(15)
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    threading.Thread(target=later, daemon=True).start()


def module_of(path):
    path = path.removesuffix(".lean")
    i = path.find("RecursionFast/")
    return (path[i:] if i >= 0 else path).replace("/", ".")


def harness_stage(slot, cores, threads, mid, logs, accprobe=False):
    """The organiser tests that run compiled contract code: ("KILLED", by), ("SURVIVED", note) or
    ("ERROR", reason) (a build failure without a Lean error, or a test that timed out or was killed)."""
    rc, errs, job, _ = run_build(slot, cores, threads, ["lake", "-f", "scripts/speed/lakefile.toml", "build",
                                                       "extract", "signer"], os.path.join(logs, f"{mid}.exe.log"),
                                 stop_at_first=False)
    first = errs[0] if errs else None
    if rc != 0:
        if first:
            return "KILLED", f"build of extract/signer: {module_of(first[0])}"
        return "ERROR", f"extract/signer build failed without a Lean error (rc {rc}, {job})"
    tests = [("extract", [".lake/build/bin/extract"], 120)]
    svc = os.path.join(slot, "service", "target")
    if os.path.exists(os.path.join(svc, "test-keys", "release", "rf-oracle")):
        tests.append(("lean signer vs service", ["python3", "-I", "tests/service/test_lean_signer.py",
                                                 ".lake/build/bin/signer"], 300))
    if accprobe and os.path.exists(os.path.join(svc, "release", "rf-oracle")):
        tests.append(("accprobe", ["python3", "-I", "tests/harness/accprobe/run.py"], 3000))
    notes = []
    for name, argv, t in tests:
        with open(os.path.join(logs, f"{mid}.{name.replace(' ', '-')}.log"), "w") as log:
            r = subprocess.run(scoped(cores, t, argv), cwd=slot, stdout=log, stderr=subprocess.STDOUT,
                               env=dict(os.environ, LEAN_NUM_THREADS=str(threads)))
        if r.returncode in (124, 137, -9):  # timeout, or killed (out of memory)
            return "ERROR", f"harness: {name} timed out or was killed (exit {r.returncode})"
        if r.returncode != 0:
            return "KILLED", f"harness: {name} (exit {r.returncode})"
        notes.append(name)
    return "SURVIVED", "harness passed: " + ", ".join(notes)


def run_mutant(m, slot, cores, threads, logs, harness, every, targets=("RecursionFast",)):
    res = {"id": m["id"], "file": m["file"], "breaks": m["breaks"], "expect": m["expect"],
           "calibrate": m.get("calibrate", ""), "equivalent": m.get("equivalent", False)}
    t0 = time.time()
    try:
        sync_slot(slot)
        apply_mutant(slot, m)
    except Exception as e:  # noqa: BLE001
        return res | {"status": "ERROR", "by": f"setup: {e}", "seconds": round(time.time() - t0, 1)}
    rc, errs, job, s1 = run_build(slot, cores, threads, ["lake", "build", "RecursionFast.Contract"],
                                  os.path.join(logs, f"{m['id']}.contract.log"))
    first = errs[0] if errs else None
    res["stage_seconds"] = {"contract": s1}
    if first is not None:
        res |= {"status": "INVALID", "by": module_of(first[0]), "line": first[1], "error": first[2][:300]}
    elif rc != 0:
        res |= {"status": "ERROR", "by": f"contract build exit {rc} without a Lean error ({job})"}
    else:
        rc, errs, job, s2 = run_build(slot, cores, threads, ["lake", "build", *targets],
                                      os.path.join(logs, f"{m['id']}.build.log"), stop_at_first=not every)
        first = errs[0] if errs else None
        res["stage_seconds"]["build"] = s2
        if first is not None:
            res |= {"status": "KILLED", "stage": "proofs", "by": module_of(first[0]), "line": first[1],
                    "error": first[2][:300]}
            if every:
                res["failing"] = [[module_of(e[0]), e[1]] for e in errs]
        elif rc != 0:
            res |= {"status": "ERROR", "by": f"build exit {rc} without a Lean error ({job})"}
        elif harness:
            t3 = time.time()
            st, what = harness_stage(slot, cores, threads, m["id"], logs, harness == "accprobe")
            res["stage_seconds"]["harness"] = round(time.time() - t3, 1)
            res |= {"status": st, "stage": "harness", "by": what} if st != "SURVIVED" else {"status": st, "note": what}
        else:
            res |= {"status": "SURVIVED"}
    res["seconds"] = round(time.time() - t0, 1)
    return res


def write_results(out, results, ms):
    order = {m["id"]: i for i, m in enumerate(ms)}
    path = os.path.join(out, "results.json")
    old = {}
    if os.path.exists(path):
        old = {r["id"]: r for r in json.load(open(path))}
    old.update({r["id"]: r for r in results})
    rs = sorted((r for r in old.values() if r["id"] in order), key=lambda r: order[r["id"]])
    json.dump(rs, open(path, "w"), indent=1, ensure_ascii=False)
    open(path, "a").write("\n")
    accepted = {}
    ap = os.path.join(HERE, "accepted.toml")
    if os.path.exists(ap):
        with open(ap, "rb") as f:
            accepted = {a["id"]: a["reason"] for a in tomllib.load(f).get("accepted", [])}
    counts, per_file = {}, {}
    for r in rs:
        st = r["status"]
        if st == "SURVIVED" and r["id"] in accepted:
            st = "SURVIVED (accepted)"
        counts[st] = counts.get(st, 0) + 1
        pf = per_file.setdefault(r["file"], {})
        pf[st] = pf.get(st, 0) + 1
    lines = ["# Mutation testing of the trusted contract: results", "",
             "Generated by `python3 -I tests/mutation/run.py` (`tests/mutation/README.md`); do not edit by hand.",
             "Mutants: `tests/mutation/mutants.toml`. A mutant is KILLED by the first module whose build fails",
             "(stage `proofs`: the library and the controls) or by an organiser test (stage `harness`), INVALID",
             "if the contract itself no longer compiles, SURVIVED otherwise. An accepted survivor's reason, and a",
             "note on a mutant whose kill or invalidity is worth explaining, are in `tests/mutation/accepted.toml`.", "",
             "**Totals**: " + ", ".join(f"{k} {v}" for k, v in sorted(counts.items())), "",
             "| file | " + " | ".join(sorted(counts)) + " |", "|---|" + "---|" * len(counts)]
    for f, c in per_file.items():
        lines.append(f"| {f} | " + " | ".join(str(c.get(k, 0)) for k in sorted(counts)) + " |")
    lines += ["", "| id | file | breaks | status | killed by | s |", "|---|---|---|---|---|---|"]
    for r in rs:
        st = r["status"] + (" (calibration: expected to survive)" if r.get("calibrate") == "survive" else "")
        by = r.get("by", "")
        if r["status"] in ("KILLED", "INVALID") and r.get("line"):
            by = f"`{by}`:{r['line']}"
        elif by:
            by = f"`{by}`" if r["status"] == "KILLED" else by
        if r["status"] == "SURVIVED":
            by = accepted.get(r["id"], "**not killed**") + (f" ({r['note']})" if r.get("note") else "")
        elif r["id"] in accepted:
            by += f" ({accepted[r['id']]})"
        if r.get("failing") and len(r["failing"]) > 1:
            by += "; also " + ", ".join(f"`{f}`" for f, _ in r["failing"][1:])
        lines.append(f"| `{r['id']}` | {r['file']} | {r['breaks']} | {st} | {by} | {r.get('seconds', '')} |")
    lines.append("")
    open(os.path.join(out, "results.md"), "w").write("\n".join(lines))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--only", help="comma-separated mutant ids")
    ap.add_argument("--file", help="only the mutants of this contract file (e.g. Relation.lean)")
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--threads", type=int, default=4, help="LEAN_NUM_THREADS per job")
    ap.add_argument("--cores", default="16-20,21-25,26-31", help="taskset core list per job, ';'- or ','-separated ranges")
    ap.add_argument("--scratch", default=os.environ.get("RF_MUTATION_SCRATCH", ROOT + "-mutation"),
                    help="the slots' directory (default $RF_MUTATION_SCRATCH, else a sibling of this checkout)")
    ap.add_argument("--harness", action="store_true", help="stage 3 for mutants that survive the build")
    ap.add_argument("--accprobe", action="store_true",
                    help="stage 3 also runs accprobe (it links a badge executable against every object of the "
                         "organiser's closure: run org-setup step 4 in this checkout first, or Lake builds "
                         "missing package objects into the package tree)")
    ap.add_argument("--every", action="store_true",
                    help="build to the end and record every failing module (the controls among them)")
    ap.add_argument("--targets", default="RecursionFast",
                    help="comma-separated Lake targets of stage 2 (e.g. one control module, to check that it "
                         "kills a mutant on its own; results then go to --out, not merged with a full run)")
    ap.add_argument("--check", action="store_true", help="only check the mutants' original texts")
    ap.add_argument("--out", default=HERE)
    a = ap.parse_args()
    ms = load_mutants()
    bad = check_mutants(ms)
    if bad:
        print("\n".join(bad))
        return 1
    if a.check:
        print(f"{len(ms)} mutants, every original text found exactly once")
        return 0
    sel = ms
    if a.only:
        ids = a.only.split(",")
        unknown = set(ids) - {m["id"] for m in ms}
        if unknown:
            print(f"unknown ids: {sorted(unknown)}")
            return 1
        sel = [m for m in ms if m["id"] in ids]
    if a.file:
        sel = [m for m in sel if m["file"] == a.file]
    r = subprocess.run(["timeout", "300", "lake", "build", "--no-build", "RecursionFast"], cwd=ROOT,
                       capture_output=True, text=True)
    if r.returncode != 0:
        print("the checkout's build is not up to date: run `lake build` first\n" + r.stdout[-2000:])
        return 1
    if a.targets != "RecursionFast" and os.path.abspath(a.out) == HERE:
        print("--targets builds part of the library: give --out, so as not to merge into this directory's results")
        return 1
    if a.accprobe and not a.harness:
        print("--accprobe needs --harness")
        return 1
    cores = [c for c in re.split(r"[;,]", a.cores) if c]
    jobs = min(a.jobs, len(cores))
    logs = os.path.join(a.scratch, "logs")
    os.makedirs(logs, exist_ok=True)
    free = list(range(jobs))
    lock = threading.Lock()
    results = []

    def one(m):
        with lock:
            k = free.pop()
        try:
            r = run_mutant(m, os.path.join(a.scratch, f"s{k}"), cores[k], a.threads, logs,
                           ("accprobe" if a.accprobe else True) if a.harness else False, a.every,
                           a.targets.split(","))
        finally:
            with lock:
                free.append(k)
        with lock:
            results.append(r)
            write_results(a.out, results, ms)
            print(f"{r['id']:32} {r['status']:9} {r.get('by', '')[:70]:70} {r['seconds']:8.1f} s", flush=True)
        return r

    with ThreadPoolExecutor(jobs) as ex:
        list(ex.map(one, sel))
    counts = {}
    for r in results:
        counts[r["status"]] = counts.get(r["status"], 0) + 1
    print("totals:", counts)
    return 0


if __name__ == "__main__":
    sys.exit(main())
