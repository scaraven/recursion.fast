#!/usr/bin/env python3
"""The evaluation of one entry, in the harness order (TRUSTED RUNTIME; v3 §9.3 as amended by
V4-A1, V4-A2, V4-15).

  python3 -I harness/evaluate.py cert  --entry ENTRY --org ORG --work WORK --out CERT.json [--nanoda]
  python3 -I harness/evaluate.py bench --entry ENTRY --cert CERT.json --work WORK --out RESULT.json
                                       [--season harness/season.toml] [run-benchmark options]
  python3 -I harness/evaluate.py all   --entry ENTRY --org ORG --work WORK --out RESULT.json [...]

ENTRY: `claim.json` (the declared numbers: `error`, `completeness_error` as "a/b" strings, `qV`,
`fuel_base`, `fuel_per_word` as integers), `lean/*.lean` (the solution; `lean/Solution.lean`
defines `RecursionFast.Challenge.submission` and proves `RecursionFast.Challenge.certified`), and
`prover/*.s`. ORG: the organiser's checkout, built, with its package tree, its olean manifest
(`ORG/.lake/rf/manifest.sha256`) and import allowlist (`ORG/.lake/rf/allowlist.txt`) written by
`harness/org-setup.sh` before any entry code ran.

The certificate job (`cert`; deterministic, any machine with the package tree):
  1. render the challenge from the organiser's stub and the claim (the entry supplies no stub);
  2. the source rule on the entry's Lean files (no elaboration-time code);
  3. the comparator in a fresh tree: it builds the solution in the sandbox (`scripts/bwrap-landrun.sh`)
     and replays the exported proof of `certified` against the rendered statement in the Lean
     kernel, and in nanoda with `--nanoda` (the result says which kernels ran); the organiser's
     oleans are checked against the manifest before and after;
  4. a second fresh tree at the same path: the comparator's targets (the challenge and the
     solution's import closure) built again in the sandbox, every artifact byte-identical to the
     comparator-verified build and no other artifact; the gate (rules 1–8, badge fields V, P, ext)
     in the sandbox. Entry modules that `Solution` does not import are never built (Q7);
  5. the badge executables (`verify`, `liveness`) rendered from `harness/badge/*.lean.in` and built
     in the sandbox in that tree, which must neither build nor change an entry module (the badge's
     import closure lies inside the verified one); the organiser's `chaincheck` copied beside them.
  Status: `ok` (certified), `provisional` (everything builds and the only failures are an
  incomplete certificate: the comparator's verdict and gate rule 1's `sorryAx`), `reject`.
The benchmark job (`bench`; the GitHub-hosted runner): `harness/run-benchmark.py` with the badge.
Verdict: ACCEPT (certificate ok, benchmark pass), PROVISIONAL (certificate provisional, benchmark
pass; never ranked, V4-15, its numbers marked uncomparable), REJECT (anything else).
"""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
sys.path.insert(0, HERE)
from rfh.sandbox import Sandbox, kill_unit, memcap, scope_oom  # noqa: E402

TIMEOUT = 3600
CHALLENGE_MODULE, SOLUTION_MODULE = "Challenge", "Solution"


class Reject(Exception):
    pass


def sh(cmd, cwd=None, env=None, timeout=TIMEOUT, log=None):
    """Run a trusted command (outside the sandbox); its output goes to `log`."""
    with open(log, "ab") if log else open(os.devnull, "wb") as f:
        return subprocess.run(cmd, cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT, timeout=timeout).returncode


def lean_prefix(org):
    return subprocess.run(["lean", "--print-prefix"], cwd=org, capture_output=True, text=True, check=True).stdout.strip()


def packages_dir(org):
    m = json.load(open(os.path.join(org, "lake-manifest.json")))
    return os.path.realpath(os.path.join(org, m.get("packagesDir") or ".lake/packages"))


def entry_modules(entry):
    d = os.path.join(entry, "lean")
    files = sorted(f for f in os.listdir(d) if f.endswith(".lean")) if os.path.isdir(d) else []
    for f in files:
        p = os.path.join(d, f)
        if os.path.islink(p) or not os.path.isfile(p):
            raise Reject(f"lean/{f} is not a regular file")
    if f"{SOLUTION_MODULE}.lean" not in files:
        raise Reject(f"lean/{SOLUTION_MODULE}.lean is missing")
    return files


def mkfresh(t, org, entry, challenge, files):
    """A fresh tree `t`: the rendered challenge, the entry's Lean files, a lakefile and manifest that
    require ORG by path; every module root fresh (no organiser or package module shadowed)."""
    os.makedirs(os.path.join(t, "challenge"))
    os.makedirs(os.path.join(t, "submission"))
    shutil.copy(os.path.join(org, "lean-toolchain"), t)
    shutil.copy(challenge, os.path.join(t, "challenge", f"{CHALLENGE_MODULE}.lean"))
    for f in files:
        shutil.copy(os.path.join(entry, "lean", f), os.path.join(t, "submission", f))
    pk = packages_dir(org)
    dirs = [os.path.join(org, ".lake/build/lib/lean"), os.path.join(lean_prefix(org), "lib/lean")]
    dirs += [os.path.join(pk, p, ".lake/build/lib/lean") for p in os.listdir(pk)]
    mods = [f[:-5] for f in files]
    for r in sorted({m.split(".")[0] for m in mods + [CHALLENGE_MODULE]}):
        for d in dirs:
            if os.path.isdir(os.path.join(d, r)) or os.path.exists(os.path.join(d, r + ".olean")):
                raise Reject(f"module root {r} exists in {d}")
    q = lambda xs: "[" + ", ".join(json.dumps(x) for x in xs) + "]"  # noqa: E731
    lib = lambda n, src, roots: f'[[lean_lib]]\nname = "{n}"\nsrcDir = "{src}"\nroots = {q(roots)}\n'  # noqa: E731
    with open(os.path.join(t, "lakefile.toml"), "w") as f:
        f.write(f'name = "rfentry"\npackagesDir = {json.dumps(pk)}\n[[require]]\nname = "RecursionFast"\n'
                f'path = {json.dumps(org)}\n' + lib("RFChallenge", "challenge", [CHALLENGE_MODULE])
                + lib("RFSubmission", "submission", mods))
    m = json.load(open(os.path.join(org, "lake-manifest.json")))
    for p in m["packages"]:
        p["inherited"] = True
    m["packages"].insert(0, {"type": "path", "scope": "", "name": "RecursionFast", "manifestFile": "lake-manifest.json",
                             "inherited": False, "dir": org, "configFile": "lakefile.toml"})
    m["name"], m["packagesDir"] = "rfentry", pk
    json.dump(m, open(os.path.join(t, "lake-manifest.json"), "w"), indent=1)


def artifacts(t):
    """sha256 of the build artifacts of the tree `t` (no link or special file allowed)."""
    out = {}
    b = os.path.join(t, ".lake", "build")
    for d in ("lib/lean", "ir"):
        for dp, dns, fns in os.walk(os.path.join(b, d)):
            for fn in fns:
                p = os.path.join(dp, fn)
                if os.path.islink(p) or not os.path.isfile(p):
                    raise Reject(f"build artifact {p} is not a regular file")
                if fn.endswith((".olean", ".olean.server", ".olean.private", ".ir", ".c")):
                    out[os.path.relpath(p, b)] = hashlib.sha256(open(p, "rb").read()).hexdigest()
    return out


class Org:
    """The organiser side: checkout, toolchain, packages, manifest, allowlist, tool binaries."""

    def __init__(self, org):
        self.dir = os.path.abspath(org)
        self.prefix = lean_prefix(self.dir)
        self.packages = packages_dir(self.dir)
        rf = os.path.join(self.dir, ".lake", "rf")
        self.manifest, self.allowlist = os.path.join(rf, "manifest.sha256"), os.path.join(rf, "allowlist.txt")
        self.tools = os.path.join(REPO, "harness", "lean-tools", ".lake", "build", "bin")
        for p in (self.manifest, self.allowlist, os.path.join(self.tools, "gate"), os.path.join(self.tools, "chaincheck")):
            if not os.path.exists(p):
                raise SystemExit(f"evaluate: {p} missing (run harness/org-setup.sh first)")

    def ro_roots(self, *more):
        """What a sandboxed Lean step may read: the system's /usr, the toolchain, the organiser
        checkout and packages, and `more`."""
        return ("/usr", "/bin", "/lib", "/lib64", "/etc/ld.so.cache", self.prefix, self.dir, self.packages) + more

    def manifest_ok(self, log):
        return sh([sys.executable, "-I", os.path.join(REPO, "scripts", "olean-manifest.py"), "check", "--org", self.dir,
                   self.manifest], log=log) == 0


def sandboxed(org, cmd, tree, log, rw=(), mem="12G", env=None, timeout=TIMEOUT, extra=()):
    """Run `cmd` in the sandbox with `tree` visible at its own path (read-only unless in `rw`)."""
    binds = [("ro", tree, tree)] + [("rw", p, p) for p in rw]      # parents first: rw paths lie in the tree
    e = {"PATH": f"{org.prefix}/bin:/usr/bin:/bin", "HOME": tree, "LAKE_NO_CACHE": "1"}
    e.update(env or {})
    with open(log, "ab") as f:
        sb = Sandbox(cmd, binds, mem, env=e, cwd=tree, stdout=f, stderr=subprocess.STDOUT,
                     extra_ro_root=org.ro_roots(*extra))
        try:
            return sb.proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            return "timeout"
        finally:
            sb.kill()


def cert_job(a):
    org = Org(a.org)
    work = os.path.abspath(a.work)
    os.makedirs(work, exist_ok=False)
    entry = os.path.abspath(a.entry)
    res = {"stage": "certificate", "kernels": [], "reasons": [], "provisional_reasons": []}
    logs = {k: os.path.join(work, f"{k}.log") for k in ("render", "source-rule", "build", "gate", "badge", "manifest")}
    try:
        files = entry_modules(entry)
        # 1. the challenge
        challenge = os.path.join(work, f"{CHALLENGE_MODULE}.lean")
        if sh([sys.executable, "-I", os.path.join(HERE, "render-challenge.py"), os.path.join(HERE, "challenge",
               "Challenge.lean.in"), os.path.join(entry, "claim.json"), challenge], log=logs["render"]):
            raise Reject("claim does not render: " + open(logs["render"]).read()[-300:])
        res["claim"] = json.load(open(os.path.join(entry, "claim.json")))
        # 2. the source rule
        sr = os.path.join(work, "sr")
        os.makedirs(sr)
        for f in files:
            shutil.copy(os.path.join(entry, "lean", f), sr)
        if sh([sys.executable, "-I", os.path.join(REPO, "scripts", "source-rule.py"), sr], log=logs["source-rule"]):
            raise Reject("source rule: " + open(logs["source-rule"]).read()[-600:])
        # 3. the comparator, fresh tree
        if not org.manifest_ok(logs["manifest"]):
            raise Reject("organiser build does not match the olean manifest")
        tree = os.path.join(work, "tree")
        mkfresh(tree, org.dir, entry, challenge, files)
        home = os.environ.get("COMPARATOR_HOME", "")
        cmp_bin = os.path.join(home, ".lake", "build", "bin", "comparator")
        export = os.environ.get("COMPARATOR_LEAN4EXPORT",
                                os.path.join(home, ".lake/packages/lean4export/.lake/build/bin/lean4export"))
        if not (os.access(cmp_bin, os.X_OK) and os.access(export, os.X_OK)):
            raise Reject("harness error: the comparator or lean4export is missing (scripts/tools.env)")
        env = dict(os.environ, COMPARATOR_LANDRUN=os.path.join(REPO, "scripts", "bwrap-landrun.sh"),
                   COMPARATOR_LEAN4EXPORT=export, RF_LANDRUN_MINIMAL="1",
                   RF_LANDRUN_RO=":".join(org.ro_roots(home, os.path.dirname(export))))

        def kernel_run(kernel, mem):
            """One comparator run in its own memory-capped scope (Q12): `lean` checks with the Lean
            kernel alone; `nanoda` adds nanoda (the comparator then also re-runs the Lean kernel).
            Its outcome: ok, rejected, over budget (the scope was killed for memory) or timeout."""
            cfg = {"challenge_module": CHALLENGE_MODULE, "solution_module": SOLUTION_MODULE,
                   "theorem_names": ["RecursionFast.Challenge.certified"],
                   "definition_names": ["RecursionFast.Challenge.submission"],
                   "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"], "enable_nanoda": kernel == "nanoda"}
            json.dump(cfg, open(os.path.join(tree, f"config-{kernel}.json"), "w"))
            e = dict(env)
            if kernel == "nanoda":
                e["COMPARATOR_NANODA"] = os.environ["COMPARATOR_NANODA"]
                e["RF_LANDRUN_RO"] += ":" + os.path.dirname(os.path.abspath(os.environ["COMPARATOR_NANODA"]))
            unit, log = f"rf-cmp-{kernel}-{os.getpid()}", os.path.join(work, f"comparator-{kernel}.log")
            t0 = time.monotonic()
            try:
                rc = sh(memcap(mem, unit) + ["lake", "env", cmp_bin, f"config-{kernel}.json"], cwd=tree, env=e, log=log,
                        timeout=a.timeout)
            except subprocess.TimeoutExpired:
                rc = "timeout"
                kill_unit(unit)
            oom, peak = scope_oom(unit)
            out = open(log, errors="replace").read()
            outcome = "ok" if rc == 0 else "over budget" if oom else "timeout" if rc == "timeout" else "rejected"
            return {"outcome": outcome, "exit": rc, "seconds": round(time.monotonic() - t0, 1), "cap": mem,
                    "peak_bytes": peak, "tail": out[-1500:]}

        # RB-m2: a run's exit code decides (the comparator runs outside the sandbox; its log also holds
        # the entry's build output, so no substring of it is trusted)
        lean = kernel_run("lean", a.cert_mem)
        res["kernel_runs"] = {"lean": lean}
        res["comparator_s"] = lean["seconds"]
        if not org.manifest_ok(logs["manifest"]):
            raise Reject("organiser .olean changed during the comparator run")
        unchecked = lean["outcome"] in ("over budget", "timeout")     # Q12: the kernel's budget, not the entry
        if not unchecked and not os.path.isdir(os.path.join(tree, ".lake", "build", "lib", "lean")):
            raise Reject("the solution does not build (comparator log: " + lean["tail"][-400:] + ")")
        budget = lambda r: f"cap {r['cap']}" + (f", peak {r['peak_bytes'] / 2 ** 30:.2f} GiB" if r["peak_bytes"] else "")  # noqa: E731
        res["kernels"] = ["lean"] if lean["outcome"] == "ok" else []
        if lean["outcome"] == "rejected":
            res["provisional_reasons"].append(f"comparator (Lean kernel): exit {lean['exit']}, the certificate does not check")
        elif lean["outcome"] == "over budget":
            res["provisional_reasons"].append(f"the Lean kernel ran over its memory budget ({budget(lean)}): "
                                              "the certificate is unchecked, not refuted")
        elif lean["outcome"] == "timeout":
            res["provisional_reasons"].append(f"the Lean kernel timed out after {a.timeout} s: the certificate is unchecked")
        if not a.nanoda:
            res["second_kernel"] = "not run (no --nanoda): checked by the Lean kernel only (V4-A2)"
        elif lean["outcome"] != "ok":
            res["second_kernel"] = "not run: the Lean kernel did not accept"
        else:
            nan = kernel_run("nanoda", a.nanoda_mem)
            res["kernel_runs"]["nanoda"] = nan
            if not org.manifest_ok(logs["manifest"]):
                raise Reject("organiser .olean changed during the nanoda run")
            if nan["outcome"] == "ok":
                res["kernels"].append("nanoda")
                res["second_kernel"] = "nanoda: accepted"
            elif nan["outcome"] == "rejected":
                res["second_kernel"] = "nanoda: rejected"
                res["provisional_reasons"].append("nanoda rejected the certificate the Lean kernel accepted")
            else:      # over budget or timeout: no second check, the Lean kernel's verdict stands (V4-A2)
                res["second_kernel"] = f"nanoda: {nan['outcome']} ({budget(nan)}); checked by the Lean kernel only"
        cmp_arts = artifacts(tree)
        os.rename(tree, os.path.join(work, "cmp"))
        # 4. second tree, same path: rebuild in the sandbox, bind to the comparator's build, gate
        mkfresh(tree, org.dir, entry, challenge, files)
        lake = os.path.join(org.prefix, "bin", "lake")
        os.makedirs(os.path.join(tree, ".lake"))
        # Q7: exactly the comparator's targets, the challenge and the solution's import closure; an
        # entry module that `Solution` does not import is never built by the harness
        rc = sandboxed(org, [lake, "build", f"+{CHALLENGE_MODULE}", f"+{SOLUTION_MODULE}"], tree, logs["build"],
                       rw=(os.path.join(tree, ".lake"),), timeout=a.timeout)
        if rc != 0:
            raise Reject(f"the solution does not build in the gate tree ({rc}): " + open(logs["build"], errors="replace").read()[-400:])
        if not org.manifest_ok(logs["manifest"]):
            raise Reject("organiser .olean changed during the solution build")
        arts = artifacts(tree)
        diff = sorted(k for k in set(arts) | set(cmp_arts) if cmp_arts.get(k) != arts.get(k))
        if unchecked:      # no comparator-verified build to bind to; the entry stays provisional
            res["binding"] = "not checked: the comparator's Lean-kernel run did not finish"
        elif diff:
            raise Reject(f"the gate tree's build differs from the comparator-verified build ({len(diff)} artifacts, e.g. {diff[:3]})")
        else:
            res["binding"] = f"byte-identical ({len(arts)} artifacts)"
        res["built_modules"] = sorted(k[len("lib/lean/"):-len(".olean")].replace("/", ".") for k in arts
                                      if k.startswith("lib/lean/") and k.endswith(".olean"))
        lp = subprocess.run([lake, "env", "printenv", "LEAN_PATH"], cwd=tree, capture_output=True, text=True).stdout.strip()
        gate = os.path.join(org.tools, "gate")
        rc = sandboxed(org, [gate, SOLUTION_MODULE, "RecursionFast.Challenge.certified", "--manifest", org.manifest,
                             "--computable", "RecursionFast.Challenge.submission", "--allowed-imports", org.allowlist,
                             "--badge-root", "RecursionFast.Challenge.submission"],
                       tree, logs["gate"], env={"LEAN_PATH": lp}, extra=(org.tools, os.path.dirname(org.manifest)))
        rejects = [l for l in open(logs["gate"], errors="replace").read().splitlines() if l.startswith("gate: REJECT")]
        res["gate"] = rejects or ["PASS"]
        open_cert = ("gate: REJECT closure uses sorryAx", "gate: REJECT non-standard axiom sorryAx")
        hard = [l for l in rejects if l not in open_cert]      # only an open certificate may be provisional
        if hard or (rc != 0 and not rejects):
            raise Reject("gate: " + "; ".join(hard[:5] or [f"exit {rc}"]))
        if rejects:
            res["provisional_reasons"].append("gate rule 1: the certificate's closure uses sorryAx")
        # 5. the badge
        badge = build_badge(org, tree, res["claim"], logs["badge"], a.timeout)
        # Q7: the badge's import closure lies inside the verified one: its build adds no entry
        # module and changes no verified artifact
        after = {k: v for k, v in artifacts(tree).items() if "/RFBadge" not in "/" + k.split("/", 2)[-1]}
        moved = sorted(k for k in set(after) | set(arts) if after.get(k) != arts.get(k))
        if moved:
            raise Reject(f"the badge build built or changed entry modules outside the verified closure: {moved[:3]}")
        res["badge_dir"] = badge
        res["badge_sha256"] = {b: hashlib.sha256(open(os.path.join(badge, b), "rb").read()).hexdigest()
                               for b in os.listdir(badge)}
        res["status"] = "provisional" if res["provisional_reasons"] else "ok"
    except Reject as e:
        res["status"] = "reject"
        res["reasons"].append(str(e))
    except subprocess.TimeoutExpired as e:
        res["status"] = "reject"
        res["reasons"].append(f"timeout: {e.cmd[0] if e.cmd else ''}")
    json.dump(res, open(a.out, "w"), indent=1)
    print(f"certificate: {res['status']} {res['reasons'] or res['provisional_reasons']}")
    return res


def build_badge(org, tree, claim, log, timeout):
    """Render the badge executables into `tree` (`harness/badge/*.lean.in`: the solution module and
    the claim's declared fuel) and build them in the sandbox; returns the directory holding
    `verify`, `liveness` and the organiser's `chaincheck`."""
    bdir = os.path.join(tree, "badge")
    os.makedirs(bdir)
    subst = {"{{solution_module}}": SOLUTION_MODULE}
    for k in ("fuel_base", "fuel_per_word"):
        v = claim.get(k)
        if type(v) is not int or not 0 <= v < 2 ** 64:
            raise Reject(f"claim: {k} is not a natural number below 2^64")
        subst["{{" + k + "}}"] = str(v)
    for name in ("Common", "Verify", "Liveness"):
        src = open(os.path.join(HERE, "badge", f"{name}.lean.in")).read()
        for k, v in subst.items():
            src = src.replace(k, v)
        open(os.path.join(bdir, f"RFBadge{name}.lean"), "w").write(src)
    with open(os.path.join(tree, "lakefile.toml"), "a") as f:
        f.write('\n[[lean_lib]]\nname = "RFBadge"\nsrcDir = "badge"\nroots = ["RFBadgeCommon"]\n')
        for exe, root in (("verify", "RFBadgeVerify"), ("liveness", "RFBadgeLiveness")):
            f.write(f'\n[[lean_exe]]\nname = "{exe}"\nsrcDir = "badge"\nroot = "{root}"\n')
    # An executable links the compiled object of every module it imports. `org-setup.sh` built those
    # of the organiser's closure; the objects of other modules an entry imports are compiled here,
    # into the package tree, so its build directories are writable for this step. No entry code runs
    # in it (the entry's modules are loaded, not elaborated; gate rule 3 excludes load-time code),
    # and the olean manifest is checked afterwards.
    rw = [os.path.join(tree, ".lake"), os.path.join(org.dir, ".lake", "build")]
    rw += [os.path.join(org.packages, p, ".lake") for p in sorted(os.listdir(org.packages))
           if os.path.isdir(os.path.join(org.packages, p, ".lake"))]
    rc = sandboxed(org, [os.path.join(org.prefix, "bin", "lake"), "build", "verify", "liveness"], tree, log,
                   rw=tuple(rw), timeout=timeout)
    if rc != 0:
        raise Reject(f"badge build failed ({rc}): " + open(log, errors="replace").read()[-400:])
    if not org.manifest_ok(log):
        raise Reject("organiser .olean changed during the badge build")
    out = os.path.join(os.path.dirname(tree), "badge")
    os.makedirs(out)
    for exe in ("verify", "liveness"):
        shutil.copy(os.path.join(tree, ".lake", "build", "bin", exe), out)
    shutil.copy(os.path.join(org.tools, "chaincheck"), out)
    return out


def bench_job(a, cert):
    cmd = [sys.executable, "-I", os.path.join(HERE, "run-benchmark.py"), "--season", a.season, "--entry", a.entry,
           "--badge", cert["badge_dir"], "--service", a.service, "--bench", a.bench, "--work", a.work, "--out", a.out]
    if cert["status"] == "provisional":
        cmd.append("--provisional")
    for k in ("parts", "tree_repeats", "stream_repeats"):
        if getattr(a, k):
            cmd += [f"--{k.replace('_', '-')}", str(getattr(a, k))]
    subprocess.run(cmd, timeout=24 * 3600)
    res = json.load(open(a.out))
    res["certificate"] = {k: cert.get(k) for k in ("status", "reasons", "provisional_reasons", "kernels", "second_kernel",
                                                   "kernel_runs", "binding", "gate", "badge_sha256", "claim",
                                                   "built_modules")}
    ok = res["benchmark"] == "pass"
    res["verdict"] = ("ACCEPT" if cert["status"] == "ok" else "PROVISIONAL") if ok and cert["status"] != "reject" else "REJECT"
    res["comparable"] = res["verdict"] == "ACCEPT"
    json.dump(res, open(a.out, "w"), indent=1)
    print(f"VERDICT: {res['verdict']}")
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["cert", "bench", "all"])
    ap.add_argument("--entry", required=True)
    ap.add_argument("--org")
    ap.add_argument("--work", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--cert")
    ap.add_argument("--nanoda", action="store_true")
    ap.add_argument("--timeout", type=int, default=TIMEOUT)
    ap.add_argument("--cert-mem", default="14G", help="memory cap of the comparator run with the Lean kernel")
    ap.add_argument("--nanoda-mem", default="14G", help="memory cap of the comparator run with nanoda")
    ap.add_argument("--season", default=os.path.join(HERE, "season.toml"))
    ap.add_argument("--service", default=os.path.join(REPO, "service", "target", "release", "rf-oracle"))
    ap.add_argument("--bench", default=os.path.join(REPO, "service", "target", "release", "rf-bench"))
    ap.add_argument("--parts")
    ap.add_argument("--tree-repeats", type=int)
    ap.add_argument("--stream-repeats", type=int)
    a = ap.parse_args()
    if a.mode == "bench":
        res = bench_job(a, json.load(open(a.cert)))
    else:
        out, work = a.out, a.work
        a.out, a.work = (out if a.mode == "cert" else out + ".cert.json"), (work if a.mode == "cert" else work + "/cert")
        if a.mode == "all":
            os.makedirs(work)
        cert = cert_job(a)
        if a.mode == "cert":
            return 0 if cert["status"] != "reject" else 1
        a.out, a.work = out, work + "/bench"
        if cert["status"] == "reject":
            res = {"verdict": "REJECT", "certificate": cert}
            json.dump(res, open(out, "w"), indent=1)
            print("VERDICT: REJECT")
            return 1
        res = bench_job(a, cert)
    return 0 if res["verdict"] in ("ACCEPT", "PROVISIONAL") else 1


if __name__ == "__main__":
    sys.exit(main())
