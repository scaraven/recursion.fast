#!/usr/bin/env python3
"""The end-to-end smoke (`harness/smoke.toml`: r = 2, n = 16, M = 4).

  python3 tests/harness/smoke.py --org ORG [--work DIR] [--nanoda]     the whole evaluation
  python3 tests/harness/smoke.py --mock [--work DIR]                   the runner alone

With `--org` (ORG prepared by `harness/org-setup.sh`; the comparator from `scripts/tools.env`):
0. the witness-sending entry (`tests/harness/ws-entry/`: the library's submission, its claim) with
   the toy prover (`harness/toy-prover/honest/prover.s`, C compiled to x86-64 assembly) goes
   through `harness/evaluate.py cert` (source rule, comparator, gate, badge build) and must be
   certified;
1. `evaluate.py bench` of that entry through every part (calibration, tree, canaries, DoS, stream,
   liveness with the compiled extractor, score) with the compiled `accF` badge: verdict ACCEPT;
2. five deliberately broken provers, built from the same C source with one option each, through
   the T run with the same badge: a wrong chain end (`BROKEN_CHAIN`), an unsigned trace
   (`BROKEN_UNSIGNED`), a signature made by another run's service (`BROKEN_STALE`, the signature
   compiled into the binary): each REJECT, the root rejected by `acc`; a query above the service's
   cap (`BROKEN_CAP`): REJECT naming the service's refusal (Q13); unbounded allocation under a
   256 MiB cap (`BROKEN_OOM`): REJECT as killed out of memory (Q14);
3. the same entry with `certified := sorry`: PROVISIONAL (V4-15), not comparable;
4. an entry with `#eval` in its Lean source: REJECT by the source rule, nothing built;
5. the entry's module that `Solution` does not import is never built (Q7), and a Lean-kernel run
   over a 400 MiB budget is its own outcome, PROVISIONAL, not a failed certificate (Q12).
With `--mock`: steps 1 and 2 with the Python stand-in badge (`tests/harness/mock_badge/`), which
tests the runner without Lean.
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from rfh.sandbox import memcap_method  # noqa: E402
from rfh.service import Client, Service  # noqa: E402

SERVICE = os.path.join(ROOT, "service", "target", "release", "rf-oracle")
BENCH = os.path.join(ROOT, "service", "target", "release", "rf-bench")
TOY = os.path.join(ROOT, "harness", "toy-prover")


def run_bench(entry, badge, work, out, parts=None, season=None):
    cmd = [sys.executable, "-I", os.path.join(ROOT, "harness", "run-benchmark.py"), "--season",
           season or os.path.join(ROOT, "harness", "smoke.toml"), "--entry", entry, "--badge", badge, "--service", SERVICE,
           "--bench", BENCH, "--work", work, "--out", out]
    if parts:
        cmd += ["--parts", parts]
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=3600)
    print(p.stdout[-3000:], p.stderr[-2000:], sep="\n", flush=True)
    return json.load(open(out))


def entry_from(src_s, d):
    os.makedirs(os.path.join(d, "prover"))
    shutil.copy(src_s, os.path.join(d, "prover", "prover.s"))
    return d


def broken(tmp, flag, extra_header=None):
    d = os.path.join(tmp, f"src-{flag}")
    os.makedirs(d)
    if extra_header:
        with open(os.path.join(d, "stale_sig.h"), "w") as f:
            f.write(extra_header)
    s, raw = os.path.join(d, "prover.s"), os.path.join(d, "raw.s")
    subprocess.run(["gcc", "-S", "-O2", f"-D{flag}", "-I", d, "-o", raw, os.path.join(TOY, "toy.c")], check=True)
    # as the committed honest prover: accepted by the reference image's binutils 2.42 (RF-M2)
    subprocess.run([sys.executable, "-I", os.path.join(ROOT, "harness", "tools", "asm-compat.py"), raw, s], check=True)
    return entry_from(s, os.path.join(tmp, f"entry-{flag}"))


def evaluate(*args):
    p = subprocess.run([sys.executable, "-I", os.path.join(ROOT, "harness", "evaluate.py"), *args],
                       capture_output=True, text=True, timeout=7200)
    print(p.stdout[-2500:], p.stderr[-1500:], sep="\n", flush=True)


def ws_entry(tmp, name, prover_s, solution_patch=None):
    d = os.path.join(tmp, name)
    shutil.copytree(os.path.join(HERE, "ws-entry"), d)
    os.makedirs(os.path.join(d, "prover"))
    shutil.copy(prover_s, os.path.join(d, "prover", "prover.s"))
    if solution_patch:
        sol = os.path.join(d, "lean", "Solution.lean")
        src = open(sol).read()
        for old, new in solution_patch:
            assert old in src
            src = src.replace(old, new)
        open(sol, "w").write(src)
    return d


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--org", default=None)
    ap.add_argument("--work", default=None)
    ap.add_argument("--mock", action="store_true")
    ap.add_argument("--nanoda", action="store_true")
    a = ap.parse_args()
    tmp = a.work or tempfile.mkdtemp(prefix="rf-smoke-", dir=os.environ.get("RF_TEST_TMP"))
    os.makedirs(tmp, exist_ok=True)
    fails = []

    def check(cond, what):
        print(("ok   " if cond else "FAIL ") + what, flush=True)
        if not cond:
            fails.append(what)

    # a signature of the empty trace from another service (another run's key)
    other = Service(SERVICE, os.path.join(tmp, "other-service")).start()
    c = Client(other.socket_path)
    body = c.sign([])
    c.close()
    other.stop()
    header = "static const unsigned char stale_sig[4772] = {" + ",".join(str(b) for b in body) + "};\n"
    broken_entries = [(flag, broken(tmp, flag, hdr)) for flag, hdr in
                      (("BROKEN_CHAIN", None), ("BROKEN_UNSIGNED", None), ("BROKEN_STALE", header),
                       ("BROKEN_CAP", None), ("BROKEN_OOM", None))]
    # what each broken prover's rejection must say
    expect = {"BROKEN_CHAIN": "root rejected by acc", "BROKEN_UNSIGNED": "root rejected by acc",
              "BROKEN_STALE": "root rejected by acc",
              "BROKEN_CAP": "refused (status 2): a query above 2^20 bytes",            # Q13
              # Q14; under the prlimit fallback an allocation fails instead and the prover exits 1
              "BROKEN_OOM": "killed: out of memory (cap 256M" if memcap_method() == "systemd" else "prover tree exit 1"}
    lowmem = os.path.join(tmp, "smoke-256M.toml")    # the OOM prover runs under a 256 MiB cap
    open(lowmem, "w").write(open(os.path.join(ROOT, "harness", "smoke.toml")).read().replace('prover = "11G"', 'prover = "256M"'))
    season_of = lambda flag: lowmem if flag == "BROKEN_OOM" else os.path.join(ROOT, "harness", "smoke.toml")  # noqa: E731
    honest_s = os.path.join(TOY, "honest", "prover.s")

    if a.mock:
        badge = os.path.join(tmp, "badge")
        os.makedirs(badge)
        for f in os.listdir(os.path.join(HERE, "mock_badge")):
            shutil.copy(os.path.join(HERE, "mock_badge", f), badge)
        shutil.copy(os.path.join(ROOT, "tests", "service", "wots_ref.py"), badge)
        shutil.copy(os.path.join(ROOT, "harness", "rfh", "signed.py"), badge)
        honest = entry_from(honest_s, os.path.join(tmp, "entry-honest"))
        r = run_bench(honest, badge, os.path.join(tmp, "work-honest"), os.path.join(tmp, "result-honest.json"))
        check(r["benchmark"] == "pass", f"honest toy prover: {r['benchmark']} {r['reasons']}")
        results = {"honest": r}
        for flag, e in broken_entries:
            results[flag] = run_bench(e, badge, os.path.join(tmp, f"work-{flag}"), os.path.join(tmp, f"result-{flag}.json"),
                                      "calibrate,tree", season_of(flag))
    else:
        if not a.org:
            raise SystemExit("smoke: --org ORG or --mock")
        entry = ws_entry(tmp, "entry-ws", honest_s)
        cert = os.path.join(tmp, "cert.json")
        evaluate("cert", "--entry", entry, "--org", a.org, "--work", os.path.join(tmp, "cert"), "--out", cert,
                 *(["--nanoda"] if a.nanoda else []))
        cj = json.load(open(cert))
        check(cj["status"] == "ok", f"witness-sending entry certified: {cj['status']} {cj['reasons']} kernels {cj['kernels']}")
        check("Solution" in cj.get("built_modules", []) and "RfSmokeUnused" not in cj.get("built_modules", []),
              f"an entry module Solution does not import is never built (Q7): built {cj.get('built_modules')}")
        out = os.path.join(tmp, "result-honest.json")
        evaluate("bench", "--entry", entry, "--cert", cert, "--work", os.path.join(tmp, "work-honest"), "--out", out,
                 "--season", os.path.join(ROOT, "harness", "smoke.toml"))
        r = json.load(open(out))
        check(r.get("verdict") == "ACCEPT", f"honest toy prover with the compiled accF badge: {r.get('verdict')} {r.get('reasons')}")
        results = {"honest": r}
        for flag, e in broken_entries:
            out = os.path.join(tmp, f"result-{flag}.json")
            evaluate("bench", "--entry", e, "--cert", cert, "--work", os.path.join(tmp, f"work-{flag}"), "--out", out,
                     "--season", season_of(flag), "--parts", "calibrate,tree")
            results[flag] = json.load(open(out))
        # Q12: a kernel over its memory budget is its own outcome, never a failed certificate
        oc = os.path.join(tmp, "cert-overbudget.json")
        evaluate("cert", "--entry", entry, "--org", a.org, "--work", os.path.join(tmp, "cert-overbudget"), "--out", oc,
                 "--cert-mem", "400M")
        ob = json.load(open(oc))
        if memcap_method() == "systemd":
            check(ob["status"] == "provisional" and any("over its memory budget" in r for r in ob["provisional_reasons"])
                  and (ob.get("kernel_runs") or {}).get("lean", {}).get("outcome") == "over budget",
                  f"the Lean kernel over a 400M budget: {ob['status']}, {ob['provisional_reasons']}")
        else:      # an address-space limit cannot tell a kernel over budget from a failure
            check(ob["status"] != "ok", f"the Lean kernel over a 400M address-space limit is not certified: {ob['status']}")
        # 3. provisional: the same entry, its certificate left open
        pe = ws_entry(tmp, "entry-provisional", honest_s, [(
            "theorem certified : CertificateR declared submission :=\n", "theorem certified : CertificateR declared submission := by\n  sorry\n\nexample : CertificateR declared submission :=\n")])
        pc = os.path.join(tmp, "cert-provisional.json")
        evaluate("all", "--entry", pe, "--org", a.org, "--work", os.path.join(tmp, "provisional"), "--out", pc,
                 "--season", os.path.join(ROOT, "harness", "smoke.toml"), "--parts", "calibrate,tree")
        pr = json.load(open(pc))
        check(pr.get("verdict") == "PROVISIONAL" and pr.get("comparable") is False,
              f"an open certificate is PROVISIONAL and not comparable: {pr.get('verdict')} "
              f"{(pr.get('certificate') or {}).get('provisional_reasons')}")
        # 4. the source rule
        se = ws_entry(tmp, "entry-eval", honest_s, [("end RecursionFast.Challenge", "#eval 1\n\nend RecursionFast.Challenge")])
        sc = os.path.join(tmp, "cert-eval.json")
        evaluate("all", "--entry", se, "--org", a.org, "--work", os.path.join(tmp, "eval"), "--out", sc)
        sr = json.load(open(sc))
        check(sr.get("verdict") == "REJECT" and "source rule" in " ".join(sr["certificate"]["reasons"]),
              f"`#eval` in the entry: {sr.get('verdict')} {sr['certificate']['reasons'][:1]}")

    r = results["honest"]
    # RF-M1: the aggregation of this evaluation's one part ACCEPTs (or matches the certificate),
    # and with the part dropped it is ERROR, never ACCEPT
    cert_file = cert if not a.mock else os.path.join(tmp, "cert-mock.json")
    if a.mock:
        json.dump({"status": "ok", "reasons": []}, open(cert_file, "w"))
    agg = lambda files, out: (subprocess.run([sys.executable, "-I", os.path.join(ROOT, "harness", "aggregate.py"),  # noqa: E731
                                              "--plan", "single", "--season", os.path.join(ROOT, "harness", "smoke.toml"),
                                              "--cert", cert_file, "--out", out, *files], check=True,
                                             capture_output=True), json.load(open(out)))[1]
    whole = agg([os.path.join(tmp, "result-honest.json")], os.path.join(tmp, "agg-whole.json"))
    dropped = agg([], os.path.join(tmp, "agg-dropped.json"))
    check(whole["verdict"] == "ACCEPT" and dropped["verdict"] == "ERROR" and not dropped["comparable"],
          f"aggregate: the planned part gives {whole['verdict']}; the part dropped gives {dropped['verdict']} (RF-M1)")
    if r.get("benchmark") == "pass":
        sc = r["score"]
        check(all(k in sc for k in ("T_tree", "t_leaf", "t_merge", "t_link", "S")), f"score components: {sc}")
        check(r["liveness"]["ok"], f"liveness: {r['liveness']['output'][:120]}")
        check(r["tree"][0]["canaries"] > 0 and r["stream"][0]["canaries"] > 0,
              f"canaries rejected: tree {r['tree'][0]['canaries']}, stream {r['stream'][0]['canaries']}")
        check(r["dos"]["proofs"] > 0, f"DoS column: {r['dos']}")
    for flag, _ in broken_entries:
        rb = results[flag]
        why = " ".join(rb.get("reasons", []))
        check(rb.get("benchmark") == "fail" and rb.get("verdict", "REJECT") == "REJECT" and expect[flag] in why,
              f"{flag}: {rb.get('verdict', rb.get('benchmark'))}: {why[:400]}")
    print(f"\n{len(fails)} failure(s); results in {tmp}")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
