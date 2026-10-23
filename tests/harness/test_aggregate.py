#!/usr/bin/env python3
"""`harness/aggregate.py` requires exactly the planned benchmark parts (RF-M1).

  python3 tests/harness/test_aggregate.py

Six synthetic part results of the `split` plan give ACCEPT; one part dropped, one duplicated, one
with other parts, or two harness commits give ERROR; a failed part gives REJECT even with another
part missing; a rejected certificate gives REJECT; the `single` plan with no part gives ERROR.
"""
import json
import os
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
AGG = os.path.join(ROOT, "harness", "aggregate.py")
SEASON = os.path.join(ROOT, "harness", "smoke.toml")
PLAN = json.loads(subprocess.run([sys.executable, "-I", AGG, "--print-matrix", "split"], capture_output=True,
                                 text=True, check=True).stdout)


def part(parts, benchmark="pass", commit="a" * 40):
    r = {"parts": parts.split(","), "benchmark": benchmark, "reasons": [], "season_sha256": "s",
         "harness": {"commit": commit}, "machine": {"cpu_model": "cpu"}, "tree": [], "stream": []}
    if "tree" in parts:
        r["tree"] = [{"seconds": 1.0}]
    if "stream" in parts:
        r["stream"] = [{"t_leaf": 0.1, "t_merge": 0.1, "t_link": 0.2, "slowest_merge": 0.2}]
    return r


def run(tmp, parts, cert_status="ok", plan="split"):
    files = []
    for k, r in enumerate(parts):
        f = os.path.join(tmp, f"p{len(os.listdir(tmp))}-{k}.json")
        json.dump(r, open(f, "w"))
        files.append(f)
    cert = os.path.join(tmp, f"cert-{len(os.listdir(tmp))}.json")
    json.dump({"status": cert_status, "reasons": [] if cert_status != "reject" else ["x"]}, open(cert, "w"))
    out = os.path.join(tmp, f"out-{len(os.listdir(tmp))}.json")
    subprocess.run([sys.executable, "-I", AGG, "--plan", plan, "--season", SEASON, "--cert", cert, "--out", out, *files],
                   check=True, capture_output=True)
    return json.load(open(out))


def main():
    tmp = tempfile.mkdtemp(prefix="rf-agg-", dir=os.environ.get("RF_TEST_TMP"))
    full = [part(p) for p in PLAN]
    fails = 0

    def check(r, verdict, what):
        nonlocal fails
        ok = r["verdict"] == verdict and (r["comparable"] is (verdict == "ACCEPT"))
        print(("ok   " if ok else "FAIL ") + f"{what}: {r['verdict']}, comparable {r['comparable']}")
        fails += not ok
    check(run(tmp, full), "ACCEPT", "the six planned parts")
    check(run(tmp, full[1:]), "ERROR", "job 0 (DoS, liveness) missing")
    check(run(tmp, full[:5]), "ERROR", "a stream part missing")
    check(run(tmp, full + [part(PLAN[3])]), "ERROR", "a stream part duplicated")
    check(run(tmp, full[:2] + [part("calibrate,stream")] + full[3:]), "ERROR", "a tree part replaced by a stream part")
    check(run(tmp, full[:5] + [part(PLAN[5], commit="b" * 40)]), "ERROR", "a part from another harness commit")
    check(run(tmp, full[1:4] + [part(PLAN[4], benchmark="fail")]), "REJECT", "a failed part, others missing")
    check(run(tmp, full, cert_status="reject"), "REJECT", "a rejected certificate")
    check(run(tmp, [], plan="single"), "ERROR", "the single plan with no part")
    check(run(tmp, [part("calibrate,tree,dos,stream,liveness")], plan="single"), "ACCEPT", "the single plan's one part")
    print(f"{fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
