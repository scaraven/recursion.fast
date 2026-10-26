#!/usr/bin/env python3
"""`harness/aggregate.py` requires exactly the planned benchmark parts (RF-M1).

  python3 tests/harness/test_aggregate.py

The two synthetic part results of the `split` plan (the tree job, the stream job) give ACCEPT,
scored from the one tree run and the one stream run (V4-A9: no repeats, no medians); one part
dropped, one duplicated, one with other parts, or two harness commits give ERROR; a failed part
gives REJECT even with the other part missing; a rejected certificate gives REJECT; the `single`
plan with no part gives ERROR.
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
    return {"parts": parts.split(","), "benchmark": benchmark, "reasons": [], "season_sha256": "s",
            "harness": {"commit": commit}, "machine": {"cpu_model": "cpu"},
            "tree": {"seconds": 1.0} if "tree" in parts else None,
            "stream": {"t_leaf": 0.1, "t_merge": 0.1, "t_link": 0.2, "slowest_merge": 0.2} if "stream" in parts else None}


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

    def holds(ok, what):
        nonlocal fails
        print(("ok   " if ok else "FAIL ") + what)
        fails += not ok
    holds(PLAN == ["calibrate,tree,dos", "calibrate,stream"], f"two parallel jobs, tree and stream: {PLAN}")
    r = run(tmp, full)
    check(r, "ACCEPT", "the two planned parts")
    sc = r.get("score", {})
    holds(sc.get("T_tree") == 1.0 and sc.get("t_link") == 0.2 and abs(sc.get("S", 0) - 5.0) < 1e-9
          and not any("repeats" in k or "median" in k for k in sc), f"the score is the single runs', S = T_tree + K · t_link: {sc}")
    check(run(tmp, full[1:]), "ERROR", "the tree job (tree, DoS) missing")
    check(run(tmp, full[:1]), "ERROR", "the stream job missing")
    check(run(tmp, full + [part(PLAN[1])]), "ERROR", "the stream part duplicated")
    check(run(tmp, [part("calibrate,stream")] + full[1:]), "ERROR", "the tree part replaced by a stream part")
    check(run(tmp, full[:1] + [part(PLAN[1], commit="b" * 40)]), "ERROR", "a part from another harness commit")
    check(run(tmp, [part(PLAN[1], benchmark="fail")]), "REJECT", "a failed part, the other missing")
    check(run(tmp, full, cert_status="reject"), "REJECT", "a rejected certificate")
    check(run(tmp, [], plan="single"), "ERROR", "the single plan with no part")
    check(run(tmp, [part("calibrate,tree,dos,stream")], plan="single"), "ACCEPT", "the single plan's one part")
    print(f"{fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
