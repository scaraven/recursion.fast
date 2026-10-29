#!/usr/bin/env python3
"""`harness/aggregate.py` requires exactly the planned benchmark part (RF-M1) and recomputes the score
(V4-A11), and `--rank` ranks provisionally (R-M1).

  python3 tests/harness/test_aggregate.py

Since V4-A11 the plan is one job (`split` and `single` both): its part gives ACCEPT, scored from the
stream's per-step records with `rfh.bench.score` (the S the runner wrote is ignored); the part
dropped, duplicated, replaced by another part set, or two harness commits give ERROR; a failed part
gives REJECT; a rejected certificate gives REJECT; a truncated stream is ACCEPTed but not comparable.
The ranking takes, per entry (not per binary), the median of its last three evaluations, a REJECT or a
truncated run counting as its worst, and ranks only from three evaluations (review M-4).
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


def part(parts, benchmark="pass", commit="a" * 40, truncated=False, P=1.0):
    steps = [{"index": i, "n": 1 << 18, "P_s": P, "V_ns": 0, "pi_bytes": 0} for i in (1, 2)]
    return {"parts": parts.split(","), "benchmark": benchmark, "reasons": [], "season_sha256": "s",
            "harness": {"commit": commit}, "machine": {"cpu_model": "cpu"}, "prover": {"binary_sha256": "h"},
            "score": {"S": 999.0},
            "stream": {"steps": steps, "truncated": truncated,
                       "calibration": {"c_P": 1.0, "v_ref_ns": 177.8e6, "T_triv_ns": 1.778e9}}}


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
    full = [part("calibrate,stream,dos")]
    fails = 0

    def check(r, verdict, what, comparable=None):
        nonlocal fails
        want = (verdict == "ACCEPT") if comparable is None else comparable
        ok = r["verdict"] == verdict and r["comparable"] is want
        print(("ok   " if ok else "FAIL ") + f"{what}: {r['verdict']}, comparable {r['comparable']}")
        fails += not ok

    def holds(ok, what):
        nonlocal fails
        print(("ok   " if ok else "FAIL ") + what)
        fails += not ok
    holds(PLAN == ["all"], f"one benchmark job (V4-A11): {PLAN}")
    r = run(tmp, full)
    check(r, "ACCEPT", "the planned part")
    sc = r.get("score", {})
    holds(abs(sc.get("S", 0) - 1.0) < 1e-9 and sc.get("M") == 2,
          f"the score is recomputed from the steps (two steps of 1 s at n_ref, V = 0: S = 1, not the part's 999): {sc.get('S')}")
    check(run(tmp, full, plan="single"), "ACCEPT", "the single plan's one part")
    check(run(tmp, []), "ERROR", "the part missing")
    check(run(tmp, full + full), "ERROR", "the part duplicated")
    check(run(tmp, [part("calibrate,stream")]), "ERROR", "a part without the DoS column")
    check(run(tmp, [part("calibrate,stream,dos", commit="b" * 40), part("calibrate,stream,dos")]), "ERROR",
          "parts from two harness commits")
    check(run(tmp, [part("calibrate,stream,dos", benchmark="fail")]), "REJECT", "a failed part")
    check(run(tmp, full, cert_status="reject"), "REJECT", "a rejected certificate")
    check(run(tmp, [part("calibrate,stream,dos", truncated=True)]), "ACCEPT", "a truncated stream", comparable=False)

    def res(S, verdict="ACCEPT", when="t", e="e", comparable=None, binary=None):
        return {"verdict": verdict, "comparable": (verdict == "ACCEPT") if comparable is None else comparable,
                "finished": when, "entry": {"name": e}, "prover_sha256": binary or when,
                "score": {"S": S} if S is not None else {}}
    rk = os.path.join(tmp, "rank.json")
    files = []
    for k, r in enumerate([res(3.0, when="1"), res(1.0, when="2"), res(2.0, when="3"), res(9.0, when="4"),
                           res(None, "REJECT", when="0", e="g"), res(1.5, when="1", e="g"), res(1.0, when="2", e="g"),
                           res(0.5, "ERROR", when="5", e="g"),
                           res(5.0, when="1", e="t"), res(0.9, when="2", e="t", comparable=False),
                           res(0.9, when="3", e="t", comparable=False), res(1.0, when="4", e="t"),
                           res(0.1, when="1", e="one")]):
        files.append(os.path.join(tmp, f"r{k}.json"))
        json.dump(r, open(files[-1], "w"))
    subprocess.run([sys.executable, "-I", AGG, "--rank", "--out", rk, *files], check=True, capture_output=True)
    rows = {x["entry"]: x for x in json.load(open(rk))["entries"]}
    holds(rows["e"]["median_S"] == 2.0 and rows["e"]["evaluations"] == 4 and rows["g"]["median_S"] == 1.5
          and rows["g"]["failures"] == 1 and rows["g"]["evaluations"] == 3,
          f"ranking per entry, though every run has its own binary: median of the last three (e: 1, 2, 9 → 2), a REJECT "
          f"as the worst (g: fail, 1.5, 1 → 1.5), ERROR not counted: {rows['e']}, {rows['g']}")
    holds(rows["t"]["median_S"] == "failed" and rows["t"]["not_scored"] == 2,
          f"truncated (not comparable) runs count as infinite (review M-4: 5, trunc, trunc, 1 → failed): {rows['t']}")
    holds(isinstance(rows["one"]["median_S"], str) and "unranked" in rows["one"]["median_S"],
          f"an entry with fewer than three evaluations is not ranked: {rows['one']}")
    print(f"{fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
