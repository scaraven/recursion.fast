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
A duel (`--duel`, the record decided head-to-head on one runner) pairs the candidate with the
incumbent: both scores in the result, the order, one CPU model; an incumbent certificate that is not
`ok`, an incumbent harness error or missing part, or a pairing that does not hold (another duel's
run, another draw of lengths, another runner) is ERROR; an incumbent REJECT or truncated stream is
the incumbent's failure (`entry_failed`); the candidate's own REJECT stands. Without `--duel` the
result has no duel field.
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


def part(parts, benchmark="pass", commit="a" * 40, truncated=False, P=1.0, duel=None, lengths=None, runner="r1"):
    steps = [{"index": i, "n": 1 << 18, "P_s": P, "V_ns": 0, "pi_bytes": 0} for i in (1, 2)]
    r = {"parts": parts.split(","), "benchmark": benchmark, "reasons": [], "season_sha256": "s",
         "harness": {"commit": commit}, "machine": {"cpu_model": "cpu", "runner_name": runner}, "prover": {"binary_sha256": "h"},
         "score": {"S": 999.0},
         "stream": {"steps": steps, "truncated": truncated, "lengths": lengths or [16, 17, 18],
                    "calibration": {"c_P": 1.0, "v_ref_ns": 177.8e6, "T_triv_ns": 1.778e9}}}
    if duel:
        r["duel"] = {"id": duel[0], "role": duel[1], "position": 0}
    return r


DRAW = {"id": "d1", "order": ["incumbent", "candidate"], "M": 2, "lengths": [16, 17, 18]}


def run(tmp, parts, cert_status="ok", plan="split", inc=None, inc_cert="ok", draw=DRAW):
    files = []
    for k, r in enumerate(parts):
        f = os.path.join(tmp, f"p{len(os.listdir(tmp))}-{k}.json")
        json.dump(r, open(f, "w"))
        files.append(f)
    cert = os.path.join(tmp, f"cert-{len(os.listdir(tmp))}.json")
    json.dump({"status": cert_status, "reasons": [] if cert_status != "reject" else ["x"]}, open(cert, "w"))
    out = os.path.join(tmp, f"out-{len(os.listdir(tmp))}.json")
    duel = []
    if inc is not None:      # a duel: the incumbent's certificate (None: missing), parts and the draws
        ic = os.path.join(tmp, f"inc-cert-{len(os.listdir(tmp))}.json")
        if inc_cert is not None:
            json.dump({"status": inc_cert, "reasons": []}, open(ic, "w"))
        d = os.path.join(tmp, f"duel-{len(os.listdir(tmp))}.json")
        json.dump(draw, open(d, "w"))
        duel = ["--duel", d, "--incumbent-cert", ic, "--incumbent-sha", "b" * 40, "--incumbent-path", "submissions/rec"]
        for k, r in enumerate(inc):
            f = os.path.join(tmp, f"i{len(os.listdir(tmp))}-{k}.json")
            json.dump(r, open(f, "w"))
            duel += ["--incumbent-part", f]
    subprocess.run([sys.executable, "-I", AGG, "--plan", plan, "--season", SEASON, "--cert", cert, "--out", out, *duel, *files],
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
    holds("duel" not in r and "incumbent" not in r, "without --duel the result has no duel field (today's result)")

    # the duel
    A = "calibrate,stream,dos"
    cand = lambda **k: [part(A, duel=("d1", "candidate"), P=1.0, **k)]  # noqa: E731
    incu = lambda **k: [part(A, duel=("d1", "incumbent"), P=2.0, **k)]  # noqa: E731
    d = run(tmp, cand(), inc=incu())
    check(d, "ACCEPT", "a duel, both runs ACCEPTed")
    ic = d.get("incumbent") or {}
    holds(d.get("duel") is True and d.get("order") == DRAW["order"] and d.get("cpu_models") == ["cpu"]
          and abs(d["score"]["S"] - 1.0) < 1e-9 and abs((ic.get("score") or {}).get("S", 0) - 2.0) < 1e-9
          and ic.get("verdict") == "ACCEPT" and ic.get("comparable") is True and ic.get("entry_failed") is False
          and ic.get("certificate_status") == "ok" and ic.get("sha") == "b" * 40 and ic.get("path") == "submissions/rec",
          f"the duel's facts: both scores from the one job ({d['score']['S']}, {(ic.get('score') or {}).get('S')}), "
          f"order {d.get('order')}, one CPU model, the incumbent's sha and path")
    d = run(tmp, cand(), inc=incu(benchmark="fail"))
    check(d, "ACCEPT", "the incumbent's benchmark REJECTed on this runner: the candidate stands")
    holds(d["incumbent"]["verdict"] == "REJECT" and d["incumbent"]["entry_failed"] is True, "... and is entry_failed")
    d = run(tmp, cand(), inc=incu(truncated=True))
    holds(d["verdict"] == "ACCEPT" and d["incumbent"]["entry_failed"] is True and d["incumbent"]["comparable"] is False,
          "a truncated incumbent stream is the incumbent's failure (entry_failed)")
    for st in ("error", "reject", "provisional"):
        d = run(tmp, cand(), inc=[], inc_cert=st)
        check(d, "ERROR", f"the incumbent's certificate {st}: the organiser's failure, ERROR")
        holds(d["incumbent"]["entry_failed"] is False, f"... never entry_failed ({st})")
    check(run(tmp, cand(), inc=[], inc_cert=None), "ERROR", "the incumbent's certificate missing")
    check(run(tmp, cand(), inc=incu(benchmark="error")), "ERROR", "the incumbent's benchmark had a harness error")
    check(run(tmp, cand(), inc=[]), "ERROR", "the incumbent's part missing (RF-M1 for the incumbent)")
    check(run(tmp, cand(), inc=incu() + incu()), "ERROR", "the incumbent's part duplicated")
    check(run(tmp, cand(), inc=[part(A, duel=("d0", "incumbent"))]), "ERROR", "an incumbent part from another duel")
    check(run(tmp, cand(), inc=[part(A, duel=("d1", "candidate"))]), "ERROR", "the candidate's part passed as the incumbent's")
    check(run(tmp, [part(A)], inc=incu()), "ERROR", "a candidate part that is not this duel's")
    check(run(tmp, cand(), inc=incu(lengths=[16, 17, 19])), "ERROR", "the incumbent ran other chain lengths")
    check(run(tmp, cand(), inc=incu(runner="r2")), "ERROR", "the two runs on different runners")
    check(run(tmp, cand(), inc=incu(commit="c" * 40)), "ERROR", "the two runs from different harness commits")
    check(run(tmp, cand(), inc=incu(), draw={}), "ERROR", "the duel's draws missing")
    d = run(tmp, [], cert_status="reject", inc=[])
    check(d, "REJECT", "the candidate's certificate rejected (no benchmark): its REJECT stands")
    holds(d["incumbent"]["benchmarked"] is False, "... and the incumbent was not benchmarked")
    check(run(tmp, cand(benchmark="fail"), inc=[], inc_cert="error"), "REJECT", "the candidate's own REJECT stands over an organiser failure")

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
