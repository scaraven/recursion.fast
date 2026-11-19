#!/usr/bin/env python3
"""`harness/aggregate.py` requires exactly the planned benchmark part and recomputes the score,
and `--rank` ranks provisionally.

  python3 tests/harness/test_aggregate.py

The plan is one job (`split` and `single` both): its part gives ACCEPT, the scores `S` and `S_every`
and the tracks recomputed from the stream's per-step records (their three timed times) with
`rfh.bench.score` (the score the runner wrote is ignored; a hand-computed vector pins it; a run whose
intermediate output was rejected is in the track `final` only); a step record without exactly three
timed times is an organiser ERROR named `malformed`, never comparable, and so is a part the runner
named `malformed`; the part
dropped, duplicated, replaced by another part set, or two harness commits give ERROR; a failed part
gives REJECT; a rejected certificate gives REJECT; a stream flagged truncated (no v6 runner writes one)
is not comparable. The ranking takes, per entry (not per binary) and per track (`final` from `S`,
`every` from `S_every`, read through `score.tracks`), the median of its last three evaluations, a
REJECT, a not comparable run or a run outside the track counting as its worst, and ranks only from
three evaluations.
AGENTS.md §6: with a season that names a machine fingerprint, a benchmark on another machine, or with a
missing or unreadable fingerprint, is an organiser ERROR whatever the entry did (the reason says
which); a rejected certificate stays REJECT; the smoke season (`"any"`) accepts any machine. The score does not depend on `c_P` (AGENTS.md §6), and the result records the runner (AGENTS.md §8) and no CPU model. A stream whose shape
(`M`, `n`) is not the season's (one of them changed, none recorded) is an organiser ERROR
named `lengths`, whatever the entry did; a rejected certificate stays REJECT. A season file whose
`[stream]` shape is malformed is named `lengths` by `--check-machine`, `--organiser-error` (whatever
kind the workflow passed) and `--plan`.
"""
import json
import os
import subprocess
import sys
import tempfile
import tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
AGG = os.path.join(ROOT, "harness", "aggregate.py")
SEASON = os.path.join(ROOT, "harness", "smoke.toml")
PLAN = json.loads(subprocess.run([sys.executable, "-I", AGG, "--print-matrix", "split"], capture_output=True,
                                 text=True, check=True).stdout)


FP = "f" * 64
_S = tomllib.load(open(SEASON, "rb"))["stream"]
SHAPE = {"M": _S["M"], "n": _S["n"]}      # the smoke's shape
N = SHAPE["n"]                            # n_i


def part(parts, benchmark="pass", commit="a" * 40, truncated=False, P=1.0, fp=FP, c_P=1.0, fp_status=None,
         shape=SHAPE, pi=(0, 0), accepted=(True, True)):
    steps = [{"index": i, "n": N, "P_timed_s": [P] * 3, "P_service_s": 5.0, "V_ns": 10 ** 6, "pi_bytes": pi[i - 1],
              "accepted": accepted[i - 1], "canaries_accepted": []} for i in (1, 2)]
    r = {"parts": parts.split(","), "benchmark": benchmark, "reasons": [], "season_sha256": "s",
         "harness": {"commit": commit}, "machine": {"fingerprint": fp, "fingerprint_status": fp_status or ("ok" if fp else "missing"),
                                                     "fingerprint_reason": None if fp else "RF_MACHINE_FINGERPRINT is not set",
                                                     "runner_name": "rf-bench-1",
                                                     "runner_environment": "self-hosted",
                                                     "runner_labels": ["rf-bench"]}, "prover": {"binary_sha256": "h"},
         "score": {"S": 999.0, "tracks": {"final": "S", "every": "S"}},
         "stream": {"steps": steps, "truncated": truncated, "shape": shape,
                    "calibration": {"c_P": c_P}}}
    return r


def run(tmp, parts, cert_status="ok", plan="split", season=SEASON):
    files = []
    for k, r in enumerate(parts):
        f = os.path.join(tmp, f"p{len(os.listdir(tmp))}-{k}.json")
        json.dump(r, open(f, "w"))
        files.append(f)
    cert = os.path.join(tmp, f"cert-{len(os.listdir(tmp))}.json")
    json.dump({"status": cert_status, "reasons": [] if cert_status != "reject" else ["x"]}, open(cert, "w"))
    out = os.path.join(tmp, f"out-{len(os.listdir(tmp))}.json")
    subprocess.run([sys.executable, "-I", AGG, "--plan", plan, "--season", season, "--cert", cert, "--out", out, *files],
                   check=True, capture_output=True)
    return json.load(open(out))


def main():
    tmp = tempfile.mkdtemp(prefix="rf-agg-", dir=os.environ.get("RF_TEST_TMP"))
    full = [part("calibrate,stream")]
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
    holds(PLAN == ["all"], f"one benchmark job: {PLAN}")
    r = run(tmp, full)
    check(r, "ACCEPT", "the planned part")
    sc = r.get("score", {})
    one = 2.0                    # P_total of two steps of 1 s
    holds(abs(sc.get("S", 0) - one) < 1e-12 and sc.get("P_total_s") == 2.0
          and sc.get("tracks") == {"final": "S", "every": "S_every"} and sc.get("S_every") == one and sc.get("M") == 2,
          f"the score is recomputed from the steps (two steps of 1 s, |π_M| = 0: S = P_total = 2 s, not the "
          f"part's 999), both tracks: {sc.get('S')}, {sc.get('tracks')}")
    # the part's timed times tampered (its score field says 999): step 2 at 2, 4 and 3 s, step 1 at 1 s, |π_1| =
    # 384 KiB, |π_M| = 256 KiB: pass totals 3, 5, 4 s, P_total = 4 s (pass 3), S = 4 √2, S_every = 4 · 2^(3/4)
    vec = part("calibrate,stream", pi=(384 << 10, 256 << 10))
    vec["stream"]["steps"][1]["P_timed_s"] = [2.0, 4.0, 3.0]
    vec["stream"]["steps"][1]["P_s"] = 0.5            # a stale per-step field is ignored, recomputed
    sc = run(tmp, [vec]).get("score", {})
    want, want_e = 4 * 2 ** 0.5, 4 * 2 ** 0.75
    holds(sc.get("S") == want and sc.get("S_every") == want_e and sc.get("final_pi_bytes") == 256 << 10
          and sc.get("max_pi_bytes") == 384 << 10 and sc.get("pass_totals_s") == [3.0, 5.0, 4.0] and sc.get("median_pass") == 3
          and abs(sc.get("size_factor", 0) - 2 ** 0.5) < 1e-12,
          f"the aggregation recomputes S and S_every exactly from the tampered times: S {sc.get('S')} = {want}, "
          f"S_every {sc.get('S_every')} = {want_e}")
    bad = part("calibrate,stream")
    bad["stream"]["steps"][1]["P_timed_s"] = [1.0, 1.0]
    r = run(tmp, [bad])
    check(r, "ERROR", "a step with two timed times (a runner fault)")
    holds(r.get("organiser_error") == "malformed" and "score" not in r and any("is malformed" in x for x in r["reasons"]),
          f"... named `malformed`, no score: {r['reasons'][-1:]}")
    check(run(tmp, [bad], cert_status="reject"), "REJECT", "a rejected certificate stays REJECT whatever the stream's record")
    mal = part("calibrate,stream", benchmark="error")
    mal["organiser_error"] = "malformed"
    holds(run(tmp, [mal]).get("organiser_error") == "malformed", "a part the runner named `malformed` is that ERROR")
    r = run(tmp, [part("calibrate,stream", accepted=(False, True))])
    check(r, "ACCEPT", "an intermediate output rejected (the final accepted)")
    holds(r["score"]["tracks"] == {"final": "S"} and "output 1 rejected by acc" in r["score"]["tracks_reason"]["every"],
          f"... scored in `final` only, recomputed: {r['score'].get('tracks_reason')}")
    r = run(tmp, full)
    check(run(tmp, full, plan="single"), "ACCEPT", "the single plan's one part")
    check(run(tmp, []), "ERROR", "the part missing")
    check(run(tmp, full + full), "ERROR", "the part duplicated")
    check(run(tmp, [part("calibrate")]), "ERROR", "a part without the stream")
    check(run(tmp, [part("calibrate,stream,extra")]), "ERROR", "a part with a part the plan does not name")
    check(run(tmp, [part("calibrate,stream", commit="b" * 40), part("calibrate,stream")]), "ERROR",
          "parts from two harness commits")
    check(run(tmp, [part("calibrate,stream", benchmark="fail")]), "REJECT", "a failed part")
    check(run(tmp, full, cert_status="reject"), "REJECT", "a rejected certificate")
    check(run(tmp, [part("calibrate,stream", truncated=True)]), "ACCEPT", "a stream flagged truncated", comparable=False)
    holds("duel" not in r and "incumbent" not in r and "cpu_models" not in r and "mixed_cpu" not in r,
          "no duel, incumbent or CPU-model field")
    holds(r.get("runner") == {"name": "rf-bench-1", "environment": "self-hosted", "labels": ["rf-bench"]},
          f"the runner is recorded: {r.get('runner')}")
    holds(abs(run(tmp, [part("calibrate,stream", c_P=1.7)])["score"]["S"] - one) < 1e-12,
          "c_P does not scale the score: c_P = 1.7 gives the same S")

    # AGENTS.md §6: the season's machine fingerprint
    fixed = os.path.join(tmp, "fixed.toml")
    open(fixed, "w").write(open(SEASON).read().replace('fingerprint = "any"', f'fingerprint = "{FP}"'))
    A = "calibrate,stream"
    r = run(tmp, [part(A)], season=fixed)
    check(r, "ACCEPT", "the season's fingerprint: comparable")
    holds({k: r["machine"][k] for k in ("fingerprint", "expected", "matches")} == {"fingerprint": FP, "expected": FP, "matches": True},
          f"... recorded: {r['machine']}")
    holds("microcode" not in r["machine"], f"the microcode revision is not published: {r['machine']}")
    for prt, why in ((part(A, fp="e" * 64), "mismatched (fingerprint " + "e" * 64), (part(A, fp=None), "missing (RF_MACHINE"),
                     (part(A, fp=None, fp_status="unreadable"), "unreadable"),
                     (part(A, benchmark="fail", fp="e" * 64), "mismatched")):
        r = run(tmp, [prt], season=fixed)
        check(r, "ERROR", f"fingerprint {why.split()[0]} (benchmark {prt['benchmark']}): the organiser's ERROR")
        holds(any(f"machine fingerprint is {why}" in x for x in r["reasons"]), f"... the reason says which: {r['reasons'][-1:]}")
    check(run(tmp, [], cert_status="reject", season=fixed), "REJECT", "a rejected certificate (no benchmark) stays REJECT")
    # the named organiser errors (they never count against the author in the bot's fair order)
    holds(run(tmp, [part(A, fp="e" * 64)], season=fixed).get("organiser_error") == "fingerprint", "a fingerprint ERROR is named")
    drift = part(A, benchmark="error")
    drift["organiser_error"] = "drift"
    holds(run(tmp, [drift]).get("organiser_error") == "drift", "a drift ERROR is named")
    cache = part(A, benchmark="error")
    cache["organiser_error"] = "cache"
    holds(run(tmp, [cache]).get("organiser_error") == "cache", "a cache ERROR is named")
    holds(run(tmp, [part(A, benchmark="error")]).get("organiser_error") is None, "an unnamed harness ERROR is not named")
    holds("organiser_error" not in run(tmp, full), "an ACCEPT names no organiser error")
    out = os.path.join(tmp, "org-error.json")
    subprocess.run([sys.executable, "-I", AGG, "--organiser-error", "setup", "--reason", "setup failure", "--season", SEASON,
                    "--out", out, "--harness-commit", "a" * 40, "--job", "o/r/actions/runs/1/attempts/1"], check=True,
                   capture_output=True)
    o = json.load(open(out))
    holds((o["verdict"], o["comparable"], o["organiser_error"], o["harness_commit"], o["job"]) ==
          ("ERROR", False, "setup", "a" * 40, "o/r/actions/runs/1/attempts/1") and "setup failure" in o["reasons"][0],
          f"--organiser-error writes a named ERROR result: {o['reasons']}")
    cm = lambda env, season: subprocess.run([sys.executable, "-I", AGG, "--check-machine", "--season", season],  # noqa: E731
                                            capture_output=True, text=True, check=True, env=env).stdout.strip()
    noenv = {k: v for k, v in os.environ.items() if k != "RF_MACHINE_FINGERPRINT"}
    holds(cm(noenv, SEASON) == "" and "is missing" in cm(noenv, fixed),
          f"--check-machine: the smoke accepts any machine; a fixed season names a missing fingerprint: {cm(noenv, fixed)!r}")
    check(run(tmp, [part(A, fp="e" * 64)]), "ACCEPT", "the smoke season (\"any\") accepts any fingerprint")
    # the season's stream shape: a stream of another shape is the organiser's ERROR, never comparable
    for sh, what in ((dict(SHAPE, n=SHAPE["n"] + 1), "n changed"), (dict(SHAPE, M=SHAPE["M"] - 1), "one step fewer"),
                     (dict(SHAPE, chains=4), "an extra key (v6's four chains)"), (None, "none recorded")):
        for bench in ("pass", "fail"):
            r = run(tmp, [part(A, benchmark=bench, shape=sh)])
            check(r, "ERROR", f"a stream shape not the season's ({what}; benchmark {bench}): the organiser's ERROR")
            holds(r.get("organiser_error") == "lengths" and any("is not the season's" in x for x in r["reasons"]),
                  f"... named `lengths`, the reason says so: {r['reasons'][-1:]}")
    check(run(tmp, [part(A, shape=None)], cert_status="reject"), "REJECT",
          "a rejected certificate stays REJECT whatever the stream's shape")
    # a malformed [stream] shape in the season file: named `lengths` in every mode, never a crash
    smoke_text = open(SEASON).read()
    for what, text in (("n above leafCap = 2^20", smoke_text.replace("\nn = 6 ", "\nn = 1048577 ")),
                       ("n zero", smoke_text.replace("\nn = 6 ", "\nn = 0 ")),
                       ("no M", smoke_text.replace("\nM = 4\n", "\n")),
                       ("an even timed_runs", smoke_text.replace("\ntimed_runs = 3 ", "\ntimed_runs = 2 "))):
        assert text != smoke_text
        bad = os.path.join(tmp, f"bad-{len(os.listdir(tmp))}.toml")
        open(bad, "w").write(text)
        why = cm(noenv, bad)
        holds(why.startswith("the season file's [stream] shape is malformed"),
              f"--check-machine names a season with {what} as the organiser's problem: {why!r}")
        out = os.path.join(tmp, f"org-len-{len(os.listdir(tmp))}.json")
        subprocess.run([sys.executable, "-I", AGG, "--organiser-error", "fingerprint", "--reason", why + " (checked in the setup job)",
                        "--season", bad, "--out", out, "--harness-commit", "a" * 40], check=True, capture_output=True)
        o = json.load(open(out))
        holds(o["organiser_error"] == "lengths" and o["verdict"] == "ERROR" and o["reasons"][0].count("is malformed") == 1
              and o["schema"] == "recursion.fast/v6/result-1",
              f"... and --organiser-error (passed `fingerprint` by the workflow) names it `lengths`: {o['reasons']}")
        r = run(tmp, full, season=bad)
        check(r, "ERROR", f"--plan with a season with {what}: the organiser's ERROR")
        holds(r.get("organiser_error") == "lengths" and any("is malformed" in x for x in r["reasons"]),
              f"... named `lengths`: {r['reasons'][-1:]}")
    check(run(tmp, [part(A, fp=None)]), "ACCEPT", "... and none")
    check(run(tmp, [part(A, fp=FP), part(A, fp="e" * 64)], season=fixed), "ERROR",
          "two parts (a plan error first) with different fingerprints")

    def res(S, verdict="ACCEPT", when="t", e="e", comparable=None, binary=None, every=True):
        """A result scoring S in `final` and S + 100 in `every` (S_every, read through score.tracks)."""
        return {"verdict": verdict, "comparable": (verdict == "ACCEPT") if comparable is None else comparable,
                "finished": when, "entry": {"name": e}, "prover_sha256": binary or when,
                "score": {"S": S, **({"S_every": S + 100} if every else {}),
                          "tracks": {"final": "S", **({"every": "S_every"} if every else {})}} if S is not None else {}}
    rk = os.path.join(tmp, "rank.json")
    files = []
    for k, r in enumerate([res(3.0, when="1"), res(1.0, when="2", every=False), res(2.0, when="3"), res(9.0, when="4"),
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
          f"truncated (not comparable) runs count as infinite (5, trunc, trunc, 1 → failed): {rows['t']}")
    holds(isinstance(rows["one"]["median_S"], str) and "unranked" in rows["one"]["median_S"],
          f"an entry with fewer than three evaluations is not ranked: {rows['one']}")
    holds(rows["e"]["median_S_every"] == 109.0 and rows["e"]["last_three_every"] == ["failed or not scored", 102.0, 109.0]
          and rows["g"]["median_S_every"] == 101.5 and rows["t"]["median_S_every"] == "failed"
          and "unranked" in rows["one"]["median_S_every"],
          f"the track `every` is ranked the same way from each run's S_every, a run outside it counting as infinite "
          f"(e: ∞, 102, 109 → 109): {rows['e']['last_three_every']}")
    print(f"{fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
