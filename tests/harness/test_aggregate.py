#!/usr/bin/env python3
"""`harness/aggregate.py` requires exactly the planned benchmark part and recomputes the score,
and `--rank` ranks provisionally.

  python3 tests/harness/test_aggregate.py

The plan is one job (`split` and `single` both): its part gives ACCEPT, scored from the
stream's per-step records with `rfh.bench.score` (the S the runner wrote is ignored); the part
dropped, duplicated, replaced by another part set, or two harness commits give ERROR; a failed part
gives REJECT; a rejected certificate gives REJECT; a truncated stream is ACCEPTed but not comparable.
The ranking takes, per entry (not per binary), the median of its last three evaluations, a REJECT or a
truncated run counting as its worst, and ranks only from three evaluations.
AGENTS.md §6: with a season that names a machine fingerprint, a benchmark on another machine, or with a
missing or unreadable fingerprint, is an organiser ERROR whatever the entry did (the reason says
which); a rejected certificate stays REJECT; the smoke season (`"any"`) accepts any machine. The score does not depend on `c_P` (AGENTS.md §6), and the result records the runner (AGENTS.md §8) and no CPU model. A stream whose chain lengths are
not the season's fixed `[stream] lengths` (other values, one more or one fewer, none recorded) is an
organiser ERROR named `lengths`, whatever the entry did; a rejected certificate stays REJECT. A
season file whose `[stream] lengths` is malformed is named `lengths` by `--check-machine`,
`--organiser-error` (whatever kind the workflow passed) and `--plan`.
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
LENGTHS = tomllib.load(open(SEASON, "rb"))["stream"]["lengths"]      # the smoke's fixed list


def part(parts, benchmark="pass", commit="a" * 40, truncated=False, P=1.0, fp=FP, c_P=1.0, fp_status=None,
         lengths=LENGTHS):
    steps = [{"index": i, "n": 1 << 18, "P_s": P, "V_ns": 0, "pi_bytes": 0} for i in (1, 2)]
    r = {"parts": parts.split(","), "benchmark": benchmark, "reasons": [], "season_sha256": "s",
         "harness": {"commit": commit}, "machine": {"fingerprint": fp, "fingerprint_status": fp_status or ("ok" if fp else "missing"),
                                                     "fingerprint_reason": None if fp else "RF_MACHINE_FINGERPRINT is not set",
                                                     "runner_name": "rf-bench-1",
                                                     "runner_environment": "self-hosted",
                                                     "runner_labels": ["rf-bench"]}, "prover": {"binary_sha256": "h"},
         "score": {"S": 999.0},
         "stream": {"steps": steps, "truncated": truncated, "lengths": lengths,
                    "calibration": {"c_P": c_P, "v_ref_ns": 177.8e6, "T_triv_ns": 1.778e9}}}
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
    holds(PLAN == ["all"], f"one benchmark job: {PLAN}")
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
    holds("duel" not in r and "incumbent" not in r and "cpu_models" not in r and "mixed_cpu" not in r,
          "no duel, incumbent or CPU-model field")
    holds(r.get("runner") == {"name": "rf-bench-1", "environment": "self-hosted", "labels": ["rf-bench"]},
          f"the runner is recorded: {r.get('runner')}")
    holds(abs(run(tmp, [part("calibrate,stream,dos", c_P=1.7)])["score"]["S"] - 1.0) < 1e-9,
          "c_P does not scale the score: c_P = 1.7 gives the same S = 1")

    # AGENTS.md §6: the season's machine fingerprint
    fixed = os.path.join(tmp, "fixed.toml")
    open(fixed, "w").write(open(SEASON).read().replace('fingerprint = "any"', f'fingerprint = "{FP}"'))
    A = "calibrate,stream,dos"
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
    # the season's fixed chain lengths: a stream with others is the organiser's ERROR, never comparable
    for ns, what in ((LENGTHS[:1] + [LENGTHS[1] + 1] + LENGTHS[2:], "one length changed"), (LENGTHS[:-1], "one fewer"),
                     (LENGTHS + [16], "one more"), (None, "none recorded")):
        for bench in ("pass", "fail"):
            r = run(tmp, [part(A, benchmark=bench, lengths=ns)])
            check(r, "ERROR", f"chain lengths not the season's ({what}; benchmark {bench}): the organiser's ERROR")
            holds(r.get("organiser_error") == "lengths" and any("chain lengths are not the season's" in x for x in r["reasons"]),
                  f"... named `lengths`, the reason says so: {r['reasons'][-1:]}")
    check(run(tmp, [part(A, lengths=LENGTHS[:-1])], cert_status="reject"), "REJECT",
          "a rejected certificate stays REJECT whatever the stream's lengths")
    # a malformed [stream] lengths in the season file: named `lengths` in every mode, never a crash
    smoke_text = open(SEASON).read()
    for what, text in (("one value too few", smoke_text.replace("lengths = [16, 55, 20, 74, 22, 90, 20]",
                                                                 "lengths = [16, 55, 20, 74, 22, 90]")),
                       ("a value out of range", smoke_text.replace("lengths = [16, 55,", "lengths = [15, 55,")),
                       ("no list", smoke_text.replace("lengths = [16, 55, 20, 74, 22, 90, 20]", ""))):
        assert text != smoke_text
        bad = os.path.join(tmp, f"bad-{len(os.listdir(tmp))}.toml")
        open(bad, "w").write(text)
        why = cm(noenv, bad)
        holds(why.startswith("the season file's [stream] lengths is malformed"),
              f"--check-machine names a season with {what} as the organiser's problem: {why!r}")
        out = os.path.join(tmp, f"org-len-{len(os.listdir(tmp))}.json")
        subprocess.run([sys.executable, "-I", AGG, "--organiser-error", "fingerprint", "--reason", why + " (checked in the setup job)",
                        "--season", bad, "--out", out, "--harness-commit", "a" * 40], check=True, capture_output=True)
        o = json.load(open(out))
        holds(o["organiser_error"] == "lengths" and o["verdict"] == "ERROR" and o["reasons"][0].count("is malformed") == 1,
              f"... and --organiser-error (passed `fingerprint` by the workflow) names it `lengths`: {o['reasons']}")
        r = run(tmp, full, season=bad)
        check(r, "ERROR", f"--plan with a season with {what}: the organiser's ERROR")
        holds(r.get("organiser_error") == "lengths" and any("is malformed" in x for x in r["reasons"]),
              f"... named `lengths`: {r['reasons'][-1:]}")
    check(run(tmp, [part(A, fp=None)]), "ACCEPT", "... and none")
    check(run(tmp, [part(A, fp=FP), part(A, fp="e" * 64)], season=fixed), "ERROR",
          "two parts (a plan error first) with different fingerprints")

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
          f"truncated (not comparable) runs count as infinite (5, trunc, trunc, 1 → failed): {rows['t']}")
    holds(isinstance(rows["one"]["median_S"], str) and "unranked" in rows["one"]["median_S"],
          f"an entry with fewer than three evaluations is not ranked: {rows['one']}")
    print(f"{fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
