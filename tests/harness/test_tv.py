#!/usr/bin/env python3
"""The checks, the score and the season's constants (AGENTS.md §6, §7), with a stub badge and
synthetic steps.

  python3 tests/harness/test_tv.py

1. One badge run gives one measurement per item, the run warmed with an untimed first check; a
   rejected output is an answer of the check, not a failure (the stream decides what it means); the
   badge run is bounded only by the stream's cap plus 30 s; a badge run outside the stream has no
   time bound and is refused. The verifier check (`Bench.judged`): every proof is judged in three
   separate fresh, warmed badge runs of its own, each checking it once and nothing else; `V` is the
   median of its three times; a rejection in the first run is a rejection, in a later run a rejection
   when checked again; every judged run (an intermediate output's and the final output's) and every
   canary run of `c` checks is bounded by `60 s + 2 (c + 1) v_cap`, within the stream's cap. Past the stream's cap no badge run starts (`stream-cap`); a badge run that failed
   past it stays a failed check (`check`), its message naming the cap.
2. The score (AGENTS.md §7), pinned by hand-computed vectors: `T_t = Σ_i P_{i,t}` per timed pass,
   `P_total = T_{t*}` the median of the three (ties: the lowest index), `P_i = P_{i,t*}`;
   `S = P_total · |π_M|` and, when eligible for `every`, `S_every = P_total · max_i |π_i|` (seconds ·
   bytes, no size scale: halving the proof halves S, a proof 1 % smaller is worth a prover 1 %
   faster; no `size_ref`, `size_exponent` or `size_unit` in the score); deferring work to the
   last step changes nothing; `c_P` is a health check, never a factor (AGENTS.md §6); `V` is not
   scored; the tracks: `final` always, `every` only when every output is accepted within the caps and
   the canaries of outputs 1 and 2 are rejected, else `tracks_reason` says why; a step without
   exactly three timed times is `MalformedStream`.
3. The season's constants (AGENTS.md §6, the v6 rules): `M = 16` steps of one leaf of `n = 2^18`
   blocks of 32 bytes, 3 timed passes, `step_s` 20 s, `stream_s` 2,000 s, the caps 1 MiB, 512 KiB and
   64 ms, no `size_ref`, `scrub_batches` 4096, the prover's 8 GiB; the smoke's exceptions (its `v_cap_ms` 128
   and `scrub_batches` 256, its size caps the season's); `Params.load` refuses a malformed shape (`n` above
   `leafCap = 2^20` among them, `n = 2^20` accepted, an even `timed_runs`, a `scrub_batches` the scrub refuses); the seeds are fresh OS CSPRNG draws,
   with no seeded generator, expanded by SHAKE-256 under the published domain; the runner's leaf statements through
   `rf-oracle --data-roots` equal the pure-Python reference; the local season copy keeps every parameter but the two
   it changes.
4. The machine fingerprint's required fields; only they are hashed.
"""
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from types import SimpleNamespace

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from rfh import draws  # noqa: E402
from rfh.bench import Bench, Fail, MalformedStream, Params, fingerprint, fingerprint_problem, score  # noqa: E402
from rfh.checks import BadgeError  # noqa: E402


class StubBadge:
    def __init__(self, script, reject=()):
        self.script, self.calls, self.warm, self.reject, self.timeouts = list(script), 0, [], set(reject), []

    def verify(self, items, store, timeout, warm=False, clock=None):
        self.calls += 1
        self.warm.append(warm)
        self.timeouts.append(timeout)
        self.items = getattr(self, "items", []) + [[rel for _, _, rel in items]]
        return [((self.calls, k) not in self.reject, self.script.pop(0)) for k in range(len(items))]


def bench(script, reject=()):
    b = Bench.__new__(Bench)
    b.p = SimpleNamespace(v_cap_ms=64.0)
    b.badge, b.store = StubBadge(script, reject), "/nonexistent"
    b.deadline = (time.monotonic() + 1000, "the stream's cap")
    return b


def main():
    fails = 0

    def check(cond, what):
        nonlocal fails
        print(("ok   " if cond else "FAIL ") + what)
        fails += not cond
    two = [(b"v", b"c", "f"), (b"v", b"c", "g")]
    b = bench([150, 60])
    res = b.check(two, "two")
    t = b.badge.timeouts[0]
    check(res == [(True, 150), (True, 60)] and b.badge.calls == 1 and b.badge.warm == [True] and 1029 < t <= 1030,
          f"V_i is one warmed measurement, the badge run bounded only by the stream's cap plus 30 s: {res}, {t:.1f} s")
    check(bench([1, 1], reject={(1, 1)}).check(two, "x") == [(True, 1), (False, 1)],
          "a rejected output is an answer of the check, not a failure")
    b = bench([1])
    b.deadline = None
    try:
        b.check(two[:1], "outside")
        check(False, "a badge run outside the stream runs without a time bound")
    except RuntimeError:
        check(b.badge.calls == 0, "a badge run outside the stream is refused (it would have no time bound)")
    b = bench([1, 1])
    b.deadline = (time.monotonic() - 0.5, "the stream's cap stream_s = 2000 s was reached")
    for name, f in (("a check", lambda: b.check(two[:1], "late")), ("a judged check", lambda: b.judged(two[0], "late")),
                    ("a canary run", lambda: b.canary_check(b"v", [(1, "f", b"c" * 32, [])], "late"))):
        try:
            f()
            check(False, f"{name} past the stream's cap: runs")
        except Fail as e:
            check(e.stage == "stream-cap" and b.badge.calls == 0 and "stream_s" in str(e),
                  f"{name} past the stream's cap: no badge run starts, REJECT at stream-cap: {e}")

    class Late(StubBadge):
        def verify(self, items, store, timeout, warm=False, clock=None):
            self.calls += 1
            b.deadline = (time.monotonic() - 30.1, b.deadline[1])         # cut at the shared bound
            raise BadgeError("verify: timeout, 0 of 1 answers", "timeout")
    b = bench([])
    b.badge = Late([])
    try:
        b.check(two[:1], "the final output, judged run 1 of 3")
        check(False, "a badge run cut by the stream's cap passes")
    except Fail as e:
        check(e.stage == "check" and str(e).endswith("(cut 30 s past the stream's cap: the stream's cap)")
              and e.kind == "timeout",
              f"a badge run that failed once the stream's cap had passed: REJECT at check (the badge's failure, which "
              f"the bot re-runs without the record cache), the message names the cap: {e}")

    # the verifier check: three separate fresh badge runs per proof, each checking it alone, the median of
    # its times
    b = bench([30, 70, 40, 900, 10, 60])
    b.p = SimpleNamespace(v_cap_ms=64.0)
    res = [b.judged(it, "output") for it in two]
    check(res == [(True, True, [30, 70, 40], 40), (True, True, [900, 10, 60], 60)] and b.badge.calls == 6
          and b.badge.warm == [True] * 6 and b.badge.items == [["f"]] * 3 + [["g"]] * 3,
          f"each proof judged in three separate warmed badge runs of its own, each checking it once and nothing else; V "
          f"the median of its three times (one fast or one slow run decides nothing): {res}")
    vc = 64.0 / 1e3
    check([round(t, 9) for t in b.badge.timeouts] == [round(60 + 2 * 2 * vc, 9)] * 6
          and abs(Bench.bounded(b, 1) - (60 + 4 * vc)) < 1e-12
          and abs(Bench.bounded(b, 10 ** 6) - b.capped()) < 1,
          f"every judged run (c = 1) is bounded by 60 s + 2 (c + 1) v_cap, within the stream's cap: {b.badge.timeouts}")
    b = bench([1] * 6, reject={(1, 0), (5, 0)})
    b.p = SimpleNamespace(v_cap_ms=64.0)
    res = [b.judged(it, "output") for it in two]
    check([(ok, again) for ok, again, _, _ in res] == [(False, False), (True, False)]
          and [round(t, 9) for t in b.badge.timeouts] == [round(60 + 4 * vc, 9)] * 6,
          "rejected in the first run: rejected; accepted in the first and rejected in a later run: rejected when "
          "checked again (both recorded); every judged run bounded by 60 s + 4 v_cap")
    b = bench([1, 1, 1])
    b.p = SimpleNamespace(v_cap_ms=64.0)
    b.deadline = (time.monotonic() + 10, b.deadline[1])          # 10 s of the stream left: its cap binds first
    b.judged(two[0], "output")
    check(9 < b.badge.timeouts[0] <= 40,
          f"... and within the stream's cap plus 30 s when that comes first ({b.badge.timeouts[0]:.1f} s)")

    p = Params.load(os.path.join(ROOT, "harness", "season.toml"))
    cal = {"c_P": 1.0}
    N = 1 << 18

    def mk(i, P, pi=100, n=N, times=None, **kw):
        """A step of P s in each of the three timed passes (or `times`)."""
        return dict({"index": i, "n": n, "P_timed_s": times or [P] * 3, "P_service_s": 2 * P, "V_ns": 10 ** 6,
                     "pi_bytes": pi, "accepted": True}, **kw)

    def stream(steps, c_P=1.0):
        for s in steps[:2]:
            s.setdefault("canaries_accepted", [])
        return {"steps": steps, "calibration": dict(cal, c_P=c_P)}
    # vector 1: two steps at 1 s and 2 s, |π_M| = 256 KiB = 262,144 B: P_total = 3 s, the size factor
    # |π_M| = 262,144 B, S = 786,432 s·B
    sc = score(p, stream([mk(1, 1.0, pi=1 << 30), mk(2, 2.0, pi=256 << 10)]))
    check(sc["P_total_s"] == 3.0 and sc["size_factor"] == 262144 and not hasattr(p, "size_ref")
          and sc["S"] == 786432.0 and sc["final_pi_bytes"] == 256 << 10
          and not any(k in sc for k in ("size_ref", "size_exponent", "size_unit", "P_bar", "n_ref")),
          f"vector 1: S = P_total · |π_M| in s·B, 3 s · 262,144 B = 786,432, the final |π| only (output 1's 1 GiB "
          f"ignored), no size_ref, size_exponent or size_unit: {sc['S']!r}")
    # the product's trade-off: halving |π_M| halves S; |π_M| 1 % smaller equals P_total 1 % smaller
    half = score(p, stream([mk(1, 1.0), mk(2, 2.0, pi=128 << 10)]))["S"]
    small = score(p, stream([mk(1, 1.0), mk(2, 2.0, pi=259522)]))["S"]      # 262,144 · 0.99 = 259,522.56
    fast = score(p, stream([mk(1, 0.99), mk(2, 1.98, pi=256 << 10)]))["S"]
    check(half == 786432.0 / 2 and abs(small / 786432.0 - 0.99) < 1e-5 and abs(fast / 786432.0 - 0.99) < 1e-12,
          f"halving |π_M| halves S ({half!r}); a proof 1 % smaller and a prover 1 % faster score alike "
          f"({small / 786432.0:.6f}, {fast / 786432.0:.6f} of S)")
    sc_f = score(p, stream([mk(1, 1.0), mk(2, 2.0, pi=256 << 10, file_bytes=(256 << 10) + 4840)]))
    check(sc_f["final_file_bytes"] == (256 << 10) + 4840 and sc_f["S"] == score(p, stream([mk(1, 1.0), mk(2, 2.0, pi=256 << 10)]))["S"],
          "the final output's whole file size is published beside |π_M| (final_file_bytes), never scored")
    check(sc["tracks"] == {"final": "S"} and "output 1: |π| = 1073741824 bytes above pi_cap" in sc["tracks_reason"]["every"],
          f"an intermediate |π| above pi_cap (recorded): `final` only: {sc['tracks_reason']}")
    # vector 2: the season's shape, P_i = i s (i = 1 … 16), |π_i| = 256 KiB: P_total = 136 s,
    # S = S_every = 136 · 262,144 = 35,651,584 s·B
    st = stream([mk(i, float(i), pi=256 << 10) for i in range(1, 17)])
    sc = score(p, st)
    check(sc["P_total_s"] == 136.0 and sc["S"] == 35651584.0 and sc["S_every"] == sc["S"]
          and sc["size_factor_every"] == 262144
          and sc["tracks"] == {"final": "S", "every": "S_every"} and "tracks_reason" not in sc and sc["M"] == 16,
          f"vector 2 (M = 16): P_total = Σ P_i = 136 s, S = S_every = 136 s · 262,144 B = 35,651,584, both tracks: "
          f"{sc['S']!r}")
    check(sc["P_total_service_run_s"] == 272.0 and abs(sum(s["share_P"] for s in st["steps"]) - 1) < 1e-12
          and st["steps"][15]["share_P"] == 16 / 136,
          "the service run's total and each step's share of P_total are published")
    # the median of three pass totals: passes of 5, 3 and 4 s over two steps: P_total = 4 s (pass 3)
    st = stream([mk(1, 0, times=[2.0, 1.0, 1.5], pi=256 << 10), mk(2, 0, times=[3.0, 2.0, 2.5], pi=256 << 10)])
    sc = score(p, st)
    check(sc["pass_totals_s"] == [5.0, 3.0, 4.0] and sc["median_pass"] == 3 and sc["P_total_s"] == 4.0
          and [s["P_s"] for s in st["steps"]] == [1.5, 2.5] and [s["share_P"] for s in st["steps"]] == [1.5 / 4, 2.5 / 4]
          and sc["S"] == 4.0 * 262144,
          f"P_total is the median of the pass totals {sc['pass_totals_s']} (pass {sc['median_pass']}), not the sum of "
          f"each step's least time (2.5 s); P_i and share_P from that pass: {[s['P_s'] for s in st['steps']]}")
    for totals, want in (([4.0, 3.0, 4.0], 1), ([3.0, 4.0, 4.0], 2), ([4.0, 4.0, 3.0], 1), ([5.0, 4.0, 4.0], 2),
                         ([2.0, 2.0, 2.0], 1)):
        st = stream([mk(1, 0, times=[t / 2 for t in totals]), mk(2, 0, times=[t / 2 for t in totals])])
        sc = score(p, st)
        check(sc["median_pass"] == want and sc["P_total_s"] == sorted(totals)[1],
              f"ties: pass totals {totals}: the median {sorted(totals)[1]} s, the lowest index among the passes with it: "
              f"pass {sc['median_pass']}")
    # S_every prices the largest proof: |π| 384, 128, 256 KiB (final): S = 3 s · 262,144 B = 786,432,
    # S_every = 3 s · 393,216 B = 1,179,648
    sc = score(p, stream([mk(1, 1.0, pi=384 << 10), mk(2, 1.0, pi=128 << 10), mk(3, 1.0, pi=256 << 10)]))
    check(sc["S"] == 786432.0 and sc["S_every"] == 1179648.0 and sc["max_pi_bytes"] == 384 << 10
          and sc["size_factor_every"] == 384 << 10 and sc["size_factor"] == 256 << 10 and sc["final_pi_bytes"] == 256 << 10,
          f"S prices |π_M| (256 KiB), S_every the largest |π_i| (384 KiB): {sc['S']!r}, {sc['S_every']!r}")
    sc = score(p, stream([mk(1, 1.0, pi=384 << 10, accepted=False), mk(2, 1.0, pi=128 << 10)]))
    check(sc["tracks"] == {"final": "S"} and not any(k in sc for k in ("S_every", "size_factor_every", "max_pi_bytes")),
          f"not eligible for `every`: no S_every, the track absent: {sorted(sc)}")
    for what, t in (("two timed times", [1.0, 1.0]), ("four", [1.0] * 4), ("none", None), ("a string", [1.0, "1", 1.0]),
                    ("a negative time", [1.0, -1.0, 1.0]), ("NaN", [1.0, float("nan"), 1.0])):
        steps = [mk(1, 1.0), mk(2, 1.0)]
        steps[1]["P_timed_s"] = t
        try:
            score(p, stream(steps))
            check(False, f"a step with {what} is scored")
        except MalformedStream as e:
            check("step 2" in str(e), f"a step with {what} is MalformedStream: {e}")
    even = score(p, stream([mk(i, 1.0) for i in range(1, 17)]))["S"]
    late = score(p, stream([mk(i, 0.0 if i < 16 else 16.0) for i in range(1, 17)]))["S"]
    check(even == late, f"deferring all work to the last step changes nothing: {even} = {late}")
    st2 = [mk(i, float(i), pi=256 << 10) for i in range(1, 17)]
    check(score(p, stream(st2, c_P=2.0))["S"] == 35651584.0, "c_P does not scale the score")
    slow_v = stream([mk(1, 1.0), mk(2, 1.0, V_ns=10 ** 12), mk(3, 1.0)])
    check(score(p, slow_v)["S"] == score(p, stream([mk(1, 1.0), mk(2, 1.0), mk(3, 1.0)]))["S"]
          and "output 2: V = 1000000.0 ms above v_cap = 64 ms" in score(p, slow_v)["tracks_reason"]["every"],
          "V is not scored; an intermediate V above v_cap only leaves `every`")
    for what, steps, why in (
            ("output 2 rejected", [mk(1, 1.0), mk(2, 1.0, accepted=False), mk(3, 1.0)], "output 2 rejected by acc"),
            ("a canary of output 2 accepted", [mk(1, 1.0), mk(2, 1.0, canaries_accepted=["stmt-bit"]), mk(3, 1.0)],
             "output 2: statement canaries accepted by acc ['stmt-bit']"),
            ("the canaries of output 1 not recorded", [mk(1, 1.0, canaries_accepted=None), mk(2, 1.0)],
             "output 1: statement canaries not checked"),
            ("output 2's check crashed", [mk(1, 1.0), mk(2, 1.0, check_error="`verify: exit -11`"), mk(3, 1.0)],
             "output 2: its check failed (`verify: exit -11`)"),
            ("output 2 rejected when checked again", [mk(1, 1.0), mk(2, 1.0, recheck_rejected=True), mk(3, 1.0)],
             "output 2: rejected by acc when checked again"),
            ("the canaries' check of output 1 crashed", [mk(1, 1.0, canary_error="`x`"), mk(2, 1.0)],
             "output 1: its statement canaries' check failed (`x`)")):
        sc = score(p, stream(steps))
        check(sc["tracks"] == {"final": "S"} and why in sc["tracks_reason"]["every"], f"{what}: `final` only ({why})")

    # AGENTS.md §6: c_P against the fixed ref_ns is a health check; its drift is an organiser ERROR
    # once ref_ns is measured, recorded but not enforced while it is a placeholder
    samp = [{"calib_ns": 1.3 * p.calib_ref_ns}, {"calib_ns": 1.3 * p.calib_ref_ns}]
    calib = lambda prov, k=1.3: Bench.calibration(SimpleNamespace(  # noqa: E731
        samples=[dict(x, calib_ns=k * p.calib_ref_ns) for x in samp], p=SimpleNamespace(**dict(vars(p), calib_ref_provisional=prov))))
    c = calib(False)
    check(abs(c["c_P"] - 1.3) < 1e-9 and abs(c["c_P_drift"] - 0.3) < 1e-9 and c["c_P_ok"] is False
          and "v_ref_ns" not in c and "T_triv_ns" not in c,
          f"c_P = 1.3 is unclamped and drifts beyond c_P_drift = {p.calib_drift}: not ok; no T_triv, no v_ref")
    check(calib(False, 1.02)["c_P_ok"] is True, "a drift of 0.02 is within c_P_drift")
    check(calib(True)["c_P_ok"] is True, "while ref_ns is a placeholder the drift is recorded, not enforced")
    check(p.calib_ref_provisional is False and p.calib_ref_ns == 316200000 and p.calib_drift == 0.065,
          "season 1's ref_ns and c_P_drift are measured: the drift is enforced")
    check(len(p.fingerprint) == 64 and all(c in "0123456789abcdef" for c in p.fingerprint),
          "season 1's fingerprint is a sha256 in hex")

    # the season's constants (the v6 rules)
    check((p.M, p.n, p.timed_runs, p.step_s, p.stream_s, p.ready_s) == (16, 1 << 18, 3, 20, 2000, 10)
          and not hasattr(p, "chains")
          and (p.pi_cap, p.final_pi_cap, p.v_cap_ms) == (1 << 20, 512 << 10, 64.0)
          and not hasattr(p, "size_ref") and p.mem_prover == "8G" and (p.check_every, p.calib_every) == (8, 8)
          and p.scrub_batches == 4096 and p.runner_budget_s == 900
          and p.badge_start_s == 2 and not hasattr(p, "n_ref") and not hasattr(draws, "draw_M"),
          f"season 1: M = 16 steps of one leaf of 2^18 blocks, 3 timed passes, step_s 20 s, stream_s 2000 s, caps 1 MiB "
          f"/ 512 KiB / 64 ms, no size_ref, scrub_batches 4096, runner_budget_s 900 s, check_every 8, calibration every 8, badge_start_s 2 s, prover 8G")
    sp = Params.load(os.path.join(ROOT, "harness", "smoke.toml"))
    check((sp.M, sp.n, sp.timed_runs) == (4, 6, 3) and (sp.pi_cap, sp.final_pi_cap, sp.file_cap)
          == (p.pi_cap, p.final_pi_cap, p.file_cap)
          and sp.v_cap_ms == 128.0 and p.v_cap_ms == 64.0 and (sp.step_s, sp.stream_s) == (60, 300)
          and sp.scrub_batches == 256 and sp.runner_budget_s == 300,
          f"the smoke: M = 4, n = 6, 3 timed passes, the season's size caps, scrub_batches 256 (CI's limits); the one documented exception, "
          f"its v_cap {sp.v_cap_ms:g} ms (the season's {p.v_cap_ms:g}); its own time caps")
    season_text = open(os.path.join(ROOT, "harness", "season.toml")).read()
    for what, pat, new, want in (("n above leafCap", r"(?m)^n = 262144", "n = 1048577", "leafCap = 2^20"),
                                 ("n = 2^22, the v5 cap", r"(?m)^n = 262144", "n = 4194304", "leafCap = 2^20"),
                                 ("n zero", r"(?m)^n = 262144", "n = 0", "n not a positive integer"),
                                 ("M a string", r"(?m)^M = 16", 'M = "16"', "M not a positive integer"),
                                 ("no n", r"(?m)^n = 262144", "", "n not a positive integer"),
                                 ("no timed pass", r"(?m)^timed_runs = 3", "timed_runs = 0", "timed_runs"),
                                 ("an even number of timed passes", r"(?m)^timed_runs = 3", "timed_runs = 2",
                                  "timed_runs = 2, not an odd positive integer"),
                                 ("timed_runs a float", r"(?m)^timed_runs = 3", "timed_runs = 3.0", "timed_runs"),
                                 ("scrub_batches not a power of two", r"(?m)^scrub_batches = 4096", "scrub_batches = 3000",
                                  "scrub_batches = 3000, not a power of two"),
                                 ("scrub_batches above the scrub's 65536", r"(?m)^scrub_batches = 4096",
                                  "scrub_batches = 131072", "scrub_batches")):
        bad, k = re.subn(pat, new, season_text, count=1)
        assert k == 1
        with tempfile.TemporaryDirectory(prefix="rf-shape-") as bd:
            open(os.path.join(bd, "s.toml"), "w").write(bad)
            try:
                Params.load(os.path.join(bd, "s.toml"))
                check(False, f"Params.load accepts a season with {what}")
            except ValueError as e:
                check(want in str(e) and "[stream]" in str(e), f"Params.load refuses a season with {what}: {e}")
            check(Params.load(os.path.join(bd, "s.toml"), check=False).name == p.name,
                  f"... and loads it unchecked for the aggregation ({what})")
    with tempfile.TemporaryDirectory(prefix="rf-shape-") as bd:
        open(os.path.join(bd, "s.toml"), "w").write(re.sub(r"(?m)^n = 262144", "n = 1048576", season_text, count=1))
        check(Params.load(os.path.join(bd, "s.toml")).n == 1 << 20, "Params.load accepts n = leafCap = 2^20")
    src = open(os.path.join(ROOT, "harness", "rfh", "draws.py")).read()
    check(len(set(draws.starts(1000))) == 1000 and "random.Random" not in src and "import random" not in src
          and not hasattr(draws, "published_lengths"),
          "starts are fresh CSPRNG draws; no seeded generator and no length list in the draws")
    import hashlib
    sd = bytes(range(32))
    check(draws.DOMAIN == b"recursion.fast/leaf-data/v1" and draws.LEAF_DATA == {"xof": "shake256", "domain": draws.DOMAIN.decode()}
          and draws.leaf_data(sd, 3) == hashlib.shake_256(draws.DOMAIN + sd).digest(96)
          and draws.leaf_data(sd, 5)[:96] == draws.leaf_data(sd, 3) and draws.leaf_data(sd, 0) == b"",
          "a step's data is SHAKE-256(\"recursion.fast/leaf-data/v1\" ‖ s_i) truncated to 32 n bytes")
    # the runner's leaf statements: the service's tree hasher (a total of 2^12 permutations or more) equals
    # the pure-Python reference leafStmt (dataRoot xs) n, which gives the shared known answers
    from rfh import digest
    kat = json.load(open(os.path.join(ROOT, "tests", "vectors", "data_root.json")))["vectors"]
    check([digest.leaf_digest(bytes.fromhex(v["data"])).hex() for v in kat] == [v["leafStmt"] for v in kat]
          and [digest.data_root(digest.blocks(bytes.fromhex(v["data"]))).hex() for v in kat] == [v["dataRoot"] for v in kat],
          "the Python reference gives the known answers of tests/vectors/data_root.json (0 … 7 and 9 blocks)")
    with tempfile.TemporaryDirectory(prefix="rf-roots-") as rd:
        paths = []
        for k, n in enumerate([2100, 0, 1, 3]):      # 4199 + 0 + 1 + 5 permutations: through the service
            paths.append(os.path.join(rd, f"d{k}.bin"))
            open(paths[-1], "wb").write(draws.leaf_data(bytes([k]) * 32, n))
        want = [digest.leaf_digest(open(x, "rb").read()) for x in paths]
        if os.path.exists(digest.ORACLE):
            got = digest.leaf_digests(paths, digest.ORACLE)
            check(got == want and want[1] == digest.leaf_stmt(bytes(32), 0)
                  and digest.data_root([b"x" * 32]) == digest.leaf_item(b"x" * 32),
                  "the service's tree hasher (rf-oracle --data-roots) equals the Python reference")
        else:
            check(False, f"the service binary {digest.ORACLE} is not built (cargo build --release in service/)")
        check(digest.leaf_digests(paths[1:], "/nonexistent/rf-oracle") == want[1:],
              "a tiny total (below 2^12 permutations) is hashed in Python")
        open(paths[0], "ab").write(b"z")
        try:
            digest.leaf_digests(paths, digest.ORACLE)
            check(False, "leaf_digests accepts a file that is not a whole number of blocks")
        except ValueError as e:
            check("not a whole number" in str(e), f"leaf_digests refuses a file that is not a whole number of blocks: {e}")

    # the local copy of the season (harness/local-season.py): two lines changed, as the smoke has them
    out = subprocess.run([sys.executable, "-I", os.path.join(ROOT, "harness", "local-season.py")],
                         capture_output=True, text=True, timeout=30)
    check(out.returncode == 0, f"local-season.py runs ({out.stderr.strip()})")
    with tempfile.TemporaryDirectory(prefix="rf-local-season-") as loc_dir:
        loc_path = os.path.join(loc_dir, "season-local.toml")
        with open(loc_path, "w") as f:
            f.write(out.stdout)
        lp = Params.load(loc_path)
    check(lp.fingerprint == "any" and lp.calib_ref_provisional is True and lp.name == p.name + "-local",
          "the local season accepts any machine and records c_P's drift without enforcing it")
    same = {k for k in vars(p) if k not in ("fingerprint", "calib_ref_provisional", "name")}
    diff = sorted(k for k in same if getattr(lp, k) != getattr(p, k))
    check(not diff, f"every other parameter of the local season is the season's ({diff})")

    # AGENTS.md §6: the fingerprint file's required fields; only they are hashed
    d = tempfile.mkdtemp(prefix="rf-fp-")
    good = {"cpu_model": "x", "vm_shape": {"vcpus": 8, "memory": "16G"}, "frequency_policy": "fixed",
            "image_id": "img-1", "host_kernel": "6.8.0", "microcode": "0x1"}

    def fp(obj, raw=None):
        f = os.path.join(d, f"fp{len(os.listdir(d))}.json")
        open(f, "w").write(raw if raw is not None else json.dumps(obj))
        return fingerprint(f)
    g = fp(good)
    check(g["status"] == "ok" and len(g["hash"]) == 64 and g["host_kernel"] == "6.8.0" and "microcode" not in g,
          f"a complete file hashes, host_kernel recorded, microcode not: {g}")
    check(fp(dict(good, host_kernel="6.9", microcode="0x2", extra=1))["hash"] == g["hash"],
          "host_kernel, microcode and other fields are not hashed")
    check(fp(dict(good, image_id="img-2"))["hash"] != g["hash"] and fp(dict(good, vm_shape={"vcpus": 4, "memory": "16G"}))["hash"] != g["hash"],
          "image_id and vm_shape are hashed")
    for raw in ("{}", "[]", '"any"', "null", "not json"):
        check(fp(None, raw)["status"] == "unreadable", f"a degenerate file ({raw}) is unreadable")
    for k in ("cpu_model", "vm_shape", "frequency_policy", "image_id"):
        check(fp({x: v for x, v in good.items() if x != k})["status"] == "unreadable", f"without {k}: unreadable")
    check(fp(dict(good, vm_shape={"vcpus": 0, "memory": "16G"}))["status"] == "unreadable", "vm_shape with 0 vCPUs: unreadable")
    check(fingerprint(os.path.join(d, "absent.json"))["status"] == "missing", "no file: missing")
    check([fingerprint_problem(*a) for a in (("ok", "h", "h"), ("ok", "h", "g"), ("missing", None, "g"),
                                              ("unreadable", None, "g"), ("missing", None, "any"))]
          == [None, "mismatched", "missing", "unreadable", None], "the three problems, and the smoke's \"any\"")
    shutil.rmtree(d, True)
    print(f"{fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
