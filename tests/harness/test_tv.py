#!/usr/bin/env python3
"""The verifier term and the score of V4-A11 (§4, §5.2, §11), with a stub badge and synthetic steps.

  python3 tests/harness/test_tv.py

1. `V_i` is the best of two measurements (§11 m-8), each batch warmed with an untimed first check
   (RF-m3); an output rejected on either measurement fails the entry; no check is a gate on time any
   more (the former `T_V` cap is the knee `v_ref` of the score).
2. The score: `P̄` is the work-weighted cubic mean of `P_i/n_i` times `n_ref / c_P`; `V̄ = κ · mean
   max(x, x³)` with `x = V/v_ref + |π|/s_ref`: a step at `x = 2` costs 8 units, one at `x = 0.5` half
   a unit; the marginal values have the right signs.
3. The draws (§3, §11): `M` a season constant (not drawn), lengths
   within `[n_lo, n_hi]` with equal expected work per octave, all from the OS CSPRNG.
4. The fit (§11 m-4) is not moved by one slow step.
"""
import os
import statistics
import sys
from types import SimpleNamespace

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from rfh import draws  # noqa: E402
from rfh.bench import Bench, Fail, Params, fit, score  # noqa: E402


class StubBadge:
    def __init__(self, script, reject=()):
        self.script, self.calls, self.warm, self.reject = list(script), 0, [], set(reject)

    def verify(self, items, store, timeout=None, warm=False):
        self.calls += 1
        self.warm.append(warm)
        return [((self.calls, k) not in self.reject, self.script.pop(0)) for k in range(len(items))]


def bench(script, reject=()):
    b = Bench.__new__(Bench)
    b.p = SimpleNamespace(verify_s=10)
    b.badge, b.store, b.deadline = StubBadge(script, reject), "/nonexistent", None
    return b


def main():
    fails = 0

    def check(cond, what):
        nonlocal fails
        print(("ok   " if cond else "FAIL ") + what)
        fails += not cond
    two = [(b"v", b"c", "f", "a"), (b"v", b"c", "g", "b")]
    b = bench([150, 60, 90, 70])
    res = b.check(two, "two")
    check(res == [(90, [150, 90]), (60, [60, 70])] and b.badge.calls == 2 and b.badge.warm == [True, True],
          f"V_i is the best of two warmed measurements: {res}")
    for rej, what in (({(1, 1)}, "first"), ({(2, 0)}, "second")):
        try:
            bench([1, 1, 1, 1], reject=rej).check(two, "x")
            check(False, f"an output rejected on the {what} measurement passes")
        except Fail as e:
            check("rejected by acc" in str(e), f"an output rejected on the {what} measurement fails the entry: {e}")
    b = bench([10 ** 12, 10 ** 12])                     # 1,000 s: slow, but no longer a gate
    check(b.check(two[:1], "slow") == [(10 ** 12, [10 ** 12, 10 ** 12])], "a slow check is scored, not failed")

    p = Params.load(os.path.join(ROOT, "harness", "season.toml"))
    v_ref = 177.8e6
    cal = {"c_P": 1.0, "v_ref_ns": v_ref, "T_triv_ns": 0}
    mk = lambda i, n, P, V, pi: {"index": i, "n": n, "P_s": P, "V_ns": V, "pi_bytes": pi}  # noqa: E731
    st = {"steps": [mk(1, 1 << 18, 1.0, 0, 0), mk(2, 1 << 18, 2.0, 0, 0)], "calibration": dict(cal)}
    sc = score(p, st)
    check(abs(sc["P_bar"] - ((1 + 8) / 2) ** (1 / 3)) < 1e-9 and sc["V_bar"] == 0,
          f"P̄ is the cubic mean of the per-step times at n_ref (steps of 1 s and 2 s: {sc['P_bar']:.6f})")
    st["calibration"]["c_P"] = 2.0
    check(abs(score(p, st)["P_bar"] - sc["P_bar"] / 2) < 1e-9, "a machine twice as slow (c_P = 2) halves P̄")
    st = {"steps": [mk(1, 1 << 18, 1.0, 2 * v_ref, 0), mk(2, 1 << 18, 1.0, 0, p.s_ref // 2)], "calibration": dict(cal)}
    sc = score(p, st)
    check(abs(sc["V_bar"] - p.kappa * (8 + 0.5) / 2) < 1e-9 and abs(sc["S"] - 1 - sc["V_bar"]) < 1e-9,
          f"V̄ = κ · mean max(x, x³): x = 2 (verifier) costs 8, x = 0.5 (size) costs 0.5 ({sc['V_bar']:.6f})")
    check(abs(p.kappa - p.K * 0.1778) < 1e-4, f"κ = K · v0 (season: {p.kappa} = {p.K} × 177.8 ms)")
    m = sc["marginal"]
    check(all(m[k] < 0 for k in ("chain_speed_1pct", "overhead_0.1s_per_step", "verifier_10ms", "proof_100KB")),
          f"every marginal improvement lowers S: {m}")
    check(st["steps"][0]["x_verifier"] == 2 and st["steps"][1]["x_size"] == 0.5 and sc["largest_x"]["index"] == 1,
          "x is split into its verifier and size parts per step, and the largest is named")

    check(isinstance(p.M, int) and p.M == 96 and not hasattr(draws, "draw_M"),
          f"M is one season constant ({p.M}), not drawn")
    ns = draws.lengths(40000, p.n_lo, p.n_hi)
    work = [sum(n for n in ns if (1 << o) <= n < (2 << o)) for o in (17, 18, 19)]
    check(min(ns) >= p.n_lo and max(ns) <= p.n_hi and max(work) / min(work) < 1.1,
          f"lengths within [2^17, 2^20], work per octave {[round(w / sum(work), 3) for w in work]} (equal)")
    src = open(os.path.join(ROOT, "harness", "rfh", "draws.py")).read()
    check(len(set(draws.starts(1000))) == 1000 and "random.Random" not in src and "import random" not in src,
          "starts are fresh CSPRNG draws; no seeded generator in the draws")

    nn = [100 * k for k in range(1, 21)]
    ps = [0.001 * n + 0.5 for n in nn]
    ps[7] *= 10
    a, b, _ = fit(nn, ps)
    check(abs(a - 0.001) < 1e-9 and abs(b - 0.5) < 1e-6, f"the trimmed fit ignores one slow step (a = {a:.6f}, b = {b:.4f})")
    print(f"{fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
