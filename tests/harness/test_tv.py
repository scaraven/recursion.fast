#!/usr/bin/env python3
"""The verifier term and the score (AGENTS.md §7), with a stub badge and synthetic steps.

  python3 tests/harness/test_tv.py

1. `V_i` is the best of two measurements, each batch warmed with an untimed first check;
   an output rejected on either measurement fails the entry; no check is a gate on time (the
   verifier's time is priced by the score, with its knee at `v_ref`).
2. The score: `P̄` is the work-weighted cubic mean of `P_i/n_i` times `n_ref` (`c_P` is a health
   check, never a factor: AGENTS.md §6); `V̄ = κ · mean
   max(x, x³)` with `x = V/v_ref + |π|/s_ref`: a step at `x = 2` costs 8 units, one at `x = 0.5` half
   a unit; the marginal values have the right signs.
3. The chain lengths and the draws: `M` a season constant (not drawn); the chain lengths the
   season file's fixed list, which `rfh.draws.published_lengths` re-derives from its public label
   (and the smoke's from its own), `M + 1` integers in `[n_lo, n_hi]`, with no float rounding near
   a tie (the exact rational inverse CDF rounds the same); `Params.load` refuses a list of the wrong
   length, with a value outside the range, or not of integers; the inverse CDF gives equal expected
   work per octave; the chain starts are fresh OS CSPRNG draws, with no seeded generator; the local
   season copy keeps the list unchanged.
4. The fit is not moved by one slow step.
"""
import os
import statistics
import sys
from types import SimpleNamespace

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from rfh import draws  # noqa: E402
from rfh.bench import Bench, Fail, Params, fingerprint, fingerprint_problem, fit, score  # noqa: E402


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
    b = bench([10 ** 12, 10 ** 12])                     # 1,000 s: slow, but not a gate
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
    check(abs(score(p, st)["P_bar"] - sc["P_bar"]) < 1e-9, "c_P does not scale P̄: c_P = 2 leaves it unchanged")
    st = {"steps": [mk(1, 1 << 18, 1.0, 2 * v_ref, 0), mk(2, 1 << 18, 1.0, 0, p.s_ref // 2)], "calibration": dict(cal)}
    sc = score(p, st)
    check(abs(sc["V_bar"] - p.kappa * (8 + 0.5) / 2) < 1e-9 and abs(sc["S"] - 1 - sc["V_bar"]) < 1e-9,
          f"V̄ = κ · mean max(x, x³): x = 2 (verifier) costs 8, x = 0.5 (size) costs 0.5 ({sc['V_bar']:.6f})")
    check(abs(p.kappa - p.K * 0.6595) < 1e-4, f"κ = K · v0 (season: {p.kappa} = {p.K} × 659.5 ms)")
    m = sc["marginal"]
    check(all(m[k] < 0 for k in ("chain_speed_1pct", "overhead_0.1s_per_step", "verifier_10ms", "proof_100KB")),
          f"every marginal improvement lowers S: {m}")
    check(st["steps"][0]["x_verifier"] == 2 and st["steps"][1]["x_size"] == 0.5 and sc["largest_x"]["index"] == 1,
          "x is split into its verifier and size parts per step, and the largest is named")

    # AGENTS.md §6: c_P against the fixed ref_ns is a health check; its drift is an organiser ERROR
    # once ref_ns is measured, recorded but not enforced while it is a placeholder
    samp = [{"calib_ns": 1.3 * p.calib_ref_ns, "triv_ns": 1e9}, {"calib_ns": 1.3 * p.calib_ref_ns, "triv_ns": 1e9}]
    cal = lambda prov, k=1.3: Bench.calibration(SimpleNamespace(  # noqa: E731
        samples=[dict(x, calib_ns=k * p.calib_ref_ns) for x in samp], p=SimpleNamespace(**dict(vars(p), calib_ref_provisional=prov))))
    c = cal(False)
    check(abs(c["c_P"] - 1.3) < 1e-9 and abs(c["c_P_drift"] - 0.3) < 1e-9 and c["c_P_ok"] is False,
          f"c_P = 1.3 is unclamped and drifts beyond c_P_drift = {p.calib_drift}: not ok ({c['c_P']}, {c['c_P_drift']})")
    check(cal(False, 1.02)["c_P_ok"] is True, "a drift of 0.02 is within c_P_drift")
    check(cal(True)["c_P_ok"] is True, "while ref_ns is a placeholder the drift is recorded, not enforced")
    check(p.calib_ref_provisional is False and p.calib_ref_ns == 316200000 and p.calib_drift == 0.065,
          "season 1's ref_ns and c_P_drift are measured: the drift is enforced")
    check(len(p.fingerprint) == 64 and all(c in "0123456789abcdef" for c in p.fingerprint),
          "season 1's fingerprint is a sha256 in hex")
    check(p.calib_ref_provisional or p.fingerprint != "0" * 64,
          "a measured ref_ns comes with a measured fingerprint, not the all-zero placeholder")

    # the local copy of the season (harness/local-season.py): three lines changed, as the smoke has them
    import subprocess
    import tempfile
    out = subprocess.run([sys.executable, "-I", os.path.join(ROOT, "harness", "local-season.py")],
                         capture_output=True, text=True, timeout=30)
    check(out.returncode == 0, f"local-season.py runs ({out.stderr.strip()})")
    with tempfile.TemporaryDirectory(prefix="rf-local-season-") as loc_dir:
        loc_path = os.path.join(loc_dir, "season-local.toml")
        with open(loc_path, "w") as f:
            f.write(out.stdout)
        lp = Params.load(loc_path)
    check(lp.fingerprint == "any" and lp.calib_ref_provisional is True and lp.dos_item_cap == "verify_s"
          and lp.name == p.name + "-local",
          "the local season accepts any machine, records c_P's drift without enforcing it, and caps a DoS input at verify_s")
    same = {k for k in vars(p) if k not in ("fingerprint", "calib_ref_provisional", "dos_item_cap", "name")}
    diff = sorted(k for k in same if getattr(lp, k) != getattr(p, k))
    check(not diff, f"every other parameter of the local season is the season's ({diff})")

    # AGENTS.md §6: the fingerprint file's required fields; only they are hashed
    import json
    import tempfile
    import atexit
    import shutil
    d = tempfile.mkdtemp(prefix="rf-fp-")
    atexit.register(shutil.rmtree, d, True)
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

    check(isinstance(p.M, int) and p.M == 96 and not hasattr(draws, "draw_M"),
          f"M is one season constant ({p.M}), not drawn")
    # the fixed, published chain lengths: re-derived from the public label, M + 1 of them
    from fractions import Fraction
    sp = Params.load(os.path.join(ROOT, "harness", "smoke.toml"))
    for q, label in ((p, "recursion.fast chain lengths"), (sp, "recursion.fast smoke chain lengths")):
        again = draws.published_lengths(label, q.M + 1, q.n_lo, q.n_hi)
        check(q.lengths == again and len(q.lengths) == q.M + 1 and all(q.n_lo <= n <= q.n_hi for n in q.lengths),
              f"{q.name}: [stream] lengths is the derivation of {label!r}: {len(q.lengths)} = M + 1 values in "
              f"[{q.n_lo}, {q.n_hi}], sum {sum(q.lengths)}")
        exact = []
        for k in range(q.M + 1):
            u = Fraction(draws.published_uniform(label, k))
            x = 1 / (Fraction(1, q.n_lo) - u * (Fraction(1, q.n_lo) - Fraction(1, q.n_hi)))
            exact.append((min(q.n_hi, max(q.n_lo, round(x))), abs(x - int(x) - Fraction(1, 2))))
        check([n for n, _ in exact] == q.lengths and min(d for _, d in exact) > Fraction(1, 10 ** 6),
              f"{q.name}: the exact rational inverse CDF gives the same integers, no value within 1e-6 of a tie")
    check(p.lengths[:3] == [202109, 151388, 556082] and sum(p.lengths) == 32060318,
          "season 1's sequence begins 202109, 151388, 556082 and sums to 32,060,318 (as its comment says)")
    import tomllib
    season_text = open(os.path.join(ROOT, "harness", "season.toml")).read()
    import re as _re
    for what, new in (("one value too few", lambda ns: ns[:-1]), ("one value too many", lambda ns: ns + [ns[0]]),
                      ("a value below n_lo", lambda ns: [p.n_lo - 1] + ns[1:]),
                      ("a value above n_hi", lambda ns: [p.n_hi + 1] + ns[1:]),
                      ("a float", lambda ns: [float(ns[0])] + ns[1:]), ("a boolean", lambda ns: [True] + ns[1:])):
        lst = "lengths = [" + ", ".join(str(x).lower() if isinstance(x, bool) else str(x) for x in new(list(p.lengths))) + "]"
        bad_text, k = _re.subn(r"(?ms)^lengths = \[.*?\]", lst, season_text, count=1)
        assert k == 1 and [(type(x), x) for x in tomllib.loads(bad_text)["stream"]["lengths"]] != [(int, x) for x in p.lengths]
        with tempfile.TemporaryDirectory(prefix="rf-len-") as bd:
            open(os.path.join(bd, "s.toml"), "w").write(bad_text)
            try:
                Params.load(os.path.join(bd, "s.toml"))
                check(False, f"Params.load accepts [stream] lengths with {what}")
            except ValueError as e:
                check("[stream] lengths" in str(e), f"Params.load refuses [stream] lengths with {what}: {e}")
    with tempfile.TemporaryDirectory(prefix="rf-len-") as bd:
        open(os.path.join(bd, "s.toml"), "w").write(season_text.replace("\nM = 96 ", '\nM = "96" ', 1))
        try:
            Params.load(os.path.join(bd, "s.toml"))
            check(False, "Params.load accepts a non-integer M")
        except ValueError as e:
            check("[stream] M is not an integer" in str(e), f"Params.load refuses a non-integer M with a ValueError: {e}")
    check(lp.lengths == p.lengths, "the local season copy keeps the season's lengths unchanged")
    ns = draws.published_lengths("recursion.fast test: work per octave", 40000, p.n_lo, p.n_hi)
    work = [sum(n for n in ns if (1 << o) <= n < (2 << o)) for o in (17, 18, 19)]
    check(min(ns) >= p.n_lo and max(ns) <= p.n_hi and max(work) / min(work) < 1.1,
          f"the inverse CDF: lengths within [2^17, 2^20], work per octave {[round(w / sum(work), 3) for w in work]} (equal)")
    src = open(os.path.join(ROOT, "harness", "rfh", "draws.py")).read()
    check(len(set(draws.starts(1000))) == 1000 and "random.Random" not in src and "import random" not in src,
          "starts are fresh CSPRNG draws; no seeded generator in the draws")
    check(not hasattr(draws, "lengths") and not hasattr(draws, "uniform"), "no per-evaluation length draw is left")

    nn = [100 * k for k in range(1, 21)]
    ps = [0.001 * n + 0.5 for n in nn]
    ps[7] *= 10
    a, b, _ = fit(nn, ps)
    check(abs(a - 0.001) < 1e-9 and abs(b - 0.5) < 1e-6, f"the trimmed fit ignores one slow step (a = {a:.6f}, b = {b:.4f})")
    print(f"{fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
