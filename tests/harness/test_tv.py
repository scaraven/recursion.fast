#!/usr/bin/env python3
"""The checks, the score and the season's constants (AGENTS.md §6, §7), with a stub badge and
synthetic steps.

  python3 tests/harness/test_tv.py

1. `V_i` is one measurement, the batch warmed with an untimed first check; a rejected output is an
   answer of the check, not a failure (the stream decides what it means); the badge run is bounded
   only by the stream's cap plus 30 s; a badge run outside the stream has no time bound and is
   refused.
2. The score (AGENTS.md §7), pinned by hand-computed vectors: `S = P_total · 2^(|π_M| / size_ref)`,
   `P_total = Σ_i P_i` (the stream's wall time; deferring work to the last step changes nothing;
   `c_P` is a health check, never a factor: AGENTS.md §6) with the final output's `|π|` only; `V`
   is not scored; the tracks: `final`
   always, `every` only when every output is accepted within the caps and the canaries of outputs 1
   and 2 are rejected, else `tracks_reason` says why.
3. The season's constants (AGENTS.md §6, the v6 rules): `M = 8` steps of one leaf of `n = 2^22`
   parallel hashes, 2 timed passes, the caps 1 MiB, 512 KiB and 128 ms, the prover's 8 GiB; `Params.load` refuses a
   malformed shape (`n` above `leafCap = 2^22` among them); the seeds are fresh OS CSPRNG draws, with no seeded generator; the local
   season copy keeps every parameter but the two it changes.
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
from rfh.bench import Bench, Params, fingerprint, fingerprint_problem, score  # noqa: E402


class StubBadge:
    def __init__(self, script, reject=()):
        self.script, self.calls, self.warm, self.reject, self.timeouts = list(script), 0, [], set(reject), []

    def verify(self, items, store, timeout, warm=False):
        self.calls += 1
        self.warm.append(warm)
        self.timeouts.append(timeout)
        return [((self.calls, k) not in self.reject, self.script.pop(0)) for k in range(len(items))]


def bench(script, reject=()):
    b = Bench.__new__(Bench)
    b.p = SimpleNamespace()
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

    p = Params.load(os.path.join(ROOT, "harness", "season.toml"))
    cal = {"c_P": 1.0}
    N = 1 << 22

    def mk(i, P, pi=100, n=N, **kw):
        return dict({"index": i, "n": n, "P_s": P, "P_service_s": 2 * P, "V_ns": 10 ** 6, "pi_bytes": pi,
                     "accepted": True}, **kw)

    def stream(steps, c_P=1.0):
        for s in steps[:2]:
            s.setdefault("canaries_accepted", [])
        return {"steps": steps, "calibration": dict(cal, c_P=c_P)}
    # vector 1: two steps at 1 s and 2 s, |π_M| = 256 KiB: P_total = 3 s, the size factor 2^(1/4) =
    # 1.189207115002721, S = 3.5676213450081633
    sc = score(p, stream([mk(1, 1.0, pi=1 << 30), mk(2, 2.0, pi=256 << 10)]))
    check(sc["P_total_s"] == 3.0 and abs(sc["size_factor"] - 1.189207115002721) < 1e-15
          and abs(sc["S"] - 3.5676213450081633) < 1e-14 and sc["final_pi_bytes"] == 256 << 10
          and "P_bar" not in sc and "n_ref" not in sc,
          f"vector 1: S = P_total · 2^(|π_M| / 1 MiB), the final |π| only (output 1's 1 GiB ignored): {sc['S']!r}")
    check(sc["tracks"] == {"final": "S"} and "output 1: |π| = 1073741824 bytes above pi_cap" in sc["tracks_reason"]["every"],
          f"an intermediate |π| above pi_cap (recorded): `final` only: {sc['tracks_reason']}")
    # vector 2: the season's shape, P_i = i s (i = 1 … 8), |π_M| = 512 KiB: P_total = 36 s, S = 36 √2
    st = stream([mk(i, float(i), pi=512 << 10) for i in range(1, 9)])
    sc = score(p, st)
    check(sc["P_total_s"] == 36.0 and abs(sc["S"] - 50.91168824543143) < 1e-12
          and sc["tracks"] == {"final": "S", "every": "S"} and "tracks_reason" not in sc and sc["M"] == 8,
          f"vector 2 (M = 8): P_total = Σ P_i = 36 s, S = 36 √2, both tracks: {sc['S']!r}")
    check(sc["P_total_service_run_s"] == 72.0 and abs(sum(s["share_P"] for s in st["steps"]) - 1) < 1e-12
          and st["steps"][7]["share_P"] == 8 / 36,
          "the service run's total and each step's share of P_total are published")
    even = score(p, stream([mk(i, 1.0) for i in range(1, 9)]))["S"]
    late = score(p, stream([mk(i, 0.0 if i < 8 else 8.0) for i in range(1, 9)]))["S"]
    check(even == late, f"deferring all work to the last step changes nothing: {even} = {late}")
    check(abs(score(p, stream([mk(i, float(i), pi=512 << 10) for i in range(1, 9)], c_P=2.0))["S"] - sc["S"]) < 1e-15,
          "c_P does not scale the score")
    slow_v = stream([mk(1, 1.0), mk(2, 1.0, V_ns=10 ** 12), mk(3, 1.0)])
    check(score(p, slow_v)["S"] == score(p, stream([mk(1, 1.0), mk(2, 1.0), mk(3, 1.0)]))["S"]
          and "output 2: V = 1000000.0 ms above v_cap = 128 ms" in score(p, slow_v)["tracks_reason"]["every"],
          "V is not scored; an intermediate V above v_cap only leaves `every`")
    for what, steps, why in (
            ("output 2 rejected", [mk(1, 1.0), mk(2, 1.0, accepted=False), mk(3, 1.0)], "output 2 rejected by acc"),
            ("a canary of output 2 accepted", [mk(1, 1.0), mk(2, 1.0, canaries_accepted=["stmt-bit"]), mk(3, 1.0)],
             "output 2: statement canaries accepted by acc ['stmt-bit']"),
            ("the canaries of output 1 not recorded", [mk(1, 1.0, canaries_accepted=None), mk(2, 1.0)],
             "output 1: statement canaries not checked"),
            ("output 2's check crashed", [mk(1, 1.0), mk(2, 1.0, check_error="`verify: exit -11`"), mk(3, 1.0)],
             "output 2: its check failed (`verify: exit -11`)"),
            ("output 2 rejected when timed again", [mk(1, 1.0), mk(2, 1.0, recheck_rejected=True), mk(3, 1.0)],
             "output 2: rejected by acc when timed again"),
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

    # the season's constants (the v6 rules, D5)
    check((p.M, p.n, p.timed_runs, p.step_s, p.stream_s) == (8, 1 << 22, 2, 60, 3000) and not hasattr(p, "chains")
          and (p.pi_cap, p.final_pi_cap, p.v_cap_ms) == (1 << 20, 512 << 10, 128.0)
          and (p.size_ref, p.mem_prover) == (1 << 20, "8G") and not hasattr(p, "n_ref") and not hasattr(draws, "draw_M"),
          f"season 1: M = 8 steps of one leaf of 2^22, 2 timed passes, caps 1 MiB / 512 KiB / 128 ms, prover 8G")
    sp = Params.load(os.path.join(ROOT, "harness", "smoke.toml"))
    check((sp.timed_runs, sp.pi_cap, sp.final_pi_cap) == (2, p.pi_cap, p.final_pi_cap) and sp.v_cap_ms == p.v_cap_ms,
          f"the smoke: 2 timed passes, the season's caps, v_cap {sp.v_cap_ms:g} ms (M = {sp.M}, n = {sp.n})")
    season_text = open(os.path.join(ROOT, "harness", "season.toml")).read()
    for what, pat, new, want in (("n above leafCap", r"(?m)^n = 4194304", "n = 4194305", "leafCap = 2^22"),
                                 ("n zero", r"(?m)^n = 4194304", "n = 0", "n not a positive integer"),
                                 ("M a string", r"(?m)^M = 8", 'M = "8"', "M not a positive integer"),
                                 ("no n", r"(?m)^n = 4194304", "", "n not a positive integer"),
                                 ("no timed pass", r"(?m)^timed_runs = 2", "timed_runs = 0", "timed_runs")):
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
    src = open(os.path.join(ROOT, "harness", "rfh", "draws.py")).read()
    check(len(set(draws.starts(1000))) == 1000 and "random.Random" not in src and "import random" not in src
          and not hasattr(draws, "published_lengths"),
          "starts are fresh CSPRNG draws; no seeded generator and no length list in the draws")
    # the runner's leaf digests: the service's parallel hasher (a total of 2^12 hashes or more) equals the
    # pure-Python reference, leafStmt (leafValue s n) n with leafValue the XOR of Keccak-256(0x48 ‖ s ‖ enc64 j)
    from rfh import digest
    if os.path.exists(digest.ORACLE):
        seeds = [bytes(range(32)), bytes(32), bytes([7]) * 32]
        got = digest.leaf_digests(seeds, [5000, 0, 1], digest.ORACLE)
        check(got == [digest.leaf_digest(s, n) for s, n in zip(seeds, [5000, 0, 1])]
              and digest.leaf_value(seeds[2], 1) == digest.leaf_item(seeds[2], 0) and digest.leaf_value(seeds[0], 0) == bytes(32),
              "the service's leaf hasher (rf-oracle --leaves) equals the Python reference")
    else:
        check(False, f"the service binary {digest.ORACLE} is not built (cargo build --release in service/)")

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
