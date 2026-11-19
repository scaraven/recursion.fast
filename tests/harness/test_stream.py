#!/usr/bin/env python3
"""The stream's control flow (AGENTS.md §6), with stub requests, checks and service.

  python3 tests/harness/test_stream.py

1. Inputs: step 1 gets `leaf.json` (`{"n": n}`, no seed) and `leaf.bin` (its data, the SHAKE-256
   expansion of the step's fresh seed, `32 n` bytes), step i ≥ 2 also `prev.stmt` and `prev.bin` (the
   service run's previous output); a timed request also `oracle.key` (the key the service's replay
   mode revealed, 64 hex and a newline); the service run's requests get no key; every timed pass gets
   the service run's `leaf.bin` and `leaf.json`, byte for byte. The runner's statements are
   `L_i = leafStmt (dataRoot xs_i) n`, `c_1 = L_1`, `c_i = nodeStmt c_{i-1} L_i`, computed from its own
   data files before the first request; every leaf has the season's `n`, `n_i = n`. The data files
   live in a runner-only directory beside the store, never under it or the request directories, and
   are gone after the stream; the result records the expansion (`leaf_data`).
2. The service run, then `timed_runs` = 3 timed passes, each after a `replay`; the timed passes'
   `prev.bin` is the service run's output; `P_total` is the median of the three pass totals and `P_i`
   the step's time in that pass (not the least of its times), the service run's time is recorded, not
   scored; `S = P_total · 2^(|π_M| / size_ref)`, `S_every = P_total · 2^(max_i |π_i| / size_ref)`.
3. A timed output that differs from the service run's is the entry's REJECT, naming the pass, the step
   and the first differing byte offset.
4. The verifier check: every checked proof is judged in three separate badge runs, each checking
   every proof of its batch once (no proof twice in one run), `V_i` the median of its three times
   (`V_runs_ns` in run order), so one slow run is not a breach and one fast run is no pass. The final
   output: rejected by acc (in its first run, or in a later one), |π_M| above final_pi_cap, V_M above
   v_cap, a statement canary accepted, any output above pi_cap, where an output `acc` did not accept
   (rejected in any run, or its check crashed in any run) is sized by its whole file: each the
   entry's REJECT. An intermediate output rejected by acc, or with V above v_cap, or an accepted
   canary of output 1 or 2: scored in `final` only, the reason recorded. Each judged run of `c`
   intermediate outputs, and the canary run of outputs 1 and 2, is bounded by `60 s + 2 (c + 1)
   v_cap`; the final output's runs by the stream's cap.
5. The stream's cap reached is the entry's REJECT (no truncation).
6. Calibration samples: before the service run's step 1, before each timed pass and a closing one.
7. Two evaluations have the same shape and fresh seeds.
8. The track `every` never fails the run: a crashed check of intermediate outputs (in any judged
   run) or of the canaries of outputs 1 and 2, or an intermediate rejected in a later judged run,
   costs only the track; the final output is checked on its own runs, and a crash there (or its
   rejection in a later run) is a REJECT; once `every` is lost, no canary of outputs 1 and 2 is
   checked.
9. The replay audit: a MISMATCH refusal logged in a timed pass (the third included), a MISMATCH in the
   service's final stats, or `replays ≠ timed_runs · signatures` (one SIGN missing or extra over the
   three passes) is the entry's REJECT. A step record without exactly three timed times is
   `MalformedStream` (the organiser's ERROR).
10. Before every request the page cache of the setup directory and the prover binary is warmed (every
    regular file read in full, no link followed), and the warm-up's time is recorded; every request
    gets its own empty socket directory, into which the service's socket is linked only at `go`.
"""
import json
import os
import sys
import tempfile
from types import SimpleNamespace

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from rfh import bench as bench_mod, digest, draws, signed  # noqa: E402
from rfh.bench import Bench, Fail, MalformedStream, Params, score  # noqa: E402
from rfh.prover import Step  # noqa: E402

KEY = "ab" * 32


class FakeSvc:
    vk, sock_dir, info = b"k" * 32, "/nonexistent", {}
    proc = SimpleNamespace(poll=lambda: None)

    def __init__(self, mism=(), mism_from=1):
        self.replays, self.mism, self.mism_from = 0, list(mism), mism_from

    def refusals(self, n=8):
        return []

    def mismatches(self):
        """The logged MISMATCH refusals, from the timed pass `mism_from` on."""
        return list(self.mism) if self.replays >= self.mism_from else []

    def replay(self):
        self.replays += 1
        return KEY


def proof(i, pi_bytes=100):
    """A signed-proof file of `pi_bytes` bytes of π naming step `i`."""
    return signed.Signed(f"step{i}".encode().ljust(pi_bytes, b".")).encode()


def make(times=None, timed=None, M=4, reject=(), V=None, canary_ok=(), out_bytes=None, differ=None,
         cap_at=None, crash=(), reject_later=(), stats=None, mism=(), mism_from=1):
    """A Bench over the smoke season with stubs: the service run's request i takes times[i] s, timed pass
    t's timed[t][i] s; outputs `proof(i)` (or `out_bytes[i]`); `acc` rejects the steps in `reject` in
    every judged run and those in `reject_later` in judged runs 2 and 3 only; V_i in judged run r is
    V[i][r - 1] ns (V[i] three times, or one number for all three; default 1 ms); the canaries (step,
    name) in `canary_ok` accepted; timed pass t's step i differs at byte 7 for (t, i) = `differ`; the
    cap is reached at the request tagged `cap_at`; a badge run whose description contains a string of
    `crash` crashes; the service's stats are `stats` (default: the timed passes replayed every
    signature) and its logged MISMATCH refusals `mism`, from timed pass `mism_from` on."""
    p = Params.load(os.path.join(ROOT, "harness", "smoke.toml"))
    p.M = M
    p.calib_idle_s = 0.0
    p.v_cap_ms = Params.load(os.path.join(ROOT, "harness", "season.toml")).v_cap_ms     # the season's 64 ms
    times = times or {i: 0.01 for i in range(1, M + 1)}
    timed = timed or {t: {i: 0.001 * t for i in range(1, M + 1)} for t in range(1, p.timed_runs + 1)}
    V = V or {}
    b = Bench.__new__(Bench)
    b.p, b.log, b.samples, b.deadline, b.req_root = p, (lambda m: None), [], None, None
    b.service_bin = None                     # the leaves are small: digest.py hashes them in Python
    b.work = tempfile.mkdtemp(prefix="rf-stream-", dir=os.environ.get("RF_TEST_TMP"))
    b.store = os.path.join(b.work, "store")
    b.leafdata = os.path.join(b.work, "leafdata")
    b.calls, b.reqs, b.svc, b.verify_calls, b.data_seen = [], {}, FakeSvc(mism, mism_from), [], []
    b.timeouts = []
    b.service = lambda name: b.svc
    b.stop = lambda svc, rec: rec.update(service_stats=stats or {"signatures": 7 * M, "replays": 7 * M * p.timed_runs,
                                                                 "mismatches": 0})
    b.sample = lambda before: b.samples.append({"before": before, "calib_ns": p.calib_ref_ns})

    def verify(items, what, timeout, warm=False):
        b.verify_calls.append((what, [os.path.basename(rel) for _, _, rel in items]))
        b.timeouts.append((what, timeout, warm))
        if any(c in what for c in crash):
            raise Fail(f"{what}: verify: exit -11, 0 of {len(items)} answers", kind="crash")
        run = int(what.split("judged run ")[1].split()[0]) if "judged run " in what else None
        out = []
        for vk, c, rel in items:
            i = int(os.path.basename(rel).split(".")[0][4:])
            if what.endswith("canaries"):
                out.append((False, 1))
            else:
                v = V.get(i, 10 ** 6)
                out.append((i not in reject and not (i in reject_later and run > 1),
                            v[run - 1] if isinstance(v, list) else v))
        return out
    b.verify = verify

    def canary_check(vk, targets, what, bounded=False):
        res, n = Bench.canary_check(b, vk, targets, what, bounded)
        for k, name in canary_ok:
            if k in res:
                res[k].append(name)
        b.canary_targets = getattr(b, "canary_targets", []) + [k for k, _, _, _ in targets]
        return res, n
    b.canary_check = canary_check

    def one(svc, tag, kind, ins):
        b.calls.append(tag)
        b.reqs[tag] = (kind, ins)
        b.data_seen.append(sorted(os.listdir(b.leafdata)) if os.path.isdir(b.leafdata) else None)
        if tag == cap_at:
            raise Fail(f"{tag}: {b.deadline[1]} (timeout)")
        if tag.startswith("service"):
            i = int(tag[7:])
            t = times[i]
        else:
            tp, st = tag[5:].split("-step")
            i, t = int(st), timed[int(tp)][int(st)]
        r = Step()
        r.seconds, r.startup_s, r.kill_s, r.ended = t, 0.01, 0.001, "line"
        r.warm_s, r.warm_bytes = 0.0, 0
        r.proof = (out_bytes or {}).get(i) or proof(i)
        if differ and tag == f"timed{differ[0]}-step{differ[1]}":
            r.proof = r.proof[:7] + bytes([r.proof[7] ^ 1]) + r.proof[8:]
        return r
    b.one = one
    b.left = lambda: 100.0
    return b


def main():
    fails = 0

    def check(cond, what):
        nonlocal fails
        print(("ok   " if cond else "FAIL ") + what)
        fails += not cond

    times = {1: 0.5, 2: 0.6, 3: 0.7, 4: 0.8}
    # pass totals 0.074, 0.083, 0.080 s: the median pass is pass 3 (not the per-step minima, nor pass 1)
    timed = {1: {1: 0.010, 2: 0.020, 3: 0.004, 4: 0.040}, 2: {1: 0.012, 2: 0.018, 3: 0.003, 4: 0.050},
             3: {1: 0.011, 2: 0.019, 3: 0.005, 4: 0.045}}
    b = make(times, timed)
    rec = b.stream_run()
    st = rec["steps"]
    p = b.p
    k1, in1 = b.reqs["service1"]
    k2, in2 = b.reqs["service2"]
    leaf = ["leaf.bin", "leaf.json"]
    check(k1 == "first" and sorted(in1) == leaf and k2 == "step"
          and sorted(in2) == leaf + ["prev.bin", "prev.stmt"] and in2["prev.bin"] == proof(1),
          "the service run: step 1 gets its leaf; step 2 the previous output, its statement and its leaf; no key")
    seeds = [bytes.fromhex(s) for s in rec["seeds"]]
    xs = [draws.leaf_data(s, p.n) for s in seeds]
    L = [digest.leaf_stmt(digest.data_root(digest.blocks(x)), p.n) for x in xs]
    c = [L[0]]
    for x in L[1:]:
        c.append(digest.node_stmt(c[-1], x))
    check(rec["leaf_digests"] == [x.hex() for x in L] and rec["statements"] == [x.hex() for x in c]
          and in2["prev.stmt"] == (c[0].hex() + "\n").encode(),
          "the statements: L_i = leafStmt (dataRoot xs_i) n, c_1 = L_1, c_i = nodeStmt c_{i-1} L_i, xs_i the "
          "SHAKE-256 expansion of the step's seed")
    check(len(seeds) == 4 and all(json.loads(b.reqs[f"service{i}"][1]["leaf.json"]) == {"n": p.n} for i in range(1, 5))
          and all(s["n"] == p.n for s in st) and rec["shape"] == {"M": 4, "n": p.n},
          f"M fresh seeds, one per step, every leaf of the season's n = {p.n}, n_i = n; leaf.json is {{\"n\": n}} only")
    check(all(b.reqs[f"service{i}"][1]["leaf.bin"] == xs[i - 1] and len(xs[i - 1]) == 32 * p.n for i in range(1, 5))
          and len(set(xs)) == 4
          and all(b.reqs[f"timed{t}-step{i}"][1][k] == b.reqs[f"service{i}"][1][k]
                  for t in (1, 2, 3) for i in range(1, 5) for k in ("leaf.bin", "leaf.json")),
          "every step gets its own data as leaf.bin (32 n bytes, SHAKE-256(domain ‖ s_i)); every timed pass gets the "
          "service run's leaf.bin and leaf.json byte for byte")
    check(rec["leaf_data"] == {"xof": "shake256", "domain": "recursion.fast/leaf-data/v1"}
          and draws.leaf_data(seeds[0], 2) == __import__("hashlib").shake_256(b"recursion.fast/leaf-data/v1" + seeds[0]).digest(64),
          f"the result publishes the seeds and the expansion: {rec['leaf_data']}")
    ld = os.path.realpath(b.leafdata)
    check(b.data_seen == [[f"step{i}.bin" for i in range(1, 5)]] * len(b.calls) and not os.path.exists(b.leafdata)
          and os.path.dirname(ld) == os.path.realpath(b.work)
          and not ld.startswith(os.path.realpath(b.store) + os.sep) and ld != os.path.realpath(b.store),
          "the data of all M steps is written before the first request, to a runner-only directory beside the store "
          "(never under it), and removed after the stream")
    t1 = [b.reqs[f"timed1-step{i}"] for i in range(1, 5)]
    check(b.calls == [f"service{i}" for i in range(1, 5)] + [f"timed{t}-step{i}" for t in (1, 2, 3) for i in range(1, 5)]
          and b.svc.replays == 3
          and all(ins["oracle.key"] == (KEY + "\n").encode() for _, ins in t1)
          and t1[2][1]["prev.bin"] == proof(2) and t1[0][0] == "first"
          and sorted(t1[1][1]) == sorted(leaf + ["prev.bin", "prev.stmt", "oracle.key"]),
          "three timed passes after a replay each; a timed request gets oracle.key and the service run's previous output")
    check(all("P_s" not in s for s in st) and st[3]["P_timed_s"] == [0.040, 0.050, 0.045],
          "the timed passes record each step's times in pass order (P_timed_s), and no P_s of their own")
    sc = score(p, rec)
    Ptot = 0.011 + 0.019 + 0.005 + 0.045
    check(sc["median_pass"] == 3 and [s["P_s"] for s in st] == [0.011, 0.019, 0.005, 0.045]
          and [s["P_service_s"] for s in st] == [0.5, 0.6, 0.7, 0.8]
          and [round(x, 12) for x in sc["pass_totals_s"]] == [0.074, 0.083, 0.08],
          f"P_total is the median pass total (pass 3 of {[round(x, 3) for x in sc['pass_totals_s']]}), P_i the step's time in "
          f"that pass, not its least; the service run's times are recorded: {[s['P_s'] for s in st]}")
    check(abs(sc["P_total_s"] - Ptot) < 1e-12 and sc["final_pi_bytes"] == 100 and p.size_ref == 1 << 19
          and abs(sc["S"] - Ptot * 2 ** (100 / 2 ** 19)) < 1e-12 and "P_bar" not in sc and "n_ref" not in sc
          and abs(sc["S_every"] - Ptot * 2 ** (100 / 2 ** 19)) < 1e-12 and sc["max_pi_bytes"] == 100
          and sc["tracks"] == {"final": "S", "every": "S_every"} and "tracks_reason" not in sc,
          f"S = P_total · 2^(|π_M| / size_ref), S_every = P_total · 2^(max |π_i| / size_ref): {sc['S']:.6g}, "
          f"{sc['S_every']:.6g}, {sc['tracks']}")
    check([x["before"] for x in b.samples] == ["service run, step 1", "timed pass 1", "timed pass 2", "timed pass 3",
                                               "closing"],
          f"calibration samples: {[x['before'] for x in b.samples]}")
    check(sorted(b.canary_targets) == [1, 2, 4] and st[0]["canaries_accepted"] == [] and rec["canaries"] == 5,
          "statement canaries of outputs 1, 2 and M (stmt-bit each, first-child for outputs 2 and M: output 1 is a leaf)")

    def fails_with(what, want, **kw):
        try:
            make(**kw).stream_run()
            check(False, f"{what}: passes")
        except Fail as e:
            check(want in str(e), f"{what}: REJECT: {e}")
    fails_with("a timed output one bit off", "timed pass 2, step 3: the output differs from the service run's output of the "
               "step, first at byte offset 7", differ=(2, 3))
    fails_with("the final output rejected", "the final output (step 4) is rejected by acc", reject={4})
    big = signed.Signed(b"x" * (p.final_pi_cap + 1)).encode()
    fails_with("|π_M| above final_pi_cap", f"above final_pi_cap = {p.final_pi_cap}", out_bytes={4: big})
    huge = b"z" * (p.pi_cap + 1)
    fails_with("an intermediate output above pi_cap (not a signed proof: its file size)",
               f"service run, step 2: the output's file size is {p.pi_cap + 1} bytes, above pi_cap", out_bytes={2: huge})
    stash = signed.Signed(b"", [(b"q" * (2 << 20), bytes(32))]).encode()     # |π| = 0, 2 MiB in the trace
    not_acc = f"service run, step 2: the output, not accepted by acc (rejected, or its check failed), has {len(stash)} bytes"
    fails_with("a rejected intermediate that parses, its state in the trace (sized by its file)", not_acc,
               out_bytes={2: stash}, reject={2})
    fails_with("an intermediate whose batch check crashed, its state in the trace (sized by its file)", not_acc,
               out_bytes={2: stash}, crash=("intermediate",))
    fails_with("an intermediate rejected in a later judged run, its state in the trace (sized by its file)", not_acc,
               out_bytes={2: stash}, reject_later={2})
    fails_with("an intermediate whose second judged run crashed, its state in the trace (sized by its file)", not_acc,
               out_bytes={2: stash}, crash=("intermediate outputs, judged run 2",))
    fails_with("V_M above v_cap in all three judged runs", "above v_cap = 64 ms", V={4: [200e6, 150e6, 190e6]})
    fails_with("V_M above v_cap in two of its three judged runs (the median counts, not the least)",
               "takes V = 200.000 ms (the median of its three judged runs, [200.0, 10.0, 300.0] ms), above v_cap = 64 ms",
               V={4: [200e6, 10e6, 300e6]})
    fails_with("a canary of the final output accepted", "statement canaries accepted by acc", canary_ok=[(4, "x")])
    fails_with("the stream's cap", "stream_s", cap_at="timed1-step2")

    b = make(V={4: [200e6, 10e6, 20e6], 2: [5e6, 300e6, 6e6]})
    rec = b.stream_run()
    check(rec["steps"][3]["V_ns"] == 20e6 and rec["steps"][3]["V_runs_ns"] == [200e6, 10e6, 20e6]
          and rec["steps"][1]["V_ns"] == 6e6 and rec["steps"][1]["V_runs_ns"] == [5e6, 300e6, 6e6]
          and rec["every"]["eligible"],
          "V_i is the median of its three judged times, in run order in V_runs_ns (one slow run is not a breach)")

    for what, kw, why in (("an intermediate output rejected", {"reject": {2}}, "output 2 rejected by acc"),
                          ("an intermediate V above v_cap (the median of three)", {"V": {3: [200e6, 150e6, 140e6]}},
                           "output 3: V = 150.0 ms above v_cap"),
                          ("a canary of output 1 accepted", {"canary_ok": [(1, "stmt-bit")]},
                           "output 1: statement canaries accepted")):
        b = make(**kw)
        rec = b.stream_run()
        sc = score(b.p, rec)
        check(sc["tracks"] == {"final": "S"} and why in sc.get("tracks_reason", {}).get("every", "")
              and rec["every"]["eligible"] is False,
              f"{what}: scored in `final` only: {sc.get('tracks_reason')}")
    b = make(out_bytes={1: proof(1) + b"\x01", 2: proof(2) + b"\x02", 3: proof(3) + b"\x03"}, reject={1, 2, 3})
    rec = b.stream_run()
    check([s["signed_proof"] for s in rec["steps"]] == [False, False, False, True]
          and rec["steps"][0]["pi_bytes"] == len(proof(1)) + 1 and score(b.p, rec)["tracks"] == {"final": "S"},
          "intermediate outputs that are not signed proofs are sized by their file and keep the run in `final`")

    # 8. the track `every` never fails the run; the final output's checks do
    for what, kw, why in (("a crashed check of intermediate outputs", {"crash": ("intermediate",)}, "its check failed"),
                          ("a crashed check of the canaries of outputs 1 and 2", {"crash": ("outputs 1 and 2",)},
                           "output 1: its statement canaries' check failed"),
                          ("an intermediate crashed in its third judged run",
                           {"crash": ("intermediate outputs, judged run 3",)}, "its check failed"),
                          ("an intermediate rejected in a later judged run", {"reject_later": {2}},
                           "output 2: rejected by acc when checked again")):
        b = make(**kw)
        try:
            rec = b.stream_run()
            sc = score(b.p, rec)
            check(sc["tracks"] == {"final": "S"} and why in sc["tracks_reason"]["every"],
                  f"{what}: scored in `final` only: {sc['tracks_reason']['every'][:160]}")
        except Fail as e:
            check(False, f"{what}: REJECT ({e})")
    b = make()
    b.stream_run()
    finals = [(w, f) for w, f in b.verify_calls if w.startswith("service run: the final output, judged run")]
    inter = [f for w, f in b.verify_calls if "intermediate" in w]
    check([f for _, f in finals] == [["step4.bin"]] * 3 and [w.endswith(f"judged run {r} of 3") for r, (w, _) in enumerate(finals, 1)] == [True] * 3
          and all("step4.bin" not in f for f in inter) and inter == [["step1.bin", "step2.bin"]] * 3 + [["step3.bin"]] * 3,
          f"every checked proof is judged in three separate badge runs, each checking it once; the final output in "
          f"three runs of its own, the intermediates apart: {[f for _, f in finals]}, {inter}")
    judged = [(w, t, warm) for w, t, warm in b.timeouts if "judged run" in w]
    cv = [t for w, t, _ in b.timeouts if w.endswith("outputs 1 and 2 canaries")]
    vc = b.p.v_cap_ms / 1e3
    check(len(judged) == 9 and all(warm for _, _, warm in judged)
          and [round(t, 9) for w, t, _ in judged if "intermediate" in w] == [round(60 + 2 * 3 * vc, 9)] * 3 + [round(60 + 2 * 2 * vc, 9)] * 3
          and [t for w, t, _ in judged if "final" in w] == [130.0] * 3 and [round(t, 9) for t in cv] == [round(60 + 2 * 4 * vc, 9)],
          f"each judged run is a fresh warmed badge run; a run of c intermediate outputs, and the canary run of outputs 1 "
          f"and 2 (c = 3 canaries), is bounded by 60 s + 2 (c + 1) v_cap, the final output's by the stream's cap: "
          f"{[(w[-24:], round(t, 3)) for w, t, _ in b.timeouts]}")
    fails_with("a crashed check of the final output", "service run: the final output, judged run 1 of 3: verify: exit -11",
               crash=("the final output",))
    fails_with("a crash in the final output's third judged run", "service run: the final output, judged run 3 of 3: verify: exit -11",
               crash=("the final output, judged run 3",))
    fails_with("the final output rejected in a later judged run", "is rejected when checked again", reject_later={4})
    b = make(reject={2})
    rec = b.stream_run()
    whats = [w for w, _ in b.verify_calls]
    check(not any("outputs 1 and 2" in w for w in whats) and sum("intermediate" in w for w in whats) == 6,
          f"once `every` is lost (output 2 rejected), no canaries of outputs 1 and 2: {whats}")

    # 9. the replay audit
    fails_with("a MISMATCH refusal logged in a timed pass",
               "timed pass 1: a SIGN in a timed pass differed from the service run's (1 refused; the first: "
               "`rf-oracle: refused (status 4): replay at one-time key index 5",
               mism=["rf-oracle: refused (status 4): replay at one-time key index 5: the trace digest differs"])
    fails_with("a MISMATCH in the service's stats", "a SIGN in a timed pass differed from the service run's (1 MISMATCH",
               stats={"signatures": 28, "replays": 56, "mismatches": 1})
    fails_with("fewer replays than timed_runs · signatures", "the timed passes made 55 signatures, not timed_runs · signatures",
               stats={"signatures": 28, "replays": 55, "mismatches": 0})
    fails_with("a SIGN missing in the third pass (replays = 3 · signatures - 1)",
               "the timed passes made 83 signatures, not timed_runs · signatures = 3 · 28",
               stats={"signatures": 28, "replays": 83, "mismatches": 0})
    fails_with("an extra SIGN in the third pass (replays = 3 · signatures + 1)",
               "the timed passes made 85 signatures, not timed_runs · signatures = 3 · 28",
               stats={"signatures": 28, "replays": 85, "mismatches": 0})
    fails_with("a MISMATCH refusal logged in the third timed pass", "timed pass 3: a SIGN in a timed pass differed",
               mism=["rf-oracle: refused (status 4): replay at one-time key index 9: the trace digest differs"], mism_from=3)
    b = make()
    rec = b.stream_run()
    check(b.p.timed_runs == 3 and rec["service_stats"]["replays"] == 3 * rec["service_stats"]["signatures"],
          "three passes, each replaying every signature: replays = 3 · signatures passes the audit")
    rec["steps"][1]["P_timed_s"] = rec["steps"][1]["P_timed_s"][:2]
    try:
        score(b.p, rec)
        check(False, "a step with two timed times is scored")
    except MalformedStream as e:
        check("step 2" in str(e), f"a step with two timed times is MalformedStream (the organiser's ERROR): {e}")
    fails_with("no replay statistics", "the service reported no replay statistics", stats={"signatures": 28})

    # 10. the page cache is warmed before every request
    d = tempfile.mkdtemp(prefix="rf-warm-", dir=os.environ.get("RF_TEST_TMP"))
    setup, bindir = os.path.join(d, "setup"), os.path.join(d, "bin")
    os.makedirs(os.path.join(setup, "sub"))
    os.makedirs(bindir)
    open(os.path.join(setup, "a.bin"), "wb").write(b"a" * 3_000_000)
    open(os.path.join(setup, "sub", "b.bin"), "wb").write(b"b" * 1000)
    os.symlink(os.path.join(setup, "a.bin"), os.path.join(setup, "link"))
    open(os.path.join(bindir, "prover"), "wb").write(b"p" * 5000)
    events, socks = [], []
    w = Bench.__new__(Bench)
    w.p = Params.load(os.path.join(ROOT, "harness", "smoke.toml"))
    w.run = SimpleNamespace(bin_dir=bindir, setup_dir=setup, mem="1G")
    w.req_root, w.work, w.deadline = None, d, None
    w.warm_caches = lambda: (events.append("warm"), Bench.warm_caches(w))[1]

    svc_w = FakeSvc()
    svc_w.sock_dir = os.path.join(d, "svc", "stream")
    svc_w.socket_path = os.path.join(svc_w.sock_dir, "oracle.sock")

    def fake_request(run, kind, work, sock, inputs, step_s, file_cap, **kw):
        events.append("request")
        socks.append((os.path.dirname(sock) == os.path.join(d, "svc", "requests") and os.listdir(sock) == [],
                      kw.get("sock_at_go") == svc_w.socket_path))
        r = Step()
        r.seconds, r.proof = 0.001, b"x"
        return r
    real_request, bench_mod.request = bench_mod.request, fake_request
    try:
        rs = [w.one(svc_w, f"service{i}", "first", {}) for i in (1, 2, 3)]
    finally:
        bench_mod.request = real_request
    check(events == ["warm", "request"] * 3 and all(r.warm_bytes == 3_006_000 and r.warm_s >= 0 for r in rs),
          f"the setup directory and the binary are read in full before every request (no link followed): "
          f"{events}, {rs[0].warm_bytes} bytes")
    check(socks == [(True, True)] * 3 and not os.listdir(os.path.join(d, "svc", "requests")),
          "every request gets its own empty socket directory beside the service's, the service's socket linked "
          "in only at `go` (sock_at_go), and the directory removed after it")
    b = make()
    rec = b.stream_run()
    check(all("warm_s" in s and all("warm_s" in x for x in s["timed"]) for s in rec["steps"]),
          "the warm-up's time is recorded for every request of the service run and the timed passes")

    recs = [make().stream_run() for _ in range(2)]
    check(recs[0]["shape"] == recs[1]["shape"] and len(set(recs[0]["seeds"] + recs[1]["seeds"])) == 2 * 4,
          "two evaluations: the same shape, fresh seeds each")
    print(f"{fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
