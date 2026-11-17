#!/usr/bin/env python3
"""The stream's control flow (AGENTS.md §6), with stub requests, checks and service.

  python3 tests/harness/test_stream.py

1. Inputs: step 1 gets `chain0.json … chain3.json`, step i ≥ 2 also `prev.stmt` and `prev.bin`
   (the service run's previous output); a timed request also `oracle.key` (the key the service's
   replay mode revealed, 64 hex and a newline); the service run's requests get no key. The runner's
   statements are `X_i = nodeStmt (nodeStmt L_i1 L_i2) (nodeStmt L_i3 L_i4)`, `c_1 = X_1`,
   `c_i = nodeStmt c_{i-1} X_i`; every chain has the season's `n`, every step `n_i = 4 n`.
2. The service run, then `timed_runs` timed passes, each after a `replay`; the timed passes' `prev.bin`
   is the service run's output; `P_i` is the minimum of the timed times, the service run's time is
   recorded, not scored; the score is `P̄ · 2^(|π_M| / size_ref)`.
3. A timed output that differs from the service run's is the entry's REJECT, naming the pass, the step
   and the first differing byte offset.
4. The final output: rejected by acc, |π_M| above final_pi_cap, V_M above v_cap (after two more
   timings: the minimum counts, so one slow check is not a breach), a statement canary accepted, any
   output above pi_cap: each the entry's REJECT. An intermediate output rejected by acc, or with V
   above v_cap, or an accepted canary of output 1 or 2: scored in `final` only, the reason recorded.
5. The stream's cap reached is the entry's REJECT (no truncation).
6. Calibration samples: before the service run's step 1, before each timed pass and a closing one.
7. Two evaluations have the same shape and fresh starts.
"""
import json
import os
import sys
import tempfile
from types import SimpleNamespace

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from rfh import digest, signed  # noqa: E402
from rfh.bench import Bench, Fail, Params, score  # noqa: E402
from rfh.prover import Step  # noqa: E402

KEY = "ab" * 32


class FakeSvc:
    vk, sock_dir, info = b"k" * 32, "/nonexistent", {}
    proc = SimpleNamespace(poll=lambda: None)

    def __init__(self):
        self.replays = 0

    def refusals(self, n=8):
        return []

    def replay(self):
        self.replays += 1
        return KEY


def proof(i, pi_bytes=100):
    """A signed-proof file of `pi_bytes` bytes of π naming step `i`."""
    return signed.Signed(f"step{i}".encode().ljust(pi_bytes, b".")).encode()


def make(times=None, timed=None, M=4, reject=(), V=None, recheck=None, canary_ok=(), out_bytes=None, differ=None,
         cap_at=None):
    """A Bench over the smoke season with stubs: the service run's request i takes times[i] s, timed pass
    t's timed[t][i] s; outputs `proof(i)` (or `out_bytes[i]`); `acc` rejects the steps in `reject`;
    V_i = V[i] ns (default 1 ms), the two extra timings `recheck[i]`; the canaries (step, name) in
    `canary_ok` accepted; timed pass t's step i differs at byte 7 for (t, i) = `differ`; the cap is
    reached at the request tagged `cap_at`."""
    p = Params.load(os.path.join(ROOT, "harness", "smoke.toml"))
    p.M = M
    p.calib_idle_s = 0.0
    p.v_cap_ms = Params.load(os.path.join(ROOT, "harness", "season.toml")).v_cap_ms     # the season's 128 ms
    times = times or {i: 0.01 for i in range(1, M + 1)}
    timed = timed or {t: {i: 0.001 * t for i in range(1, M + 1)} for t in range(1, p.timed_runs + 1)}
    V = V or {}
    b = Bench.__new__(Bench)
    b.p, b.log, b.samples, b.deadline, b.req_root = p, (lambda m: None), [], None, None
    b.service_bin = None                     # the chains are short: digest.py hashes them in Python
    b.work = tempfile.mkdtemp(prefix="rf-stream-", dir=os.environ.get("RF_TEST_TMP"))
    b.store = os.path.join(b.work, "store")
    b.calls, b.reqs, b.svc = [], {}, FakeSvc()
    b.service = lambda name: b.svc
    b.stop = lambda svc, rec: None
    b.sample = lambda before: b.samples.append({"before": before, "calib_ns": p.calib_ref_ns, "triv_ns": 1000})

    def verify(items, what, timeout, warm=False):
        out = []
        for vk, c, rel in items:
            i = int(os.path.basename(rel).split(".")[0][4:])
            if what.endswith("canaries"):
                out.append((False, 1))
            elif "timed again" in what:
                out.append((True, recheck[i].pop(0)))
            else:
                out.append((i not in reject, V.get(i, 10 ** 6)))
        return out
    b.verify = verify

    def canary_check(vk, targets, what):
        res, n = Bench.canary_check(b, vk, targets, what)
        for k, name in canary_ok:
            if k in res:
                res[k].append(name)
        b.canary_targets = [k for k, _, _, _ in targets]
        return res, n
    b.canary_check = canary_check

    def one(svc, tag, kind, ins):
        b.calls.append(tag)
        b.reqs[tag] = (kind, ins)
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
    timed = {1: {1: 0.010, 2: 0.020, 3: 0.004, 4: 0.040}, 2: {1: 0.012, 2: 0.018, 3: 0.003, 4: 0.050}}
    b = make(times, timed)
    rec = b.stream_run()
    st = rec["steps"]
    p = b.p
    k1, in1 = b.reqs["service1"]
    k2, in2 = b.reqs["service2"]
    chains = [f"chain{j}.json" for j in range(4)]
    check(k1 == "first" and sorted(in1) == chains and k2 == "step"
          and sorted(in2) == chains + ["prev.bin", "prev.stmt"] and in2["prev.bin"] == proof(1),
          "the service run: step 1 gets four chains; step 2 the previous output, its statement and four chains; no key")
    ld = [bytes.fromhex(d) for d in rec["leaf_digests"]]
    X = [digest.node_stmt(digest.node_stmt(ld[4 * i], ld[4 * i + 1]), digest.node_stmt(ld[4 * i + 2], ld[4 * i + 3]))
         for i in range(4)]
    c = [X[0]]
    for x in X[1:]:
        c.append(digest.node_stmt(c[-1], x))
    check(rec["statements"] == [x.hex() for x in c] and rec["step_statements"] == [x.hex() for x in X]
          and in2["prev.stmt"] == (c[0].hex() + "\n").encode(),
          "the statements: X_i = nodeStmt (nodeStmt L1 L2) (nodeStmt L3 L4), c_1 = X_1, c_i = nodeStmt c_{i-1} X_i")
    starts = rec["starts"]
    check(len(starts) == 16 and all(json.loads(b.reqs[f"service{i}"][1][f"chain{j}.json"])
                                    == {"n": p.n, "start": starts[4 * (i - 1) + j]} for i in range(1, 5) for j in range(4))
          and all(s["n"] == 4 * p.n for s in st) and rec["shape"] == {"M": 4, "chains": 4, "n": p.n},
          f"4 · M fresh starts, every chain of the season's n = {p.n}, n_i = 4 n")
    t1 = [b.reqs[f"timed1-step{i}"] for i in range(1, 5)]
    check(b.calls == [f"service{i}" for i in range(1, 5)] + [f"timed{t}-step{i}" for t in (1, 2) for i in range(1, 5)]
          and b.svc.replays == 2
          and all(ins["oracle.key"] == (KEY + "\n").encode() for _, ins in t1)
          and t1[2][1]["prev.bin"] == proof(2) and t1[0][0] == "first"
          and sorted(t1[1][1]) == sorted(chains + ["prev.bin", "prev.stmt", "oracle.key"]),
          "two timed passes after a replay each; a timed request gets oracle.key and the service run's previous output")
    check([s["P_s"] for s in st] == [0.010, 0.018, 0.003, 0.040] and [s["P_service_s"] for s in st] == [0.5, 0.6, 0.7, 0.8]
          and st[3]["P_timed_s"] == [0.040, 0.050],
          f"P_i is the minimum of the timed passes; the service run's times are recorded: {[s['P_s'] for s in st]}")
    sc = score(p, rec)
    Pbar = p.n_ref / (4 * p.n) * (sum(x ** 3 for x in (0.010, 0.018, 0.003, 0.040)) / 4) ** (1 / 3)
    check(abs(sc["P_bar"] - Pbar) < 1e-12 and sc["final_pi_bytes"] == 100
          and abs(sc["S"] - Pbar * 2 ** (100 / 2 ** 20)) < 1e-12
          and sc["tracks"] == {"final": "S", "every": "S"} and "tracks_reason" not in sc,
          f"S = P̄ · 2^(|π_M| / size_ref), both tracks: {sc['S']:.6g}, {sc['tracks']}")
    check([x["before"] for x in b.samples] == ["service run, step 1", "timed pass 1", "timed pass 2", "closing"],
          f"calibration samples: {[x['before'] for x in b.samples]}")
    check(sorted(b.canary_targets) == [1, 2, 4] and st[0]["canaries_accepted"] == [] and rec["canaries"] == 6,
          "statement canaries of outputs 1, 2 and M (stmt-bit and first-child each)")

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
    stash = signed.Signed(b"", [(b"q" * (p.pi_cap + 1), bytes(32))]).encode()
    fails_with("a rejected intermediate that parses, its state in the trace (sized by its file)",
               f"service run, step 2: the output, rejected by acc, has {len(stash)} bytes, above pi_cap",
               out_bytes={2: stash}, reject={2})
    fails_with("V_M above v_cap in all three timings", "above v_cap = 128 ms", V={4: 200e6}, recheck={4: [150e6, 190e6]})
    fails_with("a canary of the final output accepted", "statement canaries accepted by acc", canary_ok=[(4, "x")])
    fails_with("the stream's cap", "stream_s", cap_at="timed1-step2")

    b = make(V={4: 200e6}, recheck={4: [100e6, 300e6]})
    rec = b.stream_run()
    check(rec["steps"][3]["V_ns"] == 100e6 and rec["steps"][3]["V_runs_ns"] == [200e6, 100e6, 300e6],
          "V_M above the cap is timed twice more and the minimum counts (one slow check is not a breach)")

    for what, kw, why in (("an intermediate output rejected", {"reject": {2}}, "output 2 rejected by acc"),
                          ("an intermediate V above v_cap", {"V": {3: 200e6}, "recheck": {3: [150e6, 140e6]}},
                           "output 3: V = 140.0 ms above v_cap"),
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

    recs = [make().stream_run() for _ in range(2)]
    check(recs[0]["shape"] == recs[1]["shape"] and len(set(recs[0]["starts"] + recs[1]["starts"])) == 2 * 16,
          "two evaluations: the same shape, fresh chain starts each")
    print(f"{fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
