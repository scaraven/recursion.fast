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
4. The verifier check: every checked proof is judged in three separate badge runs of its own, each
   checking it once and nothing else (no proof twice in one run, and no other output of the stream
   beside it: output `i + 1` contains `π_i`), `V_i` the median of its three times (`V_runs_ns` in run
   order), so one slow run is not a breach and one fast run is no pass; a verifier that memoises its
   children's acceptance across the checks of one process gains nothing. The final
   output: rejected by acc (in its first run, or in a later one), |π_M| above final_pi_cap, V_M above
   v_cap, a statement canary accepted, any output above pi_cap, where an output `acc` did not accept
   (rejected in any run, or its check crashed in any run) is sized by its whole file: each the
   entry's REJECT. An intermediate output rejected by acc, or with V above v_cap, or an accepted
   canary of output 1 or 2: scored in `final` only, the reason recorded. Each judged run of an
   intermediate output (`c = 1`), and the canary run of outputs 1 and 2, is bounded by `60 s + 2 (c +
   1) v_cap`; the final output's runs by the stream's cap.
5. The stream's cap reached is the entry's REJECT (no truncation), also when it is reached during the
   checks: no badge run starts past it, and every badge run shares one absolute bound, 30 s past it.
6. Calibration samples: before the service run's step 1, before each timed pass and a closing one.
7. Two evaluations have the same shape and fresh seeds.
8. The track `every` never fails the run: a crashed check of intermediate outputs (in any judged
   run) or of the canaries of outputs 1 and 2, or an intermediate rejected in a later judged run,
   costs only the track; the final output is checked on its own runs, and a crash there (or its
   rejection in a later run) is a REJECT; the canaries of outputs 1 and 2 are checked even once
   `every` is lost, and every judged run is made after a failed one: the same badge runs, in the
   same order, whatever the entry's verifier does (review LR5 L1).
9. The replay audit: a MISMATCH refusal logged in a timed pass (the third included), a MISMATCH in the
   service's final stats, or `replays ≠ timed_runs · signatures` (one SIGN missing or extra over the
   three passes) is the entry's REJECT. A step record without exactly three timed times is
   `MalformedStream` (the organiser's ERROR).
10. Before every request nothing is re-read (the setup and the binary are the runner's tmpfs copies,
    `Run.publish`): a fresh copy for the service run (run-benchmark's, if no sandbox has bound it)
    and for each timed pass, made between the passes (review LR5 H1); every request stages the same five unnamed inodes (its inputs and a placeholder
    for each input it does not get, 65 bytes where the input has that fixed size); every request
    gets its own empty socket directory, named by 16 random hex characters (never its tag), into
    which the service's socket is linked only at `go`.
11.-12. The reject stage: every REJECT path above names where it was rejected (`Fail.stage`, the result's
    `reject_stage`): `request` (a service-run request's failure or a cap of its output, `final_pi_cap`
    included), `check` (a check by the badge failed, rejected or broke `v_cap`, an output not accepted
    and sized by its file above `pi_cap`, a canary accepted), `timed-pass` (a byte or replay mismatch,
    a failed timed request), `stream-cap`; a failure with no stage of its own takes its phase's; the
    real `Bench.verify` names a failed badge run `check`; the service failing at its stop never
    replaces a failure in flight (recorded as `stop_error`), and the calibration's service failing at
    its stop is a harness ERROR (no entry process ran), never a REJECT.
    `run-benchmark.py` records it as `reject_stage` (`prover` for the prover's build), and a stream
    record the score cannot be computed from (`MalformedStream`) as `benchmark: error`,
    `organiser_error: malformed`, with no reject stage; a machine whose memory caps fall back to
    prlimit is `benchmark: error`, `organiser_error: fingerprint`, before the prover's build, unless
    `RF_ALLOW_PRLIMIT=1` (recorded as `machine.memcap_override`), and so is `RF_TEST_BADGE_HOST_ROOT=1`
    unless `RF_TEST_OVERRIDES=1` (recorded as `machine.badge_host_root`). A kill by the OOM killer
    reads as the cap's only when the scope's memory events or its peak say so (`oom_label`).
"""
import importlib.util
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
         cap_at=None, crash=(), reject_later=(), stats=None, mism=(), mism_from=1, fail_at=None, memo=False):
    """A Bench over the smoke season with stubs: the service run's request i takes times[i] s, timed pass
    t's timed[t][i] s; outputs `proof(i)` (or `out_bytes[i]`); `acc` rejects the steps in `reject` in
    every judged run and those in `reject_later` in judged runs 2 and 3 only; V_i in judged run r is
    V[i][r - 1] ns (V[i] three times, or one number for all three; default 1 ms); the canaries (step,
    name) in `canary_ok` accepted; timed pass t's step i differs at byte 7 for (t, i) = `differ`; the
    cap is reached at the request tagged `cap_at`; a badge run whose description contains a string of
    `crash` crashes; the service's stats are `stats` (default: the timed passes replayed every
    signature) and its logged MISMATCH refusals `mism`, from timed pass `mism_from` on; the request
    tagged `fail_at` fails with no reject stage of its own (the stream names it from its phase); with
    `memo`, a verifier that re-checks output `i - 1` inside output `i` (200 ms) unless the same badge
    process has checked output `i - 1` already (then 1 ms), as a memo of its children's acceptance
    would."""
    p = Params.load(os.path.join(ROOT, "harness", "smoke.toml"))
    p.M = M
    p.calib_idle_s = 0.0
    p.v_cap_ms = Params.load(os.path.join(ROOT, "harness", "season.toml")).v_cap_ms     # the season's 64 ms
    times = times or {i: 0.01 for i in range(1, M + 1)}
    timed = timed or {t: {i: 0.001 * t for i in range(1, M + 1)} for t in range(1, p.timed_runs + 1)}
    V = V or {}
    b = Bench.__new__(Bench)
    b.p, b.log, b.samples, b.deadline = p, (lambda m: None), [], None
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
            raise Fail(f"{what}: verify: exit -11, 0 of {len(items)} answers", kind="crash", stage="check")
        run = int(what.split("judged run ")[1].split()[0]) if "judged run " in what else None
        out, seen = [], set()
        for vk, c, rel in items:
            i = int(os.path.basename(rel).split(".")[0][4:])
            if what.endswith("canaries"):
                out.append((False, 1))
            elif memo:
                out.append((True, 10 ** 6 if i == 1 or i - 1 in seen else 200 * 10 ** 6))
                seen.add(i)
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
            raise Fail(f"{tag}: {b.deadline[1]} (timeout)", stage="stream-cap")    # as Bench.one
        if tag == fail_at:
            raise Fail(f"{tag}: exit 1")
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

    def publish():
        b.calls.append("copy")
        b.run.view, b.run.seen = ("bin", "setup"), False
        b.run.copies.append((1000, 0.001))
        return b.run.copies[-1]
    b.run = SimpleNamespace(view=None, seen=False, copies=[], publish=publish)
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
    check(b.data_seen == [[f"step{i}.bin" for i in range(1, 5)]] * len([c for c in b.calls if c != "copy"]) and not os.path.exists(b.leafdata)
          and os.path.dirname(ld) == os.path.realpath(b.work)
          and not ld.startswith(os.path.realpath(b.store) + os.sep) and ld != os.path.realpath(b.store),
          "the data of all M steps is written before the first request, to a runner-only directory beside the store "
          "(never under it), and removed after the stream")
    t1 = [b.reqs[f"timed1-step{i}"] for i in range(1, 5)]
    check(b.calls == ["copy"] + [f"service{i}" for i in range(1, 5)]
          + [x for t in (1, 2, 3) for x in ["copy"] + [f"timed{t}-step{i}" for i in range(1, 5)]]
          and [c["for"] for c in rec["copies"]] == ["the service run", "timed pass 1", "timed pass 2", "timed pass 3"],
          f"the service run and each timed pass bind a fresh copy of the binary and the setup, made before the pass's "
          f"first request and after the previous pass's last (review LR5 H1): {b.calls}, {rec['copies']}")
    calls = [c for c in b.calls if c != "copy"]
    b0 = make()
    b0.run.view, b0.run.copies = ("bin", "setup"), [(5, 0.5)]   # run-benchmark's copy, bound by no sandbox yet
    r0 = b0.stream_run()
    b1 = make()
    b1.run.view, b1.run.seen, b1.run.copies = ("bin", "setup"), True, [(5, 0.5)]
    b1.stream_run()
    check(r0["copies"][0] == {"for": "the service run", "bytes": 5, "seconds": 0.5} and b0.calls.count("copy") == 3
          and b1.calls[0] == "copy" and b1.calls.count("copy") == 4,
          "the service run uses run-benchmark's copy if no sandbox has bound it, else makes a fresh one")
    check(calls == [f"service{i}" for i in range(1, 5)] + [f"timed{t}-step{i}" for t in (1, 2, 3) for i in range(1, 5)]
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

    def fails_with(what, want, stage, **kw):
        try:
            make(**kw).stream_run()
            check(False, f"{what}: passes")
        except Fail as e:
            check(want in str(e) and e.stage == stage, f"{what}: REJECT at {e.stage} (want {stage}): {e}")
    fails_with("a timed output one bit off", "timed pass 2, step 3: the output differs from the service run's output of the "
               "step, first at byte offset 7", "timed-pass", differ=(2, 3))
    fails_with("the final output rejected", "the final output (step 4) is rejected by acc", "check", reject={4})
    big = signed.Signed(b"x" * (p.final_pi_cap + 1)).encode()
    fails_with("|π_M| above final_pi_cap", f"above final_pi_cap = {p.final_pi_cap}", "request", out_bytes={4: big})
    huge = b"z" * (p.pi_cap + 1)
    fails_with("an intermediate output above pi_cap (not a signed proof: its file size)",
               f"service run, step 2: the output's file size is {p.pi_cap + 1} bytes, above pi_cap", "request", out_bytes={2: huge})
    stash = signed.Signed(b"", [(b"q" * (2 << 20), bytes(32))]).encode()     # |π| = 0, 2 MiB in the trace
    not_acc = f"service run, step 2: the output, not accepted by acc (rejected, or its check failed), has {len(stash)} bytes"
    fails_with("a rejected intermediate that parses, its state in the trace (sized by its file)", not_acc, "check",
               out_bytes={2: stash}, reject={2})
    fails_with("an intermediate whose check crashed, its state in the trace (sized by its file)", not_acc, "check",
               out_bytes={2: stash}, crash=("intermediate output 2,",))
    fails_with("an intermediate rejected in a later judged run, its state in the trace (sized by its file)", not_acc, "check",
               out_bytes={2: stash}, reject_later={2})
    fails_with("an intermediate whose second judged run crashed, its state in the trace (sized by its file)", not_acc, "check",
               out_bytes={2: stash}, crash=("intermediate output 2, judged run 2",))
    fails_with("V_M above v_cap in all three judged runs", "above v_cap = 64 ms", "check", V={4: [200e6, 150e6, 190e6]})
    fails_with("V_M above v_cap in two of its three judged runs (the median counts, not the least)",
               "takes V = 200.000 ms (the median of its three judged runs, [200.0, 10.0, 300.0] ms), above v_cap = 64 ms", "check",
               V={4: [200e6, 10e6, 300e6]})
    fails_with("a canary of the final output accepted", "statement canaries accepted by acc", "check", canary_ok=[(4, "x")])
    fails_with("the stream's cap", "stream_s", "stream-cap", cap_at="timed1-step2")
    fails_with("a service-run request that fails (no stage of its own: the phase's)", "service3: exit 1", "request",
               fail_at="service3")
    fails_with("a timed request that fails (no stage of its own: the phase's)", "timed2-step1: exit 1", "timed-pass",
               fail_at="timed2-step1")
    b = make()
    b.left = lambda: -1.0
    try:
        b.stream_run()
        check(False, "the stream's cap before the service run's first step: passes")
    except Fail as e:
        check(e.stage == "stream-cap" and "service run, step 1" in str(e),
              f"the stream's cap reached before a service-run step: REJECT at {e.stage}: {e}")

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
                           {"crash": ("intermediate output 1, judged run 3",)}, "output 1: its check failed"),
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
          and all("step4.bin" not in f for f in inter)
          and inter == [["step1.bin"]] * 3 + [["step2.bin"]] * 3 + [["step3.bin"]] * 3,
          f"every checked proof is judged in three separate badge runs of its own, each checking it once and nothing "
          f"else; the final output in three runs of its own, each intermediate in three of its own: "
          f"{[f for _, f in finals]}, {inter}")
    judged = [(w, t, warm) for w, t, warm in b.timeouts if "judged run" in w]
    cv = [t for w, t, _ in b.timeouts if w.endswith("outputs 1 and 2 canaries")]
    vc = b.p.v_cap_ms / 1e3
    check(len(judged) == 12 and all(warm for _, _, warm in judged)
          and [round(t, 9) for w, t, _ in judged if "intermediate" in w] == [round(60 + 2 * 2 * vc, 9)] * 9
          and [t for w, t, _ in judged if "final" in w] == [130.0] * 3 and [round(t, 9) for t in cv] == [round(60 + 2 * 4 * vc, 9)],
          f"each judged run is a fresh warmed badge run; a run of an intermediate output (c = 1), and the canary run of "
          f"outputs 1 and 2 (c = 3 canaries), is bounded by 60 s + 2 (c + 1) v_cap, the final output's by the stream's cap: "
          f"{[(w[-24:], round(t, 3)) for w, t, _ in b.timeouts]}")
    fails_with("a crashed check of the final output", "service run: the final output, judged run 1 of 3: verify: exit -11", "check",
               crash=("the final output",))
    fails_with("a crash in the final output's third judged run", "service run: the final output, judged run 3 of 3: verify: exit -11", "check",
               crash=("the final output, judged run 3",))
    fails_with("the final output rejected in a later judged run", "is rejected when checked again", "check", reject_later={4})
    b = make(reject={2})
    rec = b.stream_run()
    whats = [w for w, _ in b.verify_calls]
    check(sum("outputs 1 and 2" in w for w in whats) == 1 and sum("intermediate" in w for w in whats) == 9
          and score(b.p, rec)["tracks"] == {"final": "S"},
          f"once `every` is lost (output 2 rejected), the canaries of outputs 1 and 2 are checked all the same (review "
          f"LR5 L1), and the run stays out of `every`: {whats}")
    # review LR5 L1: the number of badge runs (sandboxes) does not depend on the entry's verifier
    base = make()
    base.stream_run()
    n0 = [w for w, _ in base.verify_calls]
    counts = {}
    for what, kw in (("an intermediate crashed in its first judged run", {"crash": ("intermediate output 1, judged run 1",)}),
                     ("every judged run of an intermediate crashed", {"crash": ("intermediate output 2",)}),
                     ("an intermediate rejected", {"reject": {2}}), ("the canaries of outputs 1 and 2 crashed",
                                                                      {"crash": ("outputs 1 and 2",)})):
        b = make(**kw)
        b.stream_run()
        counts[what] = [w for w, _ in b.verify_calls] == n0
    check(len(n0) == 14 and all(counts.values()),
          f"the same {len(n0)} badge runs, in the same order, whatever the entry's verifier does with the "
          f"intermediate outputs and the canaries: {counts}")

    # a memo of the children's acceptance across the checks of one process (review LR2 M1): output i + 1
    # re-checks π_i inside it; a process that had just checked output i would answer that from the memo.
    # Each output is judged in runs of its own, so every check of outputs 2 … M pays its child's check.
    # First a control (the final output was judged alone before the fix too): REJECT for its own 200 ms
    b = make(memo=True)
    try:
        b.stream_run()
        check(False, "a memo of the children's acceptance: the final output passes at 200 ms")
    except Fail as e:
        check(e.stage == "check" and "V = 200.000 ms" in str(e), f"a memo of the children's acceptance: the final "
              f"output judged at its own 200 ms, REJECT: {e}")
    b = make(memo=True, V=None)
    seen = []
    b.verify, inner = (lambda items, what, timeout, warm=False:
                       (seen.append((what, [os.path.basename(r) for _, _, r in items])),
                        inner(items, what, timeout, warm))[1]), b.verify
    p_m = b.p
    p_m.v_cap_ms = 300.0
    rec = b.stream_run()
    check([s["V_ns"] for s in rec["steps"]] == [10 ** 6] + [200 * 10 ** 6] * 3
          and all(len(f) == 1 for w, f in seen if "judged run" in w) and len(seen) > 12,
          f"... with v_cap 300 ms: outputs 2 and 3 are judged at 200 ms in runs that check them alone, never at the "
          f"1 ms a run that had checked their child first would give: {[s['V_ns'] / 1e6 for s in rec['steps']]} ms")
    old = inner([(b.svc.vk, b"c" * 32, "stream/step1.bin"), (b.svc.vk, b"c" * 32, "stream/step2.bin")], "a batch", 1.0)
    check(old == [(True, 10 ** 6), (True, 10 ** 6)],
          f"... the same verifier with outputs 1 and 2 in one run (the runner before review LR2): output 2 at 1 ms: {old}")

    # the stream's cap during the checks (review LR2 L4): no badge run starts past the cap, and the runs
    # share one absolute bound 30 s past it, not 30 s each
    for at, what, nxt in ((3, "an intermediate output's judged runs", "intermediate output 2, judged run 1 of 3"),
                          (11, "the final output's judged runs", "the final output, judged run 3 of 3"),
                          (13, "the canaries", "outputs 1 and 2 canaries")):
        b = make()
        n_runs = [0]
        clock = {"t": 100.0}
        inner = b.verify

        def counting(items, w, timeout, warm=False, inner=inner, n_runs=n_runs, clock=clock, at=at):
            n_runs[0] += 1
            if n_runs[0] == at:
                clock["t"] = -5.0          # the cap passes during this run
            return inner(items, w, timeout, warm)
        b.verify, b.left = counting, (lambda clock=clock: clock["t"])
        try:
            b.stream_run()
            check(False, f"the stream's cap reached during {what}: passes")
        except Fail as e:
            check(e.stage == "stream-cap" and "stream_s" in str(e) and n_runs[0] == at and nxt in str(e),
                  f"the stream's cap reached during {what} (badge run {at}): REJECT at {e.stage}, no badge run started "
                  f"after it ({n_runs[0]} runs): {str(e)[:120]}")
    b = Bench.__new__(Bench)
    b.deadline = (bench_mod.time.monotonic() - 10, "the stream's cap")
    late = b.capped()
    b.deadline = (bench_mod.time.monotonic() - 40, "the stream's cap")
    check(19 < late <= 20 and b.capped() == 0.0,
          f"past the cap every badge run gets what is left of one bound 30 s past it (10 s past: {late:.2f} s; 40 s "
          f"past: {b.capped()} s), not 30 s each")

    # 9. the replay audit
    fails_with("a MISMATCH refusal logged in a timed pass",
               "timed pass 1: a SIGN in a timed pass differed from the service run's (1 refused; the first: "
               "`rf-oracle: refused (status 4): replay at one-time key index 5", "timed-pass",
               mism=["rf-oracle: refused (status 4): replay at one-time key index 5: the trace digest differs"])
    fails_with("a MISMATCH in the service's stats", "a SIGN in a timed pass differed from the service run's (1 MISMATCH", "timed-pass",
               stats={"signatures": 28, "replays": 56, "mismatches": 1})
    fails_with("fewer replays than timed_runs · signatures", "the timed passes made 55 signatures, not timed_runs · signatures", "timed-pass",
               stats={"signatures": 28, "replays": 55, "mismatches": 0})
    fails_with("a SIGN missing in the third pass (replays = 3 · signatures - 1)",
               "the timed passes made 83 signatures, not timed_runs · signatures = 3 · 28", "timed-pass",
               stats={"signatures": 28, "replays": 83, "mismatches": 0})
    fails_with("an extra SIGN in the third pass (replays = 3 · signatures + 1)",
               "the timed passes made 85 signatures, not timed_runs · signatures = 3 · 28", "timed-pass",
               stats={"signatures": 28, "replays": 85, "mismatches": 0})
    fails_with("a MISMATCH refusal logged in the third timed pass", "timed pass 3: a SIGN in a timed pass differed", "timed-pass",
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
    fails_with("no replay statistics", "the service reported no replay statistics", "timed-pass", stats={"signatures": 28})

    # 10. no warm-up before a request; the same number of inodes staged in every request
    d = tempfile.mkdtemp(prefix="rf-warm-", dir=os.environ.get("RF_TEST_TMP"))
    setup, bindir = os.path.join(d, "setup"), os.path.join(d, "bin")
    os.makedirs(os.path.join(setup, "sub"))
    os.makedirs(bindir)
    open(os.path.join(setup, "a.bin"), "wb").write(b"a" * 3_000_000)
    open(os.path.join(setup, "sub", "b.bin"), "wb").write(b"b" * 1000)
    os.symlink(os.path.join(setup, "a.bin"), os.path.join(setup, "link"))
    open(os.path.join(bindir, "prover"), "wb").write(b"p" * 5000)
    events, socks, staged = [], [], []
    w = Bench.__new__(Bench)
    w.p = Params.load(os.path.join(ROOT, "harness", "smoke.toml"))
    w.run = SimpleNamespace(bin_dir=bindir, setup_dir=setup, mem="1G")
    w.work, w.deadline, w.scrub_bin, w.phase = d, None, None, "request"
    w.scrub = lambda: (events.append("scrub"), None)[1]

    svc_w = FakeSvc()
    svc_w.sock_dir = os.path.join(d, "svc", "stream")
    svc_w.socket_path = os.path.join(svc_w.sock_dir, "oracle.sock")

    status = ["ok"]

    def fake_request(run, kind, work, sock, inputs, step_s, file_cap, **kw):
        events.append("request")
        staged.append((sorted(inputs), [len(x) for x in kw.get("pads", ())]))
        socks.append((os.path.dirname(sock) == os.path.join(d, "svc", "requests") and os.listdir(sock) == [],
                      kw.get("sock_at_go") == svc_w.socket_path, os.path.basename(sock)))
        r = Step()
        r.seconds, r.proof, r.status = 0.001, b"x", status[0]
        return r
    real_request, bench_mod.request = bench_mod.request, fake_request
    try:
        full = {"leaf.json": b"{}", "leaf.bin": b"x" * 64, "prev.stmt": b"s" * 65, "prev.bin": b"p", "oracle.key": b"k" * 65}
        rs = [w.one(svc_w, f"service{i}", "first", {k: v for k, v in full.items() if k in names})
              for i, names in ((1, ("leaf.json", "leaf.bin")), (2, ("leaf.json", "leaf.bin", "oracle.key")),
                               (3, ("leaf.json", "leaf.bin", "prev.stmt", "prev.bin", "oracle.key")))]
        stages = []
        for phase, st, dl in (("request", "exit 1", None), ("timed-pass", "exit 1", None),
                              ("request", "timeout", (0.0, "the stream's cap stream_s = 1 s was reached")),
                              ("timed-pass", "no ready line", (0.0, "the stream's cap stream_s = 1 s was reached"))):
            w.phase, w.deadline, status[0] = phase, dl, st
            try:
                w.one(svc_w, "timed3-step5", "step", {})
                stages.append(None)
            except Fail as e:
                stages.append((e.stage, str(e).split(" (")[0]))
        w.phase, w.deadline, status[0] = "request", None, "ok"
    finally:
        bench_mod.request = real_request
    check(events == ["scrub", "request"] * 7 and all(not hasattr(r, "warm_s") for r in rs),
          f"before every request the scrub runs and nothing is re-read (the setup is the runner's tmpfs copy): {events}")
    check(staged[:3] == [(["leaf.bin", "leaf.json"], [65, 0, 65]), (["leaf.bin", "leaf.json", "oracle.key"], [65, 0]),
                         (["leaf.bin", "leaf.json", "oracle.key", "prev.bin", "prev.stmt"], [])],
          f"every request stages five inodes, a placeholder for each input it does not get (65 bytes for a statement or "
          f"the key, which have that size): {staged[:3]}")
    names = [x[2] for x in socks]
    check([x[:2] for x in socks] == [(True, True)] * 7 and not os.listdir(os.path.join(d, "svc", "requests"))
          and all(len(x) == 16 and all(c in "0123456789abcdef" for c in x) for x in names) and len(set(names)) == 7,
          f"every request gets its own empty socket directory beside the service's, named by 16 random hex characters "
          f"(never its tag: {names[:3]}), the service's socket linked in only at `go` (sock_at_go), and the directory "
          "removed after it")
    check(stages == [("request", "timed3-step5: exit 1"), ("timed-pass", "timed3-step5: exit 1"),
                     ("stream-cap", "timed3-step5: the stream's cap stream_s = 1 s was reached"),
                     ("stream-cap", "timed3-step5: the stream's cap stream_s = 1 s was reached")],
          f"a failed request is REJECTed at `request` in the service run and `timed-pass` in a timed pass, at "
          f"`stream-cap` when the stream's cap ended it; its Fail names its tag: {stages}")
    b = make()
    rec = b.stream_run()
    check(all("warm_s" not in s and all("scrub_s" in x for x in s["timed"]) for s in rec["steps"]),
          "no warm-up time is recorded (none is spent); the scrub's is, for every request")

    recs = [make().stream_run() for _ in range(2)]
    check(recs[0]["shape"] == recs[1]["shape"] and len(set(recs[0]["seeds"] + recs[1]["seeds"])) == 2 * 4,
          "two evaluations: the same shape, fresh seeds each")

    # 11. the real Bench.verify names a failed badge run `check`; a service failing at its stop while a
    # failure is in flight does not replace it (its stage stays), and is recorded
    from rfh.checks import BadgeError
    v = Bench.__new__(Bench)
    v.store = "/nonexistent"
    order = []
    v.scrub = lambda: order.append("scrub")
    v.badge = SimpleNamespace(verify=lambda *a, **kw: (order.append("badge"), (_ for _ in ()).throw(
        BadgeError("verify: exit -11", kind="crash")))[1])
    v.deadline = (bench_mod.time.monotonic() + 100, "the stream's cap stream_s = 300 s was reached")
    try:
        Bench.verify(v, [(b"k", b"c", "x")], "the final output, judged run 1 of 3", 10)
        check(False, "a crashed badge run passes")
    except Fail as e:
        check(e.stage == "check" and e.kind == "crash", f"Bench.verify: a crashed badge run is REJECTed at check: {e}")
    check(order == ["scrub", "badge"], f"Bench.verify scrubs the per-CPU inode counters before every badge run: {order}")
    del v.scrub
    v.badge = SimpleNamespace(verify=lambda *a, **kw: (_ for _ in ()).throw(BadgeError("verify: timeout", kind="timeout")))
    v.deadline = (bench_mod.time.monotonic() - 31, "the stream's cap stream_s = 300 s was reached")
    try:
        Bench.verify(v, [(b"k", b"c", "x")], "the final output, judged run 1 of 3", 0.0)
        check(False, "a badge run cut at the stream's cap passes")
    except Fail as e:
        check(e.stage == "check" and "cut 30 s past the stream's cap: the stream's cap stream_s" in str(e),
              f"Bench.verify: a badge run that failed once the stream's cap had passed is still REJECTed at check (a "
              f"hung badge may come from the record cache, which the bot re-runs without): {e}")
    b = make(reject={4})

    def stop_fails(svc, rec):
        raise Fail("the service failed during the run (exit 9); the run is aborted")
    b.stop = stop_fails
    try:
        b.stream_run()
        check(False, "the final output rejected, then the service failing at its stop: passes")
    except Fail as e:
        check(e.stage == "check" and "rejected by acc" in str(e) and "exit 9" in e.rec.get("stop_error", ""),
              f"a service failing at its stop does not replace the failure in flight: {e.stage}: {str(e)[:60]}; "
              f"stop_error {e.rec.get('stop_error')}")
    b = make()
    b.stop = stop_fails
    try:
        b.stream_run()
        check(False, "the service failing at its stop after a good stream: passes")
    except Fail as e:
        check(e.stage == "timed-pass" and "exit 9" in str(e),
              f"the service failing at its stop after the timed passes: REJECT at {e.stage}")

    # the calibration's service failing at its stop: a harness ERROR, not the entry's REJECT
    cb = Bench.__new__(Bench)
    cb.badge = SimpleNamespace(core=0)
    cb.p = SimpleNamespace(service_calib_s=0.01)
    cb.bench_bin = "/bin/true"
    cb.service = lambda name: SimpleNamespace(info={"keygen_ms": "1"}, sock_dir="/")
    cb.stop = stop_fails
    try:
        cb.calibrate()
        check(False, "the calibration's service failing at its stop passes")
    except Fail as e:
        check(False, f"the calibration's service failing at its stop is the entry's REJECT ({e.stage}: {e})")
    except RuntimeError as e:
        check("calibration" in str(e) and "exit 9" in str(e),
              f"the calibration's service failing at its stop is a harness ERROR, never the entry's: {e}")

    # 12. run-benchmark.py: the reject stage and a malformed stream record, with the prover's build, its
    # setup and the stream stubbed
    spec = importlib.util.spec_from_file_location("run_benchmark", os.path.join(ROOT, "harness", "run-benchmark.py"))
    rb = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(rb)
    good = make().stream_run()
    bad_rec = json.loads(json.dumps(good))
    bad_rec["steps"][1]["P_timed_s"] = bad_rec["steps"][1]["P_timed_s"][:2]

    class FakeBench:
        outcome = None

        def __init__(self, *a, **kw):
            self.kw = kw

        def calibrate(self):
            return {"service": {}}

        def stream_run(self):
            if isinstance(FakeBench.outcome, Exception):
                raise FakeBench.outcome
            return json.loads(json.dumps(FakeBench.outcome))

    class FakeRun:
        def __init__(self, bin_dir, setup_dir, mem):
            self.setup_dir = setup_dir

        def publish(self):
            return 0, 0.0

        def setup(self, timeout, size_cap=None):
            os.makedirs(self.setup_dir, exist_ok=True)
            return True, 0.0, ""
    tools = []
    rb.build_calib = lambda d: ("calib", {})
    rb.build_scrub = lambda d: (tools.append(d), ("scrub-bin", {"source_sha256": "s"}))[1]
    rb.Run, rb.Bench, rb.tree_sha256 = FakeRun, FakeBench, (lambda *a: "h")
    built = [(True, {"binary_sha256": "b", "binary_bytes": 1})]
    rb.build = lambda *a: built[0]
    entry = tempfile.mkdtemp(prefix="rf-rb-entry-", dir=os.environ.get("RF_TEST_TMP"))

    def bench_result(outcome, build_ok=True):
        FakeBench.outcome = outcome
        built[0] = (True, {"binary_sha256": "b", "binary_bytes": 1}) if build_ok else (False, {"error": "gcc exited with 1"})
        work = tempfile.mkdtemp(prefix="rf-rb-", dir=os.environ.get("RF_TEST_TMP"))
        out = os.path.join(work, "result.json")
        argv = sys.argv
        sys.argv = ["run-benchmark.py", "--season", os.path.join(ROOT, "harness", "smoke.toml"), "--entry", entry,
                    "--badge", work, "--service", "/nonexistent", "--bench", "/nonexistent",
                    "--work", os.path.join(work, "w"), "--out", out]
        try:
            code = rb.main()
        finally:
            sys.argv = argv
        return code, json.load(open(out))
    # the memory caps' prlimit fallback (as on a machine with no systemd user manager): an organiser ERROR
    # before the prover's build, unless the test-only override is set
    rb.memcap_method = lambda: "prlimit"
    allow = os.environ.pop("RF_ALLOW_PRLIMIT", None)
    code, r = bench_result(good)
    check(code == 2 and r["benchmark"] == "error" and r.get("organiser_error") == "fingerprint" and "prover" not in r
          and "score" not in r and any("prlimit" in x for x in r["reasons"]),
          f"run-benchmark.py: under the prlimit fallback a run is benchmark: error, organiser_error: fingerprint, "
          f"before the prover's build: {r['reasons']}")
    os.environ["RF_ALLOW_PRLIMIT"] = "1"
    code, r = bench_result(good)
    check(code == 0 and r["benchmark"] == "pass" and r["machine"].get("memcap_override") is True,
          "run-benchmark.py: with RF_ALLOW_PRLIMIT=1 (tests and local runs) it proceeds, the override recorded")
    rb.memcap_method = lambda: "systemd"
    if allow is None:
        os.environ.pop("RF_ALLOW_PRLIMIT")
    code, r = bench_result(good)
    check(code == 0 and "memcap_override" not in r["machine"], "run-benchmark.py: under systemd scopes no override")
    # the tests' stand-in badge with the host's /usr: refused unless RF_TEST_OVERRIDES=1, then recorded
    saved = {k: os.environ.pop(k, None) for k in ("RF_TEST_BADGE_HOST_ROOT", "RF_TEST_OVERRIDES")}
    os.environ["RF_TEST_BADGE_HOST_ROOT"] = "1"
    code, r = bench_result(good)
    check(code == 2 and r["benchmark"] == "error" and r.get("organiser_error") == "fingerprint" and "prover" not in r
          and any("RF_TEST_OVERRIDES" in x for x in r["reasons"]),
          f"run-benchmark.py: RF_TEST_BADGE_HOST_ROOT=1 alone is an organiser ERROR before the prover's build: {r['reasons']}")
    os.environ["RF_TEST_OVERRIDES"] = "1"
    code, r = bench_result(good)
    check(code == 0 and r["benchmark"] == "pass" and r["machine"].get("badge_host_root") is True,
          "run-benchmark.py: with RF_TEST_OVERRIDES=1 too it proceeds, the override recorded (machine.badge_host_root)")
    for k, v in saved.items():
        os.environ.pop(k, None)
        if v is not None:
            os.environ[k] = v
    code, r = bench_result(bad_rec)
    check(code == 2 and r["benchmark"] == "error" and r.get("organiser_error") == "malformed" and "score" not in r
          and "reject_stage" not in r and "traceback" not in r and any("malformed" in x for x in r["reasons"]),
          f"run-benchmark.py: a stream record with a step of two timed times is benchmark: error, organiser_error: "
          f"malformed (not a harness error, which would count against the author): {r['reasons']}")
    code, r = bench_result(good)
    check(code == 0 and r["benchmark"] == "pass" and "reject_stage" not in r and r["score"]["median_pass"] in (1, 2, 3)
          and r.get("scrub") == {"source_sha256": "s"} and tools,
          "run-benchmark.py: a good stream passes, with no reject stage; the scrub is built before the prover")
    for what, outcome, build_ok, want in (
            ("the prover's build fails", good, False, "prover"),
            ("a timed pass's byte mismatch", Fail("timed pass 1, step 2: the output differs", stage="timed-pass"), True,
             "timed-pass"),
            ("a check of the final output", Fail("service run: the final output (step 4) is rejected", stage="check"), True,
             "check"),
            ("a Fail with no stage", Fail("the service died during the run"), True, "prover")):
        code, r = bench_result(outcome, build_ok)
        check(code == 1 and r["benchmark"] == "fail" and r.get("reject_stage") == want,
              f"run-benchmark.py: {what}: benchmark: fail, reject_stage {r.get('reject_stage')!r}")
    # a kill by the OOM killer: the cap's or the machine's (review LR5 NIT)
    from rfh.prover import oom_label
    G = 1 << 30
    labels = {"cap (memory.events oom)": oom_label("8G", 8 * G, {"oom": 1, "oom_kill": 1}),
              "global (oom_kill alone)": oom_label("8G", 3 * G, {"oom": 0, "oom_kill": 1}),
              "cap (peak at the cap)": oom_label("8G", 8 * G - (1 << 20)),
              "unknown (peak below)": oom_label("8G", 3 * G), "unknown (nothing read)": oom_label("8G")}
    check(labels["cap (memory.events oom)"].startswith("killed: out of memory (cap 8G")
          and labels["cap (peak at the cap)"].startswith("killed: out of memory (cap 8G")
          and "global out-of-memory kill below its cap 8G" in labels["global (oom_kill alone)"]
          and all("possibly a global OOM" in labels[k] and not labels[k].startswith("killed: out of memory")
                  for k in ("unknown (peak below)", "unknown (nothing read)")),
          f"an OOM kill reads as the cap's only when the scope's memory events or its peak say so: {labels}")
    print(f"{fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
