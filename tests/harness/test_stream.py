#!/usr/bin/env python3
"""The stream's control flow (V4-A11 §2, §5.3, §6, §11 R-M2, m-4), with stub requests and checks.

  python3 tests/harness/test_stream.py

1. Inputs: step 1 gets `chainA.json` and `chainB.json`, step i ≥ 2 `prev.stmt`, `prev.bin` (the
   previous step's output) and `chain.json`; the runner's statements are the comb `nodeStmt` chain.
2. Re-timing: the steps above `1.3 ×` the fit, largest ratio first, at most `retime_frac` of them,
   are run again on the same inputs; the faster run's `P`, `V` and `|π|` are scored (R-M2) while the
   first output stays the next step's child; both runs are recorded.
3. Truncation: a stream whose cap stops a step is scored over its completed, checked steps, flagged
   `truncated`, and not re-timed; a cap reached during re-runs keeps the first times and is not
   `truncated`.
4. Calibration samples: before step 1 and every `calib_every` steps, plus a closing one.
"""
import json
import os
import sys
import tempfile
from types import SimpleNamespace

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from rfh import digest  # noqa: E402
from rfh.bench import Bench, Params  # noqa: E402
from rfh.prover import Step  # noqa: E402


class FakeSvc:
    vk, sock_dir, info = b"k" * 32, "/nonexistent", {}
    proc = SimpleNamespace(poll=lambda: None)

    def refusals(self, n=8):
        return []

    def stop(self):
        return {}


def make(times, stop_at=None, retime_times=None, cap_in_retime=False, M=8):
    """A Bench over the smoke season with stubs: request i takes times[i] s (or the cap stops it at
    `stop_at`); re-runs take retime_times[i] s."""
    p = Params.load(os.path.join(ROOT, "harness", "smoke.toml"))
    p.M_min = p.M_cap = M
    p.calib_idle_s, p.retime_frac = 0.0, 0.25
    b = Bench.__new__(Bench)
    b.p, b.log, b.samples, b.deadline, b.req_root = p, (lambda m: None), [], None, None
    b.store = tempfile.mkdtemp(prefix="rf-stream-", dir=os.environ.get("RF_TEST_TMP"))
    b.calls, b.inputs = [], {}
    b.service = lambda name: FakeSvc()
    b.stop = lambda svc, rec: None
    b.sample = lambda i: b.samples.append({"before_step": i, "calib_ns": p.calib_ref_ns, "triv_ns": 1000})
    b.canary_check = lambda vk, targets, what: len(targets)

    def check(items, what, timeout=None):
        return [(1000 + len(rel), [1000 + len(rel), 2000]) for _, _, rel, _ in items]
    b.check = check

    def one(svc, tag, kind, ins):
        b.calls.append(tag)
        b.inputs[tag] = (kind, ins)
        i = int(tag.lstrip("stepretime"))
        if tag.startswith("retime"):
            if cap_in_retime:
                return None
            t = retime_times[i]
        else:
            if stop_at is not None and i >= stop_at:
                return None
            t = times[i]
        r = Step()
        r.seconds, r.startup_s, r.kill_s, r.ended = t, 0.01, 0.001, "line"
        r.proof = (len(tag) + (100 if tag.startswith("retime") else 0)).to_bytes(8, "little") + tag.encode()
        return r
    b.one = one
    b.left = lambda: 1.0
    return b


def main():
    fails = 0

    def check(cond, what):
        nonlocal fails
        print(("ok   " if cond else "FAIL ") + what)
        fails += not cond
    times = {i: 0.001 for i in range(1, 9)}
    times[3], times[6] = 0.05, 0.02
    b = make(times, retime_times={3: 0.002, 6: 0.03})
    rec = b.stream_run()
    st = rec["steps"]
    k1, in1 = b.inputs["step1"]
    k2, in2 = b.inputs["step2"]
    check(k1 == "first" and sorted(in1) == ["chainA.json", "chainB.json"] and k2 == "step"
          and sorted(in2) == ["chain.json", "prev.bin", "prev.stmt"] and in2["prev.bin"].endswith(b"step1"),
          "step 1 gets two chains; step 2 gets the previous output, its statement and one chain")
    ld = [bytes.fromhex(d) for d in rec["leaf_digests"]]
    c = digest.node_stmt(ld[0], ld[1])
    for d in ld[2:]:
        c = digest.node_stmt(c, d)
    check(rec["statements"][-1] == c.hex() and json.loads(in1["chainA.json"])["n"] == rec["lengths"][0],
          "the statements are the comb nodeStmt (nodeStmt (A, B), …), the lengths those drawn")
    check(st[0]["n"] == rec["lengths"][0] + rec["lengths"][1] and st[1]["n"] == rec["lengths"][2],
          "n_1 = n_A + n_B, n_i the new chain's length")
    rt = rec["retime"]
    check(rt["rerun"] == [3, 6] and b.calls[-2:] == ["retime3", "retime6"],
          f"re-runs: the two outliers, largest ratio first, at most 25% of 8 steps: {rt['rerun']}")
    s3, s6 = st[2], st[5]
    check(s3["retime"]["kept"] == 2 and s3["P_s"] == 0.002 and s3["pi_bytes"] == len("retime3") + 100
          and s3["file"] == "stream/step3.bin" and s3["scored_file"] == "stream/step3.retime.bin",
          "a faster re-run is kept: its P and |π| are scored, the first output stays the next step's child (R-M2)")
    check(b.inputs["step4"][1]["prev.bin"].endswith(b"step3"), "step 4's child is step 3's first output")
    check(s6["retime"]["kept"] == 1 and s6["P_s"] == 0.02 and s6["retime"]["second"]["P_s"] == 0.03,
          "a slower re-run is recorded and the first run kept")
    check([x["before_step"] for x in b.samples] == [1, 5, 9] and not rec["truncated"],
          f"calibration samples before steps 1 and 5 and a closing one: {[x['before_step'] for x in b.samples]}")

    b = make(times, stop_at=6)
    rec = b.stream_run()
    check(rec["truncated"] and rec["M"] == 5 and "retime" not in rec and all("V_ns" in s for s in rec["steps"]),
          f"the cap stops step 6: truncated, scored over 5 checked steps, not re-timed (M = {rec['M']})")
    b = make(times, retime_times={}, cap_in_retime=True)
    rec = b.stream_run()
    check(not rec["truncated"] and rec["retime"].get("stopped_by_cap") and rec["steps"][2]["P_s"] == 0.05,
          "the cap reached during re-runs keeps the first times and does not truncate")
    print(f"{fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
