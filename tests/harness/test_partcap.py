#!/usr/bin/env python3
"""A benchmark part that runs past `PART_S` is judged by whose time ran it there (AGENTS.md §9),
never a missing part.

  python3 tests/harness/test_partcap.py

1. A prover whose `setup` sleeps runs through `harness/evaluate.py`'s `bench_job` with `PART_S`
   lowered to 20 s and the mock badge: the result is `benchmark: fail`, verdict REJECT at the reject
   stage `prover`, its reason names `PART_S` and the stage the runner's checkpoint reached (`prover
   setup`).
2. From the calibration on (`evaluate.part_timeout`, from the runner's last checkpoint of the
   stream's clock, `stream_clock`, brought up to the kill): the entry's REJECT (`stream-cap`) only
   when its own clock is past `stream_s` with the runner's overhead within `[stream]
   runner_budget_s` (the time since an in-flight reading counted as the entry's up to the process's
   own bound, `entry_bound_s`, the rest the runner's); the organiser's ERROR `overhead` when the
   runner's overhead is past its budget (whatever the entry's clock), when the entry's clock is
   within `stream_s`, during the calibration, or with no reading; an unnamed harness error before
   the prover's build. Every reason is at most 300 characters (the bot's cap), its verdict first;
   the time since a reading is taken from `at_monotonic` when both are given. Through `bench_job`
   (the runner replaced by one that leaves a checkpoint and times out): the verdicts ERROR
   (`organiser_error: overhead`, no reject stage) and REJECT (`stream-cap`).
3. Through `rfh.bench.Bench.one` (the last review's MEDIUM-1), the checkpoints a request leaves
   (`request`'s `clock`), judged as if the part were killed then: the runner hung inside `request`
   after the prover died (the output's read, the `/work` walk) or before its spawn (the view), the
   entry's clock near `stream_s`: the organiser's ERROR `overhead`; the prover itself overrunning
   `stream_s` within its bound: the entry's REJECT (`stream-cap`); the runner hung in the staging
   between `ready` and the timed part: ERROR `overhead`.
"""
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))


def main():
    sys.path.insert(0, os.path.join(ROOT, "harness"))
    from rfh.sandbox import memcap_method
    if memcap_method() == "prlimit":           # the test-only override (run-benchmark.py's organiser ERROR)
        os.environ["RF_ALLOW_PRLIMIT"] = "1"
    tmp = tempfile.mkdtemp(prefix="rf-partcap-", dir=os.environ.get("RF_TEST_TMP"))
    badge = os.path.join(tmp, "badge")
    os.makedirs(badge)
    for f in sorted(x for x in os.listdir(os.path.join(HERE, "mock_badge")) if os.path.isfile(os.path.join(HERE, "mock_badge", x))):
        shutil.copy(os.path.join(HERE, "mock_badge", f), badge)
    shutil.copy(os.path.join(ROOT, "tests", "service", "wots_ref.py"), badge)
    shutil.copy(os.path.join(ROOT, "harness", "rfh", "signed.py"), badge)
    shutil.copy(os.path.join(ROOT, "tests", "service", "keccak_ref.c"), badge)
    os.makedirs(os.path.join(badge, "rfh"))                # wots_ref's `from rfh import keccak`
    shutil.copy(os.path.join(ROOT, "harness", "rfh", "keccak.py"), os.path.join(badge, "rfh"))
    entry = os.path.join(tmp, "entry")
    os.makedirs(os.path.join(entry, "prover"))
    c = os.path.join(tmp, "p.c")
    open(c, "w").write('#include <string.h>\n#include <unistd.h>\n'
                       'int main(int c, char **v){if(c>1&&!strcmp(v[1],"setup"))sleep(600);return 0;}\n')
    subprocess.run(["gcc", "-S", "-O1", "-o", os.path.join(entry, "prover", "p.s"), c], check=True)
    spec = importlib.util.spec_from_file_location("evaluate", os.path.join(ROOT, "harness", "evaluate.py"))
    ev = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ev)
    ev.PART_S = 20
    out = os.path.join(tmp, "result.json")
    a = SimpleNamespace(season=os.path.join(ROOT, "harness", "smoke.toml"), entry=entry, work=os.path.join(tmp, "work"),
                        out=out, parts=None, service=os.path.join(ROOT, "service", "target", "release", "rf-oracle"),
                        bench=os.path.join(ROOT, "service", "target", "release", "rf-bench"))
    res = ev.bench_job(a, {"status": "ok", "badge_dir": badge})
    why = " ".join(res.get("reasons", []))
    ok = (res.get("benchmark") == "fail" and res.get("verdict") == "REJECT" and "PART_S" in why and "prover setup" in why
          and res.get("reject_stage") == "prover")
    print(("ok   " if ok else "FAIL ") + f"a part past PART_S during the prover's setup: {res.get('verdict')} at "
          f"{res.get('reject_stage')}: {why}")
    json.dump(res, open(out, "w"), indent=1)
    fails = 0 if ok else 1

    def check(cond, what):
        nonlocal fails
        fails += 0 if cond else 1
        print(("ok   " if cond else "FAIL ") + what)

    # 2. from the calibration on: whose time ran the part past PART_S
    ev.PART_S = 3840
    now = 1_000_000.0

    def ck(entry_s, wall_s, running=False, ago=10.0, stage="stream", bound=None):
        return {"stage": stage, "stream_clock": {"stream_s": 2000, "runner_budget_s": 900, "entry_s": entry_s,
                                                 "wall_s": wall_s, "runner_overhead_s": wall_s - entry_s,
                                                 "entry_running": running, "at": now - ago,
                                                 **({"entry_bound_s": bound} if bound is not None else {})}}
    cases = (
        ("the entry's clock past stream_s, the overhead within the budget", ck(2010.0, 2600.0), ("fail", "stream-cap", None)),
        ("an in-flight request taking the entry's clock past stream_s", ck(1995.0, 2500.0, running=True, ago=20.0),
         ("fail", "stream-cap", None)),
        ("an in-flight prover overrunning stream_s within its bound (100 s)",
         ck(1995.0, 2500.0, running=True, ago=20.0, bound=100.0), ("fail", "stream-cap", None)),
        ("the runner hung past an in-flight process's bound (5 s of 2,000 s since the reading the entry's)",
         ck(1990.0, 2300.0, running=True, ago=2000.0, bound=5.0), ("error", None, "overhead")),
        ("an in-flight reading whose bound keeps the entry within stream_s (runner within its budget)",
         ck(1900.0, 2300.0, running=True, ago=500.0, bound=95.0), ("error", None, "overhead")),
        ("the runner's overhead past runner_budget_s (the entry's clock past stream_s too)", ck(2010.0, 3000.0),
         ("error", None, "overhead")),
        ("the runner's overhead past the budget only with the time since the reading (no entry process in flight)",
         ck(1500.0, 2380.0, ago=40.0), ("error", None, "overhead")),
        ("the entry's clock within stream_s, the overhead within the budget", ck(1900.0, 2700.0), ("error", None, "overhead")),
        ("during the calibration (no clock)", {"stage": "calibration"}, ("error", None, "overhead")),
        ("the stream before its first reading", {"stage": "stream"}, ("error", None, "overhead")),
        ("a malformed reading", {"stage": "stream", "stream_clock": {"entry_s": "9999", "wall_s": 1, "at": now}},
         ("error", None, "overhead")),
        ("before the prover's build", {"stage": "organiser setup"}, ("error", None, None)),
        ("no checkpoint", None, ("error", None, None)),
        ("the prover's build", {"stage": "prover build"}, ("fail", "prover", None)))
    word = {("fail", "stream-cap", None): "REJECT", ("fail", "prover", None): "REJECT",
            ("error", None, "overhead"): "organiser ERROR", ("error", None, None): "harness ERROR"}
    for what, res0, want in cases:
        got = ev.part_timeout(res0, 2000, 900, now)
        check(got[:3] == want and "PART_S" in got[3] and len(got[3]) <= 300 and got[3].startswith(word[want]),
              f"part_timeout: {what}: {got[:3]}: ({len(got[3])} chars) {got[3]}")
    # the reason within the bot's 300 characters at the largest figures, its verdict first
    long = ev.part_timeout(ck(123456789.0, 987654321.0, running=True, ago=99999999.0, bound=99999.0, stage="s" * 500),
                           2000, 900, now)
    check(len(long[3]) <= 300 and long[3].startswith("organiser ERROR"),
          f"part_timeout: a reason at huge figures and a long stage is at most 300 characters ({len(long[3])})")
    # the time since the reading from CLOCK_MONOTONIC (machine-wide) when both readings are given
    mono = ck(1995.0, 2500.0, running=True, ago=99999.0, bound=100.0)
    mono["stream_clock"]["at_monotonic"] = 500.0
    got = ev.part_timeout(mono, 2000, 900, now, 520.0)
    check(got[:3] == ("fail", "stream-cap", None) and "20.0 s since" in got[3],
          f"part_timeout: the time since the reading from at_monotonic (20 s; the wall clock says 99,999): {got[3]}")

    # ... through bench_job, the runner replaced by one that leaves a checkpoint and is killed at PART_S
    real_run = ev.subprocess.run
    for what, clock, want in (("the runner's overhead past its budget", (1500.0, 2600.0), ("ERROR", None, "overhead")),
                              ("the entry's clock past stream_s", (2010.0, 2600.0), ("REJECT", "stream-cap", None))):
        out2 = os.path.join(tmp, f"timeout-{want[0]}.json")

        def killed(cmd, timeout=None, out2=out2, clock=clock):
            c = ck(*clock, ago=0.0)
            c["stream_clock"]["at"] = __import__("time").time()
            c.update(benchmark="incomplete", reasons=[])
            json.dump(c, open(out2, "w"))
            raise subprocess.TimeoutExpired(cmd, timeout)
        ev.subprocess.run = killed
        try:
            a2 = SimpleNamespace(**dict(vars(a), out=out2, season=os.path.join(ROOT, "harness", "season.toml")))
            r2 = ev.bench_job(a2, {"status": "ok", "badge_dir": badge})
        finally:
            ev.subprocess.run = real_run
        check((r2["verdict"], r2.get("reject_stage"), r2.get("organiser_error")) == want,
              f"bench_job: a part killed at PART_S with {what}: {r2['verdict']}, reject_stage {r2.get('reject_stage')}, "
              f"organiser_error {r2.get('organiser_error')}: {r2['reasons'][-1][:200]}")
    # 3. through Bench.one: the checkpoints a request leaves, judged as if the part were killed then
    from rfh import bench as bench_mod
    from rfh.bench import Bench
    from rfh.prover import Step
    import time as _time

    def snapshot(hang_at, entry0, prover_s=2.0, startup_s=0.5):
        """The checkpoint at a runner hang inside `request` (`hang_at`: `view` before the spawn,
        `staging` after `ready`, `timed` with the prover running, `read` after its death), the
        stream's clock at `entry0` of stream_s = 2000 s."""
        b = Bench.__new__(Bench)
        b.p = SimpleNamespace(stream_s=2000, runner_budget_s=900, ready_s=10, step_s=60, scrub_batches=0,
                             file_cap=1 << 20, work_cap=1 << 20)
        b.run, b.work, b.phase, b.log = None, tmp, "request", (lambda m: None)
        b.deadline = (_time.monotonic() + 2000, "the cap")
        b.charge(entry0)
        b._t_stream, b.scrub = _time.monotonic() - entry0 - 300, (lambda batches=0: 0.0)
        ticks, seen = [], []
        b.progress = ticks.append
        b.tick(False)                           # the reading before the request (the previous one's end)
        svc = SimpleNamespace(sock_dir=os.path.join(tmp, "svc", "s"), socket_path="/nonexistent", vk=b"k",
                              proc=SimpleNamespace(poll=lambda: None), refusals=lambda n=None: [])

        def req(run, kind, work, sock, inputs, step_s, file_cap, clock=None, **kw):
            if hang_at != "view":
                clock(True)
                clock(False, startup_s)
                if hang_at != "staging":
                    clock(True, startup_s)
                    if hang_at != "timed":
                        clock(False, startup_s + prover_s)
            seen.append(dict(ticks[-1]))
            r = Step()
            r.startup_s, r.seconds, r.proof = startup_s, prover_s, b"x"
            return r
        real = bench_mod.request
        bench_mod.request = req
        try:
            b.one(svc, "timed1-step1", "first", {"leaf.json": b"{}"})
        finally:
            bench_mod.request = real
        return {"stage": "stream", "stream_clock": seen[0]}
    for what, hang_at, entry0, since, want in (
            ("the runner hung after the prover died (the output's read, the /work walk), the entry's clock 1,999 s",
             "read", 1997.0, 3000.0, ("error", None, "overhead")),
            ("the runner hung before the spawn (the view), the entry's clock 1,999 s", "view", 1999.0, 3000.0,
             ("error", None, "overhead")),
            ("the runner hung in the staging after `ready`, the entry's clock 1,999 s", "staging", 1998.5, 3000.0,
             ("error", None, "overhead")),
            ("the runner hung with the prover running past its bound, the entry's clock 1,500 s", "timed", 1500.0, 3000.0,
             ("error", None, "overhead")),
            ("the prover overrunning stream_s within its bound (40 s in flight)", "timed", 1980.0, 40.0,
             ("fail", "stream-cap", None))):
        snap = snapshot(hang_at, entry0)
        c = snap["stream_clock"]
        got = ev.part_timeout(snap, 2000, 900, c["at"] + since, c["at_monotonic"] + since)
        check(got[:3] == want, f"Bench.one, then a PART_S kill: {what}: {got[:3]}: {got[3]}")
    print(f"{fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
