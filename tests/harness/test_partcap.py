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
   runner_budget_s` (the time since an in-flight reading counted as the entry's); the organiser's
   ERROR `overhead` when the runner's overhead is past its budget (whatever the entry's clock), when
   the entry's clock is within `stream_s`, during the calibration, or with no reading; an unnamed
   harness error before the prover's build. Through `bench_job` (the runner replaced by one that
   leaves a checkpoint and times out): the verdicts ERROR (`organiser_error: overhead`, no reject
   stage) and REJECT (`stream-cap`).
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

    def ck(entry_s, wall_s, running=False, ago=10.0, stage="stream"):
        return {"stage": stage, "stream_clock": {"stream_s": 2000, "runner_budget_s": 900, "entry_s": entry_s,
                                                 "wall_s": wall_s, "runner_overhead_s": wall_s - entry_s,
                                                 "entry_running": running, "at": now - ago}}
    cases = (
        ("the entry's clock past stream_s, the overhead within the budget", ck(2010.0, 2600.0), ("fail", "stream-cap", None)),
        ("an in-flight request taking the entry's clock past stream_s", ck(1995.0, 2500.0, running=True, ago=20.0),
         ("fail", "stream-cap", None)),
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
    for what, res0, want in cases:
        got = ev.part_timeout(res0, 2000, 900, now)
        check(got[:3] == want and "PART_S" in got[3], f"part_timeout: {what}: {got[:3]}: {got[3][:220]}")

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
    print(f"{fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
