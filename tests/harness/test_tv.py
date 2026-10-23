#!/usr/bin/env python3
"""`T_V` enforcement uses the cap's statistic (RB-M1): a check above the cap is measured again and
only its best of `checker_runs` counts. A stub badge returns scripted times.

  python3 tests/harness/test_tv.py
"""
import os
import sys
from types import SimpleNamespace

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from rfh.bench import Bench, Fail  # noqa: E402


class StubBadge:
    def __init__(self, script):
        self.script, self.calls, self.warm = list(script), 0, []

    def verify(self, items, store, timeout=None, warm=False):
        # the real badge checks the first item once more, untimed, when `warm` (RF-m3)
        self.calls += 1
        self.warm.append(warm)
        return [(True, self.script.pop(0)) for _ in items]


def bench(script, runs=3, enforce=True):
    b = Bench.__new__(Bench)
    b.p = SimpleNamespace(tv_enforce=enforce, checker_runs=runs)
    b.badge, b.store, b.tv_cap_ns, b.tv_seen, b.tv_remeasured = StubBadge(script), "/nonexistent", 100, [], 0
    return b


def main():
    fails = 0

    def check(cond, what):
        nonlocal fails
        print(("ok   " if cond else "FAIL ") + what)
        fails += not cond
    item = [(b"v", b"c", "f", "root")]
    b = bench([150, 90])                     # a transient spike, then within the cap
    b.check(item, "spike")
    check(b.tv_seen == [("root", 90)] and b.tv_remeasured == 1 and b.badge.calls == 2,
          f"a spike above the cap is measured again and passes on its best time ({b.tv_seen})")
    check(b.badge.warm == [True, True], "every timed batch is warmed with an untimed first check (RF-m3)")
    b = bench([150, 140, 130])               # above the cap every time
    try:
        b.check(item, "slow")
        check(False, "a check above the cap on every run passes")
    except Fail as e:
        check("best of 3" in str(e) and b.badge.calls == 3, f"a check above the cap on all 3 runs fails: {e}")
    b = bench([50])                          # within the cap: measured once
    b.check(item, "fast")
    check(b.badge.calls == 1 and b.tv_remeasured == 0, "a check within the cap is measured once")
    b = bench([150], enforce=False)          # not enforced (smoke shape): measured once, reported
    b.check(item, "report")
    check(b.badge.calls == 1 and b.tv_seen == [("root", 150)], "with T_V not enforced a check is measured once")
    two = [(b"v", b"c", "f", "a"), (b"v", b"c", "g", "b")]
    b = bench([150, 60, 95])                 # only the item above the cap is measured again
    b.check(two, "two")
    check(b.tv_seen == [("a", 95), ("b", 60)] and b.tv_remeasured == 1, f"only the items above the cap are re-measured ({b.tv_seen})")
    print(f"{fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
