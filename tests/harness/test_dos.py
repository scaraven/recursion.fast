#!/usr/bin/env python3
"""The DoS column's bounds (RF-M1 (2), RF-m6), with a stub badge.

  python3 tests/harness/test_dos.py

An input slower than the per-item cap (`item_factor · T_V`) fails the entry and is named and
kept; a column that does not finish within `total_s` fails the entry and names the input being
checked; an accepted input fails; a column within its bounds reports its worst input.
"""
import os
import sys
import tempfile
from types import SimpleNamespace

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from rfh import signed  # noqa: E402
from rfh.bench import Bench, Fail  # noqa: E402
from rfh.checks import BadgeError  # noqa: E402


class StubBadge:
    def __init__(self, times=None, stop_after=None, accept=()):
        self.times, self.stop_after, self.accept, self.timeout = times or {}, stop_after, set(accept), None

    def verify(self, items, store, timeout=None, warm=False):
        self.timeout = timeout
        res = [(k in self.accept, self.times.get(k, 1000)) for k in range(len(items))]
        if self.stop_after is not None:
            e = BadgeError("verify: exit timeout")
            e.partial = res[:self.stop_after]
            raise e
        return res


def bench(badge):
    b = Bench.__new__(Bench)
    b.p = SimpleNamespace(dos_proofs=50, dos_item_factor=10.0, dos_total_s=300, verify_s=60, tv_enforce=True)
    b.store = tempfile.mkdtemp(prefix="rf-dos-", dir=os.environ.get("RF_TEST_TMP"))
    b.tv_cap_ns, b.badge = 1_000_000, badge            # T_V = 1 ms, so the per-item cap is 10 ms
    b.keep("tree1/root.bin", signed.Signed(b"pi" * 20).encode())
    return b


def main():
    fails = 0

    def check(cond, what):
        nonlocal fails
        print(("ok   " if cond else "FAIL ") + what)
        fails += not cond

    def outcome(badge):
        try:
            return bench(badge).dos(b"v" * 32, b"c" * 32, "tree1/root.bin")
        except Fail as e:
            return str(e)
    r = outcome(StubBadge({7: 25_000_000}))
    check(isinstance(r, str) and "input 7" in r and "per-item cap of 10.0 ms" in r and "store/dos/7.bin" in r,
          f"an input above 10 · T_V fails the entry, named and kept: {r}")
    r = outcome(StubBadge(stop_after=12))
    check(isinstance(r, str) and "not finished within 300 s" in r and "input 12" in r,
          f"a column over its total budget fails the entry at the input being checked: {r[:160]}")
    r = outcome(StubBadge(accept=[3]))
    check(isinstance(r, str) and "accepted" in r, f"an accepted input fails the entry: {r}")
    b = StubBadge({9: 2_000_000})
    r = outcome(b)
    check(isinstance(r, dict) and r["max_input"] == "dos/9.bin" and r["over_T_V"] == 1 and b.timeout == 300,
          f"within its bounds the column reports its worst input and the budget is passed to the badge: {r}")
    print(f"{fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
