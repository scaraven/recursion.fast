#!/usr/bin/env python3
"""The DoS column's bounds (RF-M1 (2), RF-m6, V4-A9), with a stub badge.

  python3 tests/harness/test_dos.py

Only time and crashes fail the entry: an input slower than the per-item cap (`item_factor · T_V`)
fails it and is named and kept, also when the badge reports a check above `verify_s`; a column that
does not finish within `total_s` fails it and names the input being checked; a crash of the checker
fails it. An accepted input is recorded, not failed (V4-A9: malleability is not a failure). A column
within its bounds reports its worst input.
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
    def __init__(self, times=None, stop_after=None, kind="timeout", accept=(), slow=False):
        self.times, self.stop_after, self.kind, self.accept, self.slow = times or {}, stop_after, kind, set(accept), slow
        self.timeout = None

    def verify(self, items, store, timeout=None, warm=False):
        self.timeout = timeout
        res = [(k in self.accept, self.times.get(k, 1000)) for k in range(len(items))]
        if self.stop_after is not None:
            raise BadgeError(f"verify: exit {self.kind}", self.kind, res[:self.stop_after])
        if self.slow:
            raise BadgeError("verify: a check took 11.0 s, above verify_s", "slow", res)
        return res


def bench(badge):
    b = Bench.__new__(Bench)
    b.p = SimpleNamespace(dos_proofs=100, dos_item_factor=10.0, dos_total_s=180, verify_s=10, tv_enforce=True)
    b.store = tempfile.mkdtemp(prefix="rf-dos-", dir=os.environ.get("RF_TEST_TMP"))
    b.tv_cap_ns, b.badge = 1_000_000, badge            # T_V = 1 ms, so the per-item cap is 10 ms
    b.keep("tree/root.bin", signed.Signed(b"pi" * 20).encode())
    return b


def main():
    fails = 0

    def check(cond, what):
        nonlocal fails
        print(("ok   " if cond else "FAIL ") + what)
        fails += not cond

    def outcome(badge):
        try:
            return bench(badge).dos(b"v" * 32, b"c" * 32, "tree/root.bin")
        except Fail as e:
            return str(e)
    r = outcome(StubBadge({7: 25_000_000}))
    check(isinstance(r, str) and "input 7" in r and "per-item cap of 10.0 ms" in r and "store/dos/7.bin" in r,
          f"an input above 10 · T_V fails the entry, named and kept: {r}")
    r = outcome(StubBadge({4: 11_000_000_000}, slow=True))
    check(isinstance(r, str) and "input 4" in r and "store/dos/4.bin" in r,
          f"a check the badge reports above verify_s fails the entry as a slow input, named: {r}")
    r = outcome(StubBadge(stop_after=12))
    check(isinstance(r, str) and "not finished within 180 s" in r and "input 12" in r,
          f"a column over its total budget fails the entry at the input being checked: {r[:160]}")
    r = outcome(StubBadge(stop_after=5, kind="crash"))
    check(isinstance(r, str) and "crashed" in r and "input 5" in r, f"a crash of the checker fails the entry: {r[:160]}")
    r = outcome(StubBadge(accept=[3]))
    check(isinstance(r, dict) and r["accepted"] == 1 and r["accepted_inputs"] == ["dos/3.bin"],
          f"an accepted input is recorded, not failed (V4-A9): {r if isinstance(r, str) else r['accepted_inputs']}")
    b = StubBadge({9: 2_000_000})
    r = outcome(b)
    check(isinstance(r, dict) and r["max_input"] == "dos/9.bin" and r["over_T_V"] == 1 and r["accepted"] == 0
          and b.timeout == 180, f"within its bounds the column reports its worst input and the budget is passed to the badge: {r}")
    print(f"{fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
