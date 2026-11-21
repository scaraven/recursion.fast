#!/usr/bin/env python3
"""The runner's request loop against hostile stand-in badges, and the warm-up (core CI; no sandbox
and no Lean needed). `rfh.checks.serve` drives a `verify --serve` process one request at a time and
times each from outside; `rfh.checks.Badge.verify` (here through `tests/harness/localbadge.py`)
warms each process with the organiser's input and caps its start-up.

  python3 tests/harness/test_serve.py

1. A badge whose own time lies (it sleeps 0.2 s and reports 1 ns) is judged on the external time.
2. An answer written before its request, two answers to one request, a malformed answer, output
   after the last answer, a non-zero exit, and a badge that never answers (the deadline) each fail
   the run; an answer split across writes, and output on stderr, do not.
3. The warm-up: a warmed run first checks the organiser's input (`warm_file`, under a fresh random
   key and statement, never one of the items) and drops its answer; a badge that takes longer than
   the start-up cap to answer it fails with a start-up error, one within the cap does not.
Exit 1 on any failure.
"""
import os
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "harness"))
sys.path.insert(0, HERE)
from rfh.checks import BadgeError, serve, warm_file  # noqa: E402
from rfh.signed import parse  # noqa: E402
from localbadge import LocalBadge  # noqa: E402

FAILS = []


def check(cond, what):
    print(("ok   " if cond else "FAIL ") + what, flush=True)
    if not cond:
        FAILS.append(what)


def stand_in(src):
    return subprocess.Popen([sys.executable, "-I", "-c", src], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=subprocess.DEVNULL)


def run(src, n=3, timeout=10):
    p = stand_in(src)
    try:
        return serve(p, ["a b c"] * n, time.monotonic() + timeout)
    finally:
        if p.poll() is None:
            p.kill()
        p.wait()


def main():
    # 1. the external clock
    res, why = run("import sys,time\nfor l in sys.stdin:\n  time.sleep(0.2); print('accept 1', flush=True)\n")
    check(why is None and len(res) == 3 and all(ns >= 200e6 and own == 1 for _, ns, _, own in res),
          f"a badge that reports 1 ns for a 0.2 s check is judged at the external time: "
          f"{[round(ns / 1e6, 1) for _, ns, _, _ in res]} ms")
    # 2. protocol violations, and what is not one
    cases = [
        ("an answer ahead of its request", "import sys\nprint('accept 1', flush=True)\nfor l in sys.stdin:\n  print('accept 1', flush=True)\n", False),
        ("two answers to one request", "import sys,time\nfor l in sys.stdin:\n  print('accept 1', flush=True); time.sleep(0.05); print('reject 1', flush=True)\n", False),
        ("a malformed answer", "import sys\nfor l in sys.stdin:\n  print('maybe 1', flush=True)\n", False),
        ("output after the last answer", "import sys\nls = []\nfor l in sys.stdin:\n  print('accept 1', flush=True)\nprint('accept 2', flush=True)\n", False),
        ("a non-zero exit", "import sys\nfor l in sys.stdin:\n  print('accept 1', flush=True)\nsys.exit(3)\n", False),
        ("an answer split across writes", "import sys,time\nfor l in sys.stdin:\n  sys.stdout.write('acc'); sys.stdout.flush(); time.sleep(0.01); print('ept 5', flush=True)\n", True),
        ("output on stderr", "import sys\nfor l in sys.stdin:\n  sys.stderr.write('x\\n'); print('accept 5', flush=True)\n", True),
    ]
    for name, src, ok in cases:
        res, why = run(src)
        check((why is None and len(res) == 3) == ok, f"{name}: {'accepted' if ok else 'fails the run'} ({why}, {len(res)} answers)")
    t0 = time.monotonic()
    res, why = run("import sys,time\nfor l in sys.stdin:\n  time.sleep(60)\n", timeout=1)
    check(why == "timeout" and not res and time.monotonic() - t0 < 5, f"a badge that never answers: {why} at the deadline")
    # 3. the warm-up and the start-up cap
    tmp = tempfile.mkdtemp(prefix="rf-serve-", dir=os.environ.get("RF_TEST_TMP"))
    log = os.path.join(tmp, "requests.txt")
    echo = os.path.join(tmp, "echo.py")
    open(echo, "w").write(
        "import sys, time\nd = float(sys.argv[1]); log = sys.argv[2]\n"
        "for i, l in enumerate(sys.stdin):\n"
        "  open(log, 'a').write(l)\n"
        "  if i == 0 and l.split()[2].endswith('/warm.bin'): open(log + '.warm', 'wb').write(open(l.split()[2], 'rb').read())\n"
        "  if i == 0: time.sleep(d)\n"
        "  print('accept 7', flush=True)\n")
    os.makedirs(os.path.join(tmp, "store"))
    items = [(b"v" * 32, b"c" * 32, "p.bin"), (b"v" * 32, b"d" * 32, "q.bin")]
    b = LocalBadge([sys.executable, "-I", echo, "0", log], os.path.join(tmp, "scratch"), start_s=1)
    res = b.verify(items, os.path.join(tmp, "store"), 30, warm=True)
    seen = [l.split() for l in open(log).read().splitlines()]
    warm = seen[0]
    check(len(res) == 2 and len(seen) == 3 and warm[2].endswith("/warm.bin")
          and warm[1] not in (b"c" * 32).hex() + (b"d" * 32).hex() and seen[1][1] == (b"c" * 32).hex(),
          f"a warmed run checks the organiser's warm-up input first (fresh key and statement), then the items: {len(seen)} requests")
    wf = open(log + ".warm", "rb").read()           # as the badge read it: the run's copy is gone after it
    check(wf == warm_file() and parse(wf) is not None and parse(wf).trace == [] and not os.path.exists(warm[2]),
          "the warm-up file is the organiser's, a well-formed signed proof with no trace, in a copy of the run's own "
          "(removed after it)")
    open(log, "w").close()
    res2 = b.verify(items, os.path.join(tmp, "store"), 30, warm=True)
    w2 = open(log).read().splitlines()[0].split()
    check(w2[1] != warm[1] and w2[0] != warm[0], "each warmed run draws a fresh warm-up key and statement")
    slow = LocalBadge([sys.executable, "-I", echo, "2.5", log], os.path.join(tmp, "scratch"), start_s=1)
    try:
        slow.verify(items, os.path.join(tmp, "store"), 30, warm=True)
        err = None
    except BadgeError as e:
        err = e
    check(err is not None and err.kind == "timeout" and "badge_start_s" in str(err),
          f"a badge that answers its warm-up after the start-up cap fails the run: {str(err)[:90]}")
    unwarmed = LocalBadge([sys.executable, "-I", echo, "1.5", log], os.path.join(tmp, "scratch"), start_s=1)
    res3 = unwarmed.verify(items, os.path.join(tmp, "store"), 30, warm=False)
    check(len(res3) == 2, "an unwarmed run (the canaries) has no start-up cap")
    print(f"\n{len(FAILS)} failure(s)")
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
