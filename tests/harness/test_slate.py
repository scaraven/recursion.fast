#!/usr/bin/env python3
"""The clean slate between a duel's two runs (`harness/rfh/slate.py`, launch R4 m2).

  python3 tests/harness/test_slate.py

A run's leftovers are planted as a `PART_S` kill leaves them: an orphaned service (`rf-oracle`
started by a process that is then SIGKILLed; skipped if the service is not built), an orphaned
process in its own session, a request directory on `/dev/shm` with a file in it, and the work
directory, all carrying the run's token. `leftovers` must find each of them, `clean` must remove
them all, and a process and a request directory of another token, and an untagged process, must
survive.
"""
import os
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from rfh import slate  # noqa: E402
from rfh.sandbox import memcap, memcap_method  # noqa: E402

SERVICE = os.path.join(ROOT, "service", "target", "release", "rf-oracle")
FAIL = []


def check(c, what):
    print(("ok   " if c else "FAIL ") + what, flush=True)
    c or FAIL.append(what)


def orphan(token, argv):
    """`argv` started by a child that then exits at once, in a new session: an orphan with the token."""
    env = dict(os.environ, RF_RUN_TOKEN=token) if token else {k: v for k, v in os.environ.items() if k != "RF_RUN_TOKEN"}
    code = "import os, subprocess, sys; p = subprocess.Popen(sys.argv[1:], start_new_session=True, " \
           "stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, stdin=subprocess.DEVNULL); print(p.pid)"
    return int(subprocess.run([sys.executable, "-c", code, *argv], env=env, capture_output=True, text=True,
                              check=True).stdout)


def alive(pid):
    try:
        return open(f"/proc/{pid}/stat").read().split(")")[-1].split()[0] != "Z"
    except OSError:
        return False


def main():
    duel = "t" + os.urandom(6).hex()
    tok, other = f"{duel}-candidate", "x" + os.urandom(6).hex() + "-incumbent"
    tmp = tempfile.mkdtemp(prefix="rf-slate-", dir=os.environ.get("RF_TEST_TMP"))
    work = os.path.join(tmp, "work")
    os.makedirs(os.path.join(work, "svc"))
    sleeper = orphan(tok, ["sleep", "600"])
    keep_other = orphan(other, ["sleep", "600"])
    keep_plain = orphan(None, ["sleep", "600"])
    svc = None
    if os.access(SERVICE, os.X_OK):
        # an orphaned rf-oracle that does not exit by itself: its stdin held open by another orphan
        # (it exits at stdin's EOF, which a PART_S kill of its parent normally gives it)
        sock = os.path.join(tmp, "svc")
        os.makedirs(sock)
        wrap = memcap("2G", f"rf-svc-{tok}-stream") if memcap_method() == "systemd" else []
        orphan(tok, ["sh", "-c", f"cd '{sock}' && sleep 600 | exec {' '.join(wrap)} '{SERVICE}' --socket s"])
        for _ in range(50):
            svc = next((pid for pid, cmd in slate.leftovers(duel)["processes"] if SERVICE in cmd and "sh -c" not in cmd), None)
            if svc and os.path.exists(os.path.join(sock, "s")):
                break
            time.sleep(0.1)
    shm = tempfile.mkdtemp(prefix=f"rf-req-{tok}-", dir="/dev/shm")
    open(os.path.join(shm, "chain.json"), "wb").write(b"x" * 4096)
    shm_other = tempfile.mkdtemp(prefix=f"rf-req-{other}-", dir="/dev/shm")
    try:
        found = slate.leftovers(duel, work)
        pids = {p for p, _ in found["processes"]}
        check(sleeper in pids and (svc is None or svc in pids) and keep_other not in pids and keep_plain not in pids,
              f"leftovers: the run's orphans {sorted(pids)} (sleep {sleeper}, rf-oracle {svc}), not the others")
        check(found["shm"] == [shm] and found["work"] == [work], f"leftovers: its tmpfs request directory and work: {found}")
        check(not slate.empty(found), "a dirty slate is not empty")
        r = slate.clean(duel, work)
        check(r["left"] == {"processes": 0, "shm": 0, "work": 0} and slate.empty(slate.leftovers(duel, work)),
              f"clean: nothing left ({r})")
        check(not alive(sleeper) and (svc is None or not alive(svc)) and not os.path.exists(shm) and not os.path.exists(work),
              "clean: the orphans are dead, the request directory and the work directory are gone")
        check(alive(keep_other) and alive(keep_plain) and os.path.isdir(shm_other),
              "clean: another run's process and request directory, and an untagged process, survive")
        check(svc is not None, f"an orphaned rf-oracle was planted ({SERVICE} built)")
    finally:
        for pid in (sleeper, keep_other, keep_plain, svc):
            try:
                os.kill(pid, 9)
            except (OSError, TypeError):
                pass
        subprocess.run(["rm", "-rf", shm, shm_other, tmp])
    print(f"{len(FAIL)} failure(s)")
    return 1 if FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
