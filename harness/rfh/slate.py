"""A clean slate between the two runs of a duel (TRUSTED RUNTIME).

`evaluate.py bench --duel` runs `run-benchmark.py` with `RF_RUN_TOKEN=<duel id>-<role>` in its
environment. Every organiser process of the run inherits it: `systemd-run`'s scopes, `bubblewrap`'s
outer process; the sandboxed processes inside lose their environment but die with bubblewrap
(`--die-with-parent`, a private pid namespace). The service (`rf-oracle`) makes itself
non-dumpable, so its environment cannot be read: it is found by its memory scope's name,
`rf-svc-<token>-…` (with the `prlimit` fallback it has no scope; it then exits at its stdin's EOF,
which its parent's death gives it, unless an orphan holds that pipe open, which the token finds).
The stream's request directories on tmpfs are named `/dev/shm/rf-req-<token>-*`
(`rfh.bench.request_root`). So what a run can leave is found by its token: processes whose
environment holds it or whose service scope carries it, request directories that carry it, and its
work directory. `clean` kills and removes them; `leftovers` lists what is left; the second run starts
only on an empty list (`evaluate.py`).
"""
import glob
import os
import shutil
import signal
import time

SHM = "/dev/shm"
VAR = "RF_RUN_TOKEN"


def _processes(prefix):
    """(pid, command) of this user's processes whose environment holds a token starting with `prefix`,
    or whose cgroup is a service scope of such a token."""
    me, out = os.getpid(), []
    needle, scope = f"{VAR}={prefix}".encode(), f"/rf-svc-{prefix}"
    for d in os.listdir("/proc"):
        if not d.isdigit() or int(d) == me:
            continue
        try:
            if os.stat(f"/proc/{d}").st_uid != os.getuid():
                continue
            try:
                env = open(f"/proc/{d}/environ", "rb").read()
            except OSError:           # a non-dumpable process (the service)
                env = b""
            cg = open(f"/proc/{d}/cgroup").read()
            if any(e.startswith(needle) for e in env.split(b"\0")) or scope in cg:
                cmd = open(f"/proc/{d}/cmdline", "rb").read().replace(b"\0", b" ").decode(errors="replace")
                out.append((int(d), cmd.strip()[:200]))
        except OSError:
            continue                      # gone, or not ours
    return out


def leftovers(prefix, work=None):
    """What runs whose token starts with `prefix` left: processes, tmpfs request directories, the
    work directory."""
    return {"processes": _processes(prefix), "shm": sorted(glob.glob(os.path.join(SHM, f"rf-req-{prefix}*"))),
            "work": [work] if work and os.path.lexists(work) else []}


def empty(found):
    return not any(found.values())


def clean(prefix, work=None, wait=10.0):
    """Kill and remove everything `leftovers` finds (SIGKILL, then wait for the processes to go);
    returns what was found before and what is left after."""
    found = leftovers(prefix, work)
    for pid, _ in found["processes"]:
        try:
            os.kill(pid, signal.SIGKILL)
        except OSError:
            pass
    deadline = time.monotonic() + wait
    while _processes(prefix) and time.monotonic() < deadline:
        time.sleep(0.1)
    for d in found["shm"] + found["work"]:
        shutil.rmtree(d, ignore_errors=True)
    return {"found": {k: len(v) for k, v in found.items()}, "found_processes": [c for _, c in found["processes"]][:10],
            "left": {k: len(v) for k, v in leftovers(prefix, work).items()}}
