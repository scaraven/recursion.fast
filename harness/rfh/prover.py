"""Building and running the untrusted prover (TRUSTED RUNTIME; `harness/PROVER.md` is the
interface). Every step runs in `sandbox.Sandbox`.

* `build`: `gcc -static -O2 -pthread *.s -o prover -lm` inside the sandbox (`.incbin` and
  `.include` read only what the sandbox shows: the copied `.s` files and the toolchain), on a
  private tmpfs, with the toolchain's versions and the binary's hash recorded.
* `setup`: `prover setup /setup`, untimed, before any instance or service exists, its `/setup` a
  private tmpfs charged to its memory cap, measured and copied to the work disk once it is dead
  (`Run.setup`); `/setup` is read-only afterwards, and once hashed it and the binary are copied to the runner's tmpfs
  (`Run.publish`), which every request binds instead of the work disk: a fresh copy for the service
  run and for each timed pass, the previous one removed first (review LR5 H1: a tmpfs file keeps
  state a read-only handle can set, its shared memory policy among them).
* `request`: one `prover first /work` or `prover step /work` in a fresh process, its /work a
  private tmpfs (a superblock of its own, so inode numbers and free space carry nothing from one
  request to the next): the process starts and prints `ready` (within `ready_s`, untimed); the
  runner writes the inputs to unnamed files on that tmpfs, which the prover cannot see; the clock
  starts; the runner links the service's socket into the request's own socket directory (so
  `/run/rf/oracle.sock` exists only from `go` on), links the inputs into /work and sends `go`; at
  the prover's `done` line, its stdout's end or its exit the runner kills the whole sandbox and
  **stops the clock when every process of it is dead** (`harness/PROVER.md` §3); then `proof.bin`
  is read. A filesystem error in the request's directory is the entry's failure. The request's
  sandbox also refuses `sendmsg`, `sendmmsg` and `sysinfo` (`sandbox.seccomp_program(request=True)`).
* `oneshot`: a program with no handshake, timed from exec to exit (the sandbox tests).
"""
import errno
import glob
import hashlib
import os
import select
import stat
import subprocess
import threading
import time

from .files import OutputError, read_output
from .sandbox import (MAX_REL_PATH, Sandbox, copy_tree, parse_bytes, remove_tree, runner_dir,  # noqa: F401 (remove_tree: re-exported)
                      runner_path, tree_entries)

PROVER = "/prover/prover"
SETUP_ENTRIES = 1 << 16          # entries of the setup directory (each costs runner memory in every copy, review R3 M1)
SOCK_IN = "/run/rf"
LOG_CAP = 1 << 16


class Drain(threading.Thread):
    """Reads a pipe to its end, keeping its first 16 KiB and its last 48 KiB (a refusal or a
    crash message is usually at the end), so that a prover cannot block on a full pipe or fill the
    runner's disk with output."""

    HEAD, TAIL = 1 << 14, 3 << 14

    def __init__(self, f):
        super().__init__(daemon=True)
        self.f, self.head, self.tail, self.dropped = f, bytearray(), bytearray(), 0
        self.start()

    def run(self):
        try:
            while True:
                c = os.read(self.f.fileno(), 1 << 16)
                if not c:
                    return
                if len(self.head) < self.HEAD:
                    k = self.HEAD - len(self.head)
                    self.head += c[:k]
                    c = c[k:]
                self.tail += c
                if len(self.tail) > self.TAIL:
                    self.dropped += len(self.tail) - self.TAIL
                    del self.tail[:len(self.tail) - self.TAIL]
        except OSError:
            return

    @property
    def kept(self):
        gap = f"\n[… {self.dropped} bytes dropped …]\n".encode() if self.dropped else b""
        return bytes(self.head) + gap + bytes(self.tail)


def oom_status(sb, mem, events=None, peak=None):
    """The status of a sandbox the kernel's OOM killer killed, or None (`oom_label`). `events`, `peak`:
    the scope's `memory.events` and `memory.peak` as read while it existed (`Sandbox.memory_events`),
    if they were."""
    oom, scope_peak = sb.oom()
    if not oom:
        return None
    return oom_label(mem, peak or scope_peak, events)


def oom_label(mem, peak=None, events=None):
    """What a kill by the OOM killer of a process of the sandbox's scope (systemd's `Result=oom-kill`)
    was. The scope's result does not say whose OOM it was: cgroup v2's `oom_kill` counts a kill by
    any OOM killer, the scope's own (its usage reached `MemoryMax`: `oom` counts that too) or the
    machine's (a global OOM: `oom_kill` without `oom`). With the scope's `memory.events` read, it
    says which; else, with its peak at its cap (within 64 MiB), the cap's; else it says it may have
    been a global OOM, an organiser-side question (AGENTS.md §12): the caps of §9 are meant to make
    one impossible."""
    pk = f", peak {peak / 2 ** 30:.2f} GiB" if peak else ""
    if events is not None and events.get("oom", 0) > 0:
        return f"killed: out of memory (cap {mem}{pk})"
    if events is not None and events.get("oom_kill", 0) > 0:
        return (f"killed (SIGKILL) by a global out-of-memory kill below its cap {mem}{pk}: the machine ran out of "
                "memory (an organiser-side question, AGENTS.md §12)")
    if peak is not None and peak >= parse_bytes(mem) - (64 << 20):
        return f"killed: out of memory (cap {mem}{pk})"
    return (f"killed by the OOM killer (cap {mem}, {pk[2:] or 'peak unknown'}; its cap's, or possibly a global OOM: "
            "an organiser-side question, AGENTS.md §12)")


def toolchain_versions():
    """The build toolchain, as recorded in every result."""
    def first(cmd):
        try:
            return subprocess.run(cmd, capture_output=True, text=True, timeout=30).stdout.splitlines()[0]
        except (OSError, IndexError, subprocess.TimeoutExpired):
            return None
    return {"gcc": first(["gcc", "--version"]), "as": first(["as", "--version"]), "ld": first(["ld", "--version"]),
            "glibc": first(["ldd", "--version"]), "bwrap": first(["bwrap", "--version"])}


BUILD_ROOT = ("/usr", "/bin", "/lib", "/lib64", "/lib32", "/libx32", "/sbin", "/etc/alternatives",
              "/etc/ld.so.cache")


def build(entry_prover_dir, out_dir, mem, timeout, binary_cap=1 << 31):
    """Assemble and link `entry_prover_dir/*.s` into `out_dir/bin/prover`; (ok, info). The build's
    /build is a private tmpfs of its sandbox (charged to its memory cap `mem`, so an assembler
    output of any size never reaches the work disk: review R3 H3), holding the sources as copies;
    the binary is read from it through a held descriptor (`held_tmpfs`) once the sandbox is dead,
    at most `binary_cap` bytes (the season's `setup_cap`: the binary is copied with the setup and
    counted with it, M1). The build's output is kept printable and short (`info["log"]`, L3)."""
    from .bench import printable
    srcs = sorted(glob.glob(os.path.join(entry_prover_dir, "*.s")))
    info = {"sources": {}, "toolchain": toolchain_versions()}
    if not srcs:
        return False, dict(info, error="no prover/*.s file")
    files = []
    for s in srcs:
        if os.path.islink(s) or not os.path.isfile(s):
            return False, dict(info, error=f"{os.path.basename(s)} is not a regular file")
        data = open(s, "rb").read()
        info["sources"][os.path.basename(s)] = hashlib.sha256(data).hexdigest()
        files.append(("file", data, f"/build/{os.path.basename(s)}"))
    names = [f"/build/{os.path.basename(s)}" for s in srcs]
    cmd = ["/usr/bin/gcc", "-static", "-O2", "-pthread", *names, "-o", "/build/prover", "-lm"]
    info["command"] = " ".join(cmd)
    sb = Sandbox(cmd, [("tmpfs", None, "/build")] + files, mem, env={"PATH": "/usr/bin:/bin"}, cwd="/build",
                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT, extra_ro_root=BUILD_ROOT, hold=True, status=True)
    out = Drain(sb.proc.stdout)
    fd = None
    try:
        fd = held_tmpfs(sb, "/build")
        sb.release()
        try:
            code = sb.proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            sb.kill()
            return False, dict(info, error="build timed out")
        sb.kill()
        out.join(5)
        info["log"] = printable(out.kept.decode(errors="replace"), 4000)
        if code != 0:
            return False, dict(info, error=f"gcc exited with {code}")
        try:
            binary = read_output(f"/proc/self/fd/{fd}/.", "prover", binary_cap)
        except OutputError as e:
            return False, dict(info, error=str(e) + (" (the binary counts toward setup_cap)" if "cap" in str(e) else ""))
    finally:
        sb.kill()
        if fd is not None:
            os.close(fd)
    os.makedirs(os.path.join(out_dir, "bin"))
    path = os.path.join(out_dir, "bin", "prover")
    with open(path, "wb") as f:
        f.write(binary)
    os.chmod(path, 0o555)
    info["binary_sha256"] = hashlib.sha256(binary).hexdigest()
    info["binary_bytes"] = len(binary)
    return True, info


class Run:
    """Where a prover runs: its binary directory, its setup directory (both on the work disk), the
    memory cap, and once `publish`ed their current copies on the runner's tmpfs (`view`), which
    every later sandbox binds instead."""

    def __init__(self, bin_dir, setup_dir, mem):
        self.bin_dir, self.setup_dir, self.mem = bin_dir, setup_dir, mem
        self.view = self.root = None
        self.seen = False                    # whether a sandbox has bound the current copy
        self.copies = []                     # (bytes, seconds) of every copy made

    def publish(self):
        """After `setup` and the setup's hash: a **fresh** copy of the binary directory and the setup
        directory on the runner's tmpfs (`sandbox.copy_tree`: every byte written, files read-only,
        directories, files and links only), which every request binds read-only at /prover and
        /setup from then on (`binds`), the previous copy removed first. The benchmark makes one before
        the service run and one before each timed pass (`Bench.timed`), so that only the steps of
        one pass, on one clock, share a copy: a tmpfs file keeps state that a process holding it
        read-only can set and a later one read (its shared memory policy, `mbind` on a read-only
        `MAP_SHARED` mapping, read back with `get_mempolicy`: review LR5 H1; page flags), and a
        service-run request could otherwise move untimed work into a timed pass, or one timed pass
        precompute for the next. No request sees the work disk's directories, whose lookups leave
        negative dentries and whose page-cache folios keep a shape a later request could read
        (review LR4 H1, H2), and the copies are always resident (no re-read before a request). A
        copy (at most `setup_cap` and the binary) is charged to the runner's memory; at most one
        exists at a time, and the last is removed when the runner exits. A tmpfs without room is the
        runner's failure (a RuntimeError). Returns (bytes copied, seconds)."""
        import time as _t
        t0 = _t.monotonic()
        if self.root is not None:
            if not remove_tree(self.root):
                raise RuntimeError(f"the previous copy of the setup ({self.root}) could not be removed")
            self.view = self.root = None
        make_accessible(self.setup_dir)
        need = tree_bytes(self.setup_dir) + tree_bytes(self.bin_dir)
        st = os.statvfs(runner_dir())
        if need == float("inf") or need + (64 << 20) > st.f_bavail * st.f_frsize:
            raise RuntimeError(f"the runner's tmpfs ({runner_dir()}) has {st.f_bavail * st.f_frsize} bytes free, "
                               f"not enough for the setup and the binary ({need} bytes)")
        self.root = root = runner_path("prover")
        n = copy_tree(self.bin_dir, os.path.join(root, "bin")) + copy_tree(self.setup_dir, os.path.join(root, "setup"))
        self.view, self.seen = (os.path.join(root, "bin"), os.path.join(root, "setup")), False
        self.copies.append((n, _t.monotonic() - t0))
        return self.copies[-1]

    def binds(self, work, sock_dir=None, setup_rw=False):
        """The prover's mounts; `work` None: a private tmpfs at /work. Once `publish`ed, /prover and
        /setup are the tmpfs copies (`setup_rw`, the setup's own run, binds the work disk's)."""
        bin_dir, setup = self.view if self.view and not setup_rw else (self.bin_dir, self.setup_dir)
        self.seen = self.seen or bool(self.view and not setup_rw)     # the copy has been bound (`Bench.fresh_copy`)
        b = [("ro", bin_dir, "/prover"), ("rw" if setup_rw else "ro", setup, "/setup"),
             ("rw", work, "/work") if work is not None else ("tmpfs", None, "/work")]
        if sock_dir:
            b.append(("ro", sock_dir, SOCK_IN))
        return b

    def env(self, sock_dir):
        e = {"HOME": "/work", "TMPDIR": "/tmp", "RF_SETUP": "/setup", "PATH": "/prover"}
        if sock_dir:
            e["RF_ORACLE"] = f"{SOCK_IN}/oracle.sock"
        return e

    def setup(self, timeout, size_cap=None, max_entries=SETUP_ENTRIES):
        """`prover setup /setup` (untimed, no service, no instance); (ok, seconds, log). Its /setup
        is a **private tmpfs** of the sandbox (charged to its memory cap: the setup's files and its
        memory together; nothing reaches the work disk while it runs, so a setup that writes without
        bound fills its cap, never the runner's disk: review R3 H3), reached through a held
        descriptor (`held_tmpfs`). Once every process of it is dead the runner measures the tree
        (`tree_bytes`: at most `max_entries` entries, paths of at most `MAX_REL_PATH` bytes) and, if
        it and the prover binary fit `size_cap` together (`setup_cap`, M1), copies it to the work
        disk's `setup_dir` (`copy_tree`), which the hash and every later copy read; else the setup
        fails. Every error on the entry's tree is the setup's failure (the entry's), never the
        runner's."""
        if os.path.lexists(self.setup_dir):
            remove_tree(self.setup_dir)
        sb = Sandbox([PROVER, "setup", "/setup"], [("ro", self.bin_dir, "/prover"), ("tmpfs", None, "/setup")],
                     self.mem, env=self.env(None), cwd="/setup", stdout=subprocess.PIPE,
                     stderr=subprocess.STDOUT, hold=True, status=True)
        out = Drain(sb.proc.stdout)
        fd = None
        try:
            fd = held_tmpfs(sb, "/setup")
            t0 = time.monotonic()
            sb.release()
            try:
                code = sb.proc.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                code = "timeout"
            dt = time.monotonic() - t0
            sb.kill()
            out.join(5)
            log = out.kept.decode(errors="replace")
            if code != 0:
                return False, dt, log
            held = f"/proc/self/fd/{fd}/."
            used = tree_bytes(held, max_entries=max_entries)
            binary = tree_bytes(self.bin_dir)
            if size_cap is not None and used + binary > size_cap:
                return False, dt, log + (f"\nthe setup directory holds {used} bytes and the prover binary {binary} (a tree "
                                         f"the runner cannot walk, with more than {max_entries} entries or a path above "
                                         f"{MAX_REL_PATH} bytes counts as inf), together above setup_cap = {size_cap}")
            try:
                copy_tree(held, self.setup_dir, max_entries=max_entries)
            except OSError as e:
                remove_tree(self.setup_dir)
                if e.errno in (errno.ENOSPC, errno.EDQUOT, errno.EIO, errno.EROFS):
                    # the work disk's fault, not the tree's: the runner's (a harness error)
                    raise RuntimeError(f"copying the setup to the work disk: {e}") from None
                return False, dt, log + f"\nthe setup directory could not be copied ({type(e).__name__}: {e})"
            except Exception as e:  # noqa: BLE001 (the entry's tree)
                remove_tree(self.setup_dir)
                return False, dt, log + f"\nthe setup directory could not be copied ({type(e).__name__}: {e})"
            return True, dt, log
        finally:
            sb.kill()
            if fd is not None:
                os.close(fd)

    def oneshot(self, mode, work, sock_dir, timeout):
        """`prover MODE /work` with no handshake, timed from exec to exit; (status, seconds, log).
        The benchmark makes no such request; the sandbox tests run hostile programs
        through it."""
        sb = Sandbox([PROVER, mode, "/work"], self.binds(work, sock_dir), self.mem, env=self.env(sock_dir),
                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT, hold=True, request=True)
        out = Drain(sb.proc.stdout)
        sb.wait_ready()
        t0 = time.monotonic()
        sb.release()
        code, t1 = sb.wait_exit(timeout)
        dt = t1 - t0
        status = "timeout" if code is None and dt >= timeout else ("ok" if code == 0 else f"exit {code}")
        if status != "ok":
            sb.proc.wait(timeout=30)
            status = oom_status(sb, self.mem) or status
        sb.kill()
        out.join(5)
        return status, dt, out.kept.decode(errors="replace")


class Step:
    """What one request did: `status` (`ok` or the entry's failure), `seconds` (the timed part, from
    the inputs' arrival to the death of the request's last process), `t_stop_ns` (the monotonic time
    the clock stopped, `CLOCK_MONOTONIC` in ns), `startup_s` (process start to `ready`, untimed),
    `kill_s` (from `done` or the exit seen to every process dead), `mem_peak` (bytes, systemd only),
    `work_bytes` (what the prover left in /work), `proof` (the bytes of `proof.bin`) and `log`
    (stderr, head and tail)."""

    def __init__(self):
        self.status, self.seconds, self.startup_s, self.kill_s = "ok", None, None, None
        self.mem_peak, self.proof, self.log, self.ended = None, None, "", None
        self.t_stop_ns, self.work_bytes = None, None
        self.at_deadline = False             # a wait ended at `deadline` (the stream's cap), not its own cap


def request(run, kind, work, sock_dir, inputs, step_s, file_cap, deadline=None, ready_s=None,
            work_cap=None, sock_at_go=None, preset=None, pads=(), clock=None):
    """One timed `first` or `step` request in a fresh sandbox (PROVER.md §3). `work` None (the
    benchmark's requests): /work is **a private tmpfs** of the sandbox's own (bubblewrap's
    `--tmpfs`), holding at the start only `preset` (name → bytes, e.g. `vk.hex`), so its inode
    numbers and free space depend on nothing an earlier request did; the runner reaches it through
    the sandbox's init (`/proc/PID/root/work`) and keeps a descriptor on it, through which the
    outputs are read after the sandbox is dead (the mount outlives its namespace while the
    descriptor is open) and which frees it when closed. Else `work` is a host directory bound at
    /work (the sandbox tests). `inputs`: name → bytes, staged where the prover cannot see them
    (unnamed `O_TMPFILE` files on the private tmpfs, else a staging directory beside `work`) and
    linked or renamed into /work, in constant time, once the clock runs. `pads` (bytes each) are
    staged the same way on the private tmpfs and never linked: placeholders that make every
    request stage the same number of inodes (`Bench.one`), since a prover that keeps creating files
    in /work before `go` sees the staged inodes as a gap in its inode numbers (review LR4 L1). With
    `sock_at_go` (the service's socket), `sock_dir` is the request's own empty, runner-owned
    directory, bound read-only at `/run/rf`; once the clock runs, the socket is hard-linked into it
    as `oracle.sock` (a connect through the link reaches the service), so no process of the
    request can reach the service before `go` (the untimed start-up cannot `QUERY`). `ready_s`
    (default `step_s`) bounds the start-up to `ready`, `step_s` the proving; `deadline` (a monotonic
    time, the stream's cap on the entry's clock) bounds both, moved later by the runner's own work
    inside the request (the sandbox's view before its spawn, the staging before `go`); a wait it
    ended sets `Step.at_deadline`. **The clock stops when the request's process tree is
    dead**: at the prover's `done` line, its stdout's end or its exit, the runner kills the whole
    sandbox at once (`Sandbox.kill_tree`) and stops the clock when the pid namespace's init has
    exited, which the kernel allows only after every other process in it is dead; only then is
    `proof.bin` read. So nothing the prover does after `done` is untimed, and no byte written after
    the clock stopped exists.

    **Failures are the entry's by default**: once the sandbox is started, any
    exception (a staging write that fails because the prover filled the filesystem, a pid that
    vanished, a sandbox that does not die, an exit status that is not reported, an unreadable
    output) is the entry's failure with its reason, never a harness error. `/work` may hold at most
    `work_cap` bytes when the prover is dead (sparse files counted at their size). `clock(running,
    spent_s=0.0)`, if given, is told when the entry's time in the request runs and when it stops,
    with the time it has spent so far: at the sandbox's spawn (`clock(True)`), at `ready` or the
    start-up's end (`clock(False, startup_s)`), just before the timed part (`clock(True,
    startup_s)`) and at the prover's death (`clock(False, startup_s + seconds)`), so that the
    runner's work around them (the view, the staging, the output's read, the `/work` walk) is never
    read as the entry's (`Bench.one`, the stream's checkpoint). Only the first call falls inside
    a measured interval (the start-up's, a checkpoint write of a few ms); none inside the timed
    part. Returns a `Step`."""
    held = []                                   # the private tmpfs's descriptor and the staged files
    try:
        return _request(run, kind, work, sock_dir, inputs, step_s, file_cap, deadline, ready_s, work_cap,
                        sock_at_go, preset, held, pads, clock)
    finally:
        for fd in held:
            os.close(fd)


def _request(run, kind, work, sock_dir, inputs, step_s, file_cap, deadline, ready_s, work_cap, sock_at_go,
             preset, held, pads=(), clock=None):
    import select
    # `deadline` bounds the entry's time: the runner's own work inside the request (its sandbox's
    # view before the spawn, the staging between `ready` and `go`) moves it later by its duration
    # (`shift`), as the stream's clock stops for the runner's work (`Bench.deadline`, review R3 L1)
    t_call, shift = time.monotonic(), [0.0]
    cap = (lambda t: t) if deadline is None else (lambda t: min(t, deadline + shift[0]))
    at_cap = lambda: deadline is not None and time.monotonic() >= deadline + shift[0] - 1e-3  # noqa: E731
    r = Step()
    events = None
    private = work is None
    binds = run.binds(work, sock_dir) + [("file", data, f"/work/{name}") for name, data in (preset or {}).items()]
    sb = Sandbox([PROVER, kind, "/work"], binds, run.mem, env=run.env(sock_dir),
                 stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, status=True, request=True)
    t_spawn = sb.t_spawn
    shift[0] = t_spawn - t_call
    if clock is not None:
        clock(True)
    err = Drain(sb.proc.stderr)
    fd = sb.proc.stdout.fileno()
    buf = b""
    try:
        if not sb.track():
            raise EntryFailure("the prover's sandbox ended before the runner could track it")

        def wait_line(word, until):
            """Read stdout until a line equal to `word` ("line"), its end ("eof"), the death of the
            sandbox ("dead") or the time `until` ("timeout")."""
            nonlocal buf
            while True:
                lines = buf.split(b"\n")
                if word.encode() in lines[:-1]:
                    buf = b"\n".join(lines[lines.index(word.encode()) + 1:])
                    return "line"
                if len(buf) > LOG_CAP:
                    buf = buf[-64:]
                left = until - time.monotonic()
                if left <= 0:
                    return "timeout"
                ready = select.select([fd, sb.pidfd], [], [], left)[0]
                if fd in ready:
                    c = os.read(fd, 1 << 16)
                    if not c:
                        return "eof"
                    buf += c
                elif sb.pidfd in ready:
                    return "dead"

        w = wait_line("ready", cap(t_spawn + (ready_s or step_s)))
        t_ready = time.monotonic()
        r.startup_s = t_ready - t_spawn
        if clock is not None:               # the start-up's time ends; the staging is the runner's
            clock(False, r.startup_s)
        if w != "line":
            r.status = "no ready line" + ("" if w == "timeout" else f" (the prover ended: {w})")
            r.at_deadline = w == "timeout" and at_cap()
            return r
        # the inputs are written where the prover cannot see them before the clock starts, and
        # only linked or renamed into /work (constant time) once it runs
        if private:
            # the sandbox's /work, reached through its init (bubblewrap's, not the prover's: it has
            # pivoted into the sandbox's root before the prover ran, so before `ready`)
            wfd = os.open(f"/proc/{sb.child_pid}/root/work", os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
            held.append(wfd)
            work = f"/proc/self/fd/{wfd}/."     # a path through the descriptor, valid after the sandbox
            staged = []
            for name, data in inputs.items():
                tfd = os.open(".", os.O_TMPFILE | os.O_WRONLY, 0o644, dir_fd=wfd)
                held.append(tfd)
                view = memoryview(data)
                while view:
                    view = view[os.write(tfd, view):]
                staged.append((name, tfd, f".rf-input-{os.urandom(8).hex()}"))
            for data in pads:                   # placeholders: staged like an input, never linked
                tfd = os.open(".", os.O_TMPFILE | os.O_WRONLY, 0o644, dir_fd=wfd)
                held.append(tfd)
                view = memoryview(data)
                while view:
                    view = view[os.write(tfd, view):]
        else:
            stage = work.rstrip("/") + ".stage"
            os.makedirs(stage, exist_ok=True)
            for name, data in inputs.items():
                with open(os.path.join(stage, name), "wb") as f:
                    f.write(data)
        if clock is not None:               # the timed part begins: before `t0`, so its write is untimed
            clock(True, r.startup_s)
        t0 = time.monotonic()
        shift[0] += t0 - t_ready                # the staging: the runner's
        if sock_at_go:
            try:
                os.link(sock_at_go, os.path.join(sock_dir, "oracle.sock"))
            except OSError as e:
                raise HarnessError(f"linking the service's socket into the request's socket directory: {e}") from e
        try:
            if private:                     # linked under a fresh name, then renamed (as a rename would)
                for name, tfd, tmp in staged:
                    os.link(f"/proc/self/fd/{tfd}", tmp, dst_dir_fd=wfd)
                    os.rename(tmp, name, src_dir_fd=wfd, dst_dir_fd=wfd)
            else:
                for name in inputs:
                    os.rename(os.path.join(stage, name), os.path.join(work, name))
        except OSError as e:
            raise EntryFailure(f"the prover made /work unusable (moving the inputs into /work: {e.strerror or e})")
        try:
            sb.proc.stdin.write(b"go\n")
            sb.proc.stdin.flush()
        except (BrokenPipeError, OSError):
            pass
        w = wait_line("done", cap(t0 + step_s))
        if w == "eof":                          # stdout closed without `done`: wait for the exit, timed
            left = cap(t0 + step_s) - time.monotonic()
            w = "dead" if left > 0 and select.select([sb.pidfd], [], [], left)[0] else "timeout"
        t_seen = time.monotonic()
        r.mem_peak, events = sb.memory_peak(), sb.memory_events()     # while the scope exists (`oom_label`)
        dead, t1, t1_ns = sb.kill_tree()
        if not dead:
            raise EntryFailure("the prover's sandbox did not die within 30 s of SIGKILL")
        r.seconds, r.kill_s, r.ended, r.t_stop_ns = t1 - t0, t1 - t_seen, w, t1_ns
        if clock is not None:
            clock(False, r.startup_s + r.seconds)
        if w == "timeout":
            r.status = "timeout"
            r.at_deadline = at_cap()
        elif w == "dead":
            code = sb.exit_code()
            if code is None:
                r.status = "the prover exited without `done` and its exit status was not reported"
            elif code != 0:
                r.status = f"exit {code}"
    except HarnessError:
        raise
    except EntryFailure as e:
        r.status = str(e)
    except Exception as e:  # noqa: BLE001 (the default is the entry's failure)
        r.status = f"the request failed while the prover's sandbox existed ({type(e).__name__}: {e})"
    finally:
        try:
            if r.status != "ok":
                r.status = oom_status(sb, run.mem, events, r.mem_peak) or r.status
        finally:
            sb.kill()                               # kill_unit and the outer process, after the clock
            err.join(5)
            r.log = err.kept.decode(errors="replace")
    if r.status == "ok":
        try:
            r.proof = read_output(work, "proof.bin", file_cap)
            if work_cap is not None:
                r.work_bytes = tree_bytes(work, max_entries=1 << 16)
                if r.work_bytes > work_cap:
                    r.status = (f"the prover left {r.work_bytes} bytes in /work (or more than 65,536 entries), "
                                f"above work_cap = {work_cap}")
        except OutputError as e:
            r.status = oom_status(sb, run.mem, events, r.mem_peak) or str(e)
        except Exception as e:  # noqa: BLE001 (an unusable directory is the entry's failure)
            r.status = f"the prover made /work unusable (reading its outputs: {type(e).__name__}: {e})"
    return r


class EntryFailure(Exception):
    """A failure the prover caused (its reason is the step's status)."""


class HarnessError(RuntimeError):
    """A failure of the runner's own (a harness error, never the entry's)."""


def make_accessible(path):
    """Give the runner read, write and search permission on every directory and file under `path`
    (no link followed), top down, so that a tree the prover locked can be measured and removed
    (`sandbox.tree_entries`: iterative, any names)."""
    for _ in tree_entries(path, fix_access=True):
        pass


def tree_bytes(path, max_entries=1 << 20):
    """Bytes under `path`, each file counted at `max(size, allocated)` (a sparse file at its size),
    no link followed, after making the tree accessible; a tree the runner cannot walk (any error,
    whatever its kind: review R3 H2), one with a relative path above `MAX_REL_PATH` bytes, or one
    of more than `max_entries` entries (which bounds the walk's time) counts as unbounded (the
    entry's failure where a cap applies)."""
    total = 0
    try:
        for _, st in tree_entries(path, max_entries=max_entries, fix_access=True):
            total += max(st.st_size, st.st_blocks * 512)
    except Exception:  # noqa: BLE001 (an entry-written tree the runner cannot walk is unbounded)
        return float("inf")
    return total


def tree_sha256(path, max_bytes, timeout, max_entries=None):
    """A hash of a directory tree: each entry's kind (`D`, `F`, `L`, else `O`), its relative path
    as bytes (any name, review R3 H1), and a file's contents or a link's target (none followed),
    in `sandbox.tree_entries`' order: the setup's hash in the result. It reads at most `max_bytes`
    bytes and runs at most `timeout` seconds; past either, or on any error, it returns None."""
    h, read, t_end = hashlib.sha256(), 0, time.monotonic() + timeout
    top = os.fsencode(path)
    try:
        for rel, st in tree_entries(top, max_entries=max_entries):
            kind = (b"D" if stat.S_ISDIR(st.st_mode) else b"F" if stat.S_ISREG(st.st_mode)
                    else b"L" if stat.S_ISLNK(st.st_mode) else b"O")
            h.update(kind + rel + b"\0")
            if kind == b"L":
                h.update(os.readlink(top + b"/" + rel) + b"\0")
            elif kind == b"F":
                fd = os.open(top + b"/" + rel, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
                try:
                    while c := os.read(fd, 1 << 20):
                        h.update(c)
                        read += len(c)
                        if read > max_bytes or time.monotonic() > t_end:
                            return None
                finally:
                    os.close(fd)
                h.update(b"\0")
            if time.monotonic() > t_end:
                return None
    except Exception:  # noqa: BLE001 (an entry-written tree the runner cannot hash: None, the entry's failure)
        return None
    return h.hexdigest()


def held_tmpfs(sb, inside, timeout=30):
    """For a sandbox started held (`hold=True, status=True`): once bubblewrap has set it up (its
    init's /proc/PID/mountinfo lists a tmpfs at `inside`, which it does only after the root's
    pivot), a descriptor on that private tmpfs, opened through the init's root (the device checked
    against the mount's), which keeps the tmpfs, and everything on it, after the sandbox is gone;
    closing it frees them. Its pages are charged to the sandbox's memory cap while it runs.
    A RuntimeError (the runner's) if it does not appear within `timeout` s."""
    if not sb.track():
        raise RuntimeError("the sandbox ended before the runner could track it")
    t_end = time.monotonic() + timeout
    while True:
        dev = None
        try:
            for line in open(f"/proc/{sb.child_pid}/mountinfo"):
                pre, _, post = line.partition(" - ")
                f = pre.split()
                if f[4] == inside and post.split()[:1] == ["tmpfs"]:
                    major, minor = f[2].split(":")
                    dev = os.makedev(int(major), int(minor))
        except (OSError, IndexError, ValueError):
            pass
        if dev is not None:
            fd = os.open(f"/proc/{sb.child_pid}/root{inside}", os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
            if os.fstat(fd).st_dev == dev:
                return fd
            os.close(fd)
        if time.monotonic() > t_end:
            raise RuntimeError(f"the sandbox's private tmpfs at {inside} did not appear within {timeout} s")
        time.sleep(0.005)


def fresh_dir(path):
    """An empty directory at `path` (whatever a prover left there is removed first)."""
    if os.path.lexists(path) and not remove_tree(path):
        raise OSError(f"cannot remove {path}")
    os.makedirs(path)
    return path
