"""Building and running the untrusted prover (TRUSTED RUNTIME; `harness/PROVER.md` is the
interface). Every step runs in `sandbox.Sandbox`.

* `build`: `gcc -static -O2 -pthread *.s -o prover -lm` inside the sandbox (V4-A6: `.incbin` and
  `.include` read only what the sandbox shows: the copied `.s` files and the toolchain), with the
  toolchain's versions and the binary's hash recorded.
* `setup`: `prover setup /setup`, untimed, before any instance or service exists; `/setup` is
  read-only afterwards.
* `request`: one `prover first /work` or `prover step /work` in a fresh process (V4-A11): the
  process starts and prints `ready` (within `ready_s`, untimed); the runner writes the inputs to a
  staging directory the prover cannot see; the clock starts; the runner renames the inputs into
  /work and sends `go`; at the prover's `done` line, its stdout's end or its exit the runner kills
  the whole sandbox and **stops the clock when every process of it is dead** (§5.1); then
  `proof.bin` is read. A filesystem error in the request's directory is the entry's failure (R-M1).
* `oneshot`: a program with no handshake, timed from exec to exit (the sandbox tests).
"""
import glob
import hashlib
import os
import select
import shutil
import stat
import subprocess
import threading
import time

from .files import OutputError, read_output
from .sandbox import Sandbox

PROVER = "/prover/prover"
SOCK_IN = "/run/rf"
LOG_CAP = 1 << 16


class Drain(threading.Thread):
    """Reads a pipe to its end, keeping its first 16 KiB and its last 48 KiB (Q13: a refusal or a
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


def oom_status(sb, mem):
    """The status of a sandbox the memory cgroup killed (Q14), or None."""
    oom, peak = sb.oom()
    if not oom:
        return None
    return f"killed: out of memory (cap {mem}" + (f", peak {peak / 2 ** 30:.2f} GiB)" if peak else ")")


def toolchain_versions():
    """The build toolchain and the runner image, as recorded in every result (V4-A6)."""
    def first(cmd):
        try:
            return subprocess.run(cmd, capture_output=True, text=True, timeout=30).stdout.splitlines()[0]
        except (OSError, IndexError, subprocess.TimeoutExpired):
            return None
    return {"gcc": first(["gcc", "--version"]), "as": first(["as", "--version"]), "ld": first(["ld", "--version"]),
            "glibc": first(["ldd", "--version"]), "bwrap": first(["bwrap", "--version"]),
            "image_os": os.environ.get("ImageOS"), "image_version": os.environ.get("ImageVersion")}


BUILD_ROOT = ("/usr", "/bin", "/lib", "/lib64", "/lib32", "/libx32", "/sbin", "/etc/alternatives",
              "/etc/ld.so.cache")


def build(entry_prover_dir, out_dir, mem, timeout):
    """Assemble and link `entry_prover_dir/*.s` into `out_dir/prover`; (ok, info)."""
    srcs = sorted(glob.glob(os.path.join(entry_prover_dir, "*.s")))
    info = {"sources": {}, "toolchain": toolchain_versions()}
    if not srcs:
        return False, dict(info, error="no prover/*.s file")
    bdir = os.path.join(out_dir, "build")
    os.makedirs(bdir)
    for s in srcs:
        if os.path.islink(s) or not os.path.isfile(s):
            return False, dict(info, error=f"{os.path.basename(s)} is not a regular file")
        data = open(s, "rb").read()
        info["sources"][os.path.basename(s)] = hashlib.sha256(data).hexdigest()
        open(os.path.join(bdir, os.path.basename(s)), "wb").write(data)
    names = [f"/build/{os.path.basename(s)}" for s in srcs]
    cmd = ["/usr/bin/gcc", "-static", "-O2", "-pthread", *names, "-o", "/build/prover", "-lm"]
    info["command"] = " ".join(cmd)
    sb = Sandbox(cmd, [("rw", bdir, "/build")], mem, env={"PATH": "/usr/bin:/bin"}, cwd="/build",
                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT, extra_ro_root=BUILD_ROOT)
    out = Drain(sb.proc.stdout)
    try:
        code = sb.proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        sb.kill()
        return False, dict(info, error="build timed out")
    sb.kill()
    out.join(5)
    info["log"] = out.kept.decode(errors="replace")[-4000:]
    if code != 0:
        return False, dict(info, error=f"gcc exited with {code}")
    try:
        binary = read_output(bdir, "prover", 1 << 31)
    except OutputError as e:
        return False, dict(info, error=str(e))
    os.makedirs(os.path.join(out_dir, "bin"))
    path = os.path.join(out_dir, "bin", "prover")
    with open(path, "wb") as f:
        f.write(binary)
    os.chmod(path, 0o555)
    info["binary_sha256"] = hashlib.sha256(binary).hexdigest()
    info["binary_bytes"] = len(binary)
    return True, info


class Run:
    """Where a prover runs: its binary directory, its setup directory, the memory cap."""

    def __init__(self, bin_dir, setup_dir, mem):
        self.bin_dir, self.setup_dir, self.mem = bin_dir, setup_dir, mem

    def binds(self, work, sock_dir=None, setup_rw=False):
        b = [("ro", self.bin_dir, "/prover"), ("rw" if setup_rw else "ro", self.setup_dir, "/setup"),
             ("rw", work, "/work")]
        if sock_dir:
            b.append(("ro", sock_dir, SOCK_IN))
        return b

    def env(self, sock_dir):
        e = {"HOME": "/work", "TMPDIR": "/tmp", "RF_SETUP": "/setup", "PATH": "/prover"}
        if sock_dir:
            e["RF_ORACLE"] = f"{SOCK_IN}/oracle.sock"
        return e

    def setup(self, timeout, size_cap=None):
        """`prover setup /setup` (untimed, no service, no instance); (ok, seconds, log). With
        `size_cap`, a setup directory above it after the run fails the setup (R-M1, `setup_cap`)."""
        os.makedirs(self.setup_dir, exist_ok=True)
        sb = Sandbox([PROVER, "setup", "/setup"], self.binds(self.setup_dir, setup_rw=True)[:2],
                     self.mem, env=self.env(None), cwd="/setup", stdout=subprocess.PIPE,
                     stderr=subprocess.STDOUT)
        out = Drain(sb.proc.stdout)
        t0 = time.monotonic()
        try:
            code = sb.proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            code = "timeout"
        sb.kill()
        out.join(5)
        log = out.kept.decode(errors="replace")
        if code == 0 and size_cap is not None:
            used = tree_bytes(self.setup_dir)
            if used > size_cap:
                return False, time.monotonic() - t0, log + (f"\nthe setup directory holds {used} bytes (unreadable "
                                                            f"or more than 2^20 entries counts as inf), above setup_cap = {size_cap}")
        return code == 0, time.monotonic() - t0, log

    def oneshot(self, mode, work, sock_dir, timeout):
        """`prover MODE /work` with no handshake, timed from exec to exit; (status, seconds, log).
        The benchmark makes no such request since V4-A11; the sandbox tests run hostile programs
        through it."""
        sb = Sandbox([PROVER, mode, "/work"], self.binds(work, sock_dir), self.mem, env=self.env(sock_dir),
                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT, hold=True)
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


def request(run, kind, work, sock_dir, inputs, step_s, file_cap, deadline=None, ready_s=None,
            work_cap=None):
    """One timed `first` or `step` request in a fresh sandbox (PROVER.md §3; V4-A11 §5.1). `inputs`:
    name → bytes, staged outside the sandbox and renamed into `work` once the clock runs. `ready_s`
    (default `step_s`) bounds the start-up to `ready`, `step_s` the proving; `deadline` (a monotonic
    time, the stream's cap) bounds both. **The clock stops when the request's process tree is
    dead**: at the prover's `done` line, its stdout's end or its exit, the runner kills the whole
    sandbox at once (`Sandbox.kill_tree`) and stops the clock when the pid namespace's init has
    exited, which the kernel allows only after every other process in it is dead; only then is
    `proof.bin` read. So nothing the prover does after `done` is untimed, and no byte written after
    the clock stopped exists.

    **Failures are the entry's by default** (R-M1, review M-1): once the sandbox is started, any
    exception (a staging write that fails because the prover filled the filesystem, a pid that
    vanished, a sandbox that does not die, an exit status that is not reported, an unreadable
    output) is the entry's failure with its reason, never a harness error. `/work` may hold at most
    `work_cap` bytes when the prover is dead (sparse files counted at their size). Returns a `Step`."""
    import select
    cap = (lambda t: t) if deadline is None else (lambda t: min(t, deadline))
    r = Step()
    t_spawn = time.monotonic()
    sb = Sandbox([PROVER, kind, "/work"], run.binds(work, sock_dir), run.mem, env=run.env(sock_dir),
                 stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, status=True)
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
        r.startup_s = time.monotonic() - t_spawn
        if w != "line":
            r.status = "no ready line" + ("" if w == "timeout" else f" (the prover ended: {w})")
            return r
        # RB-m11: the inputs are written to a staging directory outside the sandbox before the clock
        # starts, and only renamed into /work (constant time) once it runs
        stage = work.rstrip("/") + ".stage"
        os.makedirs(stage, exist_ok=True)
        for name, data in inputs.items():
            with open(os.path.join(stage, name), "wb") as f:
                f.write(data)
        t0 = time.monotonic()
        try:
            for name in inputs:
                os.rename(os.path.join(stage, name), os.path.join(work, name))
        except OSError as e:
            raise EntryFailure(f"the prover made /work unusable (renaming the inputs into /work: {e.strerror or e})")
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
        r.mem_peak = sb.memory_peak()
        dead, t1, t1_ns = sb.kill_tree()
        if not dead:
            raise EntryFailure("the prover's sandbox did not die within 30 s of SIGKILL")
        r.seconds, r.kill_s, r.ended, r.t_stop_ns = t1 - t0, t1 - t_seen, w, t1_ns
        if w == "timeout":
            r.status = "timeout"
        elif w == "dead":
            code = sb.exit_code()
            if code is None:
                r.status = "the prover exited without `done` and its exit status was not reported"
            elif code != 0:
                r.status = f"exit {code}"
    except EntryFailure as e:
        r.status = str(e)
    except Exception as e:  # noqa: BLE001 (R-M1: the default is the entry's failure)
        r.status = f"the request failed while the prover's sandbox existed ({type(e).__name__}: {e})"
    finally:
        try:
            if r.status != "ok":
                r.status = oom_status(sb, run.mem) or r.status
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
            r.status = oom_status(sb, run.mem) or str(e)
        except Exception as e:  # noqa: BLE001 (R-M1: an unusable directory is the entry's failure)
            r.status = f"the prover made /work unusable (reading its outputs: {type(e).__name__}: {e})"
    return r


class EntryFailure(Exception):
    """A failure the prover caused (its reason is the step's status)."""


def make_accessible(path):
    """Give the runner read, write and search permission on every directory and file under `path`
    (no link followed), top down, so that a tree the prover locked can be measured and removed."""
    st = os.lstat(path)
    if stat.S_ISLNK(st.st_mode):
        return
    os.chmod(path, (st.st_mode & 0o7777) | (0o700 if stat.S_ISDIR(st.st_mode) else 0o600))
    if stat.S_ISDIR(st.st_mode):
        for n in os.listdir(path):
            make_accessible(os.path.join(path, n))


def tree_bytes(path, max_entries=1 << 20):
    """Bytes under `path`, each file counted at `max(size, allocated)` (a sparse file at its size;
    review M-2), no link followed, after making the tree accessible; a tree the runner cannot walk,
    or one of more than `max_entries` entries (which bounds the walk's time), counts as unbounded
    (the entry's failure where a cap applies)."""
    def fail(e):
        raise e
    total = entries = 0
    try:
        make_accessible(path)
        for root, dirs, files in os.walk(path, followlinks=False, onerror=fail):
            for n in dirs + files:
                entries += 1
                if entries > max_entries:
                    return float("inf")
                st = os.lstat(os.path.join(root, n))
                total += max(st.st_size, st.st_blocks * 512)
    except OSError:
        return float("inf")
    return total


def remove_tree(path):
    """Remove `path` and everything under it, after making it accessible; whether it is gone."""
    try:
        if os.path.lexists(path):
            make_accessible(path)
    except OSError:
        pass
    shutil.rmtree(path, ignore_errors=True)
    return not os.path.lexists(path)


def tree_sha256(path, max_bytes, timeout):
    """A hash of a directory tree (relative paths, kinds and contents; links by their target, none
    followed): the setup's hash in the result (§8). It reads at most `max_bytes` bytes and runs at
    most `timeout` seconds (review M-2); past either it returns None."""
    h, read, t_end = hashlib.sha256(), 0, time.monotonic() + timeout
    for root, dirs, files in sorted(os.walk(path, followlinks=False)):
        dirs.sort()
        for n in sorted(files):
            f = os.path.join(root, n)
            h.update(os.path.relpath(f, path).encode() + b"\0")
            if os.path.islink(f):
                h.update(b"L" + os.readlink(f).encode() + b"\0")
            elif os.path.isfile(f):
                try:
                    with open(f, "rb") as fh:
                        while c := fh.read(1 << 20):
                            h.update(c)
                            read += len(c)
                            if read > max_bytes or time.monotonic() > t_end:
                                return None
                except OSError:
                    h.update(b"unreadable\0")
    return h.hexdigest()


def fresh_dir(path):
    """An empty directory at `path` (whatever a prover left there is removed first)."""
    if os.path.lexists(path) and not remove_tree(path):
        raise OSError(f"cannot remove {path}")
    os.makedirs(path)
    return path
