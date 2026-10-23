"""Building and running the untrusted prover (TRUSTED RUNTIME; `harness/PROVER.md` is the
interface). Every step runs in `sandbox.Sandbox`.

* `build`: `gcc -static -O2 -pthread *.s -o prover -lm` inside the sandbox (V4-A6: `.incbin` and
  `.include` read only what the sandbox shows: the copied `.s` files and the toolchain), with the
  toolchain's versions and the binary's hash recorded.
* `setup`: `prover setup /setup`, untimed, before any instance or service exists; `/setup` is
  read-only afterwards.
* `run_tree`: `prover tree /work`, timed from the `exec` of the prover (the sandbox is set up,
  reported by bubblewrap and held first) to its exit as bubblewrap reports it (before the
  namespaces are torn down).
* `Request`: one `prover leaf /work` or `prover node /work` in a fresh process: the process starts
  and prints `ready`; the runner writes the inputs to a staging directory the prover cannot see;
  the clock starts; the runner renames the inputs into /work and sends `go`; the clock stops at
  the prover's `done` line or its exit, whichever is first; then the whole sandbox is killed and
  `proof.bin` is read.
"""
import glob
import hashlib
import os
import select
import shutil
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

    def setup(self, timeout):
        """`prover setup /setup` (untimed, no service, no instance); (ok, seconds, log)."""
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
        return code == 0, time.monotonic() - t0, out.kept.decode(errors="replace")

    def tree(self, work, sock_dir, timeout):
        """`prover tree /work`, timed from exec to exit; (status, seconds, log)."""
        sb = Sandbox([PROVER, "tree", "/work"], self.binds(work, sock_dir), self.mem, env=self.env(sock_dir),
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


def request(run, kind, work, sock_dir, inputs, step_s, file_cap):
    """One timed `leaf` or `node` request in a fresh sandbox. `inputs`: name → bytes, written after
    `ready`. Returns (status, seconds, proof bytes or None, log)."""
    sb = Sandbox([PROVER, kind, "/work"], run.binds(work, sock_dir), run.mem, env=run.env(sock_dir),
                 stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    err = Drain(sb.proc.stderr)
    fd = sb.proc.stdout.fileno()
    buf = b""

    def wait_line(word, deadline):
        """Read stdout until a line equal to `word`, end of file, or the deadline."""
        nonlocal buf
        while True:
            lines = buf.split(b"\n")
            if word.encode() in lines[:-1]:
                buf = b"\n".join(lines[lines.index(word.encode()) + 1:])
                return "line"
            if len(buf) > LOG_CAP:
                buf = buf[-64:]
            left = deadline - time.monotonic()
            if left <= 0:
                return "timeout"
            if select.select([fd], [], [], left)[0]:
                c = os.read(fd, 1 << 16)
                if not c:
                    return "eof"
                buf += c

    status, dt, proof = "ok", None, None
    try:
        if wait_line("ready", time.monotonic() + step_s) != "line":
            status = "no ready line"
        else:
            # RB-m11: the inputs are written to a staging directory outside the sandbox before the
            # clock starts, and only renamed into /work (constant time) once it runs
            stage = work.rstrip("/") + ".stage"
            os.makedirs(stage, exist_ok=True)
            for name, data in inputs.items():
                with open(os.path.join(stage, name), "wb") as f:
                    f.write(data)
            t0 = time.monotonic()
            for name in inputs:
                os.rename(os.path.join(stage, name), os.path.join(work, name))
            try:
                sb.proc.stdin.write(b"go\n")
                sb.proc.stdin.flush()
            except BrokenPipeError:
                pass
            r = wait_line("done", t0 + step_s)
            if r == "eof":                        # the prover closed stdout: wait for its exit
                try:
                    sb.proc.wait(timeout=max(0.0, t0 + step_s - time.monotonic()))
                except subprocess.TimeoutExpired:
                    r = "timeout"
            dt = time.monotonic() - t0
            if r == "timeout":
                status = "timeout"
    finally:
        if status != "ok" or sb.proc.poll() not in (None, 0):
            try:
                sb.proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                pass
            status = oom_status(sb, run.mem) or status
        sb.kill()
        err.join(5)
    if status == "ok":
        try:
            proof = read_output(work, "proof.bin", file_cap)
        except OutputError as e:
            status = oom_status(sb, run.mem) or str(e)
    return status, dt, proof, err.kept.decode(errors="replace")


def fresh_dir(path):
    if os.path.exists(path):
        shutil.rmtree(path)
    os.makedirs(path)
    return path
