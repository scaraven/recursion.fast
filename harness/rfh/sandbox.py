"""The sandbox for untrusted code (TRUSTED RUNTIME): every process of a prover, of its build and of
the badge executables (which run the entry's compiled verifier) runs under `bubblewrap` with

  * new user, pid, network, ipc, uts and cgroup namespaces, no further user namespaces
    (`--disable-userns`), all capabilities dropped, a new session, an empty environment;
  * a read-only root that is an empty tmpfs holding only what `binds` lists (for a prover: its binary
    read-only at /prover, its own directory read-write at /work, the setup directory read-only at
    /setup, the service's socket directory read-only at /run/rf), plus a fresh /dev, /proc of its
    own pid namespace, a tmpfs /tmp and the CPU topology (/sys/devices/system/cpu, read-only);
  * a seccomp filter that fails (EPERM) the system calls a prover never needs and that widen the
    kernel's attack surface or reach other processes (ptrace, process_vm_*, kcmp, pidfd_getfd, bpf,
    perf_event_open, userfaultfd, io_uring, keyrings, mounts, namespaces, module and kexec loading,
    handle-based opens), and kills a process that uses another syscall ABI;
  * a memory cap on the whole process tree: a transient systemd scope with `MemoryMax` and no swap
    (`systemd-run --user --scope`), or, where no user systemd manager is reachable, an address-space
    limit (`prlimit --as`), which is recorded as the weaker method;
  * `--die-with-parent` and a private pid namespace: when the sandbox's first process exits or the
    runner kills it, the kernel kills every process it started;
  * `oom_score_adj = 1000` (`choom`), so that under memory pressure the kernel kills the sandboxed
    process before the service (V4-A5); optionally a CPU affinity (`taskset`, the pinned core of a
    `V_i` measurement).

It needs no system user and changes no system setting. It needs unprivileged user namespaces for
bubblewrap (Ubuntu 24.04 restricts them through AppArmor; CI relaxes that, `.github/workflows/`).
"""
import json
import os
import struct
import subprocess
import threading
import time
import uuid

# x86-64 system call numbers failed with EPERM
DENY = {
    "ptrace": 101, "process_vm_readv": 310, "process_vm_writev": 311, "kcmp": 312, "pidfd_getfd": 438,
    "bpf": 321, "perf_event_open": 298, "userfaultfd": 323, "io_uring_setup": 425, "io_uring_enter": 426,
    "io_uring_register": 427, "keyctl": 250, "add_key": 248, "request_key": 249, "mount": 165, "umount2": 166,
    "pivot_root": 155, "mount_setattr": 442, "move_mount": 429, "open_tree": 428, "fsopen": 430,
    "fsconfig": 431, "fsmount": 432, "fspick": 433, "unshare": 272, "setns": 308, "init_module": 175,
    "finit_module": 313, "delete_module": 176, "kexec_load": 246, "kexec_file_load": 320,
    "open_by_handle_at": 304, "name_to_handle_at": 303, "fanotify_init": 300, "acct": 163, "swapon": 167,
    "swapoff": 168, "reboot": 169, "syslog": 103, "quotactl": 179, "iopl": 172, "ioperm": 173,
    "uselib": 134, "lookup_dcookie": 212, "vhangup": 153,
}


def seccomp_program() -> bytes:
    """The classic-BPF filter (`struct sock_filter[]`) for bubblewrap's `--seccomp FD`."""
    LD, JEQ, JGE, RET = 0x20, 0x15, 0x35, 0x06          # BPF_LD|W|ABS, BPF_JMP|JEQ|K, JGE, BPF_RET|K
    nrs = sorted(DENY.values())
    errno_at = 5 + len(nrs) + 1
    ins = [(LD, 0, 0, 4),                               # seccomp_data.arch
           (JEQ, 1, 0, 0xC000003E),                     # AUDIT_ARCH_X86_64
           (RET, 0, 0, 0x80000000),                     # SECCOMP_RET_KILL_PROCESS
           (LD, 0, 0, 0),                               # seccomp_data.nr
           (JGE, errno_at - 5, 0, 0x40000000)]          # the x32 ABI
    ins += [(JEQ, errno_at - (6 + k), 0, nr) for k, nr in enumerate(nrs)]
    ins += [(RET, 0, 0, 0x7FFF0000),                    # SECCOMP_RET_ALLOW
            (RET, 0, 0, 0x00050000 | 1)]                # SECCOMP_RET_ERRNO | EPERM
    return b"".join(struct.pack("<HBBI", *x) for x in ins)


_MEMCAP = None


def memcap_method() -> str:
    """`systemd` if a transient user scope with a memory cap can be created here, else `prlimit`."""
    global _MEMCAP
    if _MEMCAP is None:
        try:
            ok = subprocess.run(["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=64M", "true"],
                                capture_output=True, timeout=30).returncode == 0
        except (OSError, subprocess.TimeoutExpired):
            ok = False
        _MEMCAP = "systemd" if ok else "prlimit"
    return _MEMCAP


def parse_bytes(s: str) -> int:
    units = {"K": 1 << 10, "M": 1 << 20, "G": 1 << 30, "T": 1 << 40}
    s = str(s).strip()
    return int(float(s[:-1]) * units[s[-1].upper()]) if s[-1].upper() in units else int(s)


def memcap(mem: str, unit: str):
    """The command prefix that runs a command (and all it starts) under the memory cap `mem`."""
    if memcap_method() == "systemd":
        return ["systemd-run", "--user", "--scope", "--quiet", f"--unit={unit}", "-p", f"MemoryMax={mem}",
                "-p", "MemorySwapMax=0", "--"]
    return ["prlimit", f"--as={parse_bytes(mem)}", "--"]


def scope_oom(unit: str, wait: float = 2.0):
    """`(True, peak bytes)` if the scope `unit` was killed for memory (systemd keeps a failed scope
    with `Result=oom-kill`), else `(False, None)`; clears the failed unit. Always `(False, None)`
    without systemd (an address-space limit shows as an allocation failure instead)."""
    if memcap_method() != "systemd":
        return False, None
    deadline = time.monotonic() + wait
    while True:
        out = subprocess.run(["systemctl", "--user", "show", f"{unit}.scope", "-p", "Result", "-p", "MemoryPeak"],
                             capture_output=True, text=True, timeout=30).stdout
        kv = dict(l.split("=", 1) for l in out.splitlines() if "=" in l)
        if kv.get("Result") == "oom-kill" or time.monotonic() > deadline:
            break
        time.sleep(0.1)
    oom = kv.get("Result") == "oom-kill"
    if oom:
        subprocess.run(["systemctl", "--user", "reset-failed", f"{unit}.scope"], capture_output=True, timeout=30)
    peak = kv.get("MemoryPeak", "")
    return oom, int(peak) if peak.isdigit() else None


def scope_peak(unit: str):
    """The memory high-water mark of the live scope `unit` in bytes, else None (no systemd, or no
    such scope yet or any more)."""
    if memcap_method() != "systemd":
        return None
    out = subprocess.run(["systemctl", "--user", "show", f"{unit}.scope", "-p", "MemoryPeak"],
                         capture_output=True, text=True, timeout=30).stdout.strip()
    v = out.partition("=")[2]
    return int(v) if v.isdigit() else None


class PeakWatch:
    """Samples `scope_peak(unit)` once a second in a thread while a command runs; `stop()` returns
    the largest value seen. Systemd collects a scope that ends normally, so this is how the peak of
    a successful run is known; `MemoryPeak` is a high-water mark, so only the last second can be
    missed."""

    def __init__(self, unit: str, every: float = 1.0):
        self.unit, self.peak, self.done = unit, None, threading.Event()
        self.thread = threading.Thread(target=self._run, args=(every,), daemon=True)
        self.thread.start()

    def _run(self, every: float):
        while not self.done.wait(every):
            p = scope_peak(self.unit)
            if p is not None:
                self.peak = max(p, self.peak or 0)

    def stop(self):
        self.done.set()
        self.thread.join()
        return self.peak


def kill_unit(unit: str):
    """Kill every process left in the scope `unit` (no-op without systemd)."""
    if memcap_method() == "systemd":
        subprocess.run(["systemctl", "--user", "kill", "--signal=SIGKILL", f"{unit}.scope"],
                       capture_output=True, timeout=30)


class Sandbox:
    """One sandboxed command. `binds`: (kind, host path, sandbox path) with kind `ro`, `rw` or `dev`
    (a read-only bind that may be missing). `stdin`/`stdout`: `subprocess` arguments. With
    `hold=True` the command is held before `exec` until `release()` (bubblewrap's `--block-fd`);
    `wait_ready()` returns once the sandbox exists and `wait_exit()` when the command exits
    (`--json-status-fd`), so that a timer between them counts the measured program, not the
    sandbox's set-up or tear-down. With `status=True` (V4-A11, §5.1) bubblewrap reports the pid of
    the sandbox's first process (`child_pid`), the init of its pid namespace: `kill_tree()` kills
    every process of the sandbox and returns only when they are all dead (the namespace's init
    exits after the kernel has killed and reaped every other process in it, and its pidfd becomes
    readable then)."""

    def __init__(self, cmd, binds, mem, env=None, cwd="/work", stdin=subprocess.DEVNULL,
                 stdout=None, stderr=None, hold=False, extra_ro_root=(), cpus=None, status=False):
        self.unit = "rf-" + uuid.uuid4().hex[:16]
        sc_r, sc_w = os.pipe()
        prog = seccomp_program()
        os.write(sc_w, prog)
        os.close(sc_w)
        fds = [sc_r]
        args = ["bwrap", "--unshare-user", "--unshare-pid", "--unshare-net", "--unshare-ipc", "--unshare-uts",
                "--unshare-cgroup-try", "--disable-userns", "--die-with-parent", "--new-session", "--clearenv",
                "--cap-drop", "ALL", "--dev", "/dev", "--proc", "/proc", "--tmpfs", "/tmp",
                "--ro-bind-try", "/sys/devices/system/cpu", "/sys/devices/system/cpu"]
        for p in extra_ro_root:              # host directories visible at the same path (the build's /usr)
            if os.path.islink(p):
                args += ["--symlink", os.readlink(p), p]
            elif os.path.exists(p):
                args += ["--ro-bind", p, p]
        for kind, host, inside in binds:
            args += {"ro": ["--ro-bind"], "rw": ["--bind"], "dev": ["--ro-bind-try"]}[kind] + [host, inside]
        for k, v in (env or {}).items():
            args += ["--setenv", k, v]
        args += ["--remount-ro", "/", "--chdir", cwd, "--seccomp", str(sc_r)]
        self.block_w = self.info_r = None
        self.pidfd = self.cgdir = None
        self.status = b""
        if hold:
            b_r, self.block_w = os.pipe()
            fds.append(b_r)
            args += ["--block-fd", str(b_r)]
        if hold or status:
            self.info_r, i_w = os.pipe()
            fds.append(i_w)
            args += ["--json-status-fd", str(i_w)]
        prefix = memcap(mem, self.unit) + ["choom", "-n", "1000", "--"]
        if cpus is not None:
            prefix += ["taskset", "-c", str(cpus)]
        self.proc = subprocess.Popen(prefix + args + ["--"] + list(cmd), pass_fds=fds,
                                     stdin=stdin, stdout=stdout, stderr=stderr, close_fds=True)
        for fd in fds:
            os.close(fd)

    def _read_status(self, key, deadline):
        """Read bubblewrap's JSON status stream until an object holding `key`; the object's text, or
        None at end of stream or the deadline."""
        import select
        while True:
            for obj in self.status.split(b"}")[:-1]:
                if key in obj:
                    self.status = self.status[self.status.index(obj) + len(obj) + 1:]
                    return obj.decode(errors="replace")
            left = max(0.0, deadline - time.monotonic())
            if self.info_r is None or not select.select([self.info_r], [], [], left)[0]:
                return None
            c = os.read(self.info_r, 4096)
            if not c:
                return None
            self.status += c

    def wait_ready(self, timeout=120):
        """For a held command: wait until bubblewrap has created the sandbox (its first status
        object), so that a clock started now does not count the sandbox's set-up."""
        if self.info_r is not None:
            self._read_status(b"child-pid", time.monotonic() + timeout)

    def wait_exit(self, timeout):
        """For a held command: wait until the command exits (bubblewrap's `exit-code` status, written
        when the command exits, before the namespaces are torn down); (exit code or None on
        timeout, the monotonic time it was seen)."""
        obj = self._read_status(b"exit-code", time.monotonic() + timeout)
        t = time.monotonic()
        if obj is None:
            return None, t
        try:
            return int(obj.split(":")[-1].strip().rstrip(",")), t
        except ValueError:
            return -1, t

    def track(self, timeout=30):
        """For a `status` sandbox: open a pidfd on the namespace's init and find the scope's cgroup
        directory (systemd only); untimed, before a measurement starts. False if no pid came."""
        obj = self._read_status(b"child-pid", time.monotonic() + timeout)
        if obj is None:
            return False
        try:
            self.pidfd = os.pidfd_open(int(json.loads(obj + "}")["child-pid"]))
        except (ValueError, KeyError, OSError):
            return False
        if memcap_method() == "systemd":
            out = subprocess.run(["systemctl", "--user", "show", "-p", "ControlGroup", f"{self.unit}.scope"],
                                 capture_output=True, text=True, timeout=30).stdout.strip()
            d = "/sys/fs/cgroup" + out.partition("=")[2]
            if out.partition("=")[2] and os.access(os.path.join(d, "cgroup.kill"), os.W_OK):
                self.cgdir = d
        return True

    def exit_code(self, wait=1.0):
        """The command's exit code once bubblewrap reports it (within `wait` seconds), else None."""
        obj = self._read_status(b"exit-code", time.monotonic() + wait)
        try:
            return None if obj is None else int(json.loads(obj + "}")["exit-code"])
        except (ValueError, KeyError):
            return None

    def memory_peak(self):
        """The sandbox's memory high-water mark in bytes (its cgroup's `memory.peak`), else None."""
        try:
            return int(open(os.path.join(self.cgdir, "memory.peak")).read()) if self.cgdir else None
        except (OSError, ValueError):
            return None

    def kill_tree(self, timeout=30):
        """Kill every process of a tracked sandbox at once (`cgroup.kill`, else SIGKILL to the
        namespace's init, which takes the namespace with it) and wait until all are dead: (dead?,
        the monotonic time it was seen in seconds, the same in ns of `CLOCK_MONOTONIC`). Nothing in
        the sandbox runs after that time."""
        import select
        import signal
        try:
            if self.cgdir:
                with open(os.path.join(self.cgdir, "cgroup.kill"), "w") as f:
                    f.write("1")
            else:
                signal.pidfd_send_signal(self.pidfd, signal.SIGKILL)
        except OSError:
            pass                              # already gone: the pidfd says so below
        try:
            signal.pidfd_send_signal(self.pidfd, signal.SIGKILL)
        except OSError:
            pass
        dead = bool(select.select([self.pidfd], [], [], timeout)[0])
        ns = time.monotonic_ns()
        return dead, ns / 1e9, ns

    def dead(self):
        """Whether every process of a tracked sandbox has exited (its init's pidfd is readable)."""
        import select
        return self.pidfd is not None and bool(select.select([self.pidfd], [], [], 0)[0])

    def release(self):
        """Let a held command `exec`."""
        if self.block_w is not None:
            os.write(self.block_w, b"x")
            os.close(self.block_w)
            self.block_w = None

    def oom(self, wait=2.0):
        """`(killed for memory?, peak bytes)` of this sandbox's scope (after the command ended)."""
        return scope_oom(self.unit, wait)

    def kill(self):
        """Kill the sandbox and everything in it."""
        if self.block_w is not None:
            os.close(self.block_w)
            self.block_w = None
        if self.info_r is not None:
            os.close(self.info_r)
            self.info_r = None
        if self.pidfd is not None:
            if not self.dead():
                self.kill_tree()
            os.close(self.pidfd)
            self.pidfd = None
        if self.proc.poll() is None:
            self.proc.kill()
        kill_unit(self.unit)
        try:
            self.proc.wait(timeout=30)
        except subprocess.TimeoutExpired:
            pass
