"""The sandbox for untrusted code (TRUSTED RUNTIME): every process of a prover, of its build and of
the badge executables (which run the entry's compiled verifier) runs under `bubblewrap` with

  * new user, pid, network, ipc, uts and cgroup namespaces, no further user namespaces
    (`--disable-userns`), all capabilities dropped, a new session, an empty environment;
  * a read-only root that is an empty tmpfs holding only what `binds` lists (for a prover: its binary
    read-only at /prover, the setup directory read-only at /setup, the request's own socket
    directory read-only at /run/rf, and a request's own private tmpfs at /work, `prover.request`),
    plus a fresh /dev, /proc of its own pid namespace, a tmpfs /tmp and the CPU topology
    (/sys/devices/system/cpu, read-only);
  * **nothing of the host's disks, sysfs or /proc beyond the masked procfs in a request or a badge
    run**: every directory and file bound into them is on the runner's own tmpfs (`runner_dir`) or
    fresh per sandbox. A lookup of an absent name leaves a negative dentry in the host's dcache on a
    disk filesystem or sysfs, and a disk file's page-cache folios keep a shape (a PMD folio after a
    `MADV_HUGEPAGE` fault): both persist into a later sandbox that sees the same directory or file
    and can time the lookup or read `/proc/self/smaps` (review LR4 H1, H2). tmpfs keeps no negative
    dentry, and a file the runner wrote in full there is resident, order-0 and unchangeable through a
    read-only bind. So the prover binary and the setup are copied there once the setup is hashed
    (`prover.Run.publish`), the badge, its libraries and every checked file too (`checks.Badge`),
    the services' socket directories live there, the mask sources are there, and the CPU tree is a
    static copy there (`sys_cpu_view`). The build and setup sandboxes alone bind host
    directories (the toolchain, the build and setup directories), which no later sandbox sees;
  * **no machine-wide counter in /proc** (`proc_masks`): the host's /proc top level is listed when
    the sandbox is built (the set depends on the kernel), and an empty file is bound over every file
    and an empty directory over every directory of it but the pid directories, `self` and
    `thread-self` (`/proc/stat`, `vmstat`, `meminfo`, `loadavg`, `interrupts`, `softirqs`,
    `pressure`, `sys`, `cpuinfo`, … read empty). Symbolic links (`mounts`, `net`) cannot be bound
    over and stay: they lead into `self`. The CPU tree holds only its static description
    (`cpuidle`, `cpufreq` and `power` hold live counters and are absent). Counters a sandbox reads
    of its own (`/proc/self/autogroup`, `sched`, mount ids) remain; the filter stops a request from
    moving the autogroup counter (`setsid`), and the memory cap's cgroup (systemd) gives each
    sandbox its own scheduler entities;
  * a seccomp filter that fails (EPERM) the system calls a prover never needs and that widen the
    kernel's attack surface or reach other processes (ptrace, process_vm_*, kcmp, pidfd_getfd, bpf,
    perf_event_open, userfaultfd, io_uring, keyrings, mounts, namespaces, module and kexec loading,
    handle-based opens, quotas), fails `socket` and `socketpair` for every domain but `AF_UNIX` (the
    oracle's socket is the only one a prover needs; an `AF_INET` datagram would raise machine-wide
    counters, `/proc/self/net/softnet_stat`), fails the calls that read or write other machine-wide
    state a request could leave for a later one (`statfs`/`fstatfs`/`ustat`, ENOSYS: free space;
    pidfds: pidfs inode numbers; `SO_COOKIE`; `setsid`: the autogroup counter; `MADV_COLD`,
    `MADV_PAGEOUT`, `process_madvise`: reclaim of the runner's tmpfs pages; `seccomp_program`), and
    kills a process that uses another syscall ABI;
  * a memory cap on the whole process tree: a transient systemd scope with `MemoryMax` and no swap
    (`systemd-run --user --scope`), or, where no user systemd manager is reachable, an address-space
    limit (`prlimit --as`), which is recorded as the weaker method: every sandbox then shares the
    runner's cgroup and its per-CPU scheduler state (`/proc/self/sched`'s `se.vruntime` follows the
    group's run queues, review LR4 M2), so a scored benchmark under it is an organiser ERROR
    (`run-benchmark.py`; `RF_ALLOW_PRLIMIT=1` lets tests and local runs proceed, recorded);
  * `--die-with-parent` and a private pid namespace: when the sandbox's first process exits or the
    runner kills it, the kernel kills every process it started;
  * `oom_score_adj = 1000` (`choom`), so that under memory pressure the kernel kills the sandboxed
    process before the service; optionally a CPU affinity (`taskset`, the pinned core of a
    `V_i` measurement).

It needs no system user and changes no system setting. It needs unprivileged user namespaces for
bubblewrap (Ubuntu 24.04 restricts them through AppArmor; CI relaxes that, `.github/workflows/`).
"""
import json
import os
import re
import stat
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
    "uselib": 134, "lookup_dcookie": 212, "vhangup": 153, "open_tree_attr": 467, "quotactl_fd": 443,
    # the machine-wide channels a request could write and a later one read (`seccomp_program`):
    # pidfs inode numbers; the machine-wide autogroup counter (`/proc/self/autogroup`), which every
    # new session moves; another process's (or, by `PIDFD_SELF`, its own) page reclaim
    "pidfd_open": 434, "setsid": 112, "process_madvise": 440,
}
# x86-64 system call numbers failed with ENOSYS: free disk space (`seccomp_program`); glibc's
# `pathconf` falls back to its defaults on ENOSYS (on EPERM it fails); `clone3` (libc falls back to
# `clone`, where `CLONE_PIDFD` is refused)
ENOSYS = {"statfs": 137, "fstatfs": 138, "ustat": 136, "clone3": 435}


AF_UNIX = 1
SOCKET = {"socket": 41, "socketpair": 53}       # allowed only for the domain (first argument) AF_UNIX
CLONE, CLONE_PIDFD = 56, 0x1000                  # clone refused with CLONE_PIDFD
GETSOCKOPT, SETSOCKOPT = 55, 54
SO_COOKIE, SO_PEERPIDFD, SO_PASSPIDFD = 57, 77, 76
MADVISE, MADV_COLD, MADV_PAGEOUT = 28, 20, 21     # refused: they would reclaim the runner's tmpfs pages


def seccomp_program() -> bytes:
    """The classic-BPF filter (`struct sock_filter[]`) for bubblewrap's `--seccomp FD`. Besides the
    `DENY` list and the socket domains, it closes machine-wide counters a request could write and a
    later request read (AGENTS.md §5): `statfs`, `fstatfs` and `ustat` (ENOSYS: the free space of
    the filesystems behind the sandbox's binds, which the runner's writes move and a prover's
    outputs, logs and refusals move with them); every way to a pidfd, whose pidfs inode number
    counts every process and thread the machine has started (`pidfd_open`, `clone` with
    `CLONE_PIDFD`, `clone3`, which fails with ENOSYS so that libc falls back to `clone`,
    `SO_PEERPIDFD`, `SO_PASSPIDFD`); `SO_COOKIE`, a socket's cookie, drawn from a machine-wide
    counter; `setsid`, which moves the machine-wide autogroup counter that `/proc/self/autogroup`
    shows (the prover is a session leader already, bubblewrap's `--new-session`); and `madvise`
    with `MADV_COLD` or `MADV_PAGEOUT` and `process_madvise`, which could push pages of the
    runner's read-only tmpfs copies (`/setup`, `/prover`) out to swap, where one request could
    leave a pattern for a later one."""
    LD, JEQ, JGE, JSET, RET = 0x20, 0x15, 0x35, 0x45, 0x06   # BPF_LD|W|ABS, BPF_JMP|JEQ|K, JGE, JSET, BPF_RET|K
    ALLOW, ERRNO = 0x7FFF0000, 0x00050000                 # SECCOMP_RET_ALLOW, SECCOMP_RET_ERRNO
    ins = [(LD, 0, 0, 4),                               # seccomp_data.arch
           (JEQ, 1, 0, 0xC000003E),                     # AUDIT_ARCH_X86_64
           (RET, 0, 0, 0x80000000),                     # SECCOMP_RET_KILL_PROCESS
           (LD, 0, 0, 0),                               # seccomp_data.nr
           (JGE, "errno", 0, 0x40000000)]               # the x32 ABI
    ins += [(JEQ, "errno", 0, nr) for nr in sorted(DENY.values())]
    ins += [(JEQ, "enosys", 0, nr) for nr in sorted(ENOSYS.values())]
    ins += [(JEQ, "socket", 0, nr) for nr in sorted(SOCKET.values())]
    ins += [(JEQ, "clone", 0, CLONE), (JEQ, "getsockopt", 0, GETSOCKOPT), (JEQ, "setsockopt", 0, SETSOCKOPT),
            (JEQ, "madvise", 0, MADVISE)]
    # the arguments' low 32 bits (seccomp_data.args[i] at 16 + 8 i): the kernel reads the domain and
    # the option name as ints, and CLONE_PIDFD is a low bit of the flags
    ins += [(RET, 0, 0, ALLOW),
            "socket",
            (LD, 0, 0, 16),                             # args[0], the domain
            (JEQ, 0, "errno", AF_UNIX),
            (RET, 0, 0, ALLOW),
            "clone",
            (LD, 0, 0, 16),                             # args[0], the flags
            (JSET, "errno", 0, CLONE_PIDFD),
            (RET, 0, 0, ALLOW),
            "getsockopt",
            (LD, 0, 0, 32),                             # args[2], the option name (at any level)
            (JEQ, "errno", 0, SO_COOKIE),
            (JEQ, "errno", 0, SO_PEERPIDFD),
            (RET, 0, 0, ALLOW),
            "setsockopt",
            (LD, 0, 0, 32),
            (JEQ, "errno", 0, SO_PASSPIDFD),
            (RET, 0, 0, ALLOW),
            "madvise",
            (LD, 0, 0, 32),                             # args[2], the advice
            (JEQ, "errno", 0, MADV_COLD),
            (JEQ, "errno", 0, MADV_PAGEOUT),
            (RET, 0, 0, ALLOW),
            "enosys",
            (RET, 0, 0, ERRNO | 38),                    # ENOSYS
            "errno",
            (RET, 0, 0, ERRNO | 1)]                     # EPERM
    at, k = {}, 0
    for x in ins:
        if isinstance(x, str):
            at[x] = k
        else:
            k += 1
    code = [x for x in ins if not isinstance(x, str)]
    rel = lambda j, i: at[j] - (i + 1) if isinstance(j, str) else j   # noqa: E731 (a jump is relative)
    return b"".join(struct.pack("<HBBI", c, rel(jt, i), rel(jf, i), kk) for i, (c, jt, jf, kk) in enumerate(code))


PROC_ALLOW = ("self", "thread-self")              # and every pid directory
SYS_CPU = "/sys/devices/system/cpu"
SYS_CPU_ALLOW = ("online", "possible", "present", "offline", "kernel_max", "isolated", "nohz_full", "enabled",
                 "housekeeping", "smt", "vulnerabilities", "hotplug", "crash_hotplug", "modalias", "uevent")
SYS_CPU_N_ALLOW = ("topology", "cache", "online", "cpu_capacity", "hotplug", "crash_notes", "crash_notes_size",
                   "uevent")
SYS_CPU_NEVER = ("power",)                        # runtime counters, at any depth of an allowed directory


# ---- the runner's tmpfs ---------------------------------------------------------------------------
# Every file or directory a request or a badge run sees by a bind is on a tmpfs the runner owns (or
# is fresh per sandbox): a directory lookup of an absent name leaves a negative dentry in the host's
# dcache on a disk filesystem or sysfs, which a later sandbox that sees the same directory can time
# (review LR4 H1), and a disk file's page-cache folios keep a shape (a PMD folio after a
# MADV_HUGEPAGE fault, 64 KiB ones after a re-read) that a later sandbox can read in
# /proc/self/smaps (H2). tmpfs keeps no negative dentry (`always_delete_dentry`), and a file the
# runner wrote in full is resident, order-0 (`huge=never`) and unchangeable through a read-only bind:
# fadvise is a no-op, MADV_COLLAPSE fails without huge pages, no hole can be faulted in, and the
# calls that would swap a page out are refused (`seccomp_program`).

def remove_tree(path):
    """Remove `path` and everything under it, after giving the runner access to every directory
    (no link followed); whether it is gone."""
    import shutil

    def opened(p):
        try:
            st = os.lstat(p)
        except OSError:
            return
        if stat.S_ISDIR(st.st_mode):
            try:
                os.chmod(p, (st.st_mode & 0o7777) | 0o700)
                for n in os.listdir(p):
                    opened(os.path.join(p, n))
            except OSError:
                pass
    if os.path.lexists(path):
        opened(path)
    shutil.rmtree(path, ignore_errors=True)
    return not os.path.lexists(path)


def _unescape(x):
    """A path field of /proc/self/mountinfo (spaces, tabs, newlines and backslashes octal-escaped)."""
    return re.sub(r"\\([0-7]{3})", lambda m: chr(int(m.group(1), 8)), x)


def mount_of(path):
    """(mount point, mount options, filesystem type, super options) of the mount holding `path`."""
    real, best = os.path.realpath(path), None
    for line in open("/proc/self/mountinfo"):
        pre, _, post = line.partition(" - ")
        f, g = pre.split(), post.split()
        mp = _unescape(f[4])
        if (real == mp or real.startswith(mp.rstrip("/") + "/")) and (best is None or len(mp) >= len(best[0])):
            best = (mp, f[5].split(","), g[0], g[2].split(",") if len(g) > 2 else [])
    return best


def tmpfs_problem(path):
    """Why the directory `path` cannot hold the runner's copies, or None: it must be a writable
    tmpfs that allows `exec` (the prover binary and the badge run from it) and never makes huge
    pages (`huge=` absent or `never`, `shmem_enabled` not `force`), so that its files' folios are the
    order-0 ones the runner wrote."""
    if not os.path.isdir(path) or not os.access(path, os.W_OK | os.X_OK):
        return "not a writable directory"
    m = mount_of(path)
    if m is None or m[2] != "tmpfs":
        return f"not a tmpfs ({m[2] if m else 'no mount'})"
    if "noexec" in m[1]:
        return "mounted noexec"
    huge = [o for o in m[3] if o.startswith("huge=") and o != "huge=never"]
    if huge:
        return f"mounted {huge[0]}"
    try:
        if "[force]" in open("/sys/kernel/mm/transparent_hugepage/shmem_enabled").read():
            return "transparent_hugepage/shmem_enabled is force"
    except OSError:
        pass
    return None


_RUNNER_DIR = None


def _starttime(pid):
    try:
        return open(f"/proc/{pid}/stat").read().rpartition(")")[2].split()[19]
    except (OSError, IndexError):
        return None


def _reap(parent):
    """Remove the runner directories `rf-*` under `parent` whose owning process is gone (a runner
    killed before its exit handler ran): their copies would hold memory until the machine stops."""
    try:
        names = os.listdir(parent)
    except OSError:
        return
    for n in names:
        d = os.path.join(parent, n)
        if not re.fullmatch(r"rf-[0-9a-f]{16}", n) or os.path.islink(d):
            continue
        try:
            pid, start = open(os.path.join(d, "owner")).read().split()
        except (OSError, ValueError):
            continue
        if os.lstat(d).st_uid == os.getuid() and _starttime(pid) != start:
            remove_tree(d)


def runner_dir():
    """The runner's own directory on a tmpfs, made once per process: `rf-` and 16 random hex
    characters (mode 0700) under the first of `RF_RUNNER_TMPFS`, `/dev/shm` and `XDG_RUNTIME_DIR`
    that `tmpfs_problem` accepts, removed when the process exits; its memory is charged to the
    runner. None qualifying is the runner's failure (a RuntimeError)."""
    global _RUNNER_DIR
    if _RUNNER_DIR is None:
        import atexit
        import secrets
        why = []
        for c in (os.environ.get("RF_RUNNER_TMPFS"), "/dev/shm", os.environ.get("XDG_RUNTIME_DIR")):
            if not c:
                continue
            p = tmpfs_problem(c)
            if p:
                why.append(f"{c}: {p}")
                continue
            _reap(c)
            d = os.path.join(c, "rf-" + secrets.token_hex(8))
            os.mkdir(d, 0o700)
            with open(os.path.join(d, "owner"), "w") as f:
                f.write(f"{os.getpid()} {_starttime(os.getpid())}\n")
            atexit.register(remove_tree, d)
            _RUNNER_DIR = d
            break
        else:
            raise RuntimeError("no tmpfs for the runner's copies (" + "; ".join(why) + ")")
    return _RUNNER_DIR


def runner_path(name):
    """A fresh directory `name-<16 random hex>` (mode 0700) in the runner's tmpfs directory."""
    import secrets
    d = os.path.join(runner_dir(), f"{name}-{secrets.token_hex(8)}")
    os.mkdir(d, 0o700)
    return d


def copy_file(src, dst, mode=None):
    """Copy the regular file `src` (never through a link) to the new file `dst`, every byte written
    (a hole becomes zeros: on the tmpfs no page of it is left to fault in), then make it read-only:
    mode 0555 if `src` has an execute bit, else 0444, unless `mode`. Its bytes."""
    fd = os.open(src, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise OSError(f"{src} is not a regular file")
        out = os.open(dst, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
        n = 0
        try:
            buf = bytearray(1 << 20)
            while (k := os.readv(fd, [buf])) > 0:
                view = memoryview(buf)[:k]
                while view:
                    view = view[os.write(out, view):]
                n += k
        finally:
            os.close(out)
    finally:
        os.close(fd)
    os.chmod(dst, mode if mode is not None else (0o555 if st.st_mode & 0o111 else 0o444))
    return n


def copy_tree(src, dst):
    """Copy the directory tree `src` to the new directory `dst` on the runner's tmpfs: directories
    (mode 0700), regular files (`copy_file`: every byte, read-only) and symbolic links (as links);
    anything else (a FIFO, a socket, a device) is left out. No link is followed. Its bytes."""
    os.mkdir(dst, 0o700)
    total = 0
    def fail(e):
        raise e
    for root, dirs, files in os.walk(src, followlinks=False, onerror=fail):
        rel = os.path.relpath(root, src)
        out = dst if rel == "." else os.path.join(dst, rel)
        for n in dirs + files:
            s, d = os.path.join(root, n), os.path.join(out, n)
            st = os.lstat(s)
            if stat.S_ISLNK(st.st_mode):
                os.symlink(os.readlink(s), d)
            elif stat.S_ISDIR(st.st_mode):
                os.mkdir(d, 0o700)
            elif stat.S_ISREG(st.st_mode):
                total += copy_file(s, d)
        dirs[:] = [n for n in dirs if not os.path.islink(os.path.join(root, n))]
    return total


_MASK = None


def mask_sources():
    """(an empty read-only file, an empty read-only directory) on the runner's tmpfs, made once per
    process: what bubblewrap binds over a masked entry (a lookup in the directory leaves nothing)."""
    global _MASK
    if _MASK is None:
        d = runner_path("mask")
        f, e = os.path.join(d, "empty"), os.path.join(d, "dir")
        open(f, "wb").close()
        os.mkdir(e)
        os.chmod(f, 0o444)
        os.chmod(e, 0o555)
        _MASK = (f, e)
    return _MASK


def masks(root, keep):
    """bubblewrap arguments that bind the empty file over every file and the empty directory over
    every directory directly in the host directory `root`, as listed now, except the names `keep`
    accepts; symbolic links are left (a bind over a link would bind over its target)."""
    f, e = mask_sources()
    out = []
    for ent in sorted(os.scandir(root), key=lambda x: x.name):
        if keep(ent.name) or ent.is_symlink():
            continue
        try:
            is_dir = ent.is_dir(follow_symlinks=False)
        except OSError:
            is_dir = False
        out += ["--ro-bind", e if is_dir else f, os.path.join(root, ent.name)]
    return out


def proc_masks():
    """The masks over the top level of the sandbox's /proc: every entry but the pid directories,
    `self` and `thread-self`. The host's /proc is listed (the sandbox's is a fresh mount of the same
    kernel's procfs, whose entries are the same but the pids); a host /proc that does not list its
    machine-wide files (mounted with `subset=pid`) cannot be listed for them, and is refused."""
    if not os.path.isfile("/proc/stat"):
        raise RuntimeError("the host's /proc lists no /proc/stat (subset=pid?): its machine-wide entries "
                           "cannot be enumerated to mask them in the sandbox")
    return masks("/proc", lambda n: n.isdigit() or n in PROC_ALLOW)


_SYS_CPU_VIEW = None


def _copy_static(src, dst):
    """Copy the sysfs directory `src` to `dst`: its readable regular files' current contents and its
    subdirectories but `SYS_CPU_NEVER`; links and unreadable files are left out."""
    os.mkdir(dst, 0o700)
    for ent in sorted(os.scandir(src), key=lambda x: x.name):
        if ent.is_symlink() or ent.name in SYS_CPU_NEVER:
            continue
        if ent.is_dir(follow_symlinks=False):
            _copy_static(ent.path, os.path.join(dst, ent.name))
        else:
            _copy_sys_file(ent.path, os.path.join(dst, ent.name))
    os.chmod(dst, 0o555)


def _copy_sys_file(src, dst):
    try:
        data = open(src, "rb").read()
    except OSError:
        return
    with open(dst, "wb") as f:
        f.write(data)
    os.chmod(dst, 0o444)


def sys_cpu_view():
    """A static copy of the host's `/sys/devices/system/cpu` on the runner's tmpfs, made once per
    process, bound read-only at that path in every sandbox (None without it): only its static
    description (`SYS_CPU_ALLOW`, and in each `cpuN` `SYS_CPU_N_ALLOW`, recursively, without any
    `power` directory), each file's contents as read when the copy was made; `cpuidle`, `cpufreq`
    and `power` (live counters), links, and whatever a kernel adds are absent. So no sandbox sees
    the host's sysfs (whose lookups leave negative dentries, review LR4 H1)."""
    global _SYS_CPU_VIEW
    if _SYS_CPU_VIEW is None and os.path.isdir(SYS_CPU):
        root = os.path.join(runner_path("sys"), "cpu")
        os.mkdir(root, 0o700)

        def put(path, name, into):
            if os.path.islink(path):
                return
            if os.path.isdir(path):
                _copy_static(path, os.path.join(into, name))
            else:
                _copy_sys_file(path, os.path.join(into, name))
        for ent in sorted(os.scandir(SYS_CPU), key=lambda x: x.name):
            if ent.name in SYS_CPU_ALLOW:
                put(ent.path, ent.name, root)
            elif ent.name.startswith("cpu") and ent.name[3:].isdigit() and ent.is_dir(follow_symlinks=False):
                d = os.path.join(root, ent.name)
                os.mkdir(d, 0o700)
                for sub in sorted(os.scandir(ent.path), key=lambda x: x.name):
                    if sub.name in SYS_CPU_N_ALLOW:
                        put(sub.path, sub.name, d)
                os.chmod(d, 0o555)
        os.chmod(root, 0o555)
        _SYS_CPU_VIEW = root
    return _SYS_CPU_VIEW


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
    (a read-only bind that may be missing), `tmpfs` (a fresh tmpfs of the sandbox's own, no host
    path), `symlink` (a link to the target in place of the host path) or `file` (a regular
    file made in the sandbox, its bytes in place of the host path; after the tmpfs it lies on).
    `stdin`/`stdout`: `subprocess` arguments. With `hold=True` the command is held before `exec` until `release()` (bubblewrap's `--block-fd`);
    `wait_ready()` returns once the sandbox exists and `wait_exit()` when the command exits
    (`--json-status-fd`), so that a timer between them counts the measured program, not the
    sandbox's set-up or tear-down. With `status=True` bubblewrap reports the pid of
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
                "--cap-drop", "ALL", "--dev", "/dev", "--proc", "/proc", *proc_masks(), "--tmpfs", "/tmp"]
        if sys_cpu_view():
            args += ["--ro-bind", sys_cpu_view(), SYS_CPU]
        for p in extra_ro_root:              # host directories visible at the same path (the build's /usr)
            if os.path.islink(p):
                args += ["--symlink", os.readlink(p), p]
            elif os.path.exists(p):
                args += ["--ro-bind", p, p]
        for kind, host, inside in binds:
            if kind == "tmpfs":
                args += ["--tmpfs", inside]
            elif kind == "symlink":            # `host` is the link's target
                args += ["--symlink", host, inside]
            elif kind == "file":
                fd, data = os.memfd_create("rf-file"), memoryview(host)
                while data:
                    data = data[os.write(fd, data):]
                os.lseek(fd, 0, os.SEEK_SET)
                fds.append(fd)
                args += ["--file", str(fd), inside]
            else:
                args += {"ro": ["--ro-bind"], "rw": ["--bind"], "dev": ["--ro-bind-try"]}[kind] + [host, inside]
        for k, v in (env or {}).items():
            args += ["--setenv", k, v]
        args += ["--remount-ro", "/", "--chdir", cwd, "--seccomp", str(sc_r)]
        self.block_w = self.info_r = None
        self.pidfd = self.cgdir = self.child_pid = None
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
        """For a `status` sandbox: open a pidfd on the namespace's init (its host pid: `child_pid`)
        and find the scope's cgroup directory (systemd only); untimed, before a measurement starts.
        False if no pid came. The pidfd is opened after the pid is read, so the pid could in principle
        have been reaped and reused in between (it would take the machine's pids to wrap around):
        a live process behind the pidfd that does not descend from the outer bubblewrap (`proc.pid`,
        which `memcap`'s and `choom`'s wrappers exec into) is refused (False), and a dead one is harmless
        (`dead()` is then true and a kill reaches nobody)."""
        obj = self._read_status(b"child-pid", time.monotonic() + timeout)
        if obj is None:
            return False
        try:
            self.child_pid = int(json.loads(obj + "}")["child-pid"])
            self.pidfd = os.pidfd_open(self.child_pid)
            up, ppid = self.child_pid, None
            for _ in range(4):                    # the outer bubblewrap, at most a few wrappers up
                up = int(open(f"/proc/{up}/stat").read().rpartition(")")[2].split()[1])
                if up == self.proc.pid:
                    ppid = up
                    break
        except (ValueError, KeyError, OSError, IndexError):
            if self.pidfd is not None and not self.dead():
                os.close(self.pidfd)
                self.pidfd = None
                return False
            return self.pidfd is not None
        if ppid != self.proc.pid and not self.dead():     # alive after the read: the read was of it
            os.close(self.pidfd)
            self.pidfd = None
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
