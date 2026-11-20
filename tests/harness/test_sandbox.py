#!/usr/bin/env python3
"""Tests of the prover sandbox with a hostile prover (`hostile.c`).

  python3 tests/harness/test_sandbox.py [RF_ORACLE_BINARY]

1. the sandboxed build: a `.s` file that `.incbin`s a host file does not build; `hostile.c`'s
   assembly does;
2. `prover tree` of the hostile prover next to a live service: every escape attempt in its report
   failed (other processes, ptrace, process_vm_readv, bpf, perf_event_open, userfaultfd, io_uring,
   keyctl, new user namespaces, network, writes outside /work, host files, outer environment);
3. its planted outputs (a link to a host file, a FIFO, a link as a directory component) are refused
   by the runner's reader without reading through them;
4. no process it started survives the run, and the service still answers after its garbage;
5. the memory cap kills a prover above it and not one below it;
6. the handshake: a request whose prover never prints `ready` times out (`ready_s`), and one that
   prints `done` is stopped there;
7. the clock stops when the sandbox is dead (`harness/PROVER.md` §3): a prover
   that prints `done` and keeps writing `proof.bin` from a thread, or from a forked child, has none
   of its late bytes read; one that closes stdout without `done` and leaves a child computing is
   charged until every process is dead; no process survives any request;
8. a prover that makes /work unusable (an input's name taken by a directory, or /work made
   unreadable) is the entry's failure with that reason, never a harness error;
9. a badge `verify` that gives one answer and hangs is killed at the batch's timeout (the only
   bound on a check): `BadgeError` of kind `timeout`, and none of its processes survives;
10. the oracle socket exists only from `go` on: with `sock_at_go` (the benchmark's requests), a
    connect to `RF_ORACLE` before `ready` fails (no such file) and one after `go` reaches the service;
11. isolation (`isoprobe.c`), in a request, in `prover setup` and in a badge run: every top-level
    /proc entry but the pid directories, `self` and `thread-self` reads as empty (a file) or lists
    nothing (a directory), and /sys/devices/system/cpu holds only its static description (a copy on
    the runner's tmpfs); after `Run.publish` a request binds /prover and /setup from the runner's
    tmpfs; `socket`/`socketpair` fail with EPERM for every domain but AF_UNIX (UDP among them);
    `statfs`/`fstatfs`/`statvfs`/`ustat` (free disk space) fail with ENOSYS while `pathconf`
    answers; every way to a pidfd (pidfs inode numbers), `SO_COOKIE`, `setsid` in a child,
    `madvise` MADV_COLD and MADV_PAGEOUT, `process_madvise`, `quotactl_fd` and `open_tree_attr` are
    refused (EPERM), `clone3` is ENOSYS and `fork` and threads work; the `utime` family (by path and
    by fd, on /dev/null and on /tmp), the inotify calls and `madvise` MADV_COLLAPSE fail with EPERM
    and /dev/null's timestamps do not move, while the devices still read and write data; the mount
    table of a request, of `prover setup` and of a badge run holds no read-write mount of a
    superblock the host has mounted (which every other sandbox could bind), but the six device
    nodes, each a single node of the host's devtmpfs (the filter closes their timestamps; bubblewrap
    cannot bind them read-only); with a host directory bound read-write, the control, it does;
    `mlock` of N pages in one request raises the host's `unevictable_pgs_mlocked` by N and the next
    request sees none of it; a request's first inode number does not depend on how many files an
    earlier request made (with a shared tmpfs, the control, it does); with the runner's scrub
    (`harness/tools/scrub.c`) before every request, the per-CPU inode counters of pipes and memfds
    show a later request nothing of the K pipes and memfds an earlier one made on every CPU (without
    it, the control, each CPU's counter has moved by K);
12. what one request leaves for a later one, through the benchmark's binds (review LR4): negative
    dentries in every directory a request sees (`/setup`, `/prover`, the masked `/proc` entries,
    the CPU tree: the reader classifies one timed lookup per name at chance; a work-disk directory
    bound into both, the control, carries the bits), the folio shape of a setup file (evicted
    regions faulted back through MADV_HUGEPAGE, MADV_COLLAPSE and MADV_PAGEOUT refused: FilePmdMapped
    does not move; a disk file re-read by the runner, the control, shows the written regions), the
    autogroup counter (a request's setsid attempts fail and move it by about nothing; K setsids on
    the host move it by K), and the inodes staged before `go` through `Bench.one` (the same count at
    step 1 and step i, in the service run and a timed pass; without the placeholders, the control,
    2, 3, 4 and 5).

13. what one sandbox leaves for a later one in the shared memory policy of a tmpfs file (review LR5
    H1: `mbind` on a read-only MAP_SHARED mapping, read back with `get_mempolicy(MPOL_F_ADDR)`): with
    the filter, `mbind` fails with ENOSYS and a later request reads the default policy everywhere
    (`/setup`, `/prover`, a masked /proc entry, the CPU tree); with `mbind` allowed (the class
    test, the filter changed for it alone), a request of the same pass reads the bits back from
    the copy the steps of one pass share (the control), while a request after `Run.publish` (the
    next pass's copy), a later request through the mask file and the CPU tree (each sandbox's
    own), and a later badge run through /badge, its library tree and /store (each run's own) read
    nothing; no sandbox's or badge run's directory is left on the runner's tmpfs, and one copy of the
    setup at a time.

The requests of 6.-8. and 10.-13. run as the benchmark's do, /work a private tmpfs (`request` with
no host directory).
"""
import os
import shutil
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from rfh.files import OutputError, read_output  # noqa: E402
from rfh.prover import Run, build, remove_tree, request  # noqa: E402
from rfh.bench import build_scrub  # noqa: E402
from rfh.sandbox import memcap_method, mount_of, runner_dir, tmpfs_problem  # noqa: E402
from rfh.service import Client, Service  # noqa: E402

BIN = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "service", "target", "release", "rf-oracle")
FAILS = []


def check(cond, what):
    print(("ok   " if cond else "FAIL ") + what, flush=True)
    if not cond:
        FAILS.append(what)


def survivors(argv0):
    """Host pids whose command line starts with `argv0`."""
    out = []
    for pid in os.listdir("/proc"):
        if pid.isdigit():
            try:
                cmd = open(f"/proc/{pid}/cmdline", "rb").read().split(b"\0")
            except OSError:
                continue
            if cmd and cmd[0] == argv0.encode():
                out.append(int(pid))
    return out

REGIONS = 12                       # the folio probe's 2 MiB regions of /setup/big
GAP = r"""#define _GNU_SOURCE
#include <fcntl.h>
#include <poll.h>
#include <stdio.h>
#include <sys/stat.h>
#include <unistd.h>
static long mk(long n) {
    char p[64];
    struct stat st;
    snprintf(p, sizeof p, "/work/.g%ld", n);
    int fd = open(p, O_CREAT | O_WRONLY, 0600);
    long r = fd >= 0 && !fstat(fd, &st) ? (long)st.st_ino : -1;
    close(fd);
    unlink(p);
    return r;
}
int main(void) {
    long n = 0, first = mk(n++), last = first;
    puts("ready");
    fflush(stdout);
    struct pollfd pf = {0, POLLIN, 0};
    while (poll(&pf, 1, 0) <= 0) last = mk(n++);
    FILE *f = fopen("/work/proof.bin", "w");
    fprintf(f, "%ld", last - first + 1 - n);           /* the inodes made by others before `go` */
    fclose(f);
    puts("done");
    fflush(stdout);
    return 0;
}
"""


def kv(r, key):
    """The number after `key=` in a probe's report, or None."""
    import re
    m = re.search(rf"{key}=([0-9.]+)", (r.proof or b"").decode(errors="replace"))
    return float(m.group(1)) if m else None


def channels(tmp, svc, iso_run, iso_req):
    """12. A request writes, a later one reads, through the benchmark's binds: negative dentries in
    every directory a request sees (a lookup of an absent name; the reader times one lookup of each
    name), the page-cache folio shape of a setup file (MADV_HUGEPAGE faults after an eviction,
    MADV_COLLAPSE, MADV_PAGEOUT; the reader maps each region and reads FilePmdMapped), the autogroup
    counter (setsid), and the inode numbers a prover sees on /work before `go` (Bench.one's
    staging). Each must read nothing; the controls (a host directory and a host file on a disk
    filesystem, bound as the review's probes did; setsid on the host; the staging without the
    placeholders) show the channel where the host allows it."""
    import random
    N = 20000
    disk = os.path.join(ROOT, "harness")               # a host directory on the checkout's filesystem
    ctl_ok = mount_of(disk)[2] not in ("tmpfs", "ramfs")

    class Ctl(Run):
        def binds(self, work, sock_dir=None, setup_rw=False):
            return super().binds(work, sock_dir, setup_rw) + EXTRA
    EXTRA = []
    ctl = Ctl(iso_run.bin_dir, iso_run.setup_dir, iso_run.mem)
    ctl.view = iso_run.view
    shares = {}
    for d in ("/setup", "/prover", "/proc/sys", "/proc/sysvipc", "/sys/devices/system/cpu",
              "/sys/devices/system/cpu/cpu0/cache"):
        tag = random.getrandbits(24)
        w = iso_req(f"negw {d} {N} {tag}")
        r = iso_req(f"negr {d} {N} {tag}")
        shares[d] = kv(r, "share") if w.status == "ok" else None
    check(all(x is not None and abs(x - 0.5) < 0.04 for x in shares.values()),
          f"negative dentries: {N} lookups of absent names in one request leave nothing a later request can time, in "
          f"every directory it sees (the share of names classified right, 0.5 by chance): {shares}")
    if ctl_ok:
        EXTRA[:] = [("ro", disk, "/ctl")]
        tag = random.getrandbits(24)
        iso_req(f"negw /ctl {N} {tag}", ctl)
        x = kv(iso_req(f"negr /ctl {N} {tag}", ctl), "share")
        check(x is not None and x > 0.75, f"the control: a host directory on the work disk ({disk}) bound into both "
                                          f"requests carries the lookups (share {x})")
    else:
        print(f"note the negative-dentry control is skipped: {disk} is on a tmpfs")

    def pmd(r):
        line = next((l for l in (r.proof or b"").decode().splitlines() if l.startswith("pmd")), "pmd")
        return line.split()[1:]
    before = pmd(iso_req(f"pmd /setup/big {REGIONS}"))
    reads = []
    for bits in (0b100110010, 0b011001101):
        w = iso_req(f"fold /setup/big {REGIONS} {bits}")
        t = (w.proof or b"").decode()
        reads.append((pmd(iso_req(f"pmd /setup/big {REGIONS}")), "pageout -1(1)" in t and "collapse -1(1)" in t))
    check(len(before) == REGIONS and all(v == before and refused for v, refused in reads),
          f"folio shape: evicting chosen 2 MiB regions of a setup file and faulting them back through MADV_HUGEPAGE "
          f"(MADV_COLLAPSE and MADV_PAGEOUT refused) leaves the copy's folios as they were: FilePmdMapped "
          f"{before} before, {[v for v, _ in reads]} after two patterns")
    cand = [os.environ.get("RF_FOLIO_CONTROL")] + sorted(
        (os.path.join(d, n) for d in ("/usr/lib/x86_64-linux-gnu",) if os.path.isdir(d) for n in os.listdir(d)),
        key=lambda f: -os.path.getsize(f) if os.path.isfile(f) and not os.path.islink(f) else 0)[:3]
    big = next((f for f in cand if f and os.path.isfile(f) and os.path.getsize(f) >= REGIONS << 21
                and mount_of(f)[2] not in ("tmpfs", "ramfs")), None)
    if big:
        def warm(evict=False):                         # the runner's former re-read before every request
            fd = os.open(big, os.O_RDONLY)
            if evict:
                os.posix_fadvise(fd, 0, 0, os.POSIX_FADV_DONTNEED)
            while os.read(fd, 1 << 20):
                pass
            os.close(fd)
        EXTRA[:] = [("ro", big, "/ctl")]
        warm(True)
        bits = 0b100110010
        iso_req(f"fold /ctl {REGIONS} {bits}", ctl)
        warm()
        got = pmd(iso_req(f"pmd /ctl {REGIONS}", ctl))
        seen = [k for k, v in enumerate(got) if v not in ("0", "-1")]
        print(("ok   " if seen == [k for k in range(REGIONS) if bits >> k & 1] else "note ")
              + f"the folio control: a host file on disk ({big}), re-read in full by the runner after the writer, "
              f"shows the written regions as PMD folios: {got} (written {bin(bits)})")
    else:
        print("note the folio control is skipped: no large host file on a disk filesystem")

    def group(r):
        t = (r.proof or b"").decode()
        return int(t.split("autogroup-")[1].split()[0]) if "autogroup-" in t else None
    K = 3000
    a = group(iso_req("autogroup"))
    w = iso_req(f"setsid {K}")
    b = group(iso_req("autogroup"))
    for _ in range(K):                                 # the control: K new sessions on the host
        pid = os.fork()
        if pid == 0:
            os.setsid()
            os._exit(0)
        os.waitpid(pid, 0)
    c = group(iso_req("autogroup"))
    check(a is not None and b is not None and c is not None and b"setsid 0 of" in (w.proof or b"") and b - a < K // 2
          and c - b >= K,
          f"the autogroup counter: a request's {K} setsid attempts all fail and move /proc/self/autogroup by "
          f"{None if None in (a, b) else b - a} (< {K // 2}); the control, {K} sessions on the host, by "
          f"{None if None in (b, c) else c - b}")

    # the inodes staged before `go`, through the benchmark's own Bench.one and Bench.inputs
    from rfh.bench import Bench, Params
    gd = os.path.join(tmp, "gap")
    os.makedirs(os.path.join(gd, "bin"))
    open(os.path.join(gd, "gap.c"), "w").write(GAP)
    subprocess.run(["gcc", "-static", "-O1", "-o", os.path.join(gd, "bin", "prover"), os.path.join(gd, "gap.c")],
                   check=True)
    b = Bench.__new__(Bench)
    b.p = Params.load(os.path.join(ROOT, "harness", "smoke.toml"))
    b.work, b.service_bin, b.deadline, b.log, b.scrub_bin, b.phase = gd, BIN, None, (lambda m: None), None, "request"
    b.leafdata = os.path.join(gd, "leafdata")
    b.run = Run(os.path.join(gd, "bin"), os.path.join(gd, "setup"), "256M")
    os.makedirs(b.run.setup_dir)
    b.run.publish()
    gsvc = b.service("gap")
    try:
        from rfh import draws
        data = b.write_leaf_data(draws.starts(2))
        stmts = [os.urandom(32) for _ in range(2)]
        cases = [("service1", 1, None), ("timed1-step1", 1, "11" * 32), ("service2", 2, None), ("timed1-step2", 2, "11" * 32)]
        gaps, plain = [], []
        for tag, i, key in cases:
            kind, ins = b.inputs(i, data, stmts, b"p" * 1000 if i > 1 else None, key)
            gaps.append(int(b.one(gsvc, tag, kind, ins).proof or b"-1"))
            r = request(b.run, kind, None, svc.sock_dir, ins, 20, 1 << 20, ready_s=10)     # the control: no placeholders
            plain.append(int(r.proof or b"-1"))
        check(tmpfs_problem(gsvc.sock_dir) is None and len(set(gaps)) == 1 and gaps[0] >= 5 and len(set(plain)) == 4,
              f"the inodes staged before `go`: a prover counting /work's inode numbers sees the same gap in a "
              f"service-run and a timed request, at step 1 and at step i ({gaps}); without the placeholders, the "
              f"control, {plain}; the service's socket directory is on the runner's tmpfs")
    finally:
        gsvc.stop()


def policies(tmp, iso_run, iso_req, probe):
    """13. The shared memory policy of a tmpfs file (review LR5 H1), across requests of one pass,
    across passes, across sandboxes (the mask file, the CPU tree) and across badge runs."""
    import random
    import rfh.sandbox as sbx
    from rfh.checks import Badge, BadgeError
    from rfh.prover import tree_bytes
    files = [("/setup/big", REGIONS << 9), ("/prover/prover", 64), ("/proc/stat", 64),
             ("/sys/devices/system/cpu/online", 64)]

    def got(r, key):
        line = next((l for l in (r.proof or b"").decode(errors="replace").splitlines() if l.startswith(key)), "")
        return dict(w.split("=", 1) for w in line.split() if "=" in w)
    refused, read = {}, {}
    for f, n in files:
        tag = random.getrandbits(24)
        w = got(iso_req(f"polw {f} {n} {tag}"), "polw")
        r = got(iso_req(f"polr {f} {n} {tag}"), "polr")
        refused[f] = (w.get("set"), w.get("errno"))
        read[f] = (r.get("preferred"), r.get("share"))
    check(all(v == ("0", "38") for v in refused.values()) and all(p == "0" for p, _ in read.values()),
          f"mbind on a read-only MAP_SHARED mapping fails with ENOSYS in every file a request sees (set, errno: "
          f"{refused}); a later request reads the default policy everywhere (preferred, share right: {read})")
    saved = dict(sbx.ENOSYS)
    del sbx.ENOSYS["mbind"]                       # the class test: the copies' boundaries alone
    try:
        n = REGIONS << 9
        tag = random.getrandbits(24)
        w = got(iso_req(f"polw /setup/big {n} {tag}"), "polw")
        same = got(iso_req(f"polr /setup/big {n} {tag}"), "polr")
        old_root = iso_run.root
        nb, dt = iso_run.publish()                # the next pass's copy
        nxt = got(iso_req(f"polr /setup/big {n} {tag}"), "polr")
        check(int(w.get("set", 0)) > n // 3 and same.get("right") == str(n) and nxt.get("preferred") == "0"
              and not os.path.exists(old_root),
              f"with mbind allowed: {w.get('set')} policies set on /setup/big are read back by a request of the same "
              f"pass ({same.get('right')} of {n} right: the copy the steps of one pass share, the control) and by none "
              f"after Run.publish, the next pass's copy ({nxt.get('preferred')} preferred, share {nxt.get('share')}; "
              f"the previous copy removed; {nb} bytes in {dt:.3f} s)")
        per = {}
        for f in ("/proc/stat", "/sys/devices/system/cpu/online"):
            tag = random.getrandbits(24)
            w = got(iso_req(f"polw {f} 64 {tag}"), "polw")
            r = got(iso_req(f"polr {f} 64 {tag}"), "polr")
            per[f] = (w.get("set"), r.get("preferred"))
        check(all(int(a or 0) > 10 and b == "0" for a, b in per.values()),
              f"... through the mask file and the CPU tree (each sandbox's own): set, then read back preferred by a later "
              f"request: {per}")
        # badge runs: the probe as `verify`; a checked file that begins with `mode ` names what it does
        bdir, store = os.path.join(tmp, "pol-badge"), os.path.join(tmp, "pol-store")
        os.makedirs(bdir)
        os.makedirs(store)
        shutil.copy(probe, os.path.join(bdir, "verify"))
        badge = Badge(bdir, "256M", os.path.join(tmp, "hang-scratch"))
        tag = random.getrandbits(24)
        targets = ["/badge/verify", "/etc/ld.so.cache", "/store/w.bin"]
        targets = [t for t in targets if t != "/etc/ld.so.cache" or os.path.isfile(t)]
        open(os.path.join(store, "w.bin"), "w").write("mode " + ";".join(f"polw {t} 16 {tag}" for t in targets)
                                                       + f";polr /badge/verify 16 {tag}")
        for k, t in enumerate(targets):
            open(os.path.join(store, f"r{k}.bin"), "w").write(f"mode polr {t} 16 {tag}")
        try:
            badge.verify([(b"v" * 32, b"c" * 32, "w.bin")], store, timeout=30)
            inside = badge.last[0][1]
            # w.bin last (a run's /store holds its own items alone): its policies are read before it runs again
            badge.verify([(b"v" * 32, b"c" * 32, f"r{k}.bin") for k in range(len(targets))]
                         + [(b"v" * 32, b"c" * 32, "w.bin")], store, timeout=30)
            later = [own for _, own in badge.last][:len(targets)]
            why = ""
        except BadgeError as e:
            inside, later, why = None, None, str(e)[-300:]
        want = sum(1 for i in range(16) if bit(i, tag))
        check(inside == 16 and later is not None and all(abs(x - (16 - want)) == 0 for x in later),
              f"... a badge run's policies on {targets} are read back inside it ({inside} of 16 right) and by no later "
              f"badge run (each run's own copies: {later} right, the default policy's {16 - want}) {why}")
        c = badge.copies[-1]
        print(f"note one badge run's copies: {c[0]} bytes in {c[1] * 1e3:.1f} ms")
    finally:
        sbx.ENOSYS.clear()
        sbx.ENOSYS.update(saved)
    left = sorted(n for n in os.listdir(runner_dir()) if n.split("-")[0] in ("sb", "badge", "store"))
    check(not left and tree_bytes(iso_run.root) > 0 and len(iso_run.copies) == 2,
          f"no sandbox's or badge run's directory is left on the runner's tmpfs ({left}); the setup's copies were made "
          f"one at a time ({iso_run.copies})")


def bit(i, tag):
    """isoprobe.c's `bit`."""
    m = (1 << 64) - 1
    x = (i * 0x9E3779B97F4A7C15 & m) ^ tag
    x ^= x >> 29
    x = x * 0xBF58476D1CE4E5B9 & m
    x ^= x >> 32
    return x & 1


def main():
    tmp = tempfile.mkdtemp(prefix="rf-sandbox-test-", dir=os.environ.get("RF_TEST_TMP"))
    print(f"tests in {tmp}; memory cap method: {memcap_method()}")
    # 1. the build
    evil = os.path.join(tmp, "evil", "prover")
    os.makedirs(evil)
    with open(os.path.join(evil, "x.s"), "w") as f:
        f.write(f'.section .rodata\n.incbin "{os.path.abspath(__file__)}"\n.text\n.globl main\nmain: xor %eax,%eax\nret\n')
    ok, info = build(evil, os.path.join(tmp, "evil-build"), "2G", 300)
    check(not ok and "file not found" in info.get("log", ""),
          f"a .s that .incbins a host file does not build ({info.get('error')}: {info.get('log', '')[-120:]!r})")
    src = os.path.join(tmp, "hostile", "prover")
    os.makedirs(src)
    subprocess.run(["gcc", "-S", "-O1", "-o", os.path.join(src, "hostile.s"), os.path.join(HERE, "hostile.c")], check=True)
    ok, info = build(src, os.path.join(tmp, "hostile-build"), "2G", 300)
    check(ok, f"the hostile prover builds in the sandbox ({info.get('error')})")
    run = Run(os.path.join(tmp, "hostile-build", "bin"), os.path.join(tmp, "setup"), "1G")
    os.makedirs(run.setup_dir)

    # 2.-4. one run of the hostile program (no handshake)
    svc = Service(BIN, os.path.join(tmp, "svc")).start()
    work = os.path.join(tmp, "work")
    os.makedirs(work)
    os.environ["HOSTILE_ENV_LEAK"] = "1"
    status, dt, log = run.oneshot("tree", work, svc.sock_dir, 300)
    check(status == "ok", f"the hostile prover ran ({status}, {dt:.2f} s)")
    report = open(os.path.join(work, "report.txt")).read().splitlines()
    for line in report:
        check(" ok" in line and " LEAK" not in line, f"escape attempt refused: {line}")
    check(len(report) >= 25, f"{len(report)} escape attempts reported")
    for rel in ("root.bin", "proofs/L0.bin", "proofs/L1.bin", "proofs/sub/hostname", "report.txt/x"):
        try:
            read_output(work, rel, 1 << 20)
            check(False, f"planted output {rel} was read")
        except OutputError as e:
            check(True, f"planted output {rel} refused: {e}")
    check(read_output(work, "report.txt", 1 << 20).startswith(b"proc-visible"), "a regular output is read")
    time.sleep(0.5)
    left = survivors("/prover/prover")
    check(not left and os.path.exists(os.path.join(work, "orphan.pid")),
          f"the detached grandchild was started and killed with the sandbox (left: {left})")
    c = Client(svc.socket_path)
    check(len(c.query([b"still alive"])[0]) == 32, "the service answers after the prover's garbage")
    c.close()

    # 6.-8. the handshake, the clock, an unusable /work
    def req(prog_s, kind="step", step=5, inputs=None, work_cap=None):
        d = os.path.join(tmp, f"req-{kind}-{time.monotonic_ns()}")
        os.makedirs(os.path.join(d, "bin"))
        os.makedirs(os.path.join(d, "work"))
        with open(os.path.join(d, "p.c"), "w") as f:
            f.write("#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n#include <unistd.h>\n"
                    "#include <pthread.h>\n#include <sys/stat.h>\n#include <fcntl.h>\n#include <time.h>\n" + prog_s)
        subprocess.run(["gcc", "-static", "-O1", "-pthread", "-w", "-o", os.path.join(d, "bin", "prover"), os.path.join(d, "p.c")],
                       check=True)
        r = Run(os.path.join(d, "bin"), run.setup_dir, "256M")
        return request(r, kind, None, svc.sock_dir, inputs or {"chain.json": b"{}"}, step, 1 << 20,
                       ready_s=2, work_cap=work_cap)
    HS = 'static void hs(void){puts("ready");fflush(stdout);char b[8];if(!fgets(b,8,stdin))exit(9);}\n'
    r = req('int main(){sleep(100);}\n')
    check(r.status == "no ready line" and r.startup_s < 3, f"no ready line within ready_s: {r.status} ({r.startup_s:.2f} s)")
    r = req(HS + 'int main(){hs();FILE*f=fopen("proof.bin","w");fputs("P",f);fclose(f);'
            'puts("done");fflush(stdout);sleep(100);}\n')
    check(r.status == "ok" and r.proof == b"P" and r.seconds < 1 and r.kill_s is not None and r.kill_s < 1,
          f"the done line stops the clock once the sandbox is dead ({r.status}, P {r.seconds:.4f} s, kill {r.kill_s:.4f} s, {r.proof!r})")
    r = req(HS + 'int main(){hs();sleep(100);}\n', step=2)
    check(r.status == "timeout", f"a request over step_s times out ({r.status})")
    # the late writer stamps CLOCK_MONOTONIC (the runner's clock) into proof.bin every
    # millisecond, before and after `done`; with the clock stopped at the death of the sandbox every
    # stamp is at or before that time, whereas a clock stopped at `done` with the kill after it
    # would let the stamps written between `done` and the kill be later
    late = (HS + 'static void*w(void*a){int fd=*(int*)a;struct timespec t;for(;;){clock_gettime(CLOCK_MONOTONIC,&t);'
            'long long ns=t.tv_sec*1000000000LL+t.tv_nsec;write(fd,&ns,8);usleep(1000);}return 0;}\n'
            'int main(){hs();static int fd;fd=open("proof.bin",O_WRONLY|O_CREAT|O_TRUNC,0644);'
            'pthread_t t;pthread_create(&t,0,w,&fd);usleep(20000);puts("done");fflush(stdout);'
            'for(volatile long i=0;;i++);}\n')
    r = req(late)
    stamps = [int.from_bytes(r.proof[k:k + 8], "little") for k in range(0, len(r.proof or b"") - 7, 8)]
    check(r.status == "ok" and stamps and max(stamps) <= r.t_stop_ns,
          f"a thread writing proof.bin after done: every byte that exists was written before the clock stopped "
          f"({len(stamps)} stamps, the last {(r.t_stop_ns - max(stamps or [0])) / 1e6:.3f} ms before the stop; "
          f"P {r.seconds:.4f} s)")
    n0 = len(r.proof or b"")
    time.sleep(0.3)
    check(not survivors("/prover/prover"), f"the late writer is dead when the request returns (proof had {n0} bytes)")
    forked = (HS + 'int main(){hs();if(fork()==0){usleep(300000);FILE*f=fopen("proof.bin","w");fputs("LATE",f);fclose(f);'
              'for(;;)pause();}puts("done");fflush(stdout);for(;;)pause();}\n')
    r = req(forked)
    check(r.status != "ok" and "missing" in r.status, f"a forked child's proof.bin after done does not count: {r.status}")
    bg = (HS + 'int main(){hs();if(fork()==0){usleep(500000);FILE*f=fopen("proof.bin","w");fputs("C",f);fclose(f);_exit(0);}'
          'fclose(stdout);usleep(1000000);_exit(0);}\n')
    r = req(bg)
    check(r.status == "ok" and r.proof == b"C" and r.seconds >= 1.0,
          f"stdout closed without done, the work left to a child: charged until every process is dead "
          f"({r.status}, P {r.seconds:.3f} s, {r.proof!r})")
    r = req(bg.replace("usleep(1000000);_exit(0);", "_exit(0);"))
    check(r.status != "ok" and r.seconds < 0.5,
          f"the main process exits and leaves a child to finish: the child dies with the sandbox, its late bytes "
          f"never exist ({r.status}, P {r.seconds:.3f} s)")
    check(not survivors("/prover/prover"), "no request process survives")
    r = req(HS.replace('puts("ready")', 'mkdir("chain.json",0755);puts("ready")') + 'int main(){hs();sleep(100);}\n')
    check("made /work unusable" in r.status, f"an input's name taken by a directory is the entry's failure: {r.status}")
    r = req(HS + 'int main(){hs();FILE*f=fopen("proof.bin","w");fputs("P",f);fclose(f);chmod(".",0);'
            'puts("done");fflush(stdout);sleep(100);}\n')
    check("made /work unusable" in r.status or "cannot open" in r.status or "Permission" in r.status,
          f"/work made unreadable is the entry's failure: {r.status}")
    r = req(HS + 'int main(){hs();FILE*f=fopen("proof.bin","w");fputs("P",f);fclose(f);int g=open("big",O_WRONLY|O_CREAT,0644);'
            'ftruncate(g,1LL<<40);close(g);puts("done");fflush(stdout);sleep(100);}\n', work_cap=1 << 30)
    check(r.status != "ok" and "work_cap" in r.status,
          f"a 1 TiB sparse file in /work counts at its size, above work_cap: {r.status}")
    r = req(HS + 'int main(){hs();FILE*f=fopen("proof.bin","w");fputs("P",f);fclose(f);mkdir("d",0700);'
            'FILE*h=fopen("d/x","w");fputs("x",h);fclose(h);chmod("d",0);puts("done");fflush(stdout);sleep(100);}\n',
            work_cap=1 << 30)
    check(r.status == "ok" and r.work_bytes is not None and r.work_bytes < 1 << 20,
          f"a mode-000 subdirectory is made accessible and measured ({r.status}, {r.work_bytes} bytes)")
    r = req('int main(){_exit(0);}\n')
    check(r.status.startswith("no ready line") or "ended before" in r.status,
          f"a prover that exits at once is the entry's failure, never a harness error: {r.status}")
    from rfh.prover import tree_bytes
    t = os.path.join(tmp, "locked")
    os.makedirs(os.path.join(t, "a", "b"))
    open(os.path.join(t, "a", "b", "f"), "w").write("x")
    with open(os.path.join(t, "sparse"), "wb") as f:
        f.truncate(1 << 40)
    os.chmod(os.path.join(t, "a", "b"), 0)
    os.chmod(os.path.join(t, "a"), 0)
    nb = tree_bytes(t)
    check(nb >= 1 << 40, f"tree_bytes counts a sparse file at its size, through mode-000 directories: {nb}")
    check(remove_tree(t), "a locked tree is removed (made accessible first)")

    # 10. the socket only from `go` on: connect before `ready` and after `go`, and report errno, in proof.bin
    conn = ('#include <errno.h>\n#include <sys/socket.h>\n#include <sys/un.h>\n'
            'static int try(void){struct sockaddr_un a={.sun_family=AF_UNIX};strcpy(a.sun_path,getenv("RF_ORACLE"));'
            'int s=socket(AF_UNIX,SOCK_STREAM,0);int r=connect(s,(struct sockaddr*)&a,sizeof a);int e=r?errno:0;close(s);return e;}\n')
    prog = conn + HS + ('int main(){int pre=try();hs();int post=try();char b[64];sprintf(b,"pre=%d post=%d",pre,post);'
                        'FILE*f=fopen("proof.bin","w");fputs(b,f);fclose(f);puts("done");fflush(stdout);return 0;}\n')
    d = os.path.join(tmp, "sock-at-go")
    os.makedirs(os.path.join(d, "bin"))
    with open(os.path.join(d, "p.c"), "w") as f:
        f.write("#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n#include <unistd.h>\n" + prog)
    subprocess.run(["gcc", "-static", "-O1", "-w", "-o", os.path.join(d, "bin", "prover"), os.path.join(d, "p.c")], check=True)
    link_dir = os.path.join(os.path.dirname(svc.sock_dir), "req-sock")      # the socket's filesystem
    os.makedirs(link_dir)
    import errno
    for at_go in (True, False):
        r = request(Run(os.path.join(d, "bin"), run.setup_dir, "256M"), "step", None,
                    link_dir if at_go else svc.sock_dir, {"leaf.json": b"{}"}, 5, 1 << 20, ready_s=2,
                    sock_at_go=svc.socket_path if at_go else None)
        want = f"pre={errno.ENOENT} post=0".encode() if at_go else b"pre=0 post=0"
        check(r.status == "ok" and r.proof == want,
              f"{'with' if at_go else 'without'} sock_at_go, connect before ready / after go: {r.status} {r.proof!r}")

    # 11. isolation: the probe as a request, as `prover setup` and (below) as a badge
    iso = os.path.join(tmp, "iso")
    os.makedirs(os.path.join(iso, "bin"))
    probe = os.path.join(iso, "bin", "prover")
    subprocess.run(["gcc", "-static", "-O1", "-o", probe, os.path.join(HERE, "isoprobe.c")], check=True)
    iso_run = Run(os.path.join(iso, "bin"), os.path.join(iso, "setup"), "256M")
    os.makedirs(iso_run.setup_dir)
    ok, _, slog = iso_run.setup(60)
    rp = os.path.join(iso_run.setup_dir, "report.txt")
    setup_report = (ok, open(rp).read() if os.path.exists(rp) else slog)
    with open(os.path.join(iso_run.setup_dir, "big"), "wb") as f:     # 12 regions of 2 MiB (12.)
        f.write(os.urandom(REGIONS << 21))
    nbytes, _ = iso_run.publish()          # the benchmark's binds: /prover and /setup from the runner's tmpfs
    check(nbytes >= REGIONS << 21 and all(tmpfs_problem(v) is None for v in iso_run.view)
          and all(b[1].startswith(runner_dir()) for b in iso_run.binds(None)[:2]),
          f"after publish, a request binds /prover and /setup from copies on the runner's tmpfs ({iso_run.view[1]})")

    def iso_req(mode, r=None):
        return request(r or iso_run, "step", None, svc.sock_dir, {"mode": mode.encode()}, 30, 1 << 20, ready_s=5,
                       preset={"vk.hex": b"00" * 32 + b"\n"})

    def report(what, text):
        lines = text.splitlines()
        bad = [l for l in lines if l.startswith("FAIL")]
        check(lines and lines[-1] == "checks passed" and not bad,
              f"{what}: masks, the socket rule and the counters' refusals hold ({'; '.join(l for l in lines if l.startswith('/'))}; "
              f"links left in /proc: {[l[5:] for l in lines if l.startswith('link /proc/')]}; {bad[:5]})")
    r = iso_req("probe")
    report(f"a request ({r.status})", (r.proof or b"").decode(errors="replace"))
    report(f"prover setup (ok={setup_report[0]})", setup_report[1])

    # the mount table: no read-write mount of a superblock the host has mounted (every other
    # sandbox could bind it), the device nodes aside (the probe checks they are single nodes)
    host = sorted({l.split()[2] for l in open("/proc/self/mountinfo")})
    listed = ",".join(host)

    def rw_lines(text):
        return [l.split() for l in text.splitlines() if l.startswith("rw ") and len(l.split()) == 4]
    r = iso_req(f"rw {listed}")
    req_rw = rw_lines((r.proof or b"").decode(errors="replace"))
    set_rw = rw_lines(setup_report[1])
    check(r.status == "ok" and b"rwshared=0" in (r.proof or b"") and {m[3] for m in req_rw} >= {"/work", "/tmp", "/dev"}
          and not any(m[1] in host for m in req_rw + set_rw) and {m[3] for m in set_rw} >= {"/setup", "/tmp"},
          f"the mount table: every read-write mount of a request and of prover setup is a superblock of its own, none "
          f"the host has mounted (request: {[(m[1], m[2], m[3]) for m in req_rw]}; setup: "
          f"{[(m[1], m[2], m[3]) for m in set_rw]}; the host's: {len(host)} superblocks)")

    class RwCtl(Run):
        def binds(self, work, sock_dir=None, setup_rw=False):
            return super().binds(work, sock_dir, setup_rw) + [("rw", ctl_dir, "/ctl")]
    ctl_dir = os.path.join(tmp, "rw-ctl")
    os.makedirs(ctl_dir)
    rc = RwCtl(iso_run.bin_dir, iso_run.setup_dir, iso_run.mem)
    rc.view = iso_run.view
    r = iso_req(f"rw {listed}", rc)
    check(b"rwshared=1" in (r.proof or b"") and b"FAIL rw" in (r.proof or b""),
          f"the control: a host directory bound read-write is a read-write mount of a superblock the host has "
          f"mounted, and the probe fails on it ({[l for l in (r.proof or b'').decode().splitlines() if 'ctl' in l]})")

    def vmstat(key="unevictable_pgs_mlocked"):
        for line in open("/proc/vmstat"):
            k, _, v = line.partition(" ")
            if k == key:
                return int(v)
        return None
    N = 1024
    m0 = vmstat()
    r = iso_req(f"mlock {N}")
    m1 = vmstat()
    nxt = iso_req("probe")
    text = (nxt.proof or b"").decode(errors="replace")
    check(r.status == "ok" and b"mlocked" in (r.proof or b"") and m0 is not None and m1 - m0 >= N
          and text.endswith("checks passed\n"),
          f"mlock of {N} pages in one request raises the host's unevictable_pgs_mlocked by {m1 - m0 if m0 else '?'}; "
          f"the next request reads every machine-wide /proc entry empty ({r.status}, {(r.proof or b'')[:40]!r})")

    def ino_of(r):
        kv = dict(w.split("=") for w in (r.proof or b"").decode().split())
        return int(kv.get("ino", -1))
    K = 3000
    a, many, b = iso_req("ino 0"), iso_req(f"ino {K}"), iso_req("ino 0")
    check(all(x.status == "ok" for x in (a, many, b)) and ino_of(a) == ino_of(b) == ino_of(many) and ino_of(a) > 0,
          f"a request's first inode number does not depend on an earlier request's {K} files (/work's free counts "
          f"are unreadable, statvfs refused): {ino_of(a)}, after {K} files {ino_of(b)}")
    shm = "/dev/shm"                     # the control: two requests on one shared tmpfs
    if os.path.isdir(shm) and os.access(shm, os.W_OK):
        ctl = tempfile.mkdtemp(prefix="rf-ino-ctl-", dir=shm)
        seen = []
        for k in (K, 0):
            w = os.path.join(ctl, f"w{k}")
            os.makedirs(w)
            iso_run.oneshot(f"ino{k}", w, None, 30)
            seen.append(int(open(os.path.join(w, "ino.txt")).read().split()[0].split("=")[1]))
        check(seen[1] - seen[0] > K, f"the control: on a shared tmpfs the next request's first inode number moves "
                                     f"by the earlier one's {K} files ({seen[0]} then {seen[1]})")
        remove_tree(ctl)

    # the per-CPU inode counters (pipes, sockets, pseudo files; memfds): a request makes K of each on
    # every CPU; the next request reads each CPU's next numbers. Without the scrub (the control) each
    # CPU's counter has moved by about K; with it, by a uniform random amount
    scrub_bin, _ = build_scrub(os.path.join(tmp, "tools"))

    def per_cpu(r):
        out = {}
        for line in (r.proof or b"").decode().splitlines():
            kv = dict(w.split("=") for w in line.split())
            out[int(kv["cpu"])] = (int(kv["pipe"]), int(kv["memfd"]))
        return out
    KP = 300

    def moved(scrub):
        """Per counter, the share of CPUs whose next number moved by K to K + 64 (mod 1024) across a
        request that made K pipes and memfds on every CPU."""
        rs = []
        for mode in ("inos", f"pipes {KP}", "inos"):
            if scrub:
                subprocess.run([scrub_bin], check=True, capture_output=True, timeout=60)
            rs.append(iso_req(mode))
        x, y = per_cpu(rs[0]), per_cpu(rs[2])
        cpus = sorted(set(x) & set(y))
        share = [sum(KP <= (y[c][k] - x[c][k]) % 1024 <= KP + 64 for c in cpus) / max(1, len(cpus)) for k in (0, 1)]
        return all(r.status == "ok" for r in rs) and len(cpus) > 0, share, len(cpus)
    ok0, ctl_share, n0 = moved(False)
    ok1, scr_share, n1 = moved(True)
    # the scrub's offsets are random, not only past the batch's end: after it, the CPUs' next pipe
    # numbers (mod 1024) spread over the batch
    subprocess.run([scrub_bin], check=True, capture_output=True, timeout=60)
    offs = sorted(p % 1024 for p, _ in per_cpu(iso_req("inos")).values())
    spread = len(offs) < 4 or offs[-1] - offs[0] > 256
    # with few CPUs a hit by chance is likely: the bound only binds from 8 CPUs on
    check(ok0 and ok1 and min(ctl_share) >= 0.5 and (n1 < 8 or max(scr_share) <= 0.25) and spread,
          f"with the runner's scrub before every request, an earlier request's {KP} pipes and memfds per CPU do not show "
          f"in a later one's inode numbers: CPUs whose pipe / memfd counter moved by {KP}–{KP + 64} mod 1024: "
          f"{[round(x, 2) for x in scr_share]} of {n1} (uniform: 0.06), offsets after a scrub spread over "
          f"{offs[0] if offs else '?'}–{offs[-1] if offs else '?'}; without the scrub, the control: "
          f"{[round(x, 2) for x in ctl_share]} of {n0}")

    # 12. what one request leaves for a later one through the real binds (review LR4)
    channels(tmp, svc, iso_run, iso_req)
    # 13. the shared memory policy of a tmpfs file, and the copies' boundaries (review LR5)
    policies(tmp, iso_run, iso_req, probe)
    svc.stop()

    # 5. the memory cap
    mem_run = Run(run.bin_dir, run.setup_dir, "64M")
    for mib, want in ((16, True), (200, False)):
        sb_work = os.path.join(tmp, f"mem{mib}")
        os.makedirs(sb_work)
        from rfh.sandbox import Sandbox
        sb = Sandbox(["/prover/prover", "mem", str(mib)], mem_run.binds(sb_work), mem_run.mem, env={}, stdout=subprocess.PIPE)
        out, _ = sb.proc.communicate(timeout=120)
        sb.kill()
        check((sb.proc.returncode == 0) == want, f"memory cap 64M, touching {mib} MiB: exit {sb.proc.returncode}")

    # 9. a hanging check, through the runner's own badge runner
    from rfh.checks import Badge, BadgeError
    bdir, store = os.path.join(tmp, "hang-badge"), os.path.join(tmp, "hang-store")
    os.makedirs(bdir)
    os.makedirs(store)
    open(os.path.join(store, "p.bin"), "wb").write(b"x")
    with open(os.path.join(bdir, "verify"), "w") as f:
        f.write("#!/bin/sh\nread r\necho accept 1\nread r\nexec /bin/sleep 9871\n")   # answers the first request
    os.chmod(os.path.join(bdir, "verify"), 0o755)
    badge = Badge(bdir, "256M", os.path.join(tmp, "hang-scratch"), tools=("/bin/sleep",))
    os.makedirs(badge.scratch)
    t0, kind = time.monotonic(), None
    try:
        badge.verify([(b"v" * 32, b"c" * 32, "p.bin")] * 2, store, timeout=2)
    except BadgeError as e:
        kind = e.kind
    dt = time.monotonic() - t0
    time.sleep(0.5)
    left = []
    for pid in survivors("/bin/sleep"):
        try:
            if b"9871" in open(f"/proc/{pid}/cmdline", "rb").read():
                left.append(pid)
        except OSError:
            pass
    check(kind == "timeout" and dt < 15 and not left,
          f"a hanging badge check is killed at its timeout: {kind} after {dt:.1f} s, survivors {left}")

    # 11. isolation in a badge run: the probe as `verify`, accepting only if every check passed
    pdir = os.path.join(tmp, "iso-badge")
    os.makedirs(pdir)
    shutil.copy(probe, os.path.join(pdir, "verify"))
    try:
        res = Badge(pdir, "256M", os.path.join(tmp, "hang-scratch")).verify([(b"v" * 32, b"c" * 32, "p.bin")], store,
                                                                            timeout=30)
        why = res
    except BadgeError as e:
        res, why = None, str(e)[-400:]
    check(res is not None and res[0][0], f"a badge run: masks, the socket rule and the counters' refusals hold ({why})")
    open(os.path.join(store, "rw.bin"), "w").write(f"mode rw {listed}")      # the answer: `accept N`, N shared
    rb = Badge(pdir, "256M", os.path.join(tmp, "hang-scratch"))
    try:
        rb.verify([(b"v" * 32, b"c" * 32, "rw.bin")], store, timeout=30)
        shared, why = rb.last[0][1], ""
    except BadgeError as e:
        shared, why = None, str(e)[-400:]
    check(shared == 0, f"a badge run's mount table: no read-write mount of a superblock the host has mounted, the "
                       f"device nodes aside (shared: {shared}; 10^6 added if a check failed) {why}")
    print(f"\n{len(FAILS)} failure(s)")
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
