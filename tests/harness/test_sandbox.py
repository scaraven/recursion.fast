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
    nothing (a directory), and so does everything in /sys/devices/system/cpu but its static
    description; `socket`/`socketpair` fail with EPERM for every domain but AF_UNIX (UDP among them);
    `statfs`/`fstatfs`/`statvfs`/`ustat` (free disk space), every way to a pidfd (pidfs inode
    numbers) and `SO_COOKIE` are refused, `clone3` is ENOSYS and `fork` and threads work;
    `mlock` of N pages in one request raises the host's `unevictable_pgs_mlocked` by N and the next
    request sees none of it; a request's first inode number does not depend on how many files an
    earlier request made (with a shared tmpfs, the control, it does); with the runner's scrub
    (`harness/tools/scrub.c`) before every request, the per-CPU inode counters of pipes and memfds
    show a later request nothing of the K pipes and memfds an earlier one made on every CPU (without
    it, the control, each CPU's counter has moved by K).

The requests of 6.-8., 10. and 11. run as the benchmark's do, /work a private tmpfs (`request` with
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
from rfh.sandbox import memcap_method  # noqa: E402
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

    def iso_req(mode):
        return request(iso_run, "step", None, svc.sock_dir, {"mode": mode.encode()}, 10, 1 << 20, ready_s=5,
                       preset={"vk.hex": b"00" * 32 + b"\n"})

    def report(what, text):
        lines = text.splitlines()
        bad = [l for l in lines if l.startswith("FAIL")]
        check(lines and lines[-1] == "checks passed" and not bad,
              f"{what}: masks, the socket rule and the counters' refusals hold ({'; '.join(l for l in lines if l.startswith('/'))}; "
              f"links left in /proc: {[l[5:] for l in lines if l.startswith('link /proc/')]}; {bad[:5]})")
    r = iso_req("probe")
    report(f"a request ({r.status})", (r.proof or b"").decode(errors="replace"))
    ok, _, slog = iso_run.setup(60)
    rp = os.path.join(iso_run.setup_dir, "report.txt")
    report(f"prover setup (ok={ok})", open(rp).read() if os.path.exists(rp) else slog)

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
    badge = Badge(bdir, "256M", os.path.join(tmp, "hang-scratch"))
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
    print(f"\n{len(FAILS)} failure(s)")
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
