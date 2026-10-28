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
7. the clock stops when the sandbox is dead (V4-A11 §5.1, the flock `seed_pipe` pattern): a prover
   that prints `done` and keeps writing `proof.bin` from a thread, or from a forked child, has none
   of its late bytes read; one that closes stdout without `done` and leaves a child computing is
   charged until every process is dead; no process survives any request;
8. R-M1: a prover that makes /work unusable (an input's name taken by a directory, or /work made
   unreadable) is the entry's failure with that reason, never a harness error.
"""
import os
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from rfh.files import OutputError, read_output  # noqa: E402
from rfh.prover import Run, build, request  # noqa: E402
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

    # 6.-8. the handshake, the clock, R-M1
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
        return request(r, kind, os.path.join(d, "work"), svc.sock_dir, inputs or {"chain.json": b"{}"}, step, 1 << 20,
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
    # review m-4: the late writer stamps CLOCK_MONOTONIC (the runner's clock) into proof.bin every
    # millisecond, before and after `done`; under the V4-A11 order every stamp is at or before the
    # time the clock stopped (the death of the sandbox), under v4's order (the clock stopped at
    # `done`, the kill after it) the stamps written between `done` and the kill would be later
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
    check("made /work unusable" in r.status, f"R-M1: an input's name taken by a directory is the entry's failure: {r.status}")
    r = req(HS + 'int main(){hs();FILE*f=fopen("proof.bin","w");fputs("P",f);fclose(f);chmod(".",0);'
            'puts("done");fflush(stdout);sleep(100);}\n')
    check("made /work unusable" in r.status or "cannot open" in r.status or "Permission" in r.status,
          f"R-M1: /work made unreadable is the entry's failure: {r.status}")
    r = req(HS + 'int main(){hs();FILE*f=fopen("proof.bin","w");fputs("P",f);fclose(f);int g=open("big",O_WRONLY|O_CREAT,0644);'
            'ftruncate(g,1LL<<40);close(g);puts("done");fflush(stdout);sleep(100);}\n', work_cap=1 << 30)
    check(r.status != "ok" and "work_cap" in r.status,
          f"review M-1/M-2: a 1 TiB sparse file in /work counts at its size, above work_cap: {r.status}")
    r = req(HS + 'int main(){hs();FILE*f=fopen("proof.bin","w");fputs("P",f);fclose(f);mkdir("d",0700);'
            'FILE*h=fopen("d/x","w");fputs("x",h);fclose(h);chmod("d",0);puts("done");fflush(stdout);sleep(100);}\n',
            work_cap=1 << 30)
    check(r.status == "ok" and r.work_bytes is not None and r.work_bytes < 1 << 20,
          f"a mode-000 subdirectory is made accessible and measured ({r.status}, {r.work_bytes} bytes)")
    r = req('int main(){_exit(0);}\n')
    check(r.status.startswith("no ready line") or "ended before" in r.status,
          f"review m-1: a prover that exits at once is the entry's failure, never a harness error: {r.status}")
    from rfh.prover import remove_tree, tree_bytes
    t = os.path.join(tmp, "locked")
    os.makedirs(os.path.join(t, "a", "b"))
    open(os.path.join(t, "a", "b", "f"), "w").write("x")
    with open(os.path.join(t, "sparse"), "wb") as f:
        f.truncate(1 << 40)
    os.chmod(os.path.join(t, "a", "b"), 0)
    os.chmod(os.path.join(t, "a"), 0)
    nb = tree_bytes(t)
    check(nb >= 1 << 40, f"review M-2: tree_bytes counts a sparse file at its size, through mode-000 directories: {nb}")
    check(remove_tree(t), "a locked tree is removed (made accessible first)")
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
    print(f"\n{len(FAILS)} failure(s)")
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
