#!/usr/bin/env python3
"""The request sandbox's own refusals (`sandbox.seccomp_program(request=True)`; review R5 HIGH 1,
R8 HIGH 1, R4 LOW 3), and the service's `drop` after a request.

  python3 tests/harness/test_request_filter.py [RF_ORACLE_BINARY]

0. The one table of the filter's refusals: `harness/PROVER.md` §2's copy, between its `refusals`
   markers, equals `sandbox.refusal_table()`, which is derived from the lists the filter is built
   from (`DENY`, `ENOSYS`, `REQUEST_DENY`, `REQUEST_ENOSYS`, the argument rules); every call in them
   has a reason (`WHY`), and every reason is used.
1. In a request (`prover.request`, as the benchmark makes them): `sendmsg` and `sendmmsg` fail with
   EPERM (no descriptor can be sent into the service's receive queue, on the oracle's socket or any
   other), `sysinfo` with ENOSYS (no load averages, process count or free memory); `write`, `send`
   and `sendto` on a Unix socket still work, and a `QUERY` over the oracle's socket is answered.
2. In `prover setup` (no service, untimed) `sysinfo` and `sendmsg` are not refused (the filter is the
   request's alone; the badge keeps `sysinfo` too, which the Lean runtime calls).
3. After a request that left a connection open with an unread 8 MiB response, the service's `drop`
   reports `live=0` and all 32 connection slots are free again.
"""
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from rfh.prover import Run, request  # noqa: E402
from rfh.service import Client, Service  # noqa: E402

BIN = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "service", "target", "release", "rf-oracle")
FAILS = []

PROG = r'''
#define _GNU_SOURCE
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdint.h>
#include <sys/socket.h>
#include <sys/sysinfo.h>
#include <sys/syscall.h>
#include <sys/mman.h>
#include <sys/un.h>
static int e(long r) { return r < 0 ? errno : 0; }
static int sendfd(int s, int fd) {
    char c = 0, buf[CMSG_SPACE(sizeof(int))];
    struct iovec io = {&c, 1};
    struct msghdr m = {0};
    m.msg_iov = &io; m.msg_iovlen = 1; m.msg_control = buf; m.msg_controllen = sizeof buf;
    struct cmsghdr *h = CMSG_FIRSTHDR(&m);
    h->cmsg_level = SOL_SOCKET; h->cmsg_type = SCM_RIGHTS; h->cmsg_len = CMSG_LEN(sizeof(int));
    memcpy(CMSG_DATA(h), &fd, sizeof(int));
    return e(sendmsg(s, &m, 0));
}
static void probe(FILE *o) {
    struct sysinfo si;
    int sp[2];
    socketpair(AF_UNIX, SOCK_STREAM, 0, sp);
    struct mmsghdr mm = {0};
    char c = 0;
    struct iovec io = {&c, 1};
    mm.msg_hdr.msg_iov = &io; mm.msg_hdr.msg_iovlen = 1;
    fprintf(o, "sysinfo=%d sendmsg=%d sendmmsg=%d write=%d send=%d sendto=%d",
            e(syscall(SYS_sysinfo, &si)), sendfd(sp[0], sp[1]), e(syscall(SYS_sendmmsg, sp[0], &mm, 1, 0)),
            e(write(sp[0], "x", 1)), e(send(sp[0], "x", 1, 0)), e(sendto(sp[0], "x", 1, 0, 0, 0)));
    const char *p = getenv("RF_ORACLE");
    if (p) {
        struct sockaddr_un a = {.sun_family = AF_UNIX};
        strcpy(a.sun_path, p);
        int s = socket(AF_UNIX, SOCK_STREAM, 0);
        int r = connect(s, (struct sockaddr *)&a, sizeof a);
        int fd = memfd_create("pin", 0);
        fprintf(o, " oracle_connect=%d oracle_sendmsg=%d", r ? errno : 0, sendfd(s, fd));
        /* a QUERY of one empty query over write(): 16-byte header, a 4-byte length */
        unsigned char q[20] = {1, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        unsigned char h[16];
        int ok = write(s, q, 20) == 20 && read(s, h, 16) == 16 && h[0] == 0;
        fprintf(o, " query_ok=%d", ok);
        if (getenv("RF_LEAVE") || access("leave", F_OK) == 0) {
            /* a QUERY of 2^18 empty queries, its 8 MiB answer never read, the connection left open */
            static unsigned char big[16 + 4 * (1 << 18)];
            big[0] = 1; big[6] = 4; uint64_t n = 4u << 18; memcpy(big + 8, &n, 8);
            write(s, big, sizeof big);
        }
    }
    fputc('\n', o);
}
int main(int argc, char **argv) {
    if (argc > 1 && !strcmp(argv[1], "setup")) {
        chdir(argv[2]);
        FILE *o = fopen("report.txt", "w");
        probe(o);
        fclose(o);
        return 0;
    }
    puts("ready"); fflush(stdout);
    char b[8];
    if (!fgets(b, 8, stdin)) return 9;
    FILE *o = fopen("proof.bin", "w");
    probe(o);
    fclose(o);
    puts("done"); fflush(stdout);
    return 0;
}
'''


def check(cond, what):
    print(("ok   " if cond else "FAIL ") + what)
    if not cond:
        FAILS.append(what)


def kv(text):
    return dict(x.split("=", 1) for x in text.split() if "=" in x)


def table():
    """0. The docs' table of refusals is the code's."""
    import rfh.sandbox as sbx
    text = open(os.path.join(ROOT, "harness", "PROVER.md")).read()
    start = "<!-- refusals: generated by `python3 harness/rfh/sandbox.py --refusals`; do not edit by hand -->\n"
    a, b = text.find(start), text.find("<!-- /refusals -->")
    doc = text[a + len(start):b] if 0 <= a < b else None
    check(doc == sbx.refusal_table(), "harness/PROVER.md §2's table of refusals is `refusal_table()` (regenerate it "
                                      "with `python3 harness/rfh/sandbox.py --refusals`)")
    names = [n for t in (sbx.DENY, sbx.ENOSYS, sbx.REQUEST_DENY, sbx.REQUEST_ENOSYS) for n in t]
    keys = names + ["AF_INET", "CLONE_PIDFD", "x32", "arch"] + list(sbx.GETSOCKOPT_REFUSED) + list(
        sbx.SETSOCKOPT_REFUSED) + list(sbx.MADV_REFUSED)
    unused = [k for names_, _ in sbx.REASONS for k in names_.split() if k not in keys]
    check(all(n in sbx.WHY for n in keys) and not unused and len(set(names)) == len(names)
          and all(len(set(t.values())) == len(t) for t in (sbx.DENY, sbx.ENOSYS))
          and not set(sbx.DENY.values()) & set(sbx.ENOSYS.values()),
          f"every refusal has one reason and every reason a refusal ({unused}); no call is in two lists")


def main():
    import errno
    table()
    tmp = tempfile.mkdtemp(prefix="rf-reqfilter-", dir=os.environ.get("RF_TEST_TMP"))
    os.makedirs(os.path.join(tmp, "bin"))
    open(os.path.join(tmp, "p.c"), "w").write(PROG)
    subprocess.run(["gcc", "-static", "-O1", "-w", "-o", os.path.join(tmp, "bin", "prover"), os.path.join(tmp, "p.c")],
                   check=True)
    run = Run(os.path.join(tmp, "bin"), os.path.join(tmp, "setup"), "512M")
    ok, _, log = run.setup(60)
    rep = kv(open(os.path.join(run.setup_dir, "report.txt")).read()) if ok else {}
    check(ok and rep.get("sysinfo") == "0" and rep.get("sendmsg") == "0",
          f"prover setup: sysinfo and sendmsg are not refused ({rep or log[-200:]})")
    run.publish()
    svc = Service(BIN, os.path.join(tmp, "svc"), io_timeout=60).start()
    link = os.path.join(tmp, "req-sock")
    os.makedirs(link)
    r = request(run, "step", None, link, {"leaf.json": b"{}"}, 30, 1 << 20, ready_s=5, sock_at_go=svc.socket_path)
    rep = kv((r.proof or b"").decode(errors="replace"))
    want = {"sysinfo": str(errno.ENOSYS), "sendmsg": str(errno.EPERM), "sendmmsg": str(errno.EPERM), "write": "0",
            "send": "0", "sendto": "0", "oracle_connect": "0", "oracle_sendmsg": str(errno.EPERM), "query_ok": "1"}
    check(r.status == "ok" and all(rep.get(k) == v for k, v in want.items()),
          f"a request: sysinfo ENOSYS, sendmsg and sendmmsg EPERM (on the oracle's socket too), write/send/sendto and a "
          f"QUERY work ({r.status}: {rep})")
    check(svc.drop() == 0, "after that request `drop` reports no connection left")

    # 3. a request that leaves a connection with an unread 8 MiB answer: `drop` closes it
    os.unlink(os.path.join(link, "oracle.sock"))
    r = request(run, "step", None, link, {"leave": b"1"}, 30, 1 << 20, ready_s=5, sock_at_go=svc.socket_path)
    live_before = svc.stats().get("live")
    live = svc.drop()
    clients = []
    try:
        for _ in range(32):
            c = Client(svc.socket_path)
            clients.append(c)
            c.vk()
        served = len(clients)
    except Exception:  # noqa: BLE001
        served = len(clients) - 1
    for c in clients:
        c.close()
    check(r.status == "ok" and live == 0 and served == 32,
          f"a request leaving an unread 8 MiB answer: live {live_before} before `drop`, {live} after, {served} of 32 slots "
          f"free ({r.status})")
    svc.stop()
    print(f"{len(FAILS)} failure(s)")
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
