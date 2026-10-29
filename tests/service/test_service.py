#!/usr/bin/env python3
"""Tests of the oracle service against Python's hashlib and the independent reading of BRIEF §4.2
in `wots_ref.py`.

  python3 tests/service/test_service.py [RF_ORACLE_TEST_BINARY]

1. keyed BLAKE2s (`QUERY`) against `hashlib.blake2s(key=…)` on the empty message (whose only block
   is the key block, V4-A5), one-block,
   block-boundary and multi-block messages, up to 64 KiB, in mixed-size batches, with and without
   the AVX2 path (`RF_ORACLE_NO_SIMD`);
2. `SIGN`: the answers, the signature byte for byte against `wots_ref` (from the fixed test seed),
   `SigOk` against `vk`, the index sequence, the empty trace;
3. `VK` against the root of the full Merkle tree computed by `wots_ref` from the seed;
4. malformed and over-cap requests are refused and close the connection;
5. 32 concurrent connections, a 33rd refused; 8 concurrent signers get a permutation of indices;
   32 maximal `QUERY` requests at once fit the service's 2 GiB cgroup;
6. with random keys: two services have different keys; after 2^16 signatures `SIGN` is refused;
7. shutdown on stdin end of file: exit 0, socket removed, statistics printed.
"""
import os
import random
import struct
import subprocess
import sys
import tempfile
import threading
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "harness"))
sys.path.insert(0, HERE)
import wots_ref as W  # noqa: E402
from rfh.service import Client, Service, ServiceError, OP_QUERY, OP_SIGN, OP_VK  # noqa: E402
from rfh.signed import from_wire  # noqa: E402

# the test build (`cargo build --release --features insecure-test-keys --target-dir target/test-keys`);
# the release binary rejects `--insecure-test-keys` (RB-m5)
BIN = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "service", "target", "test-keys", "release", "rf-oracle")
RELEASE = os.path.join(ROOT, "service", "target", "release", "rf-oracle")
PRF_KEY = bytes(range(32))
SEED = bytes(range(100, 132))
FAILS = []


def check(cond, what):
    print(("ok   " if cond else "FAIL ") + what, flush=True)
    if not cond:
        FAILS.append(what)


def start(d, env_extra=None, test_keys=True, wrap=()):
    """A service with fixed test keys (raw Popen: the runner's `Service` refuses test keys)."""
    os.makedirs(d)
    cmd = list(wrap) + [BIN, "--socket", "oracle.sock"]
    if test_keys:
        cmd += ["--insecure-test-keys", PRF_KEY.hex(), SEED.hex()]
    env = dict(os.environ, **(env_extra or {}))
    p = subprocess.Popen(cmd, cwd=d, stdin=subprocess.PIPE, stdout=subprocess.PIPE, env=env)
    lines = []
    while True:
        line = p.stdout.readline().decode().strip()
        if not line:
            raise RuntimeError("service died")
        lines.append(line)
        if line == "ready":
            break
    info = dict(l.split(" ", 1) for l in lines if " " in l)
    return p, info, os.path.join(d, "oracle.sock")


def stop(p):
    p.stdin.close()
    out = p.stdout.read().decode()
    return p.wait(timeout=60), out


def main():
    rnd = random.Random(1)
    tmp = tempfile.mkdtemp(prefix="rf-svc-test-", dir=os.environ.get("RF_TEST_TMP"))
    print(f"tests in {tmp}")
    sizes = [0, 1, 2, 31, 32, 33, 55, 56, 63, 64, 65, 100, 127, 128, 129, 191, 192, 193, 1000, 4096, 4265,
             9000, 65535, 65536]
    msgs = [bytes(rnd.getrandbits(8) for _ in range(n)) for n in sizes]
    msgs += [bytes([7]) * 64 for _ in range(20)] + [b""] * 3
    rnd.shuffle(msgs)
    want = [W.H(m, key=PRF_KEY) for m in msgs]

    print("computing the reference Merkle tree from the test seed ...")
    t0 = time.time()
    levels = W.tree(SEED)
    print(f"  {time.time() - t0:.1f} s")

    for simd in ("avx2", "scalar"):
        env = {"RF_ORACLE_NO_SIMD": "1"} if simd == "scalar" else {}
        p, info, sock = start(os.path.join(tmp, f"svc-{simd}"), env)
        check(info.get("simd") == simd or simd == "avx2", f"[{simd}] service reports simd={info.get('simd')}")
        check(bytes.fromhex(info["vk"]) == levels[16][0], f"[{simd}] vk equals the reference Merkle root")
        c = Client(sock)
        check(c.vk() == levels[16][0], f"[{simd}] VK request")
        got = c.query(msgs)
        check(got == want, f"[{simd}] QUERY of {len(msgs)} messages (sizes 0 … 65536) = hashlib keyed BLAKE2s")
        one = [c.query([m])[0] for m in msgs[:10]]
        check(one == want[:10], f"[{simd}] QUERY one at a time")
        for k, trace_q in enumerate([[], [b"abc"], msgs[:7], [bytes(64)] * 9]):
            body = c.sign(trace_q)
            s = from_wire(b"", trace_q, body)
            td = W.trace_digest(s.trace)
            check([a for _, a in s.trace] == [W.H(q, key=PRF_KEY) for q in trace_q],
                  f"[{simd}] SIGN {k}: answers = hashlib keyed BLAKE2s")
            check(s.idx == k, f"[{simd}] SIGN {k}: one-time key index {s.idx}")
            check(s.ots == W.wots_sign(SEED, s.idx, td), f"[{simd}] SIGN {k}: ots = reference WOTS signature")
            check(s.path == W.auth_path(levels, s.idx), f"[{simd}] SIGN {k}: path = reference authentication path")
            check(W.sig_ok(levels[16][0], td, s.idx, s.ots, s.path), f"[{simd}] SIGN {k}: SigOk vk (traceDigest tr) σ")
            bad = list(s.ots)
            bad[3] = bytes(32)
            check(not W.sig_ok(levels[16][0], td, s.idx, bad, s.path), f"[{simd}] SIGN {k}: a changed ots fails")
            check(not W.sig_ok(levels[16][0], W.H(td), s.idx, s.ots, s.path), f"[{simd}] SIGN {k}: another digest fails")
        c.close()
        code, out = stop(p)
        check(code == 0 and "stats " in out, f"[{simd}] shutdown on stdin EOF: exit {code}, stats printed")
        check(not os.path.exists(sock), f"[{simd}] socket removed at exit")

    # 4. malformed and over-cap requests
    p, info, sock = start(os.path.join(tmp, "svc-errors"))
    cases = [
        ("unknown op", struct.pack("<B3xIQ", 9, 0, 0), 1),
        ("non-zero reserved byte", struct.pack("<BBxxIQ", OP_QUERY, 1, 0, 0), 1),
        ("VK with a body", struct.pack("<B3xIQ", OP_VK, 1, 4) + bytes(4), 1),
        ("QUERY count above 2^18", struct.pack("<B3xIQ", OP_QUERY, (1 << 18) + 1, 0), 2),
        ("SIGN count above 2^16", struct.pack("<B3xIQ", OP_SIGN, (1 << 16) + 1, 0), 2),
        ("body above 2^24", struct.pack("<B3xIQ", OP_QUERY, 1, (1 << 24) + 1), 2),
        ("lengths exceed the body", struct.pack("<B3xIQ", OP_QUERY, 1, 6) + struct.pack("<I", 5) + b"ab", 1),
        ("lengths short of the body", struct.pack("<B3xIQ", OP_QUERY, 1, 8) + struct.pack("<I", 1) + b"abcd", 1),
        ("count above the length words", struct.pack("<B3xIQ", OP_QUERY, 3, 4) + struct.pack("<I", 0), 1),
        ("a query above 2^20 bytes", struct.pack("<B3xIQ", OP_QUERY, 1, 4 + (1 << 20) + 1)
         + struct.pack("<I", (1 << 20) + 1) + bytes((1 << 20) + 1), 2),
    ]
    for what, raw, st in cases:
        c = Client(sock)
        got, _, msg = c.call(None, raw=raw)
        closed = c.s.recv(1) == b""
        check(got == st and closed, f"refused: {what} (status {got}, {msg.decode(errors='replace')!r}), connection closed")
        c.close()
    # 5. concurrency
    errs = []

    def worker(t):
        try:
            r = random.Random(t)
            cl = Client(sock)
            for _ in range(20):
                qs = [bytes(r.getrandbits(8) for _ in range(r.choice([0, 5, 64, 65, 200]))) for _ in range(r.randint(1, 300))]
                if cl.query(qs) != [W.H(q, key=PRF_KEY) for q in qs]:
                    errs.append(t)
            cl.close()
        except Exception as e:  # noqa: BLE001 (a thread's failure is the test's)
            errs.append(repr(e))
    ths = [threading.Thread(target=worker, args=(t,)) for t in range(32)]
    [t.start() for t in ths]
    [t.join() for t in ths]
    check(not errs, "32 concurrent connections, 20 mixed batches each, all answers correct")
    big = bytes(range(256)) * 4096
    cb = Client(sock)
    check(cb.query([big]) == [W.H(big, key=PRF_KEY)], "a query of exactly 2^20 bytes is answered")
    cb.close()
    conns = [Client(sock) for _ in range(32)]
    extra = Client(sock)
    st, _, msg = extra.call(OP_VK)
    check(st == 2, f"33rd connection refused (status {st})")
    for cc in conns:
        cc.close()
    stop(p)

    # concurrent signers get distinct, consecutive indices (RF-m22)
    p, info, sock = start(os.path.join(tmp, "svc-perm"))
    got, lock = [], threading.Lock()

    def perm_signer():
        try:
            cl = Client(sock)
            for _ in range(64):
                body = cl.sign([])
                with lock:
                    got.append(struct.unpack("<I", body[:4])[0])
            cl.close()
        except Exception as e:  # noqa: BLE001
            with lock:
                got.append(repr(e))
    ths = [threading.Thread(target=perm_signer) for _ in range(8)]
    [t.start() for t in ths]
    [t.join() for t in ths]
    check(sorted(map(str, got)) == sorted(map(str, range(512))),
          f"8 concurrent signers: indices are a permutation of 0…511 ({len(set(got))} distinct of {len(got)})")
    stop(p)
    # 32 maximal requests at once fit the service's 2 GiB cgroup (RF-m20)
    from rfh.sandbox import memcap, memcap_method
    if memcap_method() == "systemd":
        p, info, sock = start(os.path.join(tmp, "svc-mem"), wrap=memcap("2G", f"rf-svc-memtest-{os.getpid()}"))
        qs = [bytes([i % 251]) * 60 for i in range(1 << 18)]          # body 2^18 · 64 = 16 MiB
        want = {k: W.H(qs[k], key=PRF_KEY) for k in (0, 1, 12345, (1 << 18) - 1)}
        bad, barrier = [], threading.Barrier(32)

        def big():
            try:
                cl = Client(sock)
                barrier.wait(timeout=120)
                ans = cl.query(qs)
                if any(ans[k] != v for k, v in want.items()):
                    bad.append("wrong answer")
                cl.close()
            except Exception as e:  # noqa: BLE001 (a refused or dropped connection is the failure)
                bad.append(repr(e))
        ths = [threading.Thread(target=big) for _ in range(32)]
        [t.start() for t in ths]
        [t.join() for t in ths]
        code, out = stop(p)
        check(not bad and code == 0, f"32 concurrent 16 MiB QUERY requests (2^18 queries each) in a 2 GiB scope: "
                                     f"{len(bad)} failures, service exit {code}")
    else:
        print("skip the 2 GiB cgroup test: no systemd user scope here")

    # 6. random keys, exhaustion; the runner's Service class
    s1 = Service(BIN, os.path.join(tmp, "rand1")).start()
    s2 = Service(BIN, os.path.join(tmp, "rand2")).start()
    a1, a2 = Client(s1.socket_path).query([b"x"]), Client(s2.socket_path).query([b"x"])
    check(s1.vk != s2.vk and a1 != a2, "two services: different vk and different PRF answers")
    s2.stop()
    fake = os.path.join(tmp, "fake-service.sh")
    with open(fake, "w") as f:
        f.write("#!/bin/sh\necho INSECURE fixed test keys\necho vk " + "00" * 32 + "\necho ready\ncat\n")
    os.chmod(fake, 0o755)
    refused = False
    try:
        Service(fake, os.path.join(tmp, "fake")).start()
    except ServiceError:
        refused = True
    check(refused, "the runner refuses a service that prints INSECURE")
    if os.path.exists(RELEASE):
        r = subprocess.run([RELEASE, "--socket", "x.sock", "--insecure-test-keys", PRF_KEY.hex(), SEED.hex()],
                           cwd=tmp, capture_output=True, timeout=60)
        check(r.returncode == 2 and not os.path.exists(os.path.join(tmp, "x.sock")),
              f"the release binary rejects --insecure-test-keys (exit {r.returncode})")
    t0 = time.time()
    lock = threading.Lock()
    count = [0]

    def signer():
        cl = Client(s1.socket_path)
        while True:
            st, _, _ = cl.call(OP_SIGN, [])
            if st:
                return st
            with lock:
                count[0] += 1
    res = []
    ths = [threading.Thread(target=lambda: res.append(signer())) for _ in range(8)]
    [t.start() for t in ths]
    [t.join() for t in ths]
    check(count[0] == 1 << 16 and set(res) == {3},
          f"exactly 2^16 signatures, then EXHAUSTED ({count[0]} signed, statuses {set(res)}, {time.time() - t0:.1f} s)")
    stats = s1.stop()
    check(stats.get("signatures") == 1 << 16, f"service statistics: {stats}")

    print(f"\n{len(FAILS)} failure(s)")
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
