#!/usr/bin/env python3
"""Tests of the oracle service against independent Keccak-256 references and the independent reading of
`Contract/Signature.lean` in `wots_ref.py`.

  python3 tests/service/test_service.py [RF_ORACLE_TEST_BINARY]

0. the references: `keccak_ref.c` (compiled by `wots_ref`; gcc is required) and the pure-Python
   `harness/rfh/keccak.py` against the published Keccak-256 vectors and against each other;
1. the keyed hash (`QUERY`), `PRF_k(q) = Keccak-256(k ‖ q)`, against the references on the empty
   query, queries around the permutation boundaries (`32 + |q|` a multiple of 136) and multi-block
   queries up to 64 KiB, in mixed-size batches and one at a time;
2. `SIGN`: the answers, the signature byte for byte against `wots_ref` (from the fixed test seed),
   `SigOk` against `vk`, the index sequence, the empty trace;
3. `VK` against the root of the full Merkle tree computed by `wots_ref` from the seed;
4. malformed and over-cap requests are refused and close the connection;
5. 32 concurrent connections, a 33rd refused; 8 concurrent signers get a permutation of indices;
   32 maximal `QUERY` requests at once fit the service's 2 GiB cgroup;
6. with random keys: two services have different keys; after 2^16 signatures `SIGN` is refused;
7. shutdown on stdin end of file: exit 0, socket removed, statistics printed;
8. `rf-oracle --leaves`: leaf digests of chains against the references, in input order, on 1 and
   several threads; a malformed line exits 2.
"""
import functools
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
from rfh import keccak as pykeccak  # noqa: E402

# the test build (`cargo build --release --features insecure-test-keys --target-dir target/test-keys`);
# the release binary rejects `--insecure-test-keys`
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


def pattern(n):
    """leanVM's test pattern."""
    return bytes((7 * i + 3) % 256 for i in range(n))


VECTORS = [  # Keccak-256 (Ethereum), published values
    (b"", "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"),
    (b"abc", "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"),
    (pattern(135), "00ef96af9cf4b24c7f269d922294444a197d0a33638c2e56634c57e892103a8f"),
    (pattern(136), "742061bcad767ed4c4f5883b1dcb1aad11afdcc140dc469d953759b127b9f9ed"),
    (pattern(137), "e3371f61e770abf254c34239c3b0099ad90594507415bc81dd0a10b9692bbf2a"),
    (pattern(271), "4401c4afbe16ff911bdbf2d38e556e5b861f3fdf0f9d4306b1c46f6ae4f73584"),
    (pattern(272), "ac141fd7b0a0ffcd2e967254d508da3ec616596493c36fa304425647d90e6de5"),
    (b"C" + bytes(range(32)), "db8c51208716e57c91fc944cfa0df7336f9e784f9d3c0c04347f5fa833588e97"),
]


def chain_leaf(s, n):
    """`leafStmt (chainEnd s n) n` by the C reference."""
    for _ in range(n):
        s = W.keccak_c(b"C" + s)
    return W.keccak_c(b"L" + s + W.enc64(n))


def test_leaves(binary):
    rnd = random.Random(2)
    jobs = [(bytes(rnd.getrandbits(8) for _ in range(32)), rnd.choice([0, 1, 2, 7, 100, 1000])) for _ in range(300)]
    stdin = "".join(f"{s.hex()} {n}\n" for s, n in jobs)
    want = "".join(chain_leaf(s, n).hex() + "\n" for s, n in jobs)
    check(chain_leaf(bytes(range(32)), 5) == pykeccak.keccak256(
        b"L" + functools.reduce(lambda d, _: pykeccak.keccak256(b"C" + d), range(5), bytes(range(32))) + W.enc64(5)),
        "leaf digest: the C reference equals the pure-Python reference on a 5-step chain")
    for threads in ([], ["--threads", "1"], ["--threads", "7"]):
        r = subprocess.run([binary, "--leaves"] + threads, input=stdin, capture_output=True, text=True, timeout=120)
        check(r.returncode == 0 and r.stdout == want,
              f"--leaves {' '.join(threads)}: {len(jobs)} chains (n up to 1000) equal the reference, in input order")
    r = subprocess.run([binary, "--leaves"], input="", capture_output=True, text=True, timeout=60)
    check(r.returncode == 0 and r.stdout == "", "--leaves on empty input: exit 0, no output")
    for bad in [stdin + "zz\n", f"{jobs[0][0].hex().upper()} 3\n", f"{jobs[0][0].hex()} -1\n", "\n"]:
        r = subprocess.run([binary, "--leaves"], input=bad, capture_output=True, text=True, timeout=120)
        check(r.returncode == 2 and r.stdout == "" and "rf-oracle --leaves" in r.stderr,
              f"--leaves refuses a malformed line {bad.splitlines()[-1][:20]!r}…: exit {r.returncode}, nothing on stdout")
    r = subprocess.run([binary, "--leaves", "--socket", "x.sock"], input="", capture_output=True, text=True, timeout=60)
    check(r.returncode == 2, f"--leaves with --socket is a usage error (exit {r.returncode})")


def main():
    rnd = random.Random(1)
    tmp = tempfile.mkdtemp(prefix="rf-svc-test-", dir=os.environ.get("RF_TEST_TMP"))
    print(f"tests in {tmp}")

    # 0. the references
    W.c_lib(required=True)
    for m, d in VECTORS:
        check(W.keccak_c(m).hex() == d and pykeccak.keccak256(m).hex() == d,
              f"keccak_ref.c and rfh/keccak.py: Keccak-256 of {len(m)} bytes = {d[:16]}…")
    agree = all(W.keccak_c(m) == pykeccak.keccak256(m) for m in (bytes(rnd.getrandbits(8) for _ in range(n))
                                                                  for n in range(0, 600, 3)))
    check(agree, "keccak_ref.c = rfh/keccak.py on 200 random messages of 0 … 597 bytes")

    # the queries: 32 + |q| around multiples of the rate 136, and multi-block
    sizes = [0, 1, 2, 31, 32, 33, 64, 103, 104, 105, 135, 136, 137, 239, 240, 241, 271, 272, 375, 376, 377,
             1000, 4096, 4265, 9000, 65535, 65536]
    msgs = [bytes(rnd.getrandbits(8) for _ in range(n)) for n in sizes]
    msgs += [bytes([7]) * 64 for _ in range(20)] + [b""] * 3
    rnd.shuffle(msgs)
    want = [W.H(m, key=PRF_KEY) for m in msgs]
    check(all(pykeccak.keyed(PRF_KEY, m) == w for m, w in zip(msgs, want) if len(m) < 2000),
          "keyed hash: the C reference = rfh/keccak.py keyed on the short test queries")

    print("computing the reference Merkle tree from the test seed ...")
    t0 = time.time()
    levels = W.tree(SEED)
    print(f"  {time.time() - t0:.1f} s")

    p, info, sock = start(os.path.join(tmp, "svc"))
    check(info.get("simd") == "scalar", f"service reports simd={info.get('simd')}")
    check(bytes.fromhex(info["vk"]) == levels[16][0], "vk equals the reference Merkle root")
    c = Client(sock)
    check(c.vk() == levels[16][0], "VK request")
    got = c.query(msgs)
    check(got == want, f"QUERY of {len(msgs)} messages (sizes 0 … 65536) = Keccak-256(k ‖ q) of the reference")
    one = [c.query([m])[0] for m in msgs[:10]]
    check(one == want[:10], "QUERY one at a time")
    for k, trace_q in enumerate([[], [b"abc"], msgs[:7], [bytes(64)] * 9]):
        body = c.sign(trace_q)
        s = from_wire(b"", trace_q, body)
        td = W.trace_digest(s.trace)
        check([a for _, a in s.trace] == [W.H(q, key=PRF_KEY) for q in trace_q],
              f"SIGN {k}: answers = Keccak-256(k ‖ q) of the reference")
        check(s.idx == k, f"SIGN {k}: one-time key index {s.idx}")
        check(s.ots == W.wots_sign(SEED, s.idx, td), f"SIGN {k}: ots = reference WOTS signature")
        check(s.path == W.auth_path(levels, s.idx), f"SIGN {k}: path = reference authentication path")
        check(W.sig_ok(levels[16][0], td, s.idx, s.ots, s.path), f"SIGN {k}: SigOk vk (traceDigest tr) σ")
        bad = list(s.ots)
        bad[3] = bytes(32)
        check(not W.sig_ok(levels[16][0], td, s.idx, bad, s.path), f"SIGN {k}: a changed ots fails")
        check(not W.sig_ok(levels[16][0], W.H(td), s.idx, s.ots, s.path), f"SIGN {k}: another digest fails")
    c.close()
    code, out = stop(p)
    check(code == 0 and "stats " in out, f"shutdown on stdin EOF: exit {code}, stats printed")
    check(not os.path.exists(sock), "socket removed at exit")

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

    # concurrent signers get distinct, consecutive indices
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
    # 32 maximal requests at once fit the service's 2 GiB cgroup
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

    # 8. the runner's chain hasher
    test_leaves(RELEASE if os.path.exists(RELEASE) else BIN)

    print(f"\n{len(FAILS)} failure(s)")
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
