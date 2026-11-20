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
8. `rf-oracle --data-roots FILE…`: leaf statements `leafStmt (dataRoot xs) n` against the C
   reference (`par_leaf`, itself checked against the pure-Python `rfh/digest.py` and the shared
   known answers `tests/vectors/data_root.json`), in argument order, on 1 and several threads (the
   same output), many small files and one of `leafCap = 2^20` blocks spread over the threads; an
   empty file prints `leafStmt zero 0`; a size that is not a multiple of 32, `n` above 2^20 or a
   missing file exits 2 with nothing on stdout;
9. replay mode: after the control line `replay` the service prints `key <hex k>` and `replay ready`;
   `SIGN` of the service run's traces in order returns byte-identical responses, any other trace at
   an index (never signed, or signed with another digest) is refused with status 4 `MISMATCH`;
   each `replay` resets the index to 0; `QUERY` and `VK` are unchanged; end of file still shuts down;
10. dead clients (review R5 HIGH 1): a client that never reads a 2^18-query `QUERY` response and
   leaves its own socket in flight in the service's queue (`SCM_RIGHTS`), then closes it, holds a
   slot, and so does one with 2000 pipelined `VK`s; `replay` is still ready at once (no response is
   written under the key lock); after the control line `drop` the service prints `dropped live=0`,
   the descriptors parked in the queues are released, and all 32 slots are free again;
11. a 256 MiB memfd parked the same way is freed by `drop` (`Shmem` of /proc/meminfo);
12. ancillary data on a request the service reads: refused with status 1 `BAD`, the connection
   closed, the descriptors closed unused; the service keeps serving;
13. `--io-timeout 1`: an idle connection is closed after about 1 s and its slot freed; a client that
   never reads a large response is cut after the timeout; one that reads slowly but steadily gets
   all of it (the timeout bounds one read or write, not a request);
14. the control line `stats` mid-run: the counters, `mismatches` after a `MISMATCH`, the service
   keeps serving; the runner's `Service.stats`/`Service.drop`;
15. the socket's mode is 0600;
16. `--io-timeout` other than a count from 1 to 86400 and `--threads` above 1024 are usage errors
   (exit 2), as is `--io-timeout` with `--data-roots`.
"""
import os
import random
import select
import socket
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


def par_leaf(data):
    """`leafStmt (dataRoot xs) n` of the data `data` (`n` blocks of 32 bytes) by the C reference:
    `leafItem x = Keccak-256(0x48 ‖ x)`, then levels of `dataNode l r = Keccak-256(0x44 ‖ l ‖ r)`
    over adjacent digests, an odd last one carried up unhashed; the zero digest for no block."""
    n = len(data) // 32
    ds = W.H_many([b"H" + data[o:o + 32] for o in range(0, 32 * n, 32)])
    while len(ds) > 1:
        up = W.H_many([b"D" + ds[k] + ds[k + 1] for k in range(0, len(ds) - 1, 2)])
        ds = up + ds[len(ds) - len(ds) % 2:]
    return W.H(b"L" + (ds[0] if ds else bytes(32)) + W.enc64(n))


def replay(p):
    """Write the control line `replay`; the lines the service prints up to `replay ready`."""
    p.stdin.write(b"replay\n")
    p.stdin.flush()
    lines = []
    while True:
        line = p.stdout.readline().decode()
        if not line:
            raise RuntimeError("service died")
        lines.append(line.rstrip("\n"))
        if lines[-1] == "replay ready":
            return lines


def test_replay(tmp):
    p, info, sock = start(os.path.join(tmp, "svc-replay"))
    traces = [[b"abc", bytes(200)], [], [pattern(n) for n in (0, 103, 104, 300)]]
    c = Client(sock)
    first = [c.call(OP_SIGN, t) for t in traces]
    check([r[0] for r in first] == [0, 0, 0] and [struct.unpack("<I", r[2][32 * len(t):32 * len(t) + 4])[0]
                                                   for r, t in zip(first, traces)] == [0, 1, 2],
          "service run: three SIGNs at indices 0, 1, 2")
    q = b"replay query"
    a = c.query([q])[0]
    # any other control line is ignored (a note on stderr), the service keeps serving
    p.stdin.write(b"hello\n")
    p.stdin.flush()
    check(c.vk() == bytes.fromhex(info["vk"]), "an unknown control line is ignored: the service still serves")
    lines = replay(p)
    key = lines[0].split(" ", 1)[1] if len(lines) == 2 and lines[0].startswith("key ") else ""
    check(len(lines) == 2 and len(key) == 64 and key == key.lower(),
          f"replay prints exactly `key <64 lowercase hex>` and `replay ready`: {[l[:12] for l in lines]}")
    check(bytes.fromhex(key or "00") == PRF_KEY and pykeccak.keccak256(bytes.fromhex(key or "00") + q) == a,
          "the printed key k recomputes a QUERY answer of the service run: Keccak-256(k ‖ q)")
    c2 = Client(sock)
    again = [c2.call(OP_SIGN, t) for t in traces]
    check(again == first, "replay: SIGN of the same three traces in order returns byte-identical responses")
    check(c2.query([q]) == [a] and c2.vk() == bytes.fromhex(info["vk"]), "replay: QUERY and VK unchanged")
    st, _, msg = c2.call(OP_SIGN, [b"never signed"])
    check(st == 4 and b"index 3" in msg and b"no trace" in msg and c2.s.recv(1) == b"",
          f"replay: another trace at index 3 (never signed) is refused with MISMATCH (status {st}, {msg.decode()!r}), "
          "connection closed")
    c2.close()
    lines2 = replay(p)
    check(lines2 == lines, "a second replay prints the same two lines")
    c3 = Client(sock)
    changed = [traces[0][0], bytes(199)]
    st, _, msg = c3.call(OP_SIGN, changed)
    check(st == 4 and b"index 0" in msg and b"differs" in msg,
          f"after a second replay: a changed trace at index 0 is refused with MISMATCH (status {st}, {msg.decode()!r})")
    c3.close()
    replay(p)
    c4 = Client(sock)
    check([c4.call(OP_SIGN, t) for t in traces] == first, "a third replay resets the index to 0 again: identical responses")
    st, _, _ = c4.call(OP_SIGN, traces[0])
    check(st == 4, f"replay: the trace of index 0 at index 3 is refused (status {st}): replay never signs anew")
    c4.close()
    c.close()
    code, out = stop(p)
    stats = {k: int(v) for k, v in (kv.split("=") for kv in next(l for l in out.splitlines() if l.startswith("stats ")).split()[1:])} \
        if "stats " in out else {}
    check(code == 0 and not os.path.exists(sock), f"replay mode: shutdown on stdin EOF (exit {code}), socket removed")
    check((stats.get("signatures"), stats.get("replays"), stats.get("mismatches"), stats.get("refusals")) == (3, 6, 3, 3),
          f"replay statistics: {stats}")


def raw_conn(path):
    """A plain client socket on the service's socket (no `Client` wrapper)."""
    return Client(path).s


def query_req(items):
    body = b"".join(struct.pack("<I", len(q)) + q for q in items)
    return struct.pack("<B3xIQ", OP_QUERY, len(items), len(body)) + body


VK_REQ = struct.pack("<B3xIQ", OP_VK, 0, 0)
BIG_QUERY = query_req([b""] * (1 << 18))          # an 8 MiB response


def park(path, first, fds=()):
    """A dead client: send `first` (whose response it never reads), then its own socket (and `fds`)
    by `SCM_RIGHTS` into the service's receive queue, then close it. The socket lives on only in
    that queue, as when the client's process dies."""
    s = raw_conn(path)
    s.sendall(first)
    time.sleep(0.3)                                # the service thread is now blocked writing
    socket.send_fds(s, [b"\0"], [s.fileno(), *fds])
    s.close()


def eof_within(r, timeout):
    """Whether the read end `r` of a pipe sees end of file (every write end closed) within `timeout`."""
    if not select.select([r], [], [], timeout)[0]:
        return False
    return os.read(r, 1) == b""


def shmem_mib():
    for line in open("/proc/meminfo"):
        if line.startswith("Shmem:"):
            return int(line.split()[1]) // 1024


def wait_live(svc, want, timeout=3.0):
    """Poll `stats` until `live == want` (or the timeout); the last `live`."""
    dl = time.monotonic() + timeout
    while True:
        live = svc.stats()["live"]
        if live == want or time.monotonic() > dl:
            return live
        time.sleep(0.05)


def cap_probe(path):
    """The connections served (a `VK` answered) before the first `CAP` refusal, up to 33."""
    ss, ok = [], 0
    for _ in range(33):
        c = Client(path)
        ss.append(c)
        st, _, _ = c.call(OP_VK)
        if st:
            break
        ok += 1
    for c in ss:
        c.close()
    return ok


def test_hardening(tmp):
    """10.-16.: the deadlines, `drop`, `stats`, no ancillary data, the socket mode, the options."""
    # 10. dead clients hold slots until `drop`
    svc = Service(BIN, os.path.join(tmp, "h-dead")).start()
    sock = svc.socket_path
    check(os.stat(sock).st_mode & 0o777 == 0o600, f"15. the socket's mode is 0600 ({oct(os.stat(sock).st_mode & 0o777)})")
    pipes = []
    for _ in range(3):
        r, w = os.pipe()
        park(sock, BIG_QUERY, [w])
        os.close(w)
        pipes.append(r)
    r, w = os.pipe()
    park(sock, VK_REQ * 2000, [w])
    os.close(w)
    pipes.append(r)
    time.sleep(0.3)
    st0 = svc.stats()
    check(st0["live"] == 4, f"10. four dead clients hold four slots before `drop` (live={st0['live']})")
    check(not any(eof_within(r, 0.1) for r in pipes), "10. their in-flight descriptors are held before `drop`")
    t0 = time.monotonic()
    svc.replay(timeout=10)
    check(time.monotonic() - t0 < 2, f"10. `replay` is ready at once with a dead VK client parked ({time.monotonic() - t0:.2f} s)")
    t0 = time.monotonic()
    live = svc.drop()
    dt = time.monotonic() - t0
    check(live == 0 and dt < 5, f"10. `drop` prints `dropped live=0` ({live}, {dt:.2f} s)")
    check(all(eof_within(r, 2) for r in pipes), "10. after `drop` every descriptor parked in a queue is closed")
    [os.close(r) for r in pipes]
    check(cap_probe(sock) == 32, "10. after `drop` all 32 slots are free again (the 33rd is refused)")
    check(wait_live(svc, 0) == 0 and svc.drop() == 0, "10. no connection left: live=0, a second `drop` prints live=0")
    svc.stop()

    # 11. a parked memfd is freed by `drop`
    svc = Service(BIN, os.path.join(tmp, "h-memfd")).start()
    size = 256 << 20
    base = shmem_mib()
    fd = os.memfd_create("rf-svc-test-pin")
    chunk = b"\x5a" * (1 << 20)
    for _ in range(size >> 20):
        os.write(fd, chunk)
    park(svc.socket_path, BIG_QUERY, [fd])
    os.close(fd)
    time.sleep(0.5)
    parked = shmem_mib() - base
    live = svc.drop()
    time.sleep(0.5)
    after = shmem_mib() - base
    check(parked >= 192 and live == 0 and after <= 64,
          f"11. a 256 MiB memfd parked in the queue of a dead client: Shmem +{parked} MiB, after `drop` (live={live}) +{after} MiB")
    svc.stop()

    # 12. ancillary data is refused, its descriptors closed
    svc = Service(BIN, os.path.join(tmp, "h-anc")).start()
    sock = svc.socket_path
    for first in (True, False):
        c = Client(sock)
        if not first:
            check(c.vk() == svc.vk, "12. a plain VK before the ancillary data is served")
        r, w = os.pipe()
        socket.send_fds(c.s, [VK_REQ], [w])
        os.close(w)
        st, _, msg = c.call(None, raw=b"")
        closed = c.s.recv(1) == b""
        check(st == 1 and b"ancillary" in msg and closed,
              f"12. a request with SCM_RIGHTS ({'the first' if first else 'after a served one'}) is refused "
              f"(status {st}, {msg.decode(errors='replace')!r}), connection closed")
        check(eof_within(r, 2), "12. the descriptor sent is closed by the service, not kept")
        os.close(r)
        c.close()
    check(Client(sock).vk() == svc.vk and wait_live(svc, 0) == 0, "12. the service keeps serving, no slot held")
    stats = svc.stop()
    check(stats.get("refusals") == 2 and stats.get("live") == 0, f"12. two refusals counted: {stats}")

    # 13. --io-timeout 1
    svc = Service(BIN, os.path.join(tmp, "h-timeout"), io_timeout=1).start()
    sock = svc.socket_path
    c = raw_conn(sock)
    c.settimeout(10)
    t0 = time.monotonic()
    got = c.recv(1)
    dt = time.monotonic() - t0
    check(got == b"" and 0.8 <= dt <= 3, f"13. an idle connection is closed after the io timeout ({dt:.2f} s)")
    c.close()
    check(wait_live(svc, 0) == 0, "13. the idle connection's slot is freed")
    c = raw_conn(sock)
    c.sendall(BIG_QUERY)
    time.sleep(3)
    live = svc.stats()["live"]
    c.settimeout(10)
    n = 0
    while True:
        b = c.recv(1 << 20)
        if not b:
            break
        n += len(b)
    c.close()
    check(live == 0 and n < 16 + (1 << 23),
          f"13. a client that never reads an 8 MiB response is cut after the io timeout (live={live}, {n} bytes then end)")
    c = raw_conn(sock)
    c.sendall(BIG_QUERY)
    c.settimeout(10)
    n, t0 = 0, time.monotonic()
    while n < 16 + (1 << 23):
        b = c.recv(1 << 20)
        if not b:
            break
        n += len(b)
        time.sleep(0.3)
    check(n == 16 + (1 << 23), f"13. a client that reads slowly but steadily gets the whole response "
                               f"({n} bytes in {time.monotonic() - t0:.1f} s > the 1 s timeout)")
    c.close()
    svc.stop()

    # 14. stats mid-run
    svc = Service(BIN, os.path.join(tmp, "h-stats")).start()
    c = Client(svc.socket_path)
    c.sign([b"a"])
    s1 = svc.stats()
    keys = ["requests", "queries", "query_bytes", "signatures", "refusals", "replays", "mismatches", "live"]
    check(list(s1) == keys and (s1["requests"], s1["signatures"], s1["mismatches"], s1["live"]) == (1, 1, 0, 1),
          f"14. `stats` mid-run: {s1}")
    svc.replay()
    st, _, msg = Client(svc.socket_path).call(OP_SIGN, [b"b"])
    s2 = svc.stats()
    check(st == 4 and s2["mismatches"] == 1 and s2["refusals"] == 1,
          f"14. `stats` counts the MISMATCH (status {st}): {s2}")
    check(c.vk() == svc.vk, "14. the service keeps serving after `stats`")
    c.close()
    s3 = svc.stop()
    check({k: s3.get(k) for k in keys if k != "live"} == {k: s2[k] for k in keys if k != "live"} | {"requests": s2["requests"] + 1},
          f"14. the final statistics agree: {s3}")

    # 16. usage errors
    d = os.path.join(tmp, "h-usage")
    os.makedirs(d)
    for opt, bad in [("--io-timeout", v) for v in ("x", "", "0", "-1", "1.5", "+3", " 3", "86401", "99999999999999999999")] + \
                    [("--threads", v) for v in ("1025", "4096", "1000000000000")]:
        r = subprocess.run([BIN, "--socket", "u.sock", opt, bad], cwd=d, input="", capture_output=True, text=True, timeout=60)
        check(r.returncode == 2 and "usage" in r.stderr and not os.path.exists(os.path.join(d, "u.sock")),
              f"16. {opt} {bad!r}: a usage error (exit {r.returncode})")
    f = os.path.join(d, "one.bin")
    open(f, "wb").write(bytes(32))
    r = subprocess.run([BIN, "--data-roots", "--io-timeout", "5", f], capture_output=True, text=True, timeout=60)
    check(r.returncode == 2 and r.stdout == "", f"16. --io-timeout with --data-roots: a usage error (exit {r.returncode})")


def test_data_roots(binary, tmp):
    import json
    from rfh import digest as pydigest
    d = os.path.join(tmp, "data-roots")
    os.makedirs(d)

    def put(name, data):
        path = os.path.join(d, name)
        with open(path, "wb") as f:
            f.write(data)
        return path
    kat = json.load(open(os.path.join(ROOT, "tests", "vectors", "data_root.json")))["vectors"]
    check(all(par_leaf(bytes.fromhex(v["data"])).hex() == v["leafStmt"] == pydigest.leaf_digest(bytes.fromhex(v["data"])).hex()
              and pydigest.data_root(pydigest.blocks(bytes.fromhex(v["data"]))).hex() == v["dataRoot"] for v in kat),
          "data roots: the C reference and the pure-Python reference give the known answers of 0 … 7 and 9 blocks")
    rnd = random.Random(2)
    check(all(par_leaf(x) == pydigest.leaf_digest(x) for x in (rnd.randbytes(32 * n) for n in (5, 6, 7, 33))),
          "data roots: the C reference equals the pure-Python reference on 5, 6, 7 and 33 random blocks")
    sizes = [rnd.choice([0, 1, 2, 3, 5, 6, 7, 64, 100, 4095, 4096, 4097, 9000]) for _ in range(60)]
    files = [put(f"f{k}.bin", rnd.randbytes(32 * n)) for k, n in enumerate(sizes)]
    want = "".join(par_leaf(open(f, "rb").read()).hex() + "\n" for f in files)
    outs = []
    for threads in ([], ["--threads", "1"], ["--threads", "7"]):
        r = subprocess.run([binary, "--data-roots"] + threads + files, capture_output=True, text=True, timeout=120)
        outs.append(r.stdout)
        check(r.returncode == 0 and r.stdout == want,
              f"--data-roots {' '.join(threads)}: {len(files)} files (n up to 9000 blocks) equal the reference, in order")
    check(len(set(outs)) == 1, "--data-roots: the same output on 1 and many threads")
    big = put("cap.bin", rnd.randbytes(32 << 20))
    want_big = par_leaf(open(big, "rb").read()).hex() + "\n"
    for threads in (["--threads", "1"], ["--threads", "8"]):
        r = subprocess.run([binary, "--data-roots"] + threads + [big], capture_output=True, text=True, timeout=120)
        check(r.returncode == 0 and r.stdout == want_big,
              f"--data-roots {' '.join(threads)}: one file of leafCap = 2^20 blocks equals the reference")
    empty = put("empty.bin", b"")
    r = subprocess.run([binary, "--data-roots", empty], capture_output=True, text=True, timeout=60)
    check(r.returncode == 0 and r.stdout == pydigest.leaf_stmt(bytes(32), 0).hex() + "\n",
          "--data-roots of an empty file prints leafStmt zero 0")
    r = subprocess.run([binary, "--data-roots"], capture_output=True, text=True, timeout=60)
    check(r.returncode == 0 and r.stdout == "", "--data-roots with no file: exit 0, no output")
    over = put("over.bin", bytes(32 * ((1 << 20) + 1)))
    for what, bad in (("a size not a multiple of 32", put("odd.bin", bytes(33))),
                      ("31 bytes", put("short.bin", bytes(31))),
                      ("n = 2^20 + 1 blocks, above leafCap", over),
                      ("a missing file", os.path.join(d, "missing.bin")),
                      ("a directory", d)):
        r = subprocess.run([binary, "--data-roots", files[0], bad], capture_output=True, text=True, timeout=120)
        check(r.returncode == 2 and r.stdout == "" and "rf-oracle --data-roots" in r.stderr,
              f"--data-roots refuses {what} (after a good file): exit {r.returncode}, nothing on stdout")
    r = subprocess.run([binary, "--data-roots", "--socket", "x.sock", files[0]], capture_output=True, text=True, timeout=60)
    check(r.returncode == 2, f"--data-roots with --socket is a usage error (exit {r.returncode})")
    for bad in ("x", "", "-1", "0", "1.5", "8x", "+3", " 3"):
        for mode in (["--data-roots"], ["--socket", os.path.join(d, "t.sock")]):
            r = subprocess.run([binary, *mode, "--threads", bad, *([files[0]] if mode[0] == "--data-roots" else [])],
                               input="", capture_output=True, text=True, timeout=60)
            check(r.returncode == 2 and r.stdout == "" and "usage" in r.stderr,
                  f"{mode[0]} --threads {bad!r}: refused (exit {r.returncode}), never silently every CPU")
    r = subprocess.run([binary, "--leaves"], input="", capture_output=True, text=True, timeout=60)
    check(r.returncode == 2 and r.stdout == "", f"the old --leaves mode is gone: a usage error (exit {r.returncode})")


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
    count, idxs = [0], []

    def signer():
        cl = Client(s1.socket_path)
        while True:
            st, _, body = cl.call(OP_SIGN, [])
            if st:
                return st
            with lock:
                count[0] += 1
                idxs.append(int.from_bytes(body[:4], "little"))     # an empty trace: the body starts with idx
    res = []
    ths = [threading.Thread(target=lambda: res.append(signer())) for _ in range(8)]
    [t.start() for t in ths]
    [t.join() for t in ths]
    check(count[0] == 1 << 16 and set(res) == {3},
          f"exactly 2^16 signatures, then EXHAUSTED ({count[0]} signed, statuses {set(res)}, {time.time() - t0:.1f} s)")
    check(sorted(idxs) == list(range(1 << 16)),
          "the 2^16 signatures used the indices 0 … 2^16 - 1, each once (one message per index)")
    stats = s1.stop()
    check(stats.get("signatures") == 1 << 16, f"service statistics: {stats}")

    # 8. the runner's leaf hasher
    test_data_roots(RELEASE if os.path.exists(RELEASE) else BIN, tmp)

    # 9. replay mode
    test_replay(tmp)

    # 10.-16. hardening
    test_hardening(tmp)

    print(f"\n{len(FAILS)} failure(s)")
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
