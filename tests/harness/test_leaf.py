#!/usr/bin/env python3
"""The committed-data leaf in the runner (`harness/rfh/bench.py`, `digest.py`, `draws.py`) and in the
toy prover (`harness/toy-prover/toy.c`), with real sandboxes and a real service.

  python3 tests/harness/test_leaf.py [RF_ORACLE_BINARY]

1. Known answers: the shared vectors `tests/vectors/data_root.json` (0 … 4 blocks; the same ones the
   service's `cargo test` and the Lean controls check) are the pure-Python reference's, and the toy
   prover's C `dataRoot` (a `-DTEST_DATAROOT` test build of `toy.c`, not a mode of the shipped
   prover) gives them and equals the Python reference on 1, 2, 3, 6 and 64 random blocks.
2. The inputs, through `Bench.inputs` and `Bench.one` (a real sandbox, a real service): before `go`
   neither `leaf.bin` nor `leaf.json` is in /work; after it `leaf.bin` holds exactly the runner's data
   of the step (`32 n` bytes) and `leaf.json` is `{"n": n}`; a second request of the step (as in a
   timed pass) receives the same bytes.
3. The data directory (`Bench.leafdata`, beside the store) appears in no mount of a request's sandbox,
   of `prover setup`'s or of a badge run's (their `/proc/self/mountinfo`).
4. Statements from the runner's data: the toy prover's leaf proof, run in the sandbox on the staged
   inputs, is `u64 0 ‖ u64 n ‖ x_0 … x_(n−1)` (the library's witness-sending layout), and the mock
   badge accepts it against `leafStmt (dataRoot xs) n` computed by the runner from its own file, and
   rejects it against another step's statement; the `BROKEN_LEAF` toy (one bit of one block flipped)
   is rejected against the runner's statement.
"""
import json
import os
import random
import shutil
import struct
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "harness"))
sys.path.insert(0, os.path.join(ROOT, "harness", "rfh"))          # `signed`, as the mock badge imports it
sys.path.insert(0, os.path.join(ROOT, "tests", "service"))        # `wots_ref`
sys.path.insert(0, os.path.join(HERE, "mock_badge"))
from rfh import digest, draws  # noqa: E402
from rfh.bench import Bench, Params  # noqa: E402
from rfh.checks import Badge  # noqa: E402
from rfh.prover import Run  # noqa: E402
from rfh.service import Service  # noqa: E402
import mock_acc  # noqa: E402

BIN = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "service", "target", "release", "rf-oracle")
TOY = os.path.join(ROOT, "harness", "toy-prover", "toy.c")
FAILS = []


def check(cond, what):
    print(("ok   " if cond else "FAIL ") + what, flush=True)
    if not cond:
        FAILS.append(what)


def gcc(out, src, *flags):
    subprocess.run(["gcc", "-O2", "-w", *flags, "-o", out, src], check=True, timeout=120)
    return out


PROBE = r'''#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
static char *slurp(const char *p, size_t *n) {
    FILE *f = fopen(p, "rb"); char *b = NULL; size_t k; *n = 0;
    if (!f) return NULL;
    char t[65536];
    while ((k = fread(t, 1, sizeof t, f)) > 0) { b = realloc(b, *n + k); memcpy(b + *n, t, k); *n += k; }
    fclose(f); return b ? b : calloc(1, 1);
}
static void put(FILE *f, const char *b, size_t n) {
    unsigned long long m = n; fwrite(&m, 8, 1, f); if (n) fwrite(b, 1, n, f);
}
int main(int argc, char **argv) {
    size_t nm, nb, nj;
    if (argc != 3 || chdir(argv[2])) return 2;
    char *mi = slurp("/proc/self/mountinfo", &nm);
    if (!strcmp(argv[1], "setup")) { FILE *f = fopen("mountinfo", "wb"); fwrite(mi, 1, nm, f); fclose(f); return 0; }
    char pre = '0' + (access("leaf.bin", F_OK) == 0) + 2 * (access("leaf.json", F_OK) == 0);
    puts("ready"); fflush(stdout);
    char g[8]; if (!fgets(g, sizeof g, stdin)) return 9;
    char *b = slurp("leaf.bin", &nb), *j = slurp("leaf.json", &nj);
    FILE *f = fopen("proof.bin", "wb");
    fputc(pre, f); put(f, mi, nm); put(f, j, nj); put(f, b, nb); fclose(f);
    puts("done"); fflush(stdout); return 0;
}
'''


def fields(data):
    """The probe's proof: (pre, mountinfo, leaf.json, leaf.bin)."""
    pre, o, out = chr(data[0]), 1, []
    for _ in range(3):
        n = struct.unpack("<Q", data[o:o + 8])[0]
        out.append(data[o + 8:o + 8 + n])
        o += 8 + n
    return (pre, *out)


def bench(tmp, bindir, n):
    """A Bench over the smoke season with leaves of `n` blocks, its real `inputs`, `one` and data files."""
    b = Bench.__new__(Bench)
    b.p = Params.load(os.path.join(ROOT, "harness", "smoke.toml"))
    b.p.n = n
    b.work = os.path.join(tmp, f"work-{os.path.basename(bindir)}")
    b.store, b.leafdata = os.path.join(b.work, "store"), os.path.join(b.work, "leafdata")
    os.makedirs(b.store)
    b.run = Run(bindir, os.path.join(b.work, "setup"), "256M")
    os.makedirs(b.run.setup_dir)
    b.req_root, b.deadline, b.log = None, None, (lambda m: None)
    return b


def main():
    tmp = tempfile.mkdtemp(prefix="rf-leaf-test-", dir=os.environ.get("RF_TEST_TMP"))
    print(f"tests in {tmp}")
    rnd = random.Random(5)

    # 1. the known answers; the toy's C dataRoot
    kat = json.load(open(os.path.join(ROOT, "tests", "vectors", "data_root.json")))["vectors"]
    check([v["n"] for v in kat] == [0, 1, 2, 3, 4]
          and all(digest.data_root(digest.blocks(bytes.fromhex(v["data"]))).hex() == v["dataRoot"]
                  and digest.leaf_stmt(bytes.fromhex(v["dataRoot"]), v["n"]).hex() == v["leafStmt"]
                  and bytes.fromhex(v["data"]) == bytes(i % 256 for i in range(32 * v["n"]))
                  and [digest.leaf_item(x).hex() for x in digest.blocks(bytes.fromhex(v["data"]))] == v["leafItems"]
                  for v in kat),
          "tests/vectors/data_root.json: the pure-Python reference's dataRoot and leafStmt of 0 … 4 pattern blocks")
    dr = gcc(os.path.join(tmp, "toy-dataroot"), TOY, "-DTEST_DATAROOT")

    def c_root(data):
        path = os.path.join(tmp, "dr.bin")
        open(path, "wb").write(data)
        out = subprocess.run([dr, path], capture_output=True, text=True, timeout=60, check=True).stdout.split()
        return out
    check(all(c_root(bytes.fromhex(v["data"])) == [v["dataRoot"], v["leafStmt"]] for v in kat),
          "the toy's C dataRoot gives the known answers of 0 … 4 blocks")
    for n in (1, 2, 3, 6, 64):
        x = rnd.randbytes(32 * n)
        r = digest.data_root(digest.blocks(x))
        check(c_root(x) == [r.hex(), digest.leaf_stmt(r, n).hex()], f"the toy's C dataRoot equals Python's on {n} random blocks")

    # 2., 3. the inputs and the mounts, through a probe prover in the real sandbox
    pdir = os.path.join(tmp, "probe")
    os.makedirs(pdir)
    open(os.path.join(tmp, "probe.c"), "w").write(PROBE)
    gcc(os.path.join(pdir, "prover"), os.path.join(tmp, "probe.c"), "-static")
    svc = Service(BIN, os.path.join(tmp, "svc", "stream")).start()
    try:
        n = 1 << 18
        b = bench(tmp, pdir, n)
        seeds = draws.starts(2)
        data = b.write_leaf_data(seeds)
        ld = os.path.realpath(b.leafdata)
        stmts = digest.stream_statements(digest.leaf_digests(data, BIN))[0]
        check(all(open(p, "rb").read() == draws.leaf_data(s, n) for p, s in zip(data, seeds))
              and os.path.dirname(ld) == os.path.realpath(b.work) and not ld.startswith(os.path.realpath(b.store) + os.sep),
              "the runner's data files: leafdata/step{1,2}.bin = SHAKE-256 expansions of the seeds, beside the store")
        got = []
        for tag, i in (("service2", 2), ("timed1-step2", 2), ("service1", 1)):
            kind, ins = b.inputs(i, data, stmts, b"prev" if i > 1 else None)
            r = b.one(svc, tag, kind, ins)
            got.append(fields(r.proof))
        (pre, mi, js, xs), again, first = got
        want = open(data[1], "rb").read()
        check(pre == "0" and again[0] == "0" and first[0] == "0",
              "before `go` neither leaf.bin nor leaf.json is in /work (the inputs are staged outside the sandbox)")
        check(xs == want and len(xs) == 32 * n and json.loads(js) == {"n": n},
              f"after `go`, leaf.bin is the runner's data of the step ({len(xs)} bytes = 32 n) and leaf.json is {{\"n\": n}}")
        check(again[2:] == (js, xs) and first[3] == open(data[0], "rb").read() and first[3] != xs,
              "a second request of the step (a timed pass's) receives the same leaf.json and leaf.bin; step 1 its own")
        check(b" /work " in mi and ld.encode() not in mi and b"leafdata" not in mi and all(ld.encode() not in g[1] for g in got),
              "the data directory appears in no mount of a request's sandbox (/proc/self/mountinfo, which lists /work)")
        ok, _, _ = b.run.setup(60)
        smi = open(os.path.join(b.run.setup_dir, "mountinfo"), "rb").read()
        check(ok and b"/setup" in smi and ld.encode() not in smi and b"leafdata" not in smi,
              "the data directory appears in no mount of `prover setup`'s sandbox")
        bdir = os.path.join(tmp, "badge")
        os.makedirs(bdir)
        with open(os.path.join(bdir, "verify"), "w") as f:
            f.write("#!/bin/sh\nwhile read vk c path; do\n"
                    f"  if grep -q -e '{ld}' -e leafdata /proc/self/mountinfo; then echo reject 1; "
                    "elif grep -q ' /store ' /proc/self/mountinfo; then echo accept 1; else echo reject 2; fi\ndone\n")
        os.chmod(os.path.join(bdir, "verify"), 0o755)
        open(os.path.join(b.store, "x.bin"), "wb").write(b"x")
        badge = Badge(bdir, "256M", os.path.join(tmp, "badge-scratch"))
        os.makedirs(badge.scratch)
        check([ok for ok, _ in badge.verify([(b"v" * 32, b"c" * 32, "x.bin")], b.store, timeout=30)] == [True],
              "the data directory appears in no mount of a badge run's sandbox (which binds the store)")

        # 4. the toy prover on the runner's data: the forced layout, accepted against the runner's statement
        vk = svc.vk
        for flag, accepted in ((None, True), ("BROKEN_LEAF", False)):
            tdir = os.path.join(tmp, f"toy-{flag or 'honest'}")
            os.makedirs(tdir)
            gcc(os.path.join(tdir, "prover"), TOY, "-static", *([f"-D{flag}"] if flag else []))
            t = bench(tmp, tdir, 6)
            tdata = t.write_leaf_data(draws.starts(2))
            L = digest.leaf_digests(tdata, BIN)
            kind, ins = t.inputs(1, tdata, L, None)
            r = t.one(svc, "service1", kind, ins)
            s = mock_acc.signed.parse(r.proof)
            x = open(tdata[0], "rb").read()
            layout = s is not None and s.pi[:16] == struct.pack("<QQ", 0, 6) and len(s.pi) == 16 + 32 * 6
            if flag is None:
                check(layout and s.pi[16:] == x, "the toy's leaf proof is u64 0 ‖ u64 n ‖ x_0 … x_(n−1), the runner's data")
                check(mock_acc.acc(vk, L[0], r.proof) and not mock_acc.acc(vk, L[1], r.proof),
                      "the mock badge accepts it against leafStmt (dataRoot xs) n from the runner's file, not against "
                      "another step's statement")
            else:
                check(layout and s.pi[16:] != x and sum(bin(p ^ q).count("1") for p, q in zip(s.pi[16:], x)) == 1
                      and not mock_acc.acc(vk, L[0], r.proof),
                      "BROKEN_LEAF (one bit of one block flipped) is rejected against the runner's statement")
    finally:
        svc.stop()
    shutil.rmtree(tmp, ignore_errors=True)
    print(f"\n{len(FAILS)} failure(s)")
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
