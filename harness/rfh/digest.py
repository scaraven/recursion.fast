"""The runner's digests (TRUSTED RUNTIME): chain ends, leaf and node statements and the tree root,
byte for byte as the contract (`Relation.lean`, `Tree.lean`, hashed with
Keccak-256):

  chainStep d     = Keccak-256(0x43 ‖ d)                 33 bytes, one permutation
  leafStmt h n    = Keccak-256(0x4C ‖ h ‖ enc64 n)       41 bytes
  nodeStmt c1 c2  = Keccak-256(0x4E ‖ c1 ‖ c2)           65 bytes
  treeRoot cs     = adjacent pairs hashed by nodeStmt, level by level (an odd last digest is carried
                    up; one digest is its own root; the empty list has the zero digest)

Keccak-256 is Ethereum's (`rfh/keccak.py`). The chains (millions of permutations per run) are hashed
by the trusted service binary's `rf-oracle --leaves` mode (no key, no socket; `service/src/main.rs`);
the few statement hashes here in pure Python. The runner computes every digest it checks a proof
against from its own secret starts; it never takes a digest from a prover.
"""
import os
import subprocess

from .keccak import keccak256

ZERO = bytes(32)


def enc64(n: int) -> bytes:
    """The 8 little-endian bytes of `n mod 2^64`."""
    return (n % 2 ** 64).to_bytes(8, "little")


def chain_end(s: bytes, n: int) -> bytes:
    """`chainEnd s n`: `chainStep` applied `n` times to `s` (pure Python, for small `n`)."""
    d = s
    for _ in range(n):
        d = keccak256(b"C" + d)
    return d


def leaf_stmt(h: bytes, n: int) -> bytes:
    return keccak256(b"L" + h + enc64(n))


def node_stmt(c1: bytes, c2: bytes) -> bytes:
    return keccak256(b"N" + c1 + c2)


ORACLE = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                      "service", "target", "release", "rf-oracle")


def leaf_digests(starts, n, oracle=None, threads: int = 0, timeout=None):
    """`leafStmt (chainEnd s n) n` for every start; `n` is one length for every start or a list of
    lengths, one per start. Computed by `oracle --leaves` (the service binary: the argument, else the
    environment's `RF_ORACLE_BIN`, else `service/target/release/rf-oracle` of this repository; not
    `RF_ORACLE`, which is the prover's socket) on `threads` threads (default: the binary's), within
    `timeout` seconds (default `max(60, 4 · Σn / 10^6)`; a breach raises); a tiny total (fewer than
    2^12 chain steps) in Python."""
    ns = list(n) if isinstance(n, (list, tuple)) else [n] * len(starts)
    if len(ns) != len(starts) or any(type(k) is not int or k < 0 for k in ns):
        raise ValueError("leaf_digests: one non-negative integer length per start")
    if sum(ns) < 1 << 12:
        return [leaf_stmt(chain_end(s, k), k) for s, k in zip(starts, ns)]
    cmd = [oracle or os.environ.get("RF_ORACLE_BIN") or ORACLE, "--leaves"] + (["--threads", str(threads)] if threads else [])
    if timeout is None:
        timeout = max(60.0, 4 * sum(ns) / 1e6)
    try:
        p = subprocess.run(cmd, input="".join(f"{s.hex()} {k}\n" for s, k in zip(starts, ns)), capture_output=True,
                           text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        raise RuntimeError(f"{cmd[0]} --leaves: no answer within {timeout:.0f} s for {sum(ns)} chain steps") from None
    out = p.stdout.split()
    if p.returncode != 0 or len(out) != len(starts) or any(len(x) != 64 for x in out):
        raise RuntimeError(f"{cmd[0]} --leaves: exit {p.returncode}, {len(out)} of {len(starts)} digests: {p.stderr[-500:]}")
    return [bytes.fromhex(x) for x in out]


def tree_levels(cs):
    """`[cs, treeLevel cs, treeLevel (treeLevel cs), …]` down to one digest."""
    levels = [list(cs)]
    while len(levels[-1]) > 1:
        cur = levels[-1]
        nxt = [node_stmt(cur[i], cur[i + 1]) for i in range(0, len(cur) - 1, 2)]
        if len(cur) % 2:
            nxt.append(cur[-1])
        levels.append(nxt)
    return levels


def tree_root(cs) -> bytes:
    """`treeRoot cs`."""
    return tree_levels(cs)[-1][0] if cs else ZERO
