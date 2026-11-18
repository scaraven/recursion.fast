"""The runner's digests (TRUSTED RUNTIME): leaf values, leaf and node statements and the stream's
statements, byte for byte as the contract (`Relation.lean`, hashed with Keccak-256):

  leafItem s j    = Keccak-256(0x48 ‖ s ‖ enc64 j)       41 bytes, one permutation
  leafValue s n   = leafItem s 0 ⊕ … ⊕ leafItem s (n−1)  (the zero digest for n = 0)
  leafStmt h n    = Keccak-256(0x4C ‖ h ‖ enc64 n)       41 bytes
  nodeStmt c1 c2  = Keccak-256(0x4E ‖ c1 ‖ c2)           65 bytes
  the stream      L_i = leafStmt (leafValue s_i n) n,  c_1 = L_1,  c_i = nodeStmt c_{i-1} L_i

Keccak-256 is Ethereum's (`rfh/keccak.py`). The leaves (millions of permutations per run) are hashed
by the trusted service binary's `rf-oracle --leaves` mode (no key, no socket; `service/src/main.rs`),
the hashes of one leaf spread over its threads; a tiny total and the few statement hashes here in
pure Python, which is also the reference the service's known-answer tests are pinned to. The runner
computes every digest it checks a proof against from its own secret seeds; it never takes a digest
from a prover.
"""
import os
import subprocess

from .keccak import keccak256

ZERO = bytes(32)
LEAF_CAP = 1 << 22        # the contract's leafCap


def enc64(n: int) -> bytes:
    """The 8 little-endian bytes of `n mod 2^64`."""
    return (n % 2 ** 64).to_bytes(8, "little")


def leaf_item(s: bytes, j: int) -> bytes:
    return keccak256(b"H" + s + enc64(j))


def leaf_value(s: bytes, n: int) -> bytes:
    """`leafValue s n`: the XOR of `leafItem s j` over `j < n` (pure Python, for small `n`)."""
    acc = 0
    for j in range(n):
        acc ^= int.from_bytes(leaf_item(s, j), "little")
    return acc.to_bytes(32, "little")


def leaf_stmt(h: bytes, n: int) -> bytes:
    return keccak256(b"L" + h + enc64(n))


def node_stmt(c1: bytes, c2: bytes) -> bytes:
    return keccak256(b"N" + c1 + c2)


def leaf_digest(s: bytes, n: int) -> bytes:
    """`leafStmt (leafValue s n) n` in pure Python."""
    return leaf_stmt(leaf_value(s, n), n)


ORACLE = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                      "service", "target", "release", "rf-oracle")


def leaf_digests(seeds, n, oracle=None, threads: int = 0, timeout=None):
    """`leafStmt (leafValue s n) n` for every seed; `n` is one count for every seed or a list, one per
    seed. Computed by `oracle --leaves` (the service binary: the argument, else the environment's
    `RF_ORACLE_BIN`, else `service/target/release/rf-oracle` of this repository; not `RF_ORACLE`,
    which is the prover's socket) on `threads` threads (default: the binary's), within `timeout`
    seconds (default `max(60, 4 · Σn / 10^6)`; a breach raises); a tiny total (fewer than 2^12
    hashes) in Python."""
    ns = list(n) if isinstance(n, (list, tuple)) else [n] * len(seeds)
    if len(ns) != len(seeds) or any(type(k) is not int or k < 0 for k in ns):
        raise ValueError("leaf_digests: one non-negative integer count per seed")
    if sum(ns) < 1 << 12:
        return [leaf_digest(s, k) for s, k in zip(seeds, ns)]
    cmd = [oracle or os.environ.get("RF_ORACLE_BIN") or ORACLE, "--leaves"] + (["--threads", str(threads)] if threads else [])
    if timeout is None:
        timeout = max(60.0, 4 * sum(ns) / 1e6)
    try:
        p = subprocess.run(cmd, input="".join(f"{s.hex()} {k}\n" for s, k in zip(seeds, ns)), capture_output=True,
                           text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        raise RuntimeError(f"{cmd[0]} --leaves: no answer within {timeout:.0f} s for {sum(ns)} hashes") from None
    out = p.stdout.split()
    if p.returncode != 0 or len(out) != len(seeds) or any(len(x) != 64 for x in out):
        raise RuntimeError(f"{cmd[0]} --leaves: exit {p.returncode}, {len(out)} of {len(seeds)} digests: {p.stderr[-500:]}")
    return [bytes.fromhex(x) for x in out]


def stream_statements(leaves):
    """The stream's statements from its leaf statements `L_1 … L_M`, one per step: `(c, first)`,
    lists over the steps: the output statements `c_1 = L_1`, `c_i = nodeStmt c_{i-1} L_i`, and the
    first child of each `c_i` (the statement canary `first-child`): `c_{i-1}` for `i ≥ 2`, None
    for `i = 1` (a leaf has no child)."""
    c, first = [], []
    for i, L in enumerate(leaves):
        first.append(c[-1] if i else None)
        c.append(node_stmt(c[-1], L) if i else L)
    return c, first
