"""The runner's digests (TRUSTED RUNTIME): chain ends, leaf and node statements and the tree root,
byte for byte as the contract (`Relation.lean`, `Tree.lean`; v3's layouts, unchanged by V4-16):

  chainStep d     = BLAKE2s-256(0x43 ‖ d)                 33 bytes
  leafStmt h n    = BLAKE2s-256(0x4C ‖ h ‖ enc64 n)       41 bytes
  nodeStmt c1 c2  = BLAKE2s-256(0x4E ‖ c1 ‖ c2)           65 bytes
  treeRoot cs     = adjacent pairs hashed by nodeStmt, level by level (an odd last digest is carried
                    up; one digest is its own root; the empty list has the zero digest)

The runner computes every digest it checks a proof against from its own secret starts; it never
takes a digest from a prover.
"""
import hashlib
import multiprocessing
import os
from concurrent.futures import ProcessPoolExecutor

ZERO = bytes(32)


def enc64(n: int) -> bytes:
    """The 8 little-endian bytes of `n mod 2^64`."""
    return (n % 2 ** 64).to_bytes(8, "little")


def b2s(m: bytes) -> bytes:
    """Unkeyed BLAKE2s-256."""
    return hashlib.blake2s(m, digest_size=32).digest()


def chain_end(s: bytes, n: int) -> bytes:
    """`chainEnd s n`: `chainStep` applied `n` times to `s`."""
    h, d = hashlib.blake2s, s
    for _ in range(n):
        d = h(b"C" + d).digest()
    return d


def leaf_stmt(h: bytes, n: int) -> bytes:
    return b2s(b"L" + h + enc64(n))


def node_stmt(c1: bytes, c2: bytes) -> bytes:
    return b2s(b"N" + c1 + c2)


def _leaf_digest(arg):
    s, n = arg
    return leaf_stmt(chain_end(s, n), n)


def leaf_digests(starts, n: int, workers: int = 0):
    """`leafStmt (chainEnd s n) n` for every start, on `workers` processes (default: all CPUs)."""
    jobs = [(s, n) for s in starts]
    workers = workers or os.cpu_count() or 1
    if workers == 1 or len(jobs) * n < 1 << 16:
        return [_leaf_digest(j) for j in jobs]
    with ProcessPoolExecutor(max_workers=min(workers, len(jobs)), mp_context=multiprocessing.get_context("fork")) as ex:
        return list(ex.map(_leaf_digest, jobs))


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
