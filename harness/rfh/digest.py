"""The runner's digests (TRUSTED RUNTIME): data roots, leaf and node statements and the stream's
statements, byte for byte as the contract (`Relation.lean`, hashed with Keccak-256):

  x_j             a block of a leaf's data: 32 bytes, j < n
  leafItem x      = Keccak-256(0x48 ‖ x)                 33 bytes, one permutation
  dataNode l r    = Keccak-256(0x44 ‖ l ‖ r)             65 bytes, one permutation
  dataLevel ds    = adjacent digests paired by dataNode; an odd last digest is carried up unhashed
  dataRoot xs     = dataLevel applied |xs| times to map leafItem xs, then the first digest
                    (the zero digest for no block, leafItem x for one block)
  leafStmt h n    = Keccak-256(0x4C ‖ h ‖ enc64 n)       41 bytes
  nodeStmt c1 c2  = Keccak-256(0x4E ‖ c1 ‖ c2)           65 bytes
  the stream      L_i = leafStmt (dataRoot xs_i) n,  c_1 = L_1,  c_i = nodeStmt c_{i-1} L_i

Keccak-256 is Ethereum's (`rfh/keccak.py`). The leaves (about 2^19 permutations per step) are
hashed by the trusted service binary's `rf-oracle --data-roots` mode (no key, no socket;
`service/src/main.rs`), each tree spread over its threads; a tiny total and the few statement
hashes here in pure Python, which is also the reference the service's and the toy prover's
known-answer tests are pinned to (`tests/vectors/data_root.json`). The runner computes every digest
it checks a proof against from its own data (`rfh/draws.py` `leaf_data`), before the first
request; it never takes a digest from a prover.
"""
import os
import subprocess

from .keccak import keccak256

ZERO = bytes(32)
BLOCK = 32                # bytes per block of a leaf's data
LEAF_CAP = 1 << 20        # the contract's leafCap: the most blocks a leaf statement may cover


def enc64(n: int) -> bytes:
    """The 8 little-endian bytes of `n mod 2^64`."""
    return (n % 2 ** 64).to_bytes(8, "little")


def blocks(data: bytes):
    """The 32-byte blocks of a leaf's data file (its size a multiple of 32, else a ValueError)."""
    if len(data) % BLOCK:
        raise ValueError(f"leaf data of {len(data)} bytes, not a multiple of {BLOCK}")
    return [data[o:o + BLOCK] for o in range(0, len(data), BLOCK)]


def leaf_item(x: bytes) -> bytes:
    """`leafItem x = Keccak-256(0x48 ‖ x)` of one 32-byte block."""
    assert len(x) == BLOCK
    return keccak256(b"H" + x)


def data_node(l: bytes, r: bytes) -> bytes:
    """`dataNode l r = Keccak-256(0x44 ‖ l ‖ r)`."""
    return keccak256(b"D" + l + r)


def data_level(ds):
    """`dataLevel`: adjacent digests paired by `dataNode`, an odd last one carried up unhashed."""
    out = [data_node(ds[k], ds[k + 1]) for k in range(0, len(ds) - 1, 2)]
    if len(ds) % 2:
        out.append(ds[-1])
    return out


def data_root(xs) -> bytes:
    """`dataRoot xs` of a list of 32-byte blocks (pure Python, the reference): `dataLevel` from the
    block hashes until one digest is left (`|xs|` levels reach it, and one digest is a fixed
    point); the zero digest for no block."""
    ds = [leaf_item(x) for x in xs]
    if not ds:
        return ZERO
    while len(ds) > 1:
        ds = data_level(ds)
    return ds[0]


def leaf_stmt(h: bytes, n: int) -> bytes:
    return keccak256(b"L" + h + enc64(n))


def node_stmt(c1: bytes, c2: bytes) -> bytes:
    return keccak256(b"N" + c1 + c2)


def leaf_digest(xs) -> bytes:
    """`leafStmt (dataRoot xs) |xs|` in pure Python, `xs` a list of blocks or the data's bytes."""
    if isinstance(xs, (bytes, bytearray)):
        xs = blocks(bytes(xs))
    return leaf_stmt(data_root(xs), len(xs))


def permutations(n: int) -> int:
    """Keccak-f permutations of `dataRoot` over `n` blocks: `n` block hashes and `n − 1` nodes."""
    return max(2 * n - 1, 0)


ORACLE = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                      "service", "target", "release", "rf-oracle")


def leaf_digests(paths, oracle=None, threads: int = 0, timeout=None):
    """`leafStmt (dataRoot xs) n` of every leaf data file in `paths` (`n` = its size / 32, at most
    `LEAF_CAP`; a size that is not a multiple of 32 or above the cap raises a ValueError). Computed
    by `oracle --data-roots` (the service binary: the argument, else the environment's
    `RF_ORACLE_BIN`, else `service/target/release/rf-oracle` of this repository; not `RF_ORACLE`,
    which is the prover's socket) on `threads` threads (default: the binary's), within `timeout`
    seconds (default `max(60, 4 · Σ permutations / 10^6)`; a breach raises); a tiny total (fewer
    than 2^12 permutations over all files) in Python."""
    paths = list(paths)
    ns = []
    for p in paths:
        size = os.path.getsize(p)
        if size % BLOCK or size // BLOCK > LEAF_CAP:
            raise ValueError(f"leaf_digests: {p}: {size} bytes, not a whole number of at most "
                             f"leafCap = 2^20 blocks of {BLOCK} bytes")
        ns.append(size // BLOCK)
    work = sum(permutations(k) for k in ns)
    if work < 1 << 12:
        return [leaf_digest(open(p, "rb").read()) for p in paths]
    if not paths:
        return []
    cmd = [oracle or os.environ.get("RF_ORACLE_BIN") or ORACLE, "--data-roots"] + \
          (["--threads", str(threads)] if threads else []) + [os.path.abspath(p) for p in paths]
    if timeout is None:
        timeout = max(60.0, 4 * work / 1e6)
    try:
        p = subprocess.run(cmd, stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        raise RuntimeError(f"{cmd[0]} --data-roots: no answer within {timeout:.0f} s for {work} permutations") from None
    out = p.stdout.split()
    if p.returncode != 0 or len(out) != len(paths) or any(len(x) != 64 for x in out):
        raise RuntimeError(f"{cmd[0]} --data-roots: exit {p.returncode}, {len(out)} of {len(paths)} digests: "
                           f"{p.stderr[-500:]}")
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
