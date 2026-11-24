"""The random draws of one evaluation (TRUSTED RUNTIME).

**The shape is not drawn.** Every step proves one leaf of the season file's one size `[stream] n`
(`2^17` blocks of 32 bytes in season 1, at most the contract's `leafCap = 2^20`), and the stream
has `[stream] M` steps: published constants, the same for every evaluation, every entry and every
core commit until the owner changes them.

**The leaf seeds are drawn fresh per evaluation** (32 bytes each, here) from the operating
system's CSPRNG (`secrets`, which reads `os.urandom`), never from a seeded generator, never reused,
and published only after the run. Each seed `s_i` is expanded into step `i`'s data (`leaf_data`):
`SHAKE-256(DOMAIN ‖ s_i)` truncated to `32 · n` bytes, the blocks `x_0 ‖ … ‖ x_(n−1)`. A prover
sees only the data (`leaf.bin`), never the seed; the result publishes the seeds and the expansion
(`LEAF_DATA`) after the run, so anyone can regenerate the data and recompute every statement. The
service's keys are likewise fresh per evaluation, drawn where they are used; its PRF key is
revealed to the runner (and given to the timed passes) only after the service run, its signing
seed never.
"""
import hashlib
import secrets

DOMAIN = b"recursion.fast/leaf-data/v1"
LEAF_DATA = {"xof": "shake256", "domain": DOMAIN.decode()}     # published as `stream.leaf_data`


def starts(count: int):
    """Fresh seeds, 32 bytes each, from the OS CSPRNG."""
    return [secrets.token_bytes(32) for _ in range(count)]


def leaf_data(seed: bytes, n: int) -> bytes:
    """A step's data: `SHAKE-256(DOMAIN ‖ seed)` truncated to `32 · n` bytes (`n` blocks)."""
    assert len(seed) == 32 and type(n) is int and n >= 0
    return hashlib.shake_256(DOMAIN + seed).digest(32 * n)
