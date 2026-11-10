"""The chain lengths and the random draws of one evaluation (TRUSTED RUNTIME).

**The chain lengths are not drawn per evaluation.** They are one fixed, published sequence, the
season file's `[stream] lengths` (`M + 1` integers: chains 0 and 1 are step 1's two chains, chain
`i ≥ 2` is step `i`'s), the same for every evaluation, every entry and every core commit until the
owner changes it. The sequence was derived once, publicly and reproducibly, by `published_lengths`:
the density proportional to `1/n²` on `[n_lo, n_hi]` (equal expected work per octave), sampled at
uniforms that come from SHA-256 of a public label (no seed was chosen, no draw was discarded).
`tests/harness/test_tv.py` re-derives it and checks that it equals the season file's list.

**The chain starts are drawn fresh per evaluation** (32 bytes each, here) from the operating
system's CSPRNG (`secrets`, which reads `os.urandom`), never from a seeded generator, never reused,
and published only after the run. The service's keys (never published) are likewise fresh per
evaluation, drawn where they are used. The number of steps `M` is one published
season constant.
"""
import hashlib
import secrets


def length(n_lo: int, n_hi: int, u: float) -> int:
    """The inverse CDF of the density proportional to `1/n²` on `[n_lo, n_hi]` at `u`, in doubles,
    rounded to the nearest integer (a tie to the even one: Python's `round`) and clamped."""
    n = round(1.0 / (1.0 / n_lo - u * (1.0 / n_lo - 1.0 / n_hi)))
    return min(n_hi, max(n_lo, n))


def published_uniform(label: str, k: int) -> float:
    """The `k`-th public uniform of `label`: the first 8 bytes of SHA-256(UTF-8 `label` ‖ `k` as an
    8-byte big-endian unsigned integer), read as a big-endian integer, its top 53 bits divided by
    2^53. Every such value is a double exactly, in [0, 1)."""
    h = hashlib.sha256(label.encode() + k.to_bytes(8, "big")).digest()
    return (int.from_bytes(h[:8], "big") >> 11) / (1 << 53)


def published_lengths(label: str, count: int, n_lo: int, n_hi: int):
    """The published chain lengths of `label`: `length(n_lo, n_hi, published_uniform(label, k))` for
    k = 0 … count − 1. Used once to write a season file's `[stream] lengths`, and by the test that
    re-derives it; the runner reads the list from the season file."""
    return [length(n_lo, n_hi, published_uniform(label, k)) for k in range(count)]


def starts(count: int):
    """Fresh chain starts, 32 bytes each, from the OS CSPRNG."""
    return [secrets.token_bytes(32) for _ in range(count)]
