"""The random draws of one evaluation (TRUSTED RUNTIME; V4-A11 §3, as amended by §11).

Every draw comes from the operating system's CSPRNG (`secrets`, which reads `os.urandom`), fresh per
evaluation, never from a seeded generator, never reused, and published only after the run with the
realised values. Only the distributions are public. The number of steps `M` is not drawn: it is one
published season constant, the same for every entry and evaluation (`season.toml`, the user's
decision of 2026-10-29).

* chain lengths i.i.d. with density proportional to `1/n²` on `[n_lo, n_hi]` (equal expected work
  per octave), by inverse CDF `n = 1 / (1/n_lo − u·(1/n_lo − 1/n_hi))`, rounded (no stratification,
  §11 simplification 2);
* chain starts: 32 bytes each.

A length goes through a float on its way to an integer (review m-10); the realised integers, which
the result publishes (`stream.lengths`), are what the evaluation used.
"""
import secrets


def uniform() -> float:
    """A uniform draw in the open interval (0, 1), 53 bits."""
    return (secrets.randbits(53) + 0.5) / (1 << 53)


def length(n_lo: int, n_hi: int, u: float) -> int:
    """The inverse CDF of the density proportional to `1/n²` on `[n_lo, n_hi]` at `u`, rounded."""
    n = round(1.0 / (1.0 / n_lo - u * (1.0 / n_lo - 1.0 / n_hi)))
    return min(n_hi, max(n_lo, n))


def lengths(count: int, n_lo: int, n_hi: int):
    return [length(n_lo, n_hi, uniform()) for _ in range(count)]


def starts(count: int):
    return [secrets.token_bytes(32) for _ in range(count)]
