"""The random draws of one evaluation (TRUSTED RUNTIME; V4-A11 §3, as amended by §11).

Every draw comes from the operating system's CSPRNG (`secrets`, which reads `os.urandom`), fresh per
evaluation, never from a seeded generator, never reused, and published only after the run with the
realised values. Only the distributions are public:

* `M = M_min + G`, `G` geometric on `{0, 1, …}` with mean `mean_extra` (memoryless: each further
  step is drawn with probability `mean_extra / (mean_extra + 1)`), truncated at `M_cap`;
* chain lengths i.i.d. with density proportional to `1/n²` on `[n_lo, n_hi]` (equal expected work
  per octave), by inverse CDF `n = 1 / (1/n_lo − u·(1/n_lo − 1/n_hi))`, rounded (no stratification,
  §11 simplification 2);
* chain starts: 32 bytes each.
"""
import secrets


def uniform() -> float:
    """A uniform draw in the open interval (0, 1), 53 bits."""
    return (secrets.randbits(53) + 0.5) / (1 << 53)


def draw_M(M_min: int, mean_extra: int, M_cap: int) -> int:
    """`min(M_min + G, M_cap)`: each further step with probability `mean_extra / (mean_extra + 1)`,
    exactly (an integer draw per step, no floating point)."""
    M = M_min
    while M < M_cap and secrets.randbelow(mean_extra + 1) != 0:
        M += 1
    return M


def length(n_lo: int, n_hi: int, u: float) -> int:
    """The inverse CDF of the density proportional to `1/n²` on `[n_lo, n_hi]` at `u`, rounded."""
    n = round(1.0 / (1.0 / n_lo - u * (1.0 / n_lo - 1.0 / n_hi)))
    return min(n_hi, max(n_lo, n))


def lengths(count: int, n_lo: int, n_hi: int):
    return [length(n_lo, n_hi, uniform()) for _ in range(count)]


def starts(count: int):
    return [secrets.token_bytes(32) for _ in range(count)]
