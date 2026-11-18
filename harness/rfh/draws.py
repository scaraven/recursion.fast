"""The random draws of one evaluation (TRUSTED RUNTIME).

**The shape is not drawn.** Every step proves one leaf of the season file's one size `[stream] n`
(the contract's `leafCap = 2^22` in season 1), and the stream has `[stream] M` steps: published
constants, the same for every evaluation, every entry and every core commit until the owner changes
them.

**The leaf seeds are drawn fresh per evaluation** (32 bytes each, here) from the operating
system's CSPRNG (`secrets`, which reads `os.urandom`), never from a seeded generator, never reused,
and published only after the run. The service's keys are likewise fresh per evaluation, drawn where
they are used; its PRF key is revealed to the runner (and given to the timed passes) only after the
service run, its signing seed never.
"""
import secrets


def starts(count: int):
    """Fresh seeds, 32 bytes each, from the OS CSPRNG."""
    return [secrets.token_bytes(32) for _ in range(count)]
