"""The random draws of one evaluation (TRUSTED RUNTIME).

**The shape is not drawn.** Every chain has the season file's one length `[stream] n` (the
contract's `chainCap = 2^20` in season 1), every step `[stream] chains` of them, and the stream
`[stream] M` steps: published constants, the same for every evaluation, every entry and every core
commit until the owner changes them.

**The chain starts are drawn fresh per evaluation** (32 bytes each, here) from the operating
system's CSPRNG (`secrets`, which reads `os.urandom`), never from a seeded generator, never reused,
and published only after the run. The service's keys are likewise fresh per evaluation, drawn where
they are used; its PRF key is revealed to the runner (and given to the timed passes) only after the
service run, its signing seed never.
"""
import secrets


def starts(count: int):
    """Fresh chain starts, 32 bytes each, from the OS CSPRNG."""
    return [secrets.token_bytes(32) for _ in range(count)]
