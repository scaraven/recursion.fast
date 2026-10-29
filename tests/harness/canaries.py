"""The organiser's canaries (core CI only, never in an evaluation; V4-A9). Mutations of an accepted
signed proof that `acc` rejects before the entry's `V` decides anything: they test the strict file
parser (`harness/badge/Common.lean.in`) and the trace digest and signature check of the contract's
`acc` (`traceDigest`, `SigOk`), which are organiser code, so they run once per harness commit:
`tests/harness/smoke.py` through the witness-sending entry's compiled badge, and
`tests/harness/accprobe/run.py` through a badge whose verifier asks `2^16` queries.

The per-entry canaries are the statement canaries of `harness/rfh/checks.py`. The `pi+1` and `pi-1`
canaries (a byte appended to or removed from `π`) are gone: they tested non-malleability, which no
rule requires (V4-A9).
"""
from rfh import signed


def organiser_canaries(data: bytes):
    """(name, file bytes) of every mutation of the accepted file `data` that `acc` must reject for its
    statement: a byte appended to or removed from the file; one answer or one query of the trace
    changed (if the trace is not empty); a trace entry appended; a chain value or the index of the
    signature changed."""
    s = signed.parse(data)
    out = [("file+1", data + b"\x00"), ("file-1", data[:-1])]
    if s is None:
        return out
    if s.trace:
        q, a = s.trace[0]
        tr = [(q, bytes([a[0] ^ 1]) + a[1:])] + s.trace[1:]
        out.append(("trace-answer", signed.Signed(s.pi, tr, s.idx, s.ots, s.path).encode()))
        q2 = bytes([q[0] ^ 1]) + q[1:] if q else b"\x00"      # RB-m9: a changed query
        out.append(("trace-query", signed.Signed(s.pi, [(q2, a)] + s.trace[1:], s.idx, s.ots, s.path).encode()))
    out.append(("trace-extra", signed.Signed(s.pi, s.trace + [(b"", bytes(32))], s.idx, s.ots, s.path).encode()))
    ots = [bytes([s.ots[0][0] ^ 1]) + s.ots[0][1:]] + s.ots[1:]
    out.append(("sig-ots", signed.Signed(s.pi, s.trace, s.idx, ots, s.path).encode()))
    out.append(("sig-idx", signed.Signed(s.pi, s.trace, s.idx ^ 1, s.ots, s.path).encode()))
    return out
