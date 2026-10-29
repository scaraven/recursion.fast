"""The signed-proof file (`harness/FORMAT.md`, normative; TRUSTED RUNTIME): `π`, the trace and
the signature, every length a u64 little-endian prefix:

  |π| ‖ π ‖ m ‖ (|q_i| ‖ q_i ‖ a_i)_{i<m} ‖ idx ‖ ots_0 … ots_132 ‖ path_0 … path_15

`a_i`, `ots_k` and `path_t` are 32 bytes each. The file ends exactly after `path_15`. The runner
parses files only to build canaries (`canaries`); the binding check of a file is the compiled
`acc` in the badge `verify`, which parses the same format.
"""
import struct
from dataclasses import dataclass, field

LEN, HEIGHT = 133, 16
SIG_BYTES = 8 + 32 * (LEN + HEIGHT)


@dataclass
class Signed:
    pi: bytes
    trace: list = field(default_factory=list)   # [(q: bytes, a: bytes)]
    idx: int = 0
    ots: list = field(default_factory=lambda: [bytes(32)] * LEN)
    path: list = field(default_factory=lambda: [bytes(32)] * HEIGHT)

    def encode(self) -> bytes:
        out = [struct.pack("<Q", len(self.pi)), self.pi, struct.pack("<Q", len(self.trace))]
        for q, a in self.trace:
            out += [struct.pack("<Q", len(q)), q, a]
        out.append(struct.pack("<Q", self.idx))
        out += self.ots + self.path
        return b"".join(out)


def parse(b: bytes):
    """The signed proof `b` encodes, or `None` if `b` is not exactly one encoding."""
    off = 0

    def take(n):
        nonlocal off
        if n > len(b) - off:
            raise ValueError
        off += n
        return b[off - n:off]

    def u64():
        return struct.unpack("<Q", take(8))[0]

    try:
        pi = take(u64())
        m = u64()
        if m > len(b):          # every item takes at least 40 bytes
            return None
        trace = []
        for _ in range(m):
            q = take(u64())
            trace.append((q, take(32)))
        idx = u64()
        ots = [take(32) for _ in range(LEN)]
        path = [take(32) for _ in range(HEIGHT)]
    except ValueError:
        return None
    return Signed(pi, trace, idx, ots, path) if off == len(b) else None


def from_wire(pi: bytes, queries, wire_sign_body: bytes) -> Signed:
    """A signed proof from `π`, the trace's queries and a service `SIGN` response body
    (`answers ‖ idx:u32 ‖ ots ‖ path`, `service/PROTOCOL.md` §2.2)."""
    m = len(queries)
    ans = [wire_sign_body[32 * i:32 * i + 32] for i in range(m)]
    s = wire_sign_body[32 * m:]
    idx = struct.unpack("<I", s[:4])[0]
    ds = [s[4 + 32 * k:36 + 32 * k] for k in range(LEN + HEIGHT)]
    return Signed(pi, list(zip(queries, ans)), idx, ds[:LEN], ds[LEN:])
