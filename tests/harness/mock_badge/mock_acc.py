"""A Python stand-in for the Lean badge (pre-merge testing of the runner only; never used to judge
an entry): `acc` for the toy prover's placeholder witness-sending encoding, with `SigOk` and the
trace digest from tests/service/wots_ref.py and the file format from harness/rfh/signed.py. Keccak-256
is wots_ref's `H` (tests/service/keccak_ref.c, else harness/rfh/keccak.py); the smoke copies them
beside this file, `keccak.py` as `rfh/keccak.py`."""
import functools
import struct
import wots_ref as W
import signed

CHAIN_CAP, QUERY_CAP = 1 << 20, 1 << 20
WORD = 1 << 64          # no proof cap; |π| must fit a word


def H(b):
    return W.H(b)


@functools.lru_cache(maxsize=None)
def chain_end(s, n):
    for _ in range(n):
        s = H(b"C" + s)
    return s


def leaf_stmt(h, n):
    return H(b"L" + h + struct.pack("<Q", n))


def node_stmt(a, b):
    return H(b"N" + a + b)


def u64(b, o):
    return struct.unpack("<Q", b[o:o + 8])[0]


def signed_words(pi, o):
    """A child in `signedWords` bytes at offset o: (Signed, next offset) or None."""
    def padded(o):
        if o + 8 > len(pi):
            return None
        n = u64(pi, o)
        end = o + 8 + n + (8 - n % 8) % 8
        if end > len(pi):
            return None
        return pi[o + 8:o + 8 + n], end
    r = padded(o)
    if r is None:
        return None
    p, o = r
    if o + 8 > len(pi):
        return None
    m, o, tr = u64(pi, o), o + 8, []
    for _ in range(m):
        r = padded(o)
        if r is None or r[1] + 32 > len(pi):
            return None
        tr.append((r[0], pi[r[1]:r[1] + 32]))
        o = r[1] + 32
    if o + 8 + 149 * 32 > len(pi):
        return None
    idx = u64(pi, o)
    ds = [pi[o + 8 + 32 * k:o + 40 + 32 * k] for k in range(149)]
    return signed.Signed(p, tr, idx, ds[:133], ds[133:]), o + 8 + 149 * 32


def decode(pi):
    """('leaf', s, n) | ('node', c1, c2, p1, p2) in the library's encoding (`witWords`), or None.
    (Strictness here is only the format's; the Lean `check` also re-encodes.)"""
    if len(pi) < 8:
        return None
    tag = u64(pi, 0)
    if tag == 0 and len(pi) == 48:
        return ("leaf", pi[8:40], u64(pi, 40))
    if tag != 1 or len(pi) < 72:
        return None
    a = signed_words(pi, 72)
    b = signed_words(pi, a[1]) if a else None
    if b is None or b[1] != len(pi):
        return None
    return ("node", pi[8:40], pi[40:72], a[0], b[0])


def check(vk, c, pi):
    w = decode(pi)
    if w is None:
        return False
    if w[0] == "leaf":
        return w[2] <= CHAIN_CAP and c == leaf_stmt(chain_end(w[1], w[2]), w[2])
    return c == node_stmt(w[1], w[2]) and acc_signed(vk, w[1], w[3]) and acc_signed(vk, w[2], w[4])


def acc(vk, c, data):
    return acc_signed(vk, c, signed.parse(data))


_decided = {}


def acc_signed(vk, c, s):
    """`acc` on a parsed signed proof, each distinct one decided once per process: a node carries its
    children whole, so the files of one batch share most of their signatures (in pure-Python Keccak
    a signature check is about 250 permutations)."""
    if s is None:
        return False
    key = (vk, c, s.pi, tuple(s.trace), s.idx, tuple(s.ots), tuple(s.path))
    if key not in _decided:
        _decided[key] = _acc_signed(vk, c, s)
    return _decided[key]


def _acc_signed(vk, c, s):
    if len(s.pi) >= WORD or any(len(q) > QUERY_CAP for q, _ in s.trace):
        return False
    if not W.sig_ok(vk, W.trace_digest(s.trace), s.idx, s.ots, s.path):
        return False
    return not s.trace and check(vk, c, s.pi)     # V asks nothing: the trace must be empty
