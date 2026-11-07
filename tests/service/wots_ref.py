"""An independent Python reading of `RecursionFast/Contract/Signature.lean` (the trace digest and the WOTS/Merkle
signature), written from the contract and `service/PROTOCOL.md` §2, for testing the service and the
runner. Not part of the runtime.

  H(m)        = Keccak-256(m)  (Ethereum's: rate 136, padding 0x01 … 0x80)
  traceDigest tr = H(0x54 ‖ item_0 ‖ …),  item_i = enc64 |q_i| ‖ q_i ‖ a_i
  digits(m):  d[4i+t] = (m[i] >> 2t) & 3  (i < 32, t < 4);  C = Σ_{k<128} (3 − d[k]);
              d[128+t] = (C >> 2t) & 3  (t < 5)
  F(j,i,s,x)  = H(0x57 ‖ enc64 j ‖ byte i ‖ byte s ‖ x)
  sk_i(j)     = H(seed ‖ 0x53 ‖ enc64 j ‖ byte i)      (the 32-byte seed first)
  sign:       ots[i] = F(j,i,d_i−1, … F(j,i,0, sk_i))
  verify:     end_i = F(j,i,2, … F(j,i,d_i, ots[i]));  leaf = H(0x4B ‖ enc64 j ‖ end_0 … end_132)
              node = H(0x4D ‖ left ‖ right); at level t the current value is the left child
              iff bit t of j is 0, path[t] the sibling; SigOk iff j < 2^16, |ots| = 133, |path| = 16,
              root = vk.

The hash is `keccak_ref.c` (an independent C reading of FIPS 202), compiled here with the system
`gcc` into a temporary shared object and called through ctypes: the full Merkle tree from a seed is
about 37 million permutations, out of reach of pure Python. Without `gcc`, single hashes fall back
to the pure-Python `harness/rfh/keccak.py`, and `tree` raises (the tests fail; they do not skip).
"""
import ctypes
import hashlib
import os
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ProcessPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(HERE)), "harness"))
from rfh import keccak as pykeccak  # noqa: E402

C_SOURCE = os.path.join(HERE, "keccak_ref.c")
GCC = ["gcc", "-O3", "-shared", "-fPIC"]
_LIB = []  # [lib] once loaded, [None] if gcc is unavailable


def c_lib(required=False):
    """The compiled `keccak_ref.c` (cached in the temporary directory by user, source and flags), or
    None without gcc; `required` turns None into an error."""
    if not _LIB:
        key = hashlib.sha256(open(C_SOURCE, "rb").read() + " ".join(GCC).encode()).hexdigest()[:16]
        so = os.path.join(tempfile.gettempdir(), f"rf-keccak-ref-{os.getuid()}-{key}.so")
        lib = None
        if not os.path.exists(so) and shutil.which("gcc"):
            tmp = f"{so}.{os.getpid()}.tmp"
            r = subprocess.run(GCC + ["-o", tmp, C_SOURCE], capture_output=True, text=True)
            if r.returncode != 0:
                raise RuntimeError(f"gcc failed on {C_SOURCE}:\n{r.stderr}")
            os.replace(tmp, so)
        if os.path.exists(so):
            lib = ctypes.CDLL(so)
            lib.rf_keccak_init.argtypes = []
            lib.rf_keccak_init()
            lib.rf_keccak256.argtypes = [ctypes.c_char_p, ctypes.c_size_t, ctypes.c_char_p]
            lib.rf_keccak256_many.argtypes = [ctypes.c_char_p, ctypes.c_size_t, ctypes.c_size_t, ctypes.c_char_p]
        _LIB.append(lib)
    if required and _LIB[0] is None:
        raise RuntimeError("the full Merkle tree needs gcc to compile tests/service/keccak_ref.c")
    return _LIB[0]


def keccak_c(m):
    """Keccak-256 of `m` by `keccak_ref.c` (raises without gcc)."""
    out = ctypes.create_string_buffer(32)
    c_lib(required=True).rf_keccak256(m, len(m), out)
    return out.raw


def H(b, key=b""):
    """Keccak-256 of `key ‖ b` (the keyed hashes have a 32-byte key prefix)."""
    m = key + b
    return keccak_c(m) if c_lib() else pykeccak.keccak256(m)


def H_many(msgs):
    """Keccak-256 of each of the equal-length `msgs`, in one C call."""
    if not msgs:
        return []
    n = len(msgs[0])
    assert all(len(m) == n for m in msgs)
    out = ctypes.create_string_buffer(32 * len(msgs))
    c_lib(required=True).rf_keccak256_many(b"".join(msgs), n, len(msgs), out)
    raw = out.raw
    return [raw[32 * k:32 * k + 32] for k in range(len(msgs))]


def enc64(n):
    return (n % (1 << 64)).to_bytes(8, "little")


def trace_digest(trace):
    return H(b"\x54" + b"".join(enc64(len(q)) + q + a for q, a in trace))


def digits(m):
    d = [(m[i] >> (2 * t)) & 3 for i in range(32) for t in range(4)]
    c = sum(3 - x for x in d)
    return d + [(c >> (2 * t)) & 3 for t in range(5)]


def F(j, i, s, x):
    return H(b"\x57" + enc64(j) + bytes([i, s]) + x)


def sk(seed, j, i):
    return H(b"\x53" + enc64(j) + bytes([i]), key=seed)


def wots_sign(seed, j, m):
    out = []
    for i, d in enumerate(digits(m)):
        x = sk(seed, j, i)
        for s in range(d):
            x = F(j, i, s, x)
        out.append(x)
    return out


def leaf_from_ends(j, ends):
    return H(b"\x4B" + enc64(j) + b"".join(ends))


def leaf(seed, j):
    """Leaf `j`: the 133 chains advanced together, one `H_many` call per step."""
    x = H_many([seed + b"\x53" + enc64(j) + bytes([i]) for i in range(133)])
    for s in range(3):
        x = H_many([b"\x57" + enc64(j) + bytes([i, s]) + x[i] for i in range(133)])
    return leaf_from_ends(j, x)


def node(l, r):
    return H(b"\x4D" + l + r)


def sig_ok(vk, m, idx, ots, path):
    if not (0 <= idx < 1 << 16 and len(ots) == 133 and len(path) == 16):
        return False
    ends = []
    for i, d in enumerate(digits(m)):
        x = ots[i]
        for s in range(d, 3):
            x = F(idx, i, s, x)
        ends.append(x)
    cur = leaf_from_ends(idx, ends)
    for t in range(16):
        cur = node(cur, path[t]) if (idx >> t) & 1 == 0 else node(path[t], cur)
    return cur == vk


def _leaves(args):
    seed, lo, hi = args
    return [leaf(seed, j) for j in range(lo, hi)]


def tree(seed, workers=None):
    """All levels of the Merkle tree (levels[0] = the 2^16 leaves), in parallel."""
    c_lib(required=True)
    workers = workers or os.cpu_count() or 1
    step = 1 << 10
    with ProcessPoolExecutor(max_workers=workers) as ex:
        leaves = [x for part in ex.map(_leaves, [(seed, lo, lo + step) for lo in range(0, 1 << 16, step)])
                  for x in part]
    levels = [leaves]
    while len(levels[-1]) > 1:
        cur = levels[-1]
        levels.append([node(cur[k], cur[k + 1]) for k in range(0, len(cur), 2)])
    return levels


def auth_path(levels, j):
    return [levels[t][(j >> t) ^ 1] for t in range(16)]
