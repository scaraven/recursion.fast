"""An independent Python reading of BRIEF §4.2 (the trace digest and the WOTS/Merkle signature),
written from the BRIEF's text, for testing the service and the runner. Not part of the runtime.

  traceDigest tr = BLAKE2s-256(0x54 ‖ item_0 ‖ …),  item_i = enc64 |q_i| ‖ q_i ‖ a_i
  digits(m):  d[4i+t] = (m[i] >> 2t) & 3  (i < 32, t < 4);  C = Σ_{k<128} (3 − d[k]);
              d[128+t] = (C >> 2t) & 3  (t < 5)
  F(j,i,s,x)  = BLAKE2s-256(0x57 ‖ enc64 j ‖ byte i ‖ byte s ‖ x)
  sk_i(j)     = BLAKE2s-256 keyed by seed of (0x53 ‖ enc64 j ‖ byte i)      (V4-A4)
  sign:       ots[i] = F(j,i,d_i−1, … F(j,i,0, sk_i))
  verify:     end_i = F(j,i,2, … F(j,i,d_i, ots[i]));  leaf = BLAKE2s-256(0x4B ‖ enc64 j ‖ end_0 … end_132)
              node = BLAKE2s-256(0x4D ‖ left ‖ right); at level t the current value is the left child
              iff bit t of j is 0, path[t] the sibling; SigOk iff j < 2^16, |ots| = 133, |path| = 16,
              root = vk.
"""
import hashlib
import os
from concurrent.futures import ProcessPoolExecutor


def H(b, key=b""):
    return hashlib.blake2s(b, key=key, digest_size=32).digest()


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
    ends = []
    for i in range(133):
        x = sk(seed, j, i)
        for s in range(3):
            x = F(j, i, s, x)
        ends.append(x)
    return leaf_from_ends(j, ends)


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
