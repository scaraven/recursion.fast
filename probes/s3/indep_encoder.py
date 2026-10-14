"""S3 review: an independent encoder of the compiled-argument tape, written from the module
header of `Contract/Compile.lean` ALONE (not from `compile_ref.py`, not from the Lean bodies).

Ambiguities met while reading the header, and how they were resolved (see S3-review.md):
  A1. "VKc bytes" is not defined in the header. Guess: VK elements (8 bytes LE each), then the
      32-byte index root (resolved by the docstring of `VKc.toBytes`, which is not the header).
  A2. "padded with the zero digest ... to A^depth positions": is an internal node whose children
      are all padding H(0^(32A)) or the zero digest? Guess (literal reading): padding is at the
      leaf level only; every internal node is hashed. `PAD_INTERNAL_ZERO` switches the other
      reading, to test which one Lean implements.
  A3. Children of node p are A*p .. A*p+A-1 (standard; implied by "siblings in increasing
      position").
  A4. The index oracle is committed with the same arity and hash as the prover's oracles.
Usage: python3 -I indep_encoder.py
"""
import hashlib

PAD_INTERNAL_ZERO = False


def H(b: bytes) -> bytes:
    return hashlib.blake2s(b, digest_size=32).digest()


def kb(a: int) -> bytes:  # element of K: 8 bytes little-endian
    return (a & (2**64 - 1)).to_bytes(8, "little")


def vec(xs) -> bytes:
    return b"".join(kb(a) for a in xs)


def depth(n_leaves: int, A: int) -> int:
    d = 0
    while A**d < n_leaves:
        d += 1
    return d


def tree(leaves, A):
    """leaves: list of lists of ints (elements). Returns list of levels of digests, level 0 first."""
    d = depth(len(leaves), A)
    lvl = [H(vec(lf)) for lf in leaves] + [bytes(32)] * (A**d - len(leaves))
    real = [True] * len(leaves) + [False] * (A**d - len(leaves))
    levels = [lvl]
    for _ in range(d):
        nxt, nreal = [], []
        for p in range(len(lvl) // A):
            ch = lvl[A * p:A * p + A]
            r = any(real[A * p:A * p + A])
            nxt.append(H(b"".join(ch)) if (r or not PAD_INTERNAL_ZERO) else bytes(32))
            nreal.append(r)
        lvl, real = nxt, nreal
        levels.append(lvl)
    return levels


def root(leaves, A):
    return tree(leaves, A)[-1][0]


def path(leaves, A, l):
    levels = tree(leaves, A)
    out = b""
    p = l
    for h in range(len(levels) - 1):
        par = p // A
        for i in range(A):
            if A * par + i != p:
                out += levels[h][A * par + i]
        p = par
    return out


def opening(leaves, A, l):
    return vec(leaves[l]) + path(leaves, A, l)


class Sponge:
    def __init__(self, vkc_bytes: bytes):
        self.s = H(vkc_bytes)

    def absorb(self, m: bytes):
        self.s = H(b"\x00" + self.s + m)

    def squeeze(self, n: int) -> bytes:
        out = b""
        for _ in range((n + 31) // 32):
            self.s = H(b"\x01" + self.s)
            out += self.s
        return out[:n]


def toy_tape(A: int):
    """`cmpToy` (Controls/CompileToy.lean docstring): index [100, 101] (2 leaves of 1 element);
    round 0: msg <2,0> committed, p -> p+7; round 1: chal 1 [2]; round 2: msg <0,0> plain,
    m = e.c0 + vk0 + x0; verifier: query (2,0), then (1,i), then (0, i mod 2)."""
    vk = [0x1234]
    x = [i * 0x0101 for i in range(32)]
    idx = [[100], [101]]
    o1 = [[p + 7] for p in range(4)]
    vkc = vec(vk) + root(idx, A)
    sp = Sponge(vkc)
    sp.absorb(vec(x))
    r1 = root(o1, A)
    sp.absorb(r1)
    ch = sp.squeeze(24 * 1 + 8 * 1)
    e_c0 = int.from_bytes(ch[0:8], "little")
    i = int.from_bytes(ch[24:32], "little") % 4
    m = e_c0 ^ vk[0] ^ x[0]
    sp.absorb(kb(m))
    tape = r1 + kb(m)                       # rounds section
    tape += b""                             # query (2, 0): plain, nothing
    tape += opening(o1, A, i)               # query (1, i)
    tape += opening(idx, A, i % 2)          # query (0, i mod 2)
    return tape, root(idx, A), i


def pfs_tapes(A: int = 2):
    """S3 review protocol `pfs` (probes/s3/RevMutants.lean): same key and index as cmpToy; rounds
    plain a, chal 1 [], plain m; verifier accepts iff m = e.c0 + a. Honest: a = 5. Cheat against a
    sponge that does not absorb plain messages: a = 6, m = e'.c0 + 6 with e' squeezed without a."""
    vk = [0x1234]
    x = [i * 0x0101 for i in range(32)]
    vkc = vec(vk) + root([[100], [101]], A)
    sp = Sponge(vkc); sp.absorb(vec(x)); s_x = sp.s
    sp.absorb(kb(5)); e = int.from_bytes(sp.squeeze(24)[0:8], "little")
    honest = kb(5) + kb(e ^ 5)
    sp2 = Sponge(vkc); sp2.s = s_x; e2 = int.from_bytes(sp2.squeeze(24)[0:8], "little")
    cheat = kb(6) + kb(e2 ^ 6)
    return honest, cheat


if __name__ == "__main__":
    h, c = pfs_tapes()
    print(f"pfs honest {h.hex()} cheat {c.hex()}")
    for A in (2, 4, 8, 16):
        t, ir, i = toy_tape(A)
        print(f"arity {A}: i={i} len={len(t)} index_root={ir.hex()}")
        print(f"  tape {t.hex()}")
    # Padding probe: 8 leaves of 1 element at arity 4 (depth 2, positions 16; level-1 nodes 2,3
    # are all padding) and 5 leaves at arity 2 (depth 3).
    for pad in (False, True):
        PAD_INTERNAL_ZERO = pad
        r8 = root([[p + 7] for p in range(8)], 4)
        r5 = root([[p + 7] for p in range(5)], 2)
        print(f"pad_internal_zero={pad}: root(8 leaves, A=4)={r8.hex()} root(5 leaves, A=2)={r5.hex()}")
    PAD_INTERNAL_ZERO = False
