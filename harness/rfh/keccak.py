"""Keccak-256 in pure Python (TRUSTED RUNTIME, the runner's few statement hashes; the reference of the
tests): Ethereum's Keccak-256, the sponge of FIPS 202 over Keccak-f[1600] with rate 136 bytes,
capacity 512 bits, a 32-byte output and Keccak's original padding (first padding byte 0x01, not
SHA-3's 0x06; the last byte of the block XORed with 0x80). `RecursionFast/Contract/Hash/Keccak.lean`
is the normative definition.

Written from FIPS 202 §3.2 (the step mappings) and §5.1 (`pad10*1`); the lane of `A[x, y]` is
`x + 5y`, a lane is the little-endian 64-bit word of 8 state bytes. About 0.2 ms per permutation:
the runner hashes its chains through `rf-oracle --leaves` (`rfh/digest.py`), never here.
"""

M64 = (1 << 64) - 1
RATE = 136

# ι round constants, FIPS 202 §3.2.5 (Algorithm 5 `rc`; `RecursionFast/Controls/Keccak.lean`
# re-derives them from the LFSR)
RC = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]

# ρ offsets of lane x + 5y, FIPS 202 §3.2.2 (Algorithm 2)
RHO = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]


def _rotl(v, r):
    return ((v << r) | (v >> (64 - r))) & M64 if r else v


def keccak_f(a):
    """Keccak-f[1600] on 25 lanes (a list, lane `x + 5y`), returning the new list."""
    for rc in RC:
        # θ
        c = [a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20] for x in range(5)]
        d = [c[(x - 1) % 5] ^ _rotl(c[(x + 1) % 5], 1) for x in range(5)]
        a = [a[i] ^ d[i % 5] for i in range(25)]
        # ρ and π: B[y, 2x + 3y] = rot(A[x, y], r[x, y])
        b = [0] * 25
        for x in range(5):
            for y in range(5):
                b[y + 5 * ((2 * x + 3 * y) % 5)] = _rotl(a[x + 5 * y], RHO[x + 5 * y])
        # χ
        a = [b[x + 5 * y] ^ (~b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]) & M64
             for y in range(5) for x in range(5)]
        # ι
        a[0] ^= rc
    return a


def keccak256(m: bytes) -> bytes:
    """Keccak-256 of `m` (32 bytes)."""
    p = bytearray(m)
    p.append(0x01)
    p.extend(bytes(-len(p) % RATE))
    p[-1] |= 0x80
    a = [0] * 25
    for o in range(0, len(p), RATE):
        for i in range(RATE // 8):
            a[i] ^= int.from_bytes(p[o + 8 * i:o + 8 * i + 8], "little")
        a = keccak_f(a)
    return b"".join(a[i].to_bytes(8, "little") for i in range(4))


def keyed(key: bytes, m: bytes) -> bytes:
    """The service's keyed hash (`service/PROTOCOL.md` §2): Keccak-256 of the 32-byte key, then `m`."""
    assert len(key) == 32
    return keccak256(key + m)
