#!/usr/bin/env python3
"""The smoke test's "native prover" for the NOT SECURE control protocol `cmpToy`
(Controls/CompileToy.lean; harness/smoke/RecursionFastSmoke.lean), from the compiled argument's
byte grammar (Contract/Compile.lean header) and the S3 reference probes/s3/compile_ref.py,
generalised to any key and statement. It speaks the benchmark runner's prover interface
(harness/README.md): run in the step directory, it reads `vkc.bin` (the key bytes: element 0 of
`VK L`, then the 32-byte index root) and `stmt.bin` (256 bytes) and writes the tape to
`proof.bin`. `cmpToy` ignores the layout and the witness, so leaf, wrap and node steps are the same
computation here: the test is of the runner's plumbing and timing, not of recursion.

  python3 -I harness/smoke/toy_prover.py [--arity A] [--spin SECONDS] leaf|node

`--spin` busy-waits before proving (a stand-in for prover work, to test timing and budgets)."""
import hashlib, sys, time

H = lambda b: hashlib.blake2s(bytes(b)).digest()          # BLAKE2s-256, unkeyed
M64 = (1 << 64) - 1
kb = lambda a: (a & M64).to_bytes(8, 'little')            # K: 8 bytes little-endian
ZERO = bytes(32)

def depth(arity, m):
    d = 0
    while 2 ** m > arity ** d: d += 1
    return d

def node(arity, leaves, h, p):
    if h == 0:
        return H(b''.join(kb(a) for a in leaves[p])) if p < len(leaves) else ZERO
    return H(b''.join(node(arity, leaves, h - 1, arity * p + i) for i in range(arity)))

def commit(arity, leaves):
    return node(arity, leaves, depth(arity, len(leaves).bit_length() - 1), 0)

def path(arity, leaves, l):
    out = b''
    for h in range(depth(arity, len(leaves).bit_length() - 1)):
        p = l // arity ** h
        for i in range(arity):
            if i != p % arity:
                out += node(arity, leaves, h, arity * (p // arity) + i)
    return out

absorb = lambda s, m: H(b'\x00' + s + m)
def squeeze(s, n):
    out = b''
    for _ in range((n + 31) // 32):
        s = H(b'\x01' + s); out += s
    return out[:n], s

def tape(vkc, x, arity):
    """The honest tape of cmpToy for the key bytes `vkc` and statement bytes `x`."""
    vk0 = int.from_bytes(vkc[:8], 'little')
    idx = [[100], [101]]                     # cmpIDX: 2 leaves of 1 element
    msg0 = [[p + 7] for p in range(4)]       # round 0: 4 leaves of 1 element (p + 7)
    s = absorb(H(vkc), x)                    # seed: x absorbed into D = H(key bytes)
    r1 = commit(arity, msg0)
    s = absorb(s, r1)
    ch, s = squeeze(s, 24 + 8)               # round 1: chal 1 [2]
    e_c0 = int.from_bytes(ch[0:8], 'little')
    i = int.from_bytes(ch[24:32], 'little') % 4
    plain = kb(e_c0 ^ vk0 ^ int.from_bytes(x[0:8], 'little'))   # m = e.c0 + vk 0 + x 0 (xor)
    return (r1 + plain + kb(msg0[i][0]) + path(arity, msg0, i) + kb(idx[i % 2][0]) + path(arity, idx, i % 2))

def main():
    args = sys.argv[1:]
    modes = [a for a in args if a in ("leaf", "node")]   # the runner appends the mode last
    if len(modes) != 1:
        raise SystemExit(__doc__)
    rest = [a for a in args if a not in ("leaf", "node")]
    arity, spin = 2, 0.0
    for a, v in zip(rest[::2], rest[1::2]):
        if a == "--arity": arity = int(v)
        elif a == "--spin": spin = float(v)
        else: raise SystemExit(__doc__)
    end = time.perf_counter() + spin
    while time.perf_counter() < end:
        pass
    vkc, x = open("vkc.bin", "rb").read(), open("stmt.bin", "rb").read()
    if len(x) != 256:
        raise SystemExit("toy_prover: stmt.bin is not 256 bytes")
    with open("proof.bin", "wb") as f:
        f.write(tape(vkc, x, arity))


if __name__ == "__main__":
    main()
