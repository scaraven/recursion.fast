#!/usr/bin/env python3 -I
"""Independent reference of the compiled argument's byte grammar (Contract/Compile.lean header),
written from the documented grammar only, with hashlib.blake2s. Recomputes the honest tape of the
control protocol `cmpToy` (Controls/Compile.lean) at arity 2 and 4, and Merkle roots of the
4-leaf message oracle, for comparison with the Lean `#eval`s."""
import hashlib, sys

H = lambda b: hashlib.blake2s(bytes(b)).digest()          # BLAKE2s-256, unkeyed
M64 = (1 << 64) - 1
kb = lambda a: (a & M64).to_bytes(8, 'little')            # K: 8 bytes little-endian
ZERO = bytes(32)

def depth(arity, m):            # least d with 2^m <= arity^d
    d = 0
    while 2 ** m > arity ** d: d += 1
    return d

def node(arity, leaves, h, p):  # leaves: list of lists of ints (elements); padding = zero digest
    if h == 0:
        return H(b''.join(kb(a) for a in leaves[p])) if p < len(leaves) else ZERO
    return H(b''.join(node(arity, leaves, h - 1, arity * p + i) for i in range(arity)))

def commit(arity, leaves):
    m = (len(leaves)).bit_length() - 1
    return node(arity, leaves, depth(arity, m), 0)

def path(arity, leaves, l):
    m = (len(leaves)).bit_length() - 1
    out = b''
    for h in range(depth(arity, m)):
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

def toy_tape(arity):
    vk = [0x1234]
    idx = [[100], [101]]                     # index oracle: 2 leaves of 1 element
    x = [(i * 0x0101) & M64 for i in range(32)]
    msg0 = [[p + 7] for p in range(4)]       # round 0: 4 leaves of 1 element
    root0 = commit(arity, idx)
    vkc = b''.join(kb(a) for a in vk) + root0
    s = absorb(H(vkc), b''.join(kb(a) for a in x))
    r1 = commit(arity, msg0)
    tape = r1
    s = absorb(s, r1)                        # round 0: root absorbed
    ch, s = squeeze(s, 24 * 1 + 8 * 1)      # round 1: chal 1 [2]
    e_c0 = int.from_bytes(ch[0:8], 'little')
    i = int.from_bytes(ch[24:32], 'little') % 4
    ans = (e_c0 ^ vk[0] ^ x[0]) & M64       # addition in K is xor
    plain = kb(ans)
    tape += plain
    s = absorb(s, plain)                     # round 2: plain element absorbed
    # openings in query order: oracle 1 leaf i, oracle 0 leaf i % 2, oracle 2 (plain: nothing)
    tape += kb(msg0[i][0]) + path(arity, msg0, i)
    tape += kb(idx[i % 2][0]) + path(arity, idx, i % 2)
    return tape, root0, r1

if __name__ == '__main__':
    for a in (2, 4):
        t, r0, r1 = toy_tape(a)
        print(f"arity {a}: index root {r0.hex()}")
        print(f"arity {a}: msg root   {r1.hex()}")
        print(f"arity {a}: tape ({len(t)} bytes) {t.hex()}")

def cheat_tape(arity=2):
    """A prover that commits to another oracle (p + 1000) but answers the challenges of the honest
    root, with valid openings under its own root (`fs_binding` in Controls/Compile.lean)."""
    vk = [0x1234]; idx = [[100], [101]]
    x = [(i * 0x0101) & M64 for i in range(32)]
    honest = [[p + 7] for p in range(4)]; other = [[p + 1000] for p in range(4)]
    vkc = b''.join(kb(a) for a in vk) + commit(arity, idx)
    s = absorb(absorb(H(vkc), b''.join(kb(a) for a in x)), commit(arity, honest))
    ch, _ = squeeze(s, 32)
    e_c0 = int.from_bytes(ch[0:8], 'little'); i = int.from_bytes(ch[24:32], 'little') % 4
    ans = e_c0 ^ vk[0] ^ x[0]
    return (commit(arity, other) + kb(ans) + kb(other[i][0]) + path(arity, other, i)
            + kb(idx[i % 2][0]) + path(arity, idx, i % 2)), i

if __name__ == '__main__':
    t, i = cheat_tape()
    print(f"cheat (honest index challenge i = {i}): {t.hex()}")
