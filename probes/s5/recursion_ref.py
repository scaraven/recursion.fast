#!/usr/bin/env python3 -I
"""Independent reference for Stage 5 (Contract/Recursion.lean), from DESIGN §5.1 and the byte
grammar of Contract/Compile.lean only, with hashlib.blake2s.

* digestToSlot: limb j = digest bytes 8j..8j+7, little-endian (struct '<4Q').
* nodeStmt: d0 = D(vkC), d1 = D(vkL), d2 = H(x1 bytes || x2 bytes), d3 = (t1, t2, 0, 0) with
  leaf = 0, node = 1 (S5-A11), d4..d7 = 0, where H is cfg.hash (S5-A8), the hash of D and of the
  sponge; the menu has one hash, BLAKE2s-256.
* treeRoot: the statement tree, level 1 over leaves (tags leaf, leaf), above over nodes (S5-A12).
* The second key vkK (VK element 0x1235, same index) and its honest tape of x0 (S5-m7).
* The honest compiled tape of the control protocol cmpToy (Controls/CompileToy.lean) at arity 2
  for any statement x (the S3 reference, probes/s3/compile_ref.py, generalised in x).
Prints everything as hex; Controls/Recursion.lean pins the same values."""
import hashlib, struct

H = lambda b: hashlib.blake2s(bytes(b)).digest()
M64 = (1 << 64) - 1
kb = lambda a: (a & M64).to_bytes(8, 'little')
ZERO = bytes(32)
ARITY = 2

def node(leaves, h, p):
    if h == 0:
        return H(b''.join(kb(a) for a in leaves[p])) if p < len(leaves) else ZERO
    return H(b''.join(node(leaves, h - 1, ARITY * p + i) for i in range(ARITY)))

def depth(m):
    d = 0
    while 2 ** m > ARITY ** d: d += 1
    return d

def commit(leaves):
    return node(leaves, depth(len(leaves).bit_length() - 1), 0)

def path(leaves, l):
    out = b''
    for h in range(depth(len(leaves).bit_length() - 1)):
        p = l // ARITY ** h
        for i in range(ARITY):
            if i != p % ARITY:
                out += node(leaves, h, ARITY * (p // ARITY) + i)
    return out

absorb = lambda s, m: H(b'\x00' + s + m)
def squeeze(s, n):
    out = b''
    for _ in range((n + 31) // 32):
        s = H(b'\x01' + s); out += s
    return out[:n], s

VK = [0x1234]
IDX = [[100], [101]]
ROOT0 = commit(IDX)
VKC = b''.join(kb(a) for a in VK) + ROOT0          # VKc.toBytes
D = H(VKC)                                          # VKc.digest cfg2
DK = H(kb(0x1235) + ROOT0)                          # VKc.digest cfg2 of vkK
LEAF, NODE = 0, 1

def stmt_bytes(x): return b''.join(kb(a) for a in x)
def slots(d): return list(struct.unpack('<4Q', d))  # digestToSlot

def node_stmt(x1, x2, t1, t2):
    return (slots(D) + slots(D) + slots(H(stmt_bytes(x1) + stmt_bytes(x2))) + [t1, t2, 0, 0]
            + [0] * 16)

def tree_root(xs):
    t = LEAF
    while len(xs) > 1:
        xs = [node_stmt(xs[i], xs[i + 1], t, t) for i in range(0, len(xs), 2)]
        t = NODE
    return xs[0]

def toy_tape(x, vk0=VK[0], d=D):
    s = absorb(d, stmt_bytes(x))
    msg0 = [[p + 7] for p in range(4)]
    r1 = commit(msg0)
    s = absorb(s, r1)
    ch, s = squeeze(s, 32)
    e_c0 = int.from_bytes(ch[0:8], 'little')
    i = int.from_bytes(ch[24:32], 'little') % 4
    plain = kb(e_c0 ^ vk0 ^ x[0])
    return r1 + plain + kb(msg0[i][0]) + path(msg0, i) + kb(IDX[i % 2][0]) + path(IDX, i % 2), i

x0 = [(i * 0x0101) & M64 for i in range(32)]
x1 = list(x0); x1[31] ^= 1
xN = node_stmt(x0, x1, LEAF, LEAF)   # the two-leaf node (level 1)
xR = node_stmt(xN, x0, NODE, LEAF)   # a node with a node child and a leaf child (level 2)
xD0 = list(xN); xD0[0] ^= 1          # a node statement with d0 changed (d1 intact)
xD1 = list(xN); xD1[4] ^= 1          # a node statement with d1 changed (d0 intact)
xBad0 = node_stmt(xD0, x0, NODE, LEAF)   # parents of those, as node children
xBad1 = node_stmt(xD1, x0, NODE, LEAF)
xT = tree_root([x0, x1, x0, x1])     # the statement tree of depth 2
assert xT == node_stmt(xN, xN, NODE, NODE)

if __name__ == '__main__':
    print('D(vkc2)            ', D.hex())
    print('digestToSlot D     ', ' '.join(f'{v:016x}' for v in slots(D)))
    d2 = H(stmt_bytes(x0) + stmt_bytes(x1))
    print('blake2s(x0||x1)    ', d2.hex())
    print('digestToSlot d2    ', ' '.join(f'{v:016x}' for v in slots(d2)))
    print('xN (32 words)      ', ' '.join(f'{v:016x}' for v in xN))
    print('xR (32 words)      ', ' '.join(f'{v:016x}' for v in xR))
    print('xBad0 (32 words)   ', ' '.join(f'{v:016x}' for v in xBad0))
    print('xBad1 (32 words)   ', ' '.join(f'{v:016x}' for v in xBad1))
    print('xT (32 words)      ', ' '.join(f'{v:016x}' for v in xT))
    print('D(vkK)             ', DK.hex())
    t, i = toy_tape(x0, 0x1235, DK)
    print(f'tape K x0 ({len(t)} bytes, index challenge {i})', t.hex())
    for name, x in (('x0', x0), ('x1', x1), ('xN', xN), ('xD0', xD0), ('xD1', xD1)):
        t, i = toy_tape(x)
        print(f'tape {name} ({len(t)} bytes, index challenge {i})', t.hex())
