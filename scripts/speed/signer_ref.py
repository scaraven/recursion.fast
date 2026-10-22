"""Independent Python reference of BRIEF §4.2 + V4-A4 (hashlib only), to cross-check the Lean
signer's output (vk and the signature of one message with one key)."""
import hashlib, sys
H = lambda b: hashlib.blake2s(b).digest()
e64 = lambda n: (n % 2**64).to_bytes(8, 'little')
def start(seed, j, i): return hashlib.blake2s(b'S' + e64(j) + bytes([i]), key=seed).digest()
def F(j, i, s, x): return H(b'W' + e64(j) + bytes([i, s]) + x)
def chain(j, i, s, n, x):
    for t in range(n): x = F(j, i, s + t, x)
    return x
def digits(m):
    d = [(b >> (2 * t)) & 3 for b in m for t in range(4)]
    C = sum(3 - x for x in d)
    return d + [(C >> (2 * t)) & 3 for t in range(5)]
def leaf(seed, j):
    ends = b''.join(chain(j, i, 0, 3, start(seed, j, i)) for i in range(133))
    return H(b'K' + e64(j) + ends)
def node(l, r): return H(b'M' + l + r)
seed = bytes.fromhex(sys.argv[1]); j = int(sys.argv[2]); m = bytes.fromhex(sys.argv[3])
level = [leaf(seed, k) for k in range(2**16)]
levels = [level]
while len(level) > 1:
    level = [node(level[2*k], level[2*k+1]) for k in range(len(level)//2)]
    levels.append(level)
print(levels[16][0].hex())
print(j)
for i, d in enumerate(digits(m)): print(chain(j, i, 0, d, start(seed, j, i)).hex())
for t in range(16):
    k = j >> t
    print(levels[t][k ^ 1].hex())
