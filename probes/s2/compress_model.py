"""Independent RFC 7693 §3.1–3.2 model of BLAKE2s F (python3 -I probes/s2/compress_model.py).
Validated against hashlib on ordinary inputs, then used for counters >= 2^32, which no hashlib
input can reach. Prints `compress` vectors for probes/s2/HighCounter.lean."""
import hashlib, struct
IV = [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]
SIGMA = [[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3],
 [11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4],[7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8],
 [9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13],[2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9],
 [12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11],[13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10],
 [6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5],[10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0]]
M32 = 0xFFFFFFFF
def rotr(x, n): return ((x >> n) | (x << (32 - n))) & M32
def G(v, a, b, c, d, x, y):
    v[a] = (v[a] + v[b] + x) & M32; v[d] = rotr(v[d] ^ v[a], 16)
    v[c] = (v[c] + v[d]) & M32;     v[b] = rotr(v[b] ^ v[c], 12)
    v[a] = (v[a] + v[b] + y) & M32; v[d] = rotr(v[d] ^ v[a], 8)
    v[c] = (v[c] + v[d]) & M32;     v[b] = rotr(v[b] ^ v[c], 7)
def F(h, m, t, f):
    v = h[:] + IV[:]
    v[12] ^= t & M32; v[13] ^= (t >> 32) & M32
    if f: v[14] ^= M32
    for i in range(10):
        s = SIGMA[i]
        G(v,0,4,8,12,m[s[0]],m[s[1]]); G(v,1,5,9,13,m[s[2]],m[s[3]])
        G(v,2,6,10,14,m[s[4]],m[s[5]]); G(v,3,7,11,15,m[s[6]],m[s[7]])
        G(v,0,5,10,15,m[s[8]],m[s[9]]); G(v,1,6,11,12,m[s[10]],m[s[11]])
        G(v,2,7,8,13,m[s[12]],m[s[13]]); G(v,3,4,9,14,m[s[14]],m[s[15]])
    return [h[i] ^ v[i] ^ v[i + 8] for i in range(8)]
def blake2s(msg, nn=32, key=b""):
    kk = len(key); h = IV[:]; h[0] ^= 0x01010000 ^ (kk << 8) ^ nn
    d = (key + bytes(64 - kk) if kk else b"") + msg
    blocks = [d[i:i+64] for i in range(0, max(len(d), 1), 64)] or [b""]
    for i, b in enumerate(blocks[:-1]):
        h = F(h, list(struct.unpack("<16I", b)), (i + 1) * 64, False)
    last = blocks[-1]; h = F(h, list(struct.unpack("<16I", last + bytes(64 - len(last)))), len(d), True)
    return b"".join(struct.pack("<I", w) for w in h)[:nn]
# validate the model
for ll in list(range(0, 200)) + [511, 512, 513]:
    for kk in (0, 1, 32):
        msg = bytes((5 * i + 1) % 256 for i in range(ll)); key = bytes(range(kk))
        assert blake2s(msg, 32, key) == hashlib.blake2s(msg, key=key).digest(), (ll, kk)
print("model == hashlib on 609 inputs")
h0 = IV[:]; h0[0] ^= 0x01010020
m = list(struct.unpack("<16I", b"abc" + bytes(61)))
for t in (2**32 + 3, 2**64 - 1):
    print(t, "[" + ", ".join(f"0x{w:08x}" for w in F(h0, m, t, True)) + "]")
