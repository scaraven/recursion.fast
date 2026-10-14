"""Expected digests for the S2 review's extra kernel vectors (python3 -I probes/s2/vectors.py)."""
import hashlib

def pattern(n):
    return bytes((7 * i + 3) % 256 for i in range(n))

key32 = bytes(range(32))
cases = [
    ("len1",        b"",          32, b"a"),
    ("len63",       b"",          32, pattern(63)),
    ("len128",      b"",          32, pattern(128)),
    ("len129",      b"",          32, pattern(129)),
    ("len192",      b"",          32, pattern(192)),
    ("len512",      b"",          32, pattern(512)),
    ("nn1",         b"",          1,  b"abc"),
    ("kk1",         b"\x2a",      32, b"abc"),
    ("kk1nn1empty", b"\x2a",      1,  b""),
    ("kk32len64",   key32,        32, pattern(64)),
    ("kk1len64",    b"\x2a",      32, pattern(64)),
    ("kk32len1",    key32,        32, b"a"),
    ("kk1nn16len1", b"\x2a",      16, b"a"),
]
for name, key, nn, msg in cases:
    print(name, len(key), nn, len(msg), hashlib.blake2s(msg, digest_size=nn, key=key).hexdigest())
