"""Check probes/s2/Diff.lean output against hashlib.blake2s (python3 -I probes/s2/diff.py OUT)."""
import hashlib, sys
n = bad = 0
for line in open(sys.argv[1]):
    kk, nn, ll, got = line.split()
    kk, nn, ll = int(kk), int(nn), int(ll)
    key = b"" if kk == 256 else bytes((13 * i + 5) % 256 for i in range(kk))
    msg = bytes((31 * i + 17) % 251 for i in range(ll))
    exp = hashlib.blake2s(msg, digest_size=nn, key=key).hexdigest()
    n += 1
    if got != exp:
        bad += 1
        print("MISMATCH", kk, nn, ll, got, exp)
print(f"{n} cases, {bad} mismatches")
