#!/usr/bin/env python3 -I
"""S5 review, item 5: reproduce the cmpToy node statements xN, xR in ~10 lines from DESIGN §5.1
and Compile.lean's header only (not from probes/s5/recursion_ref.py), then compare them with the
Lean literals in Controls/RecursionData.lean (parsed from the source)."""
import hashlib, re, struct, sys
H = lambda b: hashlib.blake2s(b).digest()
le = lambda a: a.to_bytes(8, 'little')
root = H(H(le(100)) + H(le(101)))                    # IDX = [100],[101], arity 2, depth 1
D = H(le(0x1234) + root)                             # VKc.digest: VK elements ‖ index root
slot = lambda d: list(struct.unpack('<4Q', d))       # digestToSlot
sb = lambda x: b''.join(le(a) for a in x)            # stmtBytes
node = lambda x1, x2: slot(D) + slot(D) + slot(H(sb(x1) + sb(x2))) + [0] * 20
x0 = [i * 0x0101 for i in range(32)]; x1 = x0[:31] + [x0[31] ^ 1]
xN = node(x0, x1); xR = node(xN, x0)
src = open(sys.argv[1]).read()
def lean(name):
    m = re.search(r'def ' + name + r' : Stmt := stmtOfWords\s*\[(.*?)\]', src, re.S)
    return [int(w, 16) for w in re.findall(r'0x[0-9a-f]+', m.group(1))]
for name, v in (('xN', xN), ('xR', xR)):
    print(name, 'match' if lean(name) == v else 'MISMATCH', ' '.join(f'{a:016x}' for a in v[:12]))
print('D', D.hex())
# stmtBytes length / injectivity: 32 elements x 8 bytes, x1 ‖ x2 is always 512 bytes
assert len(sb(x0)) == 256 and len(sb(x0) + sb(x1)) == 512
