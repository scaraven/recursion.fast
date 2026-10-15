#!/usr/bin/env python3
"""S9 feasibility: generate Lean files that kernel-check N products in K = GF(2^64) by `decide +kernel`
(the cost unit of every kernel-evaluated control: DESIGN §7.2 quotes ~40 ms per K product).
  gen.py OUTDIR N...   -> OUTDIR/KMul<N>.lean (N products, one theorem each), OUTDIR/KMul0.lean (imports only)
Products are computed here (clmul + reduction mod x^64 + x^4 + x^3 + x + 1) from a fixed seed."""
import random, sys, os
def clmul(a, b):
    r = 0
    for i in range(64):
        if (a >> i) & 1: r ^= b << i
    return r
def reduce(t):
    for _ in range(2):
        hi, lo = t >> 64, t & ((1 << 64) - 1)
        t = clmul(hi, 0x1B) ^ lo
    return t & ((1 << 64) - 1)
out = sys.argv[1]; os.makedirs(out, exist_ok=True)
rng = random.Random(9)
hdr = "import RecursionFast.Contract.Field\nopen RecursionFast\n\n"
open(os.path.join(out, "KMul0.lean"), "w").write(hdr + "#check (0 : K)\n")
for n in map(int, sys.argv[2:]):
    s = hdr
    for j in range(n):
        a, b = rng.getrandbits(64), rng.getrandbits(64)
        s += f"theorem kmul_{j} : (⟨0x{a:016x}⟩ : K) * ⟨0x{b:016x}⟩ = ⟨0x{reduce(clmul(a, b)):016x}⟩ := by decide +kernel\n"
    open(os.path.join(out, f"KMul{n}.lean"), "w").write(s)
