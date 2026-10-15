#!/usr/bin/env python3
"""S9 feasibility, O-11: which RS decoders fit the extractor budget B(k) = 2^(2k+16) steps.
Operation counts (K multiply-adds) for a single codeword of length N = 2^(k + r), r = log2(1/rho):
  * unique decoding, syndrome + Berlekamp-Massey + Chien/Forney: ~ (1 - rho) N^2 + N e  (~ 1.5 N^2 used);
  * Guruswami-Sudan with Koetter's iterative interpolation at multiplicity m: C = N m (m+1)/2 linear
    constraints, ~ C^2 multiply-adds (the polynomial count l+1 and the root finding are lower order);
    decoding radius tau < 1 - sqrt(rho (1 + 1/m)); unique radius (1 - rho)/2.
Steps per multiply-add: 10 (S4-M2's figure: clmul, clmulh, two folds by 0x1B, loads) and 14 (a
straight RV64 + Zbc loop: 2 ld, clmul, clmulh, clmul, clmulh, xor, clmul, xor, xor, 3 loop ops).
Queries s for a 2^-128 query round: s = ceil(128 / -log2(1 - tau)). The slack log2(B(k) / steps) does
not depend on k, because N^2 and B(k) are both 2^(2k + const)."""
import math
for rho_log in (2, 4):
    rho = 2 ** -rho_log
    print(f"rho = 1/{2**rho_log}: N = 2^(k+{rho_log}); unique radius {(1-rho)/2:.3f}, "
          f"s = {math.ceil(128 / -math.log2(1 - (1-rho)/2))}")
    for spm in (10, 14):
        uniq = math.log2(1.5 * spm) + 2 * rho_log           # log2(steps) - 2k
        print(f"  {spm} steps/op: unique O(N^2): log2 steps = 2k + {uniq:5.2f}  (B: 2k + 16) slack 2^{16 - uniq:5.2f}")
        for m in range(1, 8):
            C = m * (m + 1) / 2
            gs = math.log2(spm * C * C) + 2 * rho_log
            tau = 1 - math.sqrt(rho * (1 + 1 / m))
            s = math.ceil(128 / -math.log2(1 - tau)) if tau > 0 else None
            fit = "fits" if gs <= 16 else "EXCEEDS"
            print(f"    GS m = {m}: log2 steps = 2k + {gs:5.2f} {fit:7s} radius {tau:.3f} queries {s}")
