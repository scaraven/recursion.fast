#!/usr/bin/env python3
"""Tape size of the compiled baseline P_triv, and the floor for any "send the witness" protocol.

  python3 -I tape-size.py CELLS CHIPS ELAYOUT FIXED

CELLS, CHIPS: cells and chips of the benchmark layout's honest witness (gen-chain-layout.py report);
ELAYOUT: the length of `Codec.eLayout L` in K elements (Lean #eval, logs/S7/lchain1024-sizes.log);
FIXED: the cells of the fixed tables (part of CELLS, already determined by the index).

1. The compiled P_triv (Contract/Compile.lean's tape grammar on P_triv's static shapes), at every
   class: rounds section = the plain message, 8 * 2^(k+10) bytes; openings = query (0, 0) on the
   Merkle-committed index oracle, one leaf of 8 * 2^(k+8) bytes with a path of depth 0 (one leaf,
   every arity), and query (1, 0) on the plain message, which opens nothing. Kernel-checked:
   RecursionFastCandidate.triv_uncapped_length (= 5 * 2^(k+11)).
2. The instance's content at the benchmark (k = 24, L_chain(2^10)): the serialised witness
   (eWit: one height per chip, then the cells) and the serialised layout (eLayout), 8 bytes each.
   Any protocol whose proof contains the witness needs at least the witness part.
3. The best Merkle variant of P_triv with adaptive queries (open only the leaves the content
   occupies; leaves of 2^l elements; arity A; static oracle sizes 2^25 for the message, the least
   power of two above 2^24 cells + 2^8 heights, and 2^32 for the index, the shape cap):
   used leaves * (leaf bytes + depth * (A - 1) * 32), minimised over l and A.
"""
import sys

CAP_RW, CAP_L = 2 ** 20, 2 ** 17
cells, chips, elayout, fixed = map(int, sys.argv[1:5])
MiB = 2 ** 20

def fmt(b):
    return f"{b:,} B ({b / MiB:,.1f} MiB)" if b < 2 ** 30 else f"{b:,} B ({b / 2 ** 30:,.1f} GiB)"

print("1. compiled P_triv (static shapes): rounds 8*2^(k+10) + index leaf 8*2^(k+8), no path")
print(f"{'k':>3} {'tape bytes':>34} {'x 1 MiB':>12} {'x 128 KiB':>12}")
for k in range(20, 29):
    t = 8 * 2 ** (k + 10) + 8 * 2 ** (k + 8)
    assert t == 5 * 2 ** (k + 11)
    print(f"{k:>3} {fmt(t):>34} {t // CAP_RW:>12,} {t // CAP_L:>12,}")

wit, idx = 8 * (chips + cells), 8 * elayout
t24 = 5 * 2 ** 35
print(f"\n2. content of L_chain(2^10) at k = 24: witness {chips} heights + {cells:,} cells = {fmt(wit)}; "
      f"layout {elayout:,} elements = {fmt(idx)}; total {fmt(wit + idx)}")
print(f"   witness alone: {wit / CAP_RW:.1f} x 1 MiB, {wit / CAP_L:.1f} x 128 KiB; "
      f"content is {100 * (wit + idx) / t24:.3f} % of the compiled tape (the rest is zero padding)")
own = 8 * (chips + cells - fixed)
print(f"   the witness includes {fixed:,} fixed-table cells ({fmt(8 * fixed)}), which the layout holds too; "
      f"the prover-chosen part is {fmt(own)}: {own / CAP_RW:.1f} x 1 MiB, {own / CAP_L:.1f} x 128 KiB")
steps = elayout * (elayout - 1) // 2 + (2 ** 32 - elayout) * elayout
print(f"   Lean-compiled indexer at k = 24: List.ofFn over 2^32 positions of `fun p => l.getD p 0` "
      f"(|l| = {elayout:,}): {steps:.3e} list steps (2^{steps.bit_length() - 1}..2^{steps.bit_length()})")

def merkle(n, logLen, l, A):
    la = A.bit_length() - 1
    depth = -(-(logLen - l) // la)
    used = -(-n // 2 ** l)
    return used * (8 * 2 ** l + depth * (A - 1) * 32)

best = min((merkle(cells + chips, 25, l, A) + merkle(elayout, 32, l2, A), l, l2, A)
           for A in (2, 4, 8, 16) for l in range(0, 26) for l2 in range(0, 33))
print(f"\n3. best adaptive Merkle variant: {fmt(best[0])} (message leaves 2^{best[1]}, index leaves "
      f"2^{best[2]}, arity {best[3]}): {best[0] / CAP_RW:.1f} x 1 MiB, {best[0] / CAP_L:.1f} x 128 KiB")
for A in (2, 4, 8, 16):
    m = merkle(cells + chips, 25, 10, A) + merkle(elayout, 32, 10, A)
    print(f"   leaves of 2^10 elements, arity {A:>2}: {fmt(m)}")
