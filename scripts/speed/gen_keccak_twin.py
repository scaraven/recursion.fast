#!/usr/bin/env python3
"""Generates the word-level steps `thetaF`, `rhoF`, `piF`, `chiF` of `RecursionFast/Library/KeccakFast.lean`
(each the contract's step on the 25 fields of `S25`, in the contract's own association, so that the
step lemmas close by `simp` on the lane indices). `python3 scripts/speed/gen_keccak_twin.py` prints them."""
RHO = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]
def fields(es, per=4):
    rows = [", ".join(es[i:i + per]) for i in range(0, 25, per)]
    return "  ⟨" + ",\n   ".join(rows) + "⟩"
def gen():
    L = []
    L.append("/-- θ on separate words (`theta_toVec`). -/")
    L.append("@[inline] def thetaF (s : S25) : S25 :=")
    for x in range(5):
        L.append(f"  let c{x} := s.a{x} ^^^ s.a{x+5} ^^^ s.a{x+10} ^^^ s.a{x+15} ^^^ s.a{x+20}")
    for x in range(5):
        L.append(f"  let d{x} := c{(x+4)%5} ^^^ rotK c{(x+1)%5} 1")
    L.append(fields([f"s.a{i} ^^^ d{i%5}" for i in range(25)], 5))
    L.append("")
    L.append("/-- ρ on separate words, the offsets written out (`rho_toVec`). -/")
    L.append("@[inline] def rhoF (s : S25) : S25 :=")
    L.append(fields([f"rotK s.a{i} {RHO[i]}" for i in range(25)], 5))
    L.append("")
    L.append("/-- π on separate words: field `x + 5y` is field `(x + 3y) % 5 + 5x` (`pi_toVec`). -/")
    L.append("@[inline] def piF (s : S25) : S25 :=")
    L.append(fields([f"s.a{(x + 3*y) % 5 + 5*x}" for y in range(5) for x in range(5)], 9))
    L.append("")
    L.append("/-- χ on separate words (`chi_toVec`). -/")
    L.append("@[inline] def chiF (s : S25) : S25 :=")
    L.append(fields([f"s.a{x+5*y} ^^^ (~~~s.a{(x+1)%5+5*y} &&& s.a{(x+2)%5+5*y})" for y in range(5) for x in range(5)], 2))
    return "\n".join(L)
print(gen())
