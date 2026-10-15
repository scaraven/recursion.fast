/- S6a review probe P3: the kernel control's G chip is L_chain(1024)'s G chip up to the height pin.
   `lake env lean probes/s6a/GchipLink.lean` (imports the rendered ChainData). -/
import RecursionFast.Controls.ChainData

open RecursionFast RecursionFast.Controls.Chain

/-- Matrix `j` of a chip's gadget, its indices read as naturals. -/
def entsN (C : Chip K) (j : ℕ) : List (ℕ × ℕ × K) :=
  if h : j < C.gadget.t then (C.gadget.M ⟨j, h⟩).map fun e => (e.1.val, e.2.1.val, e.2.2) else []

/-- Term `i` of a chip's gadget: its matrix multiset and coefficient. -/
def termN (C : Chip K) (i : ℕ) : List ℕ × K :=
  if h : i < C.gadget.q then ((C.gadget.S ⟨i, h⟩).map Fin.val, C.gadget.c ⟨i, h⟩) else ([], 0)

/-- Same columns, ports, shape, terms, no fixed table, same gate matrix, and the same linear matrix
except entry 13 (`rho_last`'s constant: `γ^1` in the one-call harness, `γ^(160·1024 − 1)` in
the benchmark). -/
theorem G_link :
    LG0_chip1.cols = Lchain_chip1.cols ∧ LG0_chip1.ports = Lchain_chip1.ports ∧
    LG0_chip1.fixed.isNone ∧ Lchain_chip1.fixed.isNone ∧
    LG0_chip1.gadget.cons = Lchain_chip1.gadget.cons ∧ LG0_chip1.gadget.t = Lchain_chip1.gadget.t ∧
    LG0_chip1.gadget.q = Lchain_chip1.gadget.q ∧ termN LG0_chip1 0 = termN Lchain_chip1 0 ∧
    entsN LG0_chip1 0 = entsN Lchain_chip1 0 ∧
    (entsN LG0_chip1 1).eraseIdx 13 = (entsN Lchain_chip1 1).eraseIdx 13 ∧
    ((entsN LG0_chip1 1)[13]?).map (·.1) = some 6 ∧ ((entsN Lchain_chip1 1)[13]?).map (·.1) = some 6 := by
  decide +kernel

#print axioms G_link
