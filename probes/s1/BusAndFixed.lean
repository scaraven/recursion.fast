/- S1 review probe (S1-m: two clauses of `rel` that no control pins).

1. `eq` buses count multiplicity. `eqMult_neg` (proposed control): the sender puts `5` once, the
   receiver takes it twice; `rel` rejects. Yet sent and received have the same *support*, so a
   relation that compared supports (sets) would accept; on the existing controls `twoChip_pos`
   and `twoChip_neg` the support test and the multiset test agree, so neither control tells
   "counted in ℕ" (DESIGN §2.1) from "as sets".
2. The fixed-table clause requires equal heights. `fixedHeight_neg` (proposed control): the
   fixed chip's table is `range4` plus a fifth row `(9, 1)`; the cells of `range4`'s rows agree
   and the lookup of `9` is then served, so only the height equation rejects it. `lookup_neg_fixed`
   changes a cell, not the height. -/
import RecursionFast.Controls

open RecursionFast RecursionFast.Controls

namespace S1Probe

/-- Support equality of the two directions of bus `b` (the mutant reading of `eq`). -/
def sameSupport (L : Layout K) (w : List (Table K)) (b : ℕ) : Prop :=
  (∀ m ∈ traffic L w b true, m ∈ traffic L w b false) ∧
    (∀ m ∈ traffic L w b false, m ∈ traffic L w b true)

instance (L : Layout K) (w : List (Table K)) (b : ℕ) : Decidable (sameSupport L w b) := by
  unfold sameSupport; infer_instance

def wDup : List (Table K) := [tab [[el 5, 1], [el 7, 1]], tab [[el 5, 1], [el 5, 1], [el 7, 1]]]

theorem eqMult_neg : ¬ twoChip.rel 7 (stmt [el 5, 1]) wDup := by
  rw [← relBelow_iff (N := 1) (by decide)]; decide +kernel

theorem eqMult_sameSupport : sameSupport twoChip wDup 0 := by decide +kernel

/-- On the existing controls the support test agrees with `rel`'s multiset test. -/
theorem twoChip_controls_support :
    sameSupport twoChip [tab [[el 5, 1], [el 7, 1]], tab [[el 7, 1], [el 5, 1], [el 9, 0]]] 0 ∧
    ¬ sameSupport twoChip [tab [[el 5, 1], [el 7, 1]], tab [[el 7, 1], [el 6, 1], [el 9, 0]]] 0 := by
  decide +kernel

def range4plus : Table K := tab [[el 0, 1], [el 1, 1], [el 2, 1], [el 3, 1], [el 9, 1]]

def wTall : List (Table K) := [tab [[el 2, 1], [el 9, 1]], range4plus]

theorem fixedHeight_neg : ¬ lookup.rel 7 (stmt [el 2, 1]) wTall := by
  rw [← relBelow_iff (N := 2) (by decide)]; decide +kernel

/-- Only the height equation rejects `wTall`: cells agree on `range4`'s rows, the lookup is served. -/
theorem fixedHeight_only :
    (∀ r < range4.rows, ∀ c < 2, range4plus.cell r c = range4.cell r c) ∧
    (∀ m ∈ traffic lookup wTall 1 false, m ∈ traffic lookup wTall 1 true) ∧
    range4plus.rows ≠ range4.rows := by
  decide +kernel

end S1Probe
