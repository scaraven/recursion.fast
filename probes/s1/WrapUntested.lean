/- S1 review probe (S1-m1), updated in the S1 fix pass.

`viewNW` is a mutant of the trusted `view` in which the last row's "next row" is row `rows`
(outside the table) instead of row 0 (the three contract cells unchanged). The mutant relation
`relNW` (= `Layout.relBelow` with `viewNW`) agrees with `rel` on the Fibonacci controls (the
last-row flag switches the transition off on the wrapping row), and the adopted controls
`Controls.wrap_pos`/`wrap_neg` separate `rel` from the mutant in both directions. -/
import RecursionFast.Controls

open RecursionFast RecursionFast.Controls

namespace S1Probe

section
variable {F : Type} [Zero F] [One F] [Add F] [Mul F] [DecidableEq F]

/-- Mutant view: no wrap; the last row reads row `rows`. -/
def viewNW (C : Chip F) (T : Table F) (r : ℕ) : Fin (C.cols + C.cols + 3) → F := fun i =>
  if i.val < C.cols then T.cell r i
  else if i.val < C.cols + C.cols then T.cell (r + 1) (i - C.cols)
  else match i.val - (C.cols + C.cols) with
    | 0 => 1
    | 1 => if r = 0 then 1 else 0
    | _ => if r + 1 = T.rows then 1 else 0

/-- `relBelow` with the mutant view. -/
def relNW (L : Layout F) (N k : ℕ) (x : Fin 32 → F) (w : List (Table F)) : Prop :=
  w.length = L.chips.length ∧
  (∀ ct ∈ L.chips.zip w, ∀ t ∈ ct.1.fixed,
    ct.2.rows = t.rows ∧ ∀ r < t.rows, ∀ c < ct.1.cols, ct.2.cell r c = t.cell r c) ∧
  (∀ ct ∈ L.chips.zip w, ∀ r < ct.2.rows, ct.1.gadget.holds (viewNW ct.1 ct.2 r)) ∧
  (∀ b < N, (L.bus b).Balanced (traffic L w b true) (traffic L w b false)) ∧
  (∃ T ∈ w[L.pub]?, 1 ≤ T.rows ∧ ∀ i : Fin 32, T.cell 0 i = x i) ∧
  ((L.chips.zip w).map fun ct => ct.2.rows * ct.1.cols).sum ≤ 2 ^ k

instance (L : Layout F) (N k : ℕ) (x : Fin 32 → F) (w : List (Table F)) :
    Decidable (relNW L N k x w) := by
  unfold relNW Gadget.holds; infer_instance
end

/-! The mutant agrees with `rel` on the Fibonacci controls ... -/

theorem fib_pos_NW : relNW fib 0 7 (stmt [1, 1]) [fibTab] := by decide +kernel

theorem fib_neg_NW : ¬ relNW fib 0 7 (stmt [1, 1]) [tab [[1, 1], [1, 0], [0, 1], [0, 1]]] := by
  decide +kernel

/-! ... and the wrap controls separate them. -/

/-- The mutant rejects `wrap_pos`'s witness ... -/
theorem wrap_pos_NW : ¬ relNW inc 0 7 (stmt [1]) [tab [[1], [0]]] := by decide +kernel

/-- ... and accepts `wrap_neg`'s. -/
theorem wrap_neg_NW : relNW inc 0 7 (stmt [1]) [tab [[1], [0], [1]]] := by decide +kernel

end S1Probe
