/-
  RecursionFast.Library.Challenges  (UNTRUSTED, kernel-checked)

  The contract's round types are finite and nonempty, so `Nat.card` in `RbrKS` is their size:
  a challenge round `chal nE idx` has exactly `2^(192·nE + Σ idx)` values.
-/
import RecursionFast.Contract.Shapes
import RecursionFast.Library.Field
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

namespace RecursionFast

/-- `BitVec n ≃ Fin (2^n)`. -/
def bitVecEquivFin (n : ℕ) : BitVec n ≃ Fin (2 ^ n) where
  toFun := BitVec.toFin
  invFun := BitVec.ofFin
  left_inv _ := rfl
  right_inv _ := rfl

instance (n : ℕ) : Finite (BitVec n) := Finite.of_equiv _ (bitVecEquivFin n).symm

theorem natCard_bitVec (n : ℕ) : Nat.card (BitVec n) = 2 ^ n := by
  rw [Nat.card_congr (bitVecEquivFin n), Nat.card_eq_fintype_card, Fintype.card_fin]

theorem natCard_K : Nat.card K = 2 ^ 64 := by
  rw [Nat.card_eq_fintype_card, K.card_K]

theorem natCard_E : Nat.card E = 2 ^ 192 := by
  rw [Nat.card_eq_fintype_card, E.card_E]

instance (r : Round) : Finite r.Ty := by
  cases r with
  | msg o => exact inferInstanceAs (Finite (Fin _ → K))
  | chal nE idx => exact inferInstanceAs (Finite ((Fin nE → E) × ((j : Fin idx.length) → BitVec (idx.get j))))

instance (r : Round) : Nonempty r.Ty := by
  cases r with
  | msg o => exact ⟨fun _ => 0⟩
  | chal nE idx => exact ⟨(fun _ => 0, fun _ => 0)⟩

/-- Size of a challenge round. -/
theorem natCard_chal (nE : ℕ) (idx : List ℕ) :
    Nat.card (Round.chal nE idx).Ty = 2 ^ (192 * nE) * ∏ j : Fin idx.length, 2 ^ idx.get j := by
  change Nat.card ((Fin nE → E) × ((j : Fin idx.length) → BitVec (idx.get j))) = _
  rw [Nat.card_prod, Nat.card_fun, natCard_E, Nat.card_fin, ← pow_mul, Nat.card_pi]
  simp only [natCard_bitVec]

theorem natCard_pos (r : Round) : 0 < Nat.card r.Ty := Nat.card_pos

end RecursionFast
