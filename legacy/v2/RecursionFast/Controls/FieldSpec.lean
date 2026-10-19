/-
# Controls: the fields

`K_spec` (DESIGN §2: may be promoted into the controls): the contract's `+, *, 0, 1` on K are
those of `GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`, irreducible, via an explicit bijection.
`|K| = 2^64`, `|E| = 2^192`, `E` is a field. Kernel-evaluated test vectors (CompPoly's) pin the
arithmetic: `x^63 · x = 0x1B`, `y^3 = y + 1`, `1 · 1 ≠ 0`.
-/
import RecursionFast.Library.Challenges

namespace RecursionFast.Controls
open RecursionFast Polynomial

example : Irreducible K.f64 ∧ ∃ e : K ≃ AdjoinRoot K.f64,
    e 0 = 0 ∧ e 1 = 1 ∧ (∀ a b : K, e (a + b) = e a + e b) ∧ (∀ a b : K, e (a * b) = e a * e b) :=
  K.K_spec

example : Fintype.card K = 2 ^ 64 := K.card_K
example : Fintype.card E = 2 ^ 192 := E.card_E
example : ∀ a : E, a ≠ 0 → a * a⁻¹ = 1 := fun _ h => mul_inv_cancel₀ h

/-- `x^63 · x = x^64 = x^4 + x^3 + x + 1`. -/
theorem x63_mul_x : (⟨1 <<< 63⟩ : K) * ⟨2⟩ = ⟨0x1B⟩ := by decide +kernel
/-- `y · y · y = y + 1` in E. -/
theorem y_cubed : (⟨0, 1, 0⟩ : E) * ⟨0, 1, 0⟩ * ⟨0, 1, 0⟩ = ⟨1, 1, 0⟩ := by decide +kernel
theorem one_mul_one_ne_zero : (1 : K) * 1 ≠ 0 := by decide +kernel

end RecursionFast.Controls
