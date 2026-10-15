/-
  RecursionFast.Clean.FiniteField  (UNTRUSTED, kernel-checked; Stage 8, DESIGN §9.3 item 1)

  Clean's `FiniteField` class for the contract's `K = GF(2^64)` (`Contract/Field.lean`): the field
  structure is the library's `K.instField` (`Library/Field.lean`, the contract's own `0, 1, +, *`),
  and the embedding into `ℕ` is the bit-pattern reading Clean's class documents for binary fields:
  `val a` is the 64-bit word `a.bits` read as a natural number (bit `i` = coefficient of `x^i`),
  `fromNat n` is the low 64 bits of `n`, `size = 2^64`. Never `Nat.cast`, which in characteristic 2
  collapses to `{0, 1}` (`natCast_two`).
-/
import RecursionFast.Library.Field
import Clean.Utils.FiniteField

namespace RecursionFast

namespace K

/-- **`FiniteField K`**: `K.instField` with the bit-pattern embedding `val a = a.bits.toNat`,
`fromNat n = n mod 2^64` as a bit pattern, `size = 2^64`. -/
instance instFiniteField : FiniteField K :=
  { K.instField with
    val := fun a => a.bits.toNat
    fromNat := fun n => ⟨BitVec.ofNat 64 n⟩
    size := 2 ^ 64
    val_lt := fun a => a.bits.isLt
    val_injective := fun a b h => by
      cases a; cases b; exact congrArg K.mk (BitVec.eq_of_toNat_eq h)
    val_fromNat := fun n hn => by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    val_zero := rfl
    val_one := rfl }

theorem val_eq (a : K) : FiniteField.val a = a.bits.toNat := rfl

theorem fromNat_eq (n : ℕ) : (FiniteField.fromNat n : K) = ⟨BitVec.ofNat 64 n⟩ := rfl

theorem size_eq : FiniteField.size K = 2 ^ 64 := rfl

/-- `val` of `x` is `2`: the element `x` (bit 1), not `1 + 1`. -/
example : FiniteField.val (FiniteField.fromNat 2 : K) = 2 := rfl

/-- `Nat.cast` is not the embedding: `(2 : ℕ)` casts to `1 + 1 = 0` in characteristic 2. -/
theorem natCast_two : ((2 : ℕ) : K) = 0 := by
  rw [Nat.cast_ofNat]; exact CharTwo.two_eq_zero

end K

end RecursionFast
