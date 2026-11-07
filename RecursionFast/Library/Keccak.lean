/-
  RecursionFast.Library.Keccak  (UNTRUSTED, kernel-checked)

  General facts about the contract's hash (`Contract/Hash/Keccak.lean`), for the
  organiser's tools and for submitters; the known-answer vectors are in `Controls/Keccak.lean`.

  * `Keccak.rotl_eq_rotateLeft`: the trusted `rotl` (machine shifts) is `BitVec.rotateLeft` for
    every `n < 64`. The hypothesis is needed: the two differ at `n = 65`.
  * `Keccak.pad_length`: the padded message is a positive multiple of the rate, longer than the
    message, and at most one rate longer (one block of padding at most).
  * `keccak256_length`: a digest has 32 bytes.
-/
import RecursionFast.Contract.Hash.Keccak

namespace RecursionFast

/-- The trusted `rotl` (machine shifts) is the bit-vector rotation for `n < 64`. -/
theorem Keccak.rotl_eq_rotateLeft (w : UInt64) (n : Nat) (hn : n < 64) :
    Keccak.rotl w n = ⟨w.toBitVec.rotateLeft n⟩ := by
  apply UInt64.toBitVec_inj.mp
  cases n <;> simp [Keccak.rotl, BitVec.rotateLeft, BitVec.rotateLeftAux, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (Nat.sub_lt_succ 63 _), BitVec.ushiftRight_eq_zero]

/-- The padded message fills whole blocks, and the padding is `1 … rate` bytes. -/
theorem Keccak.pad_length (msg : List UInt8) :
    (Keccak.pad msg).length % Keccak.rate = 0 ∧ msg.length < (Keccak.pad msg).length ∧
      (Keccak.pad msg).length ≤ msg.length + Keccak.rate := by
  have h := Nat.mod_lt msg.length (show 0 < Keccak.rate by decide)
  have hp : (Keccak.pad msg).length = msg.length + (Keccak.rate - msg.length % Keccak.rate) := by
    simp only [Keccak.pad]
    split <;> simp_all [Keccak.rate] <;> omega
  rw [hp]
  refine ⟨?_, by omega, by omega⟩
  have := Nat.div_add_mod msg.length Keccak.rate
  rw [show msg.length + (Keccak.rate - msg.length % Keccak.rate) =
    Keccak.rate * (msg.length / Keccak.rate + 1) by rw [Nat.mul_succ]; omega, Nat.mul_mod_right]

/-- A Keccak-256 digest has 32 bytes. -/
theorem keccak256_length (msg : List UInt8) : (keccak256 msg).length = 32 := by
  simp [keccak256, List.map_const']

end RecursionFast
