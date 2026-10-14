/-
  RecursionFast.Library.Blake2s  (UNTRUSTED, kernel-checked)

  General facts about the contract's hash (`Contract/Hash/Blake2s.lean`), for later stages and
  submitters; the known-answer vectors are in `Controls/Blake2s.lean`.

  * `Blake2s.rotr_eq_rotateRight`: the trusted `rotr` (machine shifts) is leanerVM's
    `⟨x.toBitVec.rotateRight n⟩` for every `n < 32` (the vendored deviation D-S2-1 changes no
    value). The hypothesis is needed: the two differ at `n = 33`. This is the bridge from
    leanerVM's `compress` (and its Clean BLAKE2s table) to `RecursionFast.Blake2s.compress`.
  * `blake2s_length`, `blake2s256_length`: a digest has `min nn 32` bytes; BLAKE2s-256 (the `D` of
    DESIGN §5.1 and the `d2` aggregate) has 32, i.e. four elements of `K`.
-/
import RecursionFast.Contract.Hash.Blake2s

namespace RecursionFast

/-- The vendored `rotr` (machine shifts) is leanerVM's `⟨x.toBitVec.rotateRight n⟩` for `n < 32`. -/
theorem Blake2s.rotr_eq_rotateRight (x : UInt32) (n : Nat) (hn : n < 32) :
    Blake2s.rotr x n = ⟨x.toBitVec.rotateRight n⟩ := by
  apply UInt32.toBitVec_inj.mp
  cases n <;> simp [Blake2s.rotr, BitVec.rotateRight, BitVec.rotateRightAux, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (Nat.sub_lt_succ 31 _)]

/-- A digest has `min nn 32` bytes. -/
theorem blake2s_length (key : List UInt8) (nn : Nat) (msg : List UInt8) :
    (blake2s key nn msg).length = min nn 32 := by
  simp [blake2s, List.map_const']

/-- A BLAKE2s-256 digest has 32 bytes (four elements of `K`). -/
theorem blake2s256_length (msg : List UInt8) : (blake2s256 msg).length = 32 :=
  blake2s_length [] 32 msg

end RecursionFast
