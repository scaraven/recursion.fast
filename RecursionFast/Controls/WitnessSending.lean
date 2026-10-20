/-
# Controls: the library's strict witness-sending verifier (#10, V3-S2R-A5)

Ported from the S2a entry's `BaselineV3Controls.lean` (submissions repository) to the library's
`check`, which is now strict. Kernel-checked; no proof here evaluates BLAKE2s.

Format (positive): `encode_leaf_kat`, `encode_node_kat` (the bytes the native prover writes),
`decode_leaf_kat`.
Verifier (negative): `leaf_appended_rejected`, `leaf_truncated_rejected`, `node_appended_rejected`,
`node_truncated_rejected`: one appended byte and one removed byte are rejected, on a leaf and on a
node proof, whatever the statement (the canaries of DESIGN-v3 §6.3 step 7; the S1 library
accepted the two leaf ones). `bad_tag_rejected`: an unknown tag word. `leaf_over_chainCap`: a
chain longer than `chainCap`, rejected before hashing. `stmt_unique`: a proof is accepted under at
most one statement (the flipped-bit and swapped-child canaries). `node_children_capped`.
Verifier (positive): `leaf_zero_accepted`.
Linear-time decoding: `decodeF_kat`, the linear decoder on the node's bytes (the equality with the
quadratic specification is `decodeF_eq`, for every proof).
-/
import RecursionFast.Controls.Extractor

namespace RecursionFast.Controls.WitnessSending
open RecursionFast RecursionFast.WitnessSending

/-- The digest whose bytes are all `b`. -/
abbrev dg (b : UInt8) : Digest := Vector.replicate 32 b

/-- A small leaf witness: start `01…01`, length 16. -/
abbrev w₀ : Wit := .leaf (dg 1) 16

theorem encode_leaf_kat : encode w₀ = ⟨#[0, 0, 0, 0, 0, 0, 0, 0,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    16, 0, 0, 0, 0, 0, 0, 0]⟩ := by decide +kernel

theorem decode_leaf_kat : decode (encode w₀) = some w₀ :=
  decode_encode w₀ (show 16 < 2 ^ 64 by decide)

/-- A small node witness: children `02…02`, `03…03`, proofs `aa bb cc` and `dd`. -/
abbrev n₀ : Wit := .node (dg 2) (dg 3) ⟨#[0xaa, 0xbb, 0xcc]⟩ ⟨#[0xdd]⟩

theorem encode_node_kat : encode n₀ = ⟨#[1, 0, 0, 0, 0, 0, 0, 0,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
    3, 0, 0, 0, 0, 0, 0, 0, 0xaa, 0xbb, 0xcc, 0, 0, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 0, 0xdd, 0, 0, 0, 0, 0, 0, 0]⟩ := by decide +kernel

theorem decodeF_kat : decodeF (encode n₀) = some n₀ := by decide +kernel

/-- `π` with the byte `b` appended. -/
def appendByte (π : Proof) (b : UInt8) : Proof := π.push b

/-- `π` without its last byte. -/
def dropLast (π : Proof) : Proof := ⟨π.data.pop⟩

theorem leaf_appended_rejected : check (dg 0) (appendByte (encode w₀) 0) = false := by
  rw [check_eq]; decide +kernel

theorem leaf_truncated_rejected : check (dg 0) (dropLast (encode w₀)) = false := by
  rw [check_eq]; decide +kernel

theorem node_appended_rejected : check (dg 0) (appendByte (encode n₀) 0) = false := by
  rw [check_eq]; decide +kernel

theorem node_truncated_rejected : check (dg 0) (dropLast (encode n₀)) = false := by
  rw [check_eq]; decide +kernel

/-- The leaf's bytes with tag word 2. -/
theorem bad_tag_rejected :
    check (dg 0) ⟨#[2, 0, 0, 0, 0, 0, 0, 0] ++ (encode w₀).data.extract 8 48⟩ = false := by
  rw [check_eq]; decide +kernel

/-- A leaf proof of a chain of `chainCap + 1` steps is rejected, before any hash. -/
theorem leaf_over_chainCap : check (dg 0) (encode (.leaf (dg 1) (chainCap + 1))) = false := by
  rw [check_eq]; decide +kernel

/-- **A proof is accepted under at most one statement.** -/
theorem stmt_unique {c c' : Digest} {π : Proof} (h : check c π = true) (h' : check c' π = true) :
    c = c' := by
  obtain ⟨w, hd, hR⟩ := check_sound h
  obtain ⟨w', hd', hR'⟩ := check_sound h'
  rw [hd] at hd'; cases hd'
  cases w with
  | leaf s n => exact hR.2.trans hR'.2.symm
  | node c₁ c₂ π₁ π₂ => exact hR.1.trans hR'.1.symm

/-- An accepted node proof's children are within `proofCap`. -/
theorem node_children_capped {c c₁ c₂ : Digest} {π π₁ π₂ : Proof} (h : check c π = true)
    (hd : decode π = some (.node c₁ c₂ π₁ π₂)) : π₁.size ≤ proofCap ∧ π₂.size ≤ proofCap := by
  obtain ⟨w, hd', hR⟩ := check_sound h
  rw [hd] at hd'; cases hd'
  exact fits_of_rel hR

/-- The honest proof of a zero-step leaf is accepted. -/
theorem leaf_zero_accepted (s : Digest) :
    check (leafStmt (chainEnd s 0) 0) (encode (.leaf s 0)) = true :=
  check_encode ⟨Nat.zero_le _, rfl⟩

end RecursionFast.Controls.WitnessSending
