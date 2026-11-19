/-
# Controls: the library's strict witness-sending verifier

Canaries for the verifier `check vk c π` and its node proofs with signed children.
Kernel-checked; no proof here evaluates Keccak-256. Each canary is stated for every proof and
every key, not checked on one concrete proof by kernel evaluation.

Format (positive): `encode_leaf_kat` (the bytes of a leaf proof of two blocks: `u64 0 ‖ u64 2 ‖
x_0 ‖ x_1`, the layout the toy prover emits), `decode_leaf_kat`,
`encode_node_kat` (a node proof is the bytes of `Controls/Extractor.lean`'s `nodeKatWords`).
Verifier (negative), for every key and statement:
* `size_mod_eight`: an accepted proof has a multiple of 8 bytes; so **one appended byte**
  (`appended_byte_rejected`) and **one removed byte** (`truncated_rejected`) are rejected, on
  every honest proof;
* `appended_rejected`: anything appended to an accepted proof is rejected (decoding ignores
  trailing words, the canonical-encoding check does not);
* `bad_tag_rejected` (an unknown tag word), `leaf_over_leafCap_rejected` (a leaf of more than
  `leafCap` blocks, before any hash), `stmt_unique` (a proof is accepted under at most one
  statement: the flipped-bit and swapped-child canaries), `node_children_word` (an accepted
  node's children's proof lengths fit a word: no lower cap), `node_children_untraced` (an
  accepted node's children carry empty traces).
Verifier (positive): `leaf_accepted` (every leaf of at most `leafCap` blocks, under the statement
of its root and size), `leaf_empty_accepted`, `check_iff` (the library's characterisation).
Linear-time code: `decodeF_eq`, `encodeF_eq` (the twins equal the specifications for every
proof and witness), and the word-level hashes of `Library/Fast.lean`.
-/
import RecursionFast.Controls.Extractor

namespace RecursionFast.Controls.WitnessSending
open RecursionFast RecursionFast.WitnessSending
open RecursionFast.Controls.Extractor (nodeKat nodeKatWords witWords_node_kat)

/-- The digest whose bytes are all `b`. -/
abbrev dg (b : UInt8) : Digest := Vector.replicate 32 b

/-- A small leaf witness: the blocks `01…01` and `02…02`. -/
abbrev w₀ : Wit := .leaf [dg 1, dg 2]

/-- The leaf proof is the tag `u64 0`, the count `u64 2`, then the two blocks: 80 bytes. -/
theorem encode_leaf_kat : encode w₀ = ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2]⟩ := by decide +kernel

theorem decode_leaf_kat : decode (encode w₀) = some w₀ :=
  decode_encode w₀ (show 2 < 2 ^ 64 by decide)

/-- A node proof is the bytes of its output words, here `nodeKatWords`. -/
theorem encode_node_kat : encode nodeKat = ⟨(wordsBytes nodeKatWords).toArray⟩ := by
  rw [encode, witWords_node_kat]

/-! ## Strictness -/

/-- `π` with the byte `b` appended. -/
def appendByte (π : Proof) (b : UInt8) : Proof := π.push b

/-- `π` without its last byte. -/
def dropLast (π : Proof) : Proof := ⟨π.data.pop⟩

/-- **An accepted proof has a multiple of 8 bytes.** -/
theorem size_mod_eight {vk c : Digest} {π : Proof} (h : check vk c π = true) : π.size % 8 = 0 := by
  obtain ⟨w, -, rfl⟩ := check_canonical h
  rw [size_encode, Nat.mul_mod_right]

/-- **One appended byte is rejected**, on every honest proof, statement and key. -/
theorem appended_byte_rejected (vk c : Digest) (w : Wit) (b : UInt8) :
    check vk c (appendByte (encode w) b) = false := Bool.eq_false_iff.mpr fun h => by
  have := size_mod_eight h
  simp only [appendByte, ByteArray.size_push, size_encode] at this
  omega

/-- **One removed byte is rejected**, on every honest proof, statement and key. -/
theorem truncated_rejected (vk c : Digest) (w : Wit) :
    check vk c (dropLast (encode w)) = false := by
  have hpos : 0 < (witWords w).length := by cases w <;> simp [witWords]
  refine Bool.eq_false_iff.mpr fun h => ?_
  have := size_mod_eight h
  simp only [dropLast, ByteArray.size, Array.size_pop] at this
  rw [show (encode w).data.size = (encode w).size from rfl, size_encode] at this
  omega

theorem packBytes_wordsBytes_append (ws : List Word) (b : List UInt8) :
    packBytes (wordsBytes ws ++ b) = ws ++ packBytes b := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [show wordsBytes (w :: ws) = wordBytes w ++ wordsBytes ws from rfl, List.append_assoc,
      packBytes_append8 _ (wordBytes_length w), ih, ofLE_wordBytes]
    simp [toWord]

/-- Decoding ignores what follows an encoded witness. -/
theorem decode_encode_append {w : Wit} (hw : w.Fits) (b : List UInt8) :
    decode ⟨((encode w).data.toList ++ b).toArray⟩ = some w := by
  have h := readWit_witWords w hw (packBytes b)
  simp only [decode, encode_data, packBytes_wordsBytes_append, decodeWit, StateT.run',
    StateT.run] at h ⊢
  exact congrArg (Prod.fst <$> ·) h

/-- **Anything appended to an accepted proof is rejected.** -/
theorem appended_rejected {vk c : Digest} {π : Proof} (h : check vk c π = true) {b : List UInt8}
    (hb : b ≠ []) : check vk c ⟨(π.data.toList ++ b).toArray⟩ = false := by
  obtain ⟨w, -, rfl, hR⟩ := (check_iff vk c π).mp h
  refine Bool.eq_false_iff.mpr fun h' => hb ?_
  obtain ⟨w', hd, he⟩ := check_canonical h'
  rw [decode_encode_append (fits_of_rel hR)] at hd
  cases hd
  simpa using congrArg (fun π : Proof => π.data.toList) he

/-- The leaf's bytes with tag word 2: rejected under every key and statement. -/
theorem bad_tag_rejected (vk c : Digest) :
    check vk c ⟨#[2, 0, 0, 0, 0, 0, 0, 0] ++ (encode w₀).data.extract 8 80⟩ = false := by
  rw [check_eq, show decode ⟨#[2, 0, 0, 0, 0, 0, 0, 0] ++ (encode w₀).data.extract 8 80⟩ = none
    by decide +kernel]

/-- A leaf proof of `leafCap + 1` blocks is rejected, before any hash. -/
theorem leaf_over_leafCap_rejected (vk c : Digest) {xs : List Digest}
    (h : xs.length = leafCap + 1) : check vk c (encode (.leaf xs)) = false := by
  rw [check_eq, decode_encode (.leaf xs) (show xs.length < 2 ^ 64 by rw [h]; decide)]
  simp [h, leafCap]

/-- **A proof is accepted under at most one statement**, under each key. -/
theorem stmt_unique {vk c c' : Digest} {π : Proof} (h : check vk c π = true)
    (h' : check vk c' π = true) : c = c' := by
  obtain ⟨w, hd, hR⟩ := check_sound h
  obtain ⟨w', hd', hR'⟩ := check_sound h'
  cases hd ▸ hd'
  cases w with
  | leaf xs => exact hR.2.trans hR'.2.symm
  | node c₁ c₂ p₁ p₂ => exact hR.1.trans hR'.1.symm

/-- An accepted node proof's children's proof lengths fit a word. -/
theorem node_children_word {vk c c₁ c₂ : Digest} {π : Proof} {p₁ p₂ : Signed}
    (h : check vk c π = true) (hd : decode π = some (.node c₁ c₂ p₁ p₂)) :
    p₁.π.size < 2 ^ 64 ∧ p₂.π.size < 2 ^ 64 := by
  obtain ⟨w, hd', hR⟩ := check_sound h
  cases hd ▸ hd'
  exact ⟨(fits_of_acc hR.2.1).1, (fits_of_acc hR.2.2).1⟩

/-- An accepted node proof's children carry empty traces (this verifier asks no query). -/
theorem node_children_untraced {vk c c₁ c₂ : Digest} {π : Proof} {p₁ p₂ : Signed}
    (h : check vk c π = true) (hd : decode π = some (.node c₁ c₂ p₁ p₂)) :
    p₁.tr = [] ∧ p₂.tr = [] := by
  obtain ⟨w, hd', hR⟩ := check_sound h
  cases hd ▸ hd'
  obtain ⟨-, h₁, h₂⟩ := hR
  simp only [acc_eq, Bool.and_eq_true, List.isEmpty_iff] at h₁ h₂
  exact ⟨h₁.2.1, h₂.2.1⟩

/-- The honest proof of a leaf of at most `leafCap` blocks is accepted under the statement of its
root and size, under every key. -/
theorem leaf_accepted (vk : Digest) {xs : List Digest} (hn : xs.length ≤ leafCap) :
    check vk (leafStmt (dataRoot xs) xs.length) (encode (.leaf xs)) = true :=
  check_encode (show Rel _ _ (.leaf xs) from ⟨hn, rfl⟩)

/-- The honest proof of the leaf of no block is accepted, under every key. -/
theorem leaf_empty_accepted (vk : Digest) :
    check vk (leafStmt (dataRoot []) 0) (encode (.leaf [])) = true :=
  check_encode (show Rel _ _ (.leaf []) from ⟨Nat.zero_le _, rfl⟩)

example (vk c : Digest) (π : Proof) : check vk c π = true ↔
    ∃ w, decode π = some w ∧ encode w = π ∧ Rel (submission.acc vk) c w := check_iff vk c π

example (π : Proof) : decodeF π = decode π := decodeF_eq π

example (w : Wit) : encodeF w = encode w := encodeF_eq w

end RecursionFast.Controls.WitnessSending
