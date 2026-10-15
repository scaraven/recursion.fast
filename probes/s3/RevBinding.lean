/- S3 review probe (kernel-checked, general; no hash evaluation).

1. `opening_binding`: two openings that `runQ` accepts for the same oracle shape, root and leaf
   position carry the same leaf, or the configured hash has a collision. The proof uses only the
   fixed depth and the fixed per-level input lengths (`readOpening`), never a leaf/node tag: the
   formal content of S3-A2's "binding at a fixed depth reduces to collision resistance".
2. `K.bytes_ofBytes`, `kList_bytes`: every 8-byte string is the canonical encoding of an element,
   so a tape has no non-canonical (malleable) element encodings.
3. `key_digest_is_node`: the key digest `H(VKc bytes)` of a 4-element key is, at arity 2, the
   Merkle node over the key's 32 bytes and the index root: the seed hash shares the tree's input
   domain (contradicting "sponge inputs have length 1 mod 8" for the seed).
4. `pass_extend`: bytes after the rounds section change neither the round bytes nor the
   challenges (the openings cannot influence a challenge).
5. `decode_kat`: a known-answer test of challenge decoding (`E` limbs, index offsets), the
   control that kills the surviving mutant `NARGoff` of `RevMutants.lean`.
Run: `lake env lean probes/s3/RevBinding.lean` (≈ 13 s, no hash evaluation).
-/
import RecursionFast.Library.Compile

namespace RecursionFast.S3Review
open RecursionFast

variable (cfg : Cfg)

-- `Collision`, `LevelOK`, `climb_binding`, `verifyPath_binding`, `readOpening_shape` and
-- `opening_binding` moved to `RecursionFast/Library/Compile.lean` (S9 fix pass, S9D-m5).

/-! ## Canonical encodings -/

/-- Every 8-byte string is the encoding of the element it decodes to. -/
theorem K.bytes_ofBytes (b : List UInt8) (h : b.length = 8) : (K.ofBytes b).bytes = b := by
  match b, h with
  | [c0, c1, c2, c3, c4, c5, c6, c7], _ =>
    simp only [K.bytes_eq, K.ofBytes, wordOfBytes, List.take_succ_cons, List.take_zero,
      List.foldr_cons, List.foldr_nil, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · apply UInt8.toBitVec_inj.mp
      ext i hi
      simp only [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
      interval_cases i <;> simp

/-- Element lists read back from byte strings of length `8 n` re-encode to those bytes. -/
theorem kList_bytes (b : List UInt8) (n : ℕ) (h : b.length = 8 * n) :
    (kList b).flatMap K.bytes = b := by
  induction n generalizing b with
  | zero => simp at h; subst h; rfl
  | succ n ih =>
    obtain ⟨c, r, rfl, hc, hr⟩ : ∃ c r, b = c ++ r ∧ c.length = 8 ∧ r.length = 8 * n :=
      ⟨b.take 8, b.drop 8, by simp, by simp [h], by simp [h]; omega⟩
    have hk : kList (c ++ r) = K.ofBytes c :: kList r := by
      have : c ++ r = (K.ofBytes c :: kList r).flatMap K.bytes := by
        rw [List.flatMap_cons, K.bytes_ofBytes c hc, ih r hr]
      rw [this, kList_flatMap]
    rw [hk, List.flatMap_cons, K.bytes_ofBytes c hc, ih r hr]

/-! ## The key digest shares the tree's input domain -/

/-- Arity 2. -/
def c2 : Cfg := ⟨.blake2s, 2, by decide⟩

/-- At arity 2 the key digest of a 4-element key is the Merkle node over the key's 32 bytes and
the index root (`8 · vkLen + 32 = 32 · A` with `vkLen = 4`). -/
theorem key_digest_is_node (vk : Fin 4 → K) (root : Digest) :
    c2.hash.run (VKc.toBytes (vk, root)) = climb c2 root 1 [[(List.ofFn vk).flatMap K.bytes]] := by
  simp [climb, VKc.toBytes, c2]

/-! ## The challenges do not depend on the openings section -/

theorem takeN_extend : ∀ (n : ℕ) (t u acc b t' : List UInt8),
    takeN n t acc = some (b, t') → takeN n (t ++ u) acc = some (b, t' ++ u)
  | 0, t, u, acc, b, t', h => by simp [takeN] at h ⊢; exact ⟨h.1, by rw [h.2]⟩
  | n + 1, [], u, acc, b, t', h => by simp [takeN] at h
  | n + 1, c :: t, u, acc, b, t', h => by
    simp only [takeN, List.cons_append] at h ⊢; exact takeN_extend n t u (c :: acc) b t' h

/-- Appending bytes after the rounds section changes neither the round bytes nor (hence) the
Fiat–Shamir challenges: the openings cannot influence a challenge. -/
theorem pass_extend (rs : List Round) (s : Digest) (t u : Tape) (es es' : Array (List UInt8))
    (t' : Tape) (h : pass cfg rs s t es = some (es', t')) :
    pass cfg rs s (t ++ u) es = some (es', t' ++ u) := by
  induction rs generalizing s t es with
  | nil => simp [pass] at h ⊢; exact ⟨h.1, by rw [h.2]⟩
  | cons r rs ih =>
    cases r with
    | msg o =>
      simp only [pass] at h ⊢
      split at h
      · rename_i b t1 hb
        rw [takeN_extend _ _ _ _ _ _ hb]; exact ih _ _ _ h
      · simp at h
    | chal nE idx => simp only [pass] at h ⊢; exact ih _ _ _ h

/-! ## A known-answer test of challenge decoding (pins the `E` limbs and the index offsets) -/

/-- Bytes `0, 1, …, 47`. -/
def ramp : List UInt8 := (List.range 48).map Nat.toUInt8

/-- `chal 1 [8, 64]`: `E` limbs from bytes `0–7`, `8–15`, `16–23`; index 0 is the low 8 bits of
the word at byte 24 (`0x18`), index 1 the word at byte 32. A decoder reading index `j` at byte
`8 j` (the surviving mutant `NARGoff`) gives `0x00` and `0x0f0e0d0c0b0a0908` instead. -/
theorem decode_kat :
    ((Round.chal 1 [8, 64]).decode ramp).1 0 =
      ⟨⟨0x0706050403020100⟩, ⟨0x0f0e0d0c0b0a0908⟩, ⟨0x1716151413121110⟩⟩ ∧
    (((Round.chal 1 [8, 64]).decode ramp).2 ⟨0, by decide⟩).toNat = 0x18 ∧
    (((Round.chal 1 [8, 64]).decode ramp).2 ⟨1, by decide⟩).toNat = 0x2726252423222120 := by
  decide +kernel

end RecursionFast.S3Review

#print axioms RecursionFast.opening_binding
#print axioms RecursionFast.S3Review.kList_bytes
#print axioms RecursionFast.S3Review.key_digest_is_node
#print axioms RecursionFast.S3Review.decode_kat
#print axioms RecursionFast.S3Review.pass_extend
