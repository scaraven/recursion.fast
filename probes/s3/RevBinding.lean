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

/-- A collision of the configured hash. -/
def Collision : Prop := ∃ m m' : List UInt8, m ≠ m' ∧ cfg.hash.run m = cfg.hash.run m'

/-- A well-formed path level: `A - 1` digests of 32 bytes. -/
def LevelOK (lev : List Digest) : Prop := lev.length = cfg.arity - 1 ∧ ∀ d ∈ lev, d.length = 32

theorem flatten_length_32 (s : List Digest) (hs : ∀ e ∈ s, e.length = 32) :
    s.flatten.length = 32 * s.length := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons,
      hs a List.mem_cons_self, ih fun e he => hs e (List.mem_cons_of_mem _ he)]
    ring

/-- The inserted digest is recovered from the flattened level. -/
theorem flatten_insert (s : List Digest) (d : Digest) (q : ℕ)
    (hs : ∀ e ∈ s, e.length = 32) (hd : d.length = 32) :
    ((s.take q ++ d :: s.drop q).flatten.drop (32 * (s.take q).length)).take 32 = d := by
  have hl := flatten_length_32 (s.take q) fun e he => hs e (List.mem_of_mem_take he)
  rw [List.flatten_append, List.flatten_cons, ← hl, List.drop_left]
  simp [hd]

theorem climb_binding (path path' : List (List Digest)) (d d' : Digest) (p : ℕ)
    (hd : d.length = 32) (hd' : d'.length = 32) (hlen : path.length = path'.length)
    (hp : ∀ lev ∈ path, LevelOK cfg lev) (hp' : ∀ lev ∈ path', LevelOK cfg lev)
    (h : climb cfg d p path = climb cfg d' p path') : d = d' ∨ Collision cfg := by
  induction path generalizing path' d d' p with
  | nil =>
    cases path' with
    | nil => exact Or.inl (by simpa [climb] using h)
    | cons _ _ => simp at hlen
  | cons s path ih =>
    cases path' with
    | nil => simp at hlen
    | cons s' path' =>
      simp only [climb] at h
      have hA := cfg.two_le_arity
      have hs := hp s List.mem_cons_self
      have hs' := hp' s' List.mem_cons_self
      rcases ih path' _ _ (p / cfg.arity) (HashId.run_length _ _) (HashId.run_length _ _)
          (by simpa using hlen) (fun l hl => hp l (List.mem_cons_of_mem _ hl))
          (fun l hl => hp' l (List.mem_cons_of_mem _ hl)) h with he | hc
      · by_cases hm : (s.take (p % cfg.arity) ++ d :: s.drop (p % cfg.arity)).flatten =
            (s'.take (p % cfg.arity) ++ d' :: s'.drop (p % cfg.arity)).flatten
        · left
          have hq : p % cfg.arity ≤ s.length := by rw [hs.1]; have := Nat.mod_lt p (by omega : 0 < cfg.arity); omega
          have hq' : p % cfg.arity ≤ s'.length := by rw [hs'.1]; have := Nat.mod_lt p (by omega : 0 < cfg.arity); omega
          have e1 := flatten_insert s d (p % cfg.arity) hs.2 hd
          have e2 := flatten_insert s' d' (p % cfg.arity) hs'.2 hd'
          rw [List.length_take_of_le hq] at e1
          rw [List.length_take_of_le hq', ← hm] at e2
          rw [← e1, ← e2]
        · exact Or.inr ⟨_, _, hm, he⟩
      · exact Or.inr hc

theorem verifyPath_binding (r : Digest) (l : ℕ) (leaf leaf' : List K)
    (path path' : List (List Digest)) (hlen : path.length = path'.length)
    (hp : ∀ lev ∈ path, LevelOK cfg lev) (hp' : ∀ lev ∈ path', LevelOK cfg lev)
    (h : verifyPath cfg r l leaf path = true) (h' : verifyPath cfg r l leaf' path' = true) :
    leaf = leaf' ∨ Collision cfg := by
  simp only [verifyPath, beq_iff_eq] at h h'
  rcases climb_binding cfg path path' _ _ l (HashId.run_length _ _) (HashId.run_length _ _) hlen
      hp hp' (h.trans h'.symm) with he | hc
  · by_cases hb : leaf.flatMap K.bytes = leaf'.flatMap K.bytes
    · left; rw [← kList_flatMap leaf, ← kList_flatMap leaf', hb]
    · exact Or.inr ⟨_, _, hb, he⟩
  · exact Or.inr hc

theorem takeN_length : ∀ (n : ℕ) (t acc b t' : List UInt8),
    takeN n t acc = some (b, t') → b.length = n + acc.length
  | 0, t, acc, b, t', h => by simp [takeN] at h; obtain ⟨rfl, -⟩ := h; simp
  | n + 1, [], acc, b, t', h => by simp [takeN] at h
  | n + 1, c :: t, acc, b, t', h => by
    have := takeN_length n t (c :: acc) b t' h; simp at this; omega

theorem readMany_shape {α : Type} (r : Tape → Option (α × Tape)) (Q : α → Prop)
    (hr : ∀ t a t', r t = some (a, t') → Q a) :
    ∀ (n : ℕ) (t : Tape) (as : List α) (t' : Tape), readMany r n t = some (as, t') →
      as.length = n ∧ ∀ a ∈ as, Q a
  | 0, t, as, t', h => by simp [readMany] at h; obtain ⟨rfl, -⟩ := h; simp
  | n + 1, t, as, t', h => by
    simp only [readMany] at h
    split at h
    · rename_i a t1 hrt
      obtain ⟨⟨as', t''⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      obtain ⟨hl, hq⟩ := readMany_shape r Q hr n t1 as' t'' h1
      refine ⟨by simp [hl], ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hr _ _ _ hrt
      · exact hq b hb
    · simp at h

/-- What `readOpening` returns has the fixed shape: `depth` levels of `A - 1` 32-byte digests. -/
theorem readOpening_shape (o : OShape) (t : Tape) (leaf : List K) (path : List (List Digest))
    (t' : Tape) (h : readOpening cfg o t = some (leaf, path, t')) :
    path.length = cfg.depth o ∧ ∀ lev ∈ path, LevelOK cfg lev := by
  simp only [readOpening] at h
  split at h
  · obtain ⟨⟨ps, t''⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨-, rfl, -⟩ := h2
    exact readMany_shape _ (LevelOK cfg) (fun t lev t' hlev =>
      readMany_shape _ (fun d : Digest => d.length = 32)
        (fun t d t' hd => by simpa using takeN_length 32 t [] d t' hd) _ t lev t' hlev) _ _ _ _ h1
  · simp at h

/-- **Merkle binding at a fixed depth, without a leaf/node tag (S3-A2).** Two openings that
`runQ` would accept for the same oracle shape, root and leaf position (read from any two tapes)
carry the same leaf, unless the configured hash has a collision. -/
theorem opening_binding (o : OShape) (r : Digest) (l : ℕ) (t u t' u' : Tape)
    (leaf leaf' : List K) (path path' : List (List Digest))
    (h1 : readOpening cfg o t = some (leaf, path, t'))
    (h2 : readOpening cfg o u = some (leaf', path', u'))
    (v1 : verifyPath cfg r l leaf path = true) (v2 : verifyPath cfg r l leaf' path' = true) :
    leaf = leaf' ∨ Collision cfg := by
  obtain ⟨hl1, hp1⟩ := readOpening_shape cfg o t leaf path t' h1
  obtain ⟨hl2, hp2⟩ := readOpening_shape cfg o u leaf' path' u' h2
  exact verifyPath_binding cfg r l leaf leaf' path path' (hl1.trans hl2.symm) hp1 hp2 v1 v2

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

#print axioms RecursionFast.S3Review.opening_binding
#print axioms RecursionFast.S3Review.kList_bytes
#print axioms RecursionFast.S3Review.key_digest_is_node
#print axioms RecursionFast.S3Review.decode_kat
#print axioms RecursionFast.S3Review.pass_extend
