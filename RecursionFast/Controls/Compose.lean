/-
# Controls: the composition walk (`Library/Compose.lean`, V4-8; RA-M1)

Negative (what the bare disjunction does not say). `forgery_trivial` is RA's probe P1, adapted
to the capped `Forgery`: under the key of any known signer and for every log within `logCap`, a
`Forgery` exists with no other hypothesis (a signed one-entry trace whose answer to the empty
query is not in the log, which exists since the log has fewer than `2^256` entries). So
`compose_exists_free`: `compose_exists`'s conclusion holds for such a key with none of its
hypotheses used. The content is `walk`'s (and `compose`'s) membership of the forgery in the
extraction tree of the root signed proof.

Positive. On the witness-sending submission under the reference signer's key, with the empty
log (functional, potential `0`), `walk` returns the leaf starts:
* `walk_one_leaf`: a one-leaf tree whose root is the signed leaf proof of `(s, n)` gives `[s]`;
* `walk_two_leaves`: a two-leaf tree whose root is the signed node proof over the two signed leaf
  proofs gives `[s₁, s₂]`.
Symbolic (`decode_encode`, `sigOk_sign`, `extract_of_E`, `walkFrom_leaf`); no hash is evaluated.
-/
import RecursionFast.Library.Compose
import RecursionFast.Library.WitnessSending
import RecursionFast.Controls.Relation

open scoped NNReal

namespace RecursionFast.Controls.Compose
open RecursionFast RecursionFast.Compose RecursionFast.WitnessSending
open RecursionFast.Controls.Relation (leafSigned acc_leafSigned)

/-! ## Negative: the bare disjunction is free under a known signer's key -/

/-- A log of at most `logCap` entries misses some answer to the empty query. -/
theorem fresh_answer (L : Log) (hlen : L.length ≤ logCap) :
    ∃ a : Digest, (ByteArray.empty, a) ∉ L := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hsub : (Finset.univ : Finset Digest) ⊆ (L.map Prod.snd).toFinset := fun a _ => by
    simpa using ⟨_, h a⟩
  have h1 := Finset.card_le_card hsub
  have h2 := List.toFinset_card_le (L.map Prod.snd)
  rw [Finset.card_univ, fintype_card_digest] at h1
  rw [List.length_map] at h2
  unfold logCap at hlen
  omega

/-- **RA probe P1**: under the key of any known signer and for every log within `logCap`, a
forgery against the log exists, with no other hypothesis. -/
theorem forgery_trivial (sk : ℕ → ℕ → Digest) (L : Log) (hlen : L.length ≤ logCap) :
    Nonempty (Forgery (Signer.pk sk) L) := by
  obtain ⟨a, ha⟩ := fresh_answer L hlen
  exact ⟨⟨⟨ByteArray.empty, [(ByteArray.empty, a)],
      Signer.sign sk 0 (traceDigest [(ByteArray.empty, a)])⟩,
    fun e he => List.mem_singleton.mp he ▸ Nat.zero_le _, Signer.sigOk_sign sk 0 (by decide) _,
    fun h => ha (h _ (List.mem_singleton_self _))⟩⟩

/-- Hence `compose_exists`'s conclusion, for such a key, uses none of its hypotheses but the
log's length. -/
theorem compose_exists_free (sk : ℕ → ℕ → Digest) (L : Log) (hlen : L.length ≤ logCap) (n : ℕ)
    (hs : List Digest) :
    (∃ ss, List.Forall₂ (fun s h => chainEnd s n = h) ss hs) ∨ Nonempty Collision ∨
      Nonempty (Forgery (Signer.pk sk) L) :=
  Or.inr (Or.inr (forgery_trivial sk L hlen))

/-! ## Positive: the walk on honest witness-sending trees -/

/-- The empty log is functional. -/
theorem nil_functional : Log.Functional ([] : Log) := fun _ h => absurd h List.not_mem_nil

/-- The witness-sending knowledge state (potential `0`), at the submission's own `V` and `E`. -/
def ks (vk : Digest) : KState (Rel (submission.acc vk)) (submission.V vk) submission.E 0 :=
  WitnessSending.kstate vk

/-- It has potential `0` on the empty log. -/
theorem kstate_nil (vk : Digest) : (ks vk).μ [] < 1 := by
  show (0 : ℝ≥0) < 1
  exact one_pos

/-- **The walk on a one-leaf tree** returns the leaf's start. -/
theorem walk_one_leaf (sk : ℕ → ℕ → Digest) (s : Digest) {n : ℕ} (hn : n ≤ chainCap) :
    (walk (ks (Signer.pk sk)) nil_functional
      (Nat.zero_le _) (kstate_nil _) n hn 0 [chainEnd s n] rfl (leafSigned sk 0 s n)
      (acc_leafSigned sk (by decide) s hn)).starts? = some [s] :=
  walkFrom_leaf _ _ _ _ hn rfl rfl (by simp [leafSigned])
    (decode_encode (.leaf s n) (hn.trans_lt (by decide))) rfl

/-- The signature words of a reference signature: 597 words. -/
theorem sigWords_sign_length (sk : ℕ → ℕ → Digest) (j : ℕ) (m : Digest) :
    (sigWords (Signer.sign sk j m)).length = 597 := by
  simp [sigWords, Signer.sign, List.length_flatMap, packBytes_digest_length,
    Signer.wotsDigits_length, Signer.authPath, Signer.sibs_length, wotsLen, sigHeight]

/-- The witness-sending node witness over two signed leaf proofs of length `n`. -/
abbrev nodeWit (sk : ℕ → ℕ → Digest) (s₁ s₂ : Digest) (n : ℕ) : Wit :=
  .node (leafStmt (chainEnd s₁ n) n) (leafStmt (chainEnd s₂ n) n) (leafSigned sk 0 s₁ n)
    (leafSigned sk 1 s₂ n)

/-- The signed node proof over two signed leaf proofs: the empty trace, signed with key `2`. -/
def nodeSigned (sk : ℕ → ℕ → Digest) (s₁ s₂ : Digest) (n : ℕ) : Signed :=
  ⟨encode (nodeWit sk s₁ s₂ n), [], Signer.sign sk 2 (traceDigest [])⟩

/-- The signed node proof is accepted for the node statement under the signer's key. -/
theorem acc_nodeSigned (sk : ℕ → ℕ → Digest) (s₁ s₂ : Digest) {n : ℕ} (hn : n ≤ chainCap) :
    submission.acc (Signer.pk sk)
      (nodeStmt (leafStmt (chainEnd s₁ n) n) (leafStmt (chainEnd s₂ n) n))
      (nodeSigned sk s₁ s₂ n) = true := by
  have hsize : (encode (nodeWit sk s₁ s₂ n)).size ≤ proofCap := by
    rw [size_encode]
    simp [witWords, signedWords, bytesWords, logWords, packBytes_length, sigWords_sign_length,
      leafSigned, size_encode_leaf, proofCap]
  rw [acc_eq]
  simp [nodeSigned, hsize, Signer.sigOk_sign sk 2 (by decide),
    check_encode (Controls.Relation.node_of_two_leaves sk s₁ s₂ hn hn)]

/-- The same acceptance, stated at the tree's root digest. -/
theorem acc_nodeSigned_root (sk : ℕ → ℕ → Digest) (s₁ s₂ : Digest) {n : ℕ} (hn : n ≤ chainCap) :
    submission.acc (Signer.pk sk)
      (treeRoot ([chainEnd s₁ n, chainEnd s₂ n].map fun h => leafStmt h n))
      (nodeSigned sk s₁ s₂ n) = true :=
  acc_nodeSigned sk s₁ s₂ hn

/-- **The walk on a two-leaf tree** returns the two leaves' starts. -/
theorem walk_two_leaves (sk : ℕ → ℕ → Digest) (s₁ s₂ : Digest) {n : ℕ} (hn : n ≤ chainCap) :
    (walk (ks (Signer.pk sk)) nil_functional
      (Nat.zero_le _) (kstate_nil _) n hn 1 [chainEnd s₁ n, chainEnd s₂ n] rfl
      (nodeSigned sk s₁ s₂ n) (acc_nodeSigned_root sk s₁ s₂ hn)).starts? = some [s₁, s₂] := by
  have hn64 : n < 2 ^ 64 := hn.trans_lt (by decide)
  have hE : submission.E (treeRoot ([chainEnd s₁ n, chainEnd s₂ n].map fun h => leafStmt h n))
      (nodeSigned sk s₁ s₂ n).π [] = some (nodeWit sk s₁ s₂ n) :=
    decode_encode _ (fits_of_rel (Controls.Relation.node_of_two_leaves sk s₁ s₂ hn hn))
  obtain ⟨hw, hx⟩ := extract_of_E (ks (Signer.pk sk))
    nil_functional (Nat.zero_le _) (kstate_nil _) (acc_nodeSigned_root sk s₁ s₂ hn)
    (by simp [nodeSigned]) hE
  unfold walk
  rw [walkFrom.eq_def]
  dsimp only
  split
  · rename_i heq; rw [hx] at heq; cases heq
  · rename_i heq; rw [hx] at heq; cases heq
  · rename_i heq
    rw [hx] at heq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := Wit.node.inj (congrArg Subtype.val (Sum.inl.inj heq))
    rw [dite_eq_left_of_eq_true (eq_true ⟨rfl, rfl⟩)]
    split
    · rename_i e₁ e₂
      have a₁ := walkFrom_leaf _ _ _ _ hn (h := chainEnd s₁ n) rfl e₁ (by simp [leafSigned])
        (decode_encode (.leaf s₁ n) hn64) rfl
      have a₂ := walkFrom_leaf _ _ _ _ hn (h := chainEnd s₂ n) rfl e₂ (by simp [leafSigned])
        (decode_encode (.leaf s₂ n) hn64) rfl
      simp only [Outcome.starts?, Option.some.injEq] at a₁ a₂ ⊢
      rw [a₁, a₂]; rfl
    all_goals rename_i e
    · exact absurd (walkFrom_leaf _ _ _ _ hn (h := chainEnd s₁ n) rfl e (by simp [leafSigned])
        (decode_encode (.leaf s₁ n) hn64) rfl) (by simp [Outcome.starts?])
    · exact absurd (walkFrom_leaf _ _ _ _ hn (h := chainEnd s₁ n) rfl e (by simp [leafSigned])
        (decode_encode (.leaf s₁ n) hn64) rfl) (by simp [Outcome.starts?])
    · exact absurd (walkFrom_leaf _ _ _ _ hn (h := chainEnd s₂ n) rfl e (by simp [leafSigned])
        (decode_encode (.leaf s₂ n) hn64) rfl) (by simp [Outcome.starts?])
    · exact absurd (walkFrom_leaf _ _ _ _ hn (h := chainEnd s₂ n) rfl e (by simp [leafSigned])
        (decode_encode (.leaf s₂ n) hn64) rfl) (by simp [Outcome.starts?])

end RecursionFast.Controls.Compose
