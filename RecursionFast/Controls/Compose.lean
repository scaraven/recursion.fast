/-
# Controls: the composition walk and its probability (`Library/Compose.lean`, V4-8, V4-A10; RA-M1)

Negative (what the bare disjunction does not say). `forgery_trivial` is RA's probe P1, adapted
to the capped `Forgery`: under the key of any known signer and for every log within `logCap`, a
`Forgery` exists with no other hypothesis (a signed one-entry trace whose answer to the empty
query is not in the log, which exists since the log has fewer than `2^256` entries). So
`compose_exists_free`: `compose_exists`'s conclusion holds for such a key with none of its
hypotheses used. The content is `walk`'s (and `compose`'s) membership of the forgery in the
extraction tree of the root signed proof.

Negative (an escape is the knowledge-soundness failure, and `compose_prob`'s event is reachable).
`noExt` is the witness-sending submission with an extractor that returns nothing; its `acc` is the
witness-sending one. It is not knowledge-sound at any error (`noExt_not_ks`). On an honest
one-leaf tree its walk escapes at the root (`noExt_walk_escaped`), so the adversary that outputs
that root makes the event `compose_prob` bounds certain (`noExt_escape_prob`): only the hypothesis
`KS` bounds it.

Positive. On the witness-sending submission under the reference signer's key, with the empty
log, `walk` returns the leaf starts:
* `walk_one_leaf`: a one-leaf tree whose root is the signed leaf proof of `(s, n)` gives `[s]`;
* `walk_two_leaves`: a two-leaf tree whose root is the signed node proof over the two signed leaf
  proofs gives `[s₁, s₂]`.
And `ws_compose_prob`: under every key and against every adversary, its walk escapes with
probability `0` (`compose_prob` at `ε = 0`, `qV = 0`).
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
  refine by_contra fun h => ?_
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
theorem compose_exists_free (S : Submission) (sk : ℕ → ℕ → Digest) (L : Log)
    (hlen : L.length ≤ logCap) (n r : ℕ) (hs : List Digest) (p : Signed) :
    (∃ ss, List.Forall₂ (fun s h => chainEnd s n = h) ss hs) ∨ Nonempty Collision ∨
      Nonempty (Forgery (Signer.pk sk) L) ∨
      ∃ (c : Digest) (q : Signed) (bs : List Bool), bs.length ≤ r ∧
        InTree S L (treeRoot (hs.map fun h => leafStmt h n)) p bs c q ∧
        Escape S (Signer.pk sk) L c q :=
  Or.inr (Or.inr (Or.inl (forgery_trivial sk L hlen)))

/-! ## Negative: an escape is the knowledge-soundness failure -/

/-- The witness-sending submission with an extractor that returns nothing. -/
def noExt : Submission := { submission with E := fun _ _ _ => none }

/-- **Not knowledge-sound** at any error: the honest leaf proof is accepted with no answer and
not opened. -/
theorem noExt_not_ks (vk s : Digest) {n : ℕ} (hn : n ≤ chainCap) (ε : ℝ≥0) :
    ¬ KS (Rel (noExt.acc vk)) (noExt.V vk) noExt.E ε noExt.qV :=
  not_ks_of_accept (c := leafStmt (chainEnd s n) n) (π := encode (.leaf s n))
    (congrArg some (check_encode (vk := vk) (w := .leaf s n) ⟨hn, rfl⟩)) (by simp [noExt])
    (Nat.zero_le _) (by simp [noExt, submission])

/-- Its `acc` is the witness-sending one: the honest leaf proof is accepted. -/
theorem noExt_acc_leaf (sk : ℕ → ℕ → Digest) (s : Digest) {n : ℕ} (hn : n ≤ chainCap) :
    noExt.acc (Signer.pk sk) (treeRoot ([chainEnd s n].map fun h => leafStmt h n))
      (leafSigned sk 0 s n) = true :=
  acc_leafSigned (j := 0) sk (Nat.two_pow_pos _) s hn

/-- **The walk escapes**: on an honest one-leaf tree, `noExt`'s walk ends in an escape at the
root. -/
theorem noExt_walk_escaped (sk : ℕ → ℕ → Digest) (s : Digest) {n : ℕ} (hn : n ≤ chainCap) :
    (walk [] n hn 0 [chainEnd s n] rfl (leafSigned sk 0 s n)
      (noExt_acc_leaf sk s hn)).Escaped := by
  unfold walk walkFrom
  rw [extract_escape (L := []) (noExt_acc_leaf sk s hn) nofun (by simp [noExt])]
  trivial

/-- **`compose_prob`'s event is certain** for `noExt` and the adversary that outputs the honest
leaf proof. -/
theorem noExt_escape_prob (sk : ℕ → ℕ → Digest) (s : Digest) {n : ℕ} (hn : n ≤ chainCap) :
    prob (fun p L => ∃ hacc : noExt.acc (Signer.pk sk)
        (treeRoot ([chainEnd s n].map fun h => leafStmt h n)) p = true,
      (walk L n hn 0 [chainEnd s n] rfl p hacc).Escaped) (.ret (leafSigned sk 0 s n)) [] = 1 :=
  (prob_ret _ _ _).trans (ind_of ⟨_, noExt_walk_escaped sk s hn⟩)

/-! ## Positive: the walk on honest witness-sending trees -/

/-- **The walk on a one-leaf tree** returns the leaf's start. -/
theorem walk_one_leaf (sk : ℕ → ℕ → Digest) (s : Digest) {n : ℕ} (hn : n ≤ chainCap) :
    (walk [] n hn 0 [chainEnd s n] rfl (leafSigned sk 0 s n)
      (acc_leafSigned sk (by decide) s hn)).starts? = some [s] :=
  walkFrom_leaf hn rfl rfl (by simp [leafSigned])
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
    (walk [] n hn 1 [chainEnd s₁ n, chainEnd s₂ n] rfl (nodeSigned sk s₁ s₂ n)
      (acc_nodeSigned_root sk s₁ s₂ hn)).starts? = some [s₁, s₂] := by
  have hn64 : n < 2 ^ 64 := hn.trans_lt (by decide)
  have hR := Controls.Relation.node_of_two_leaves sk s₁ s₂ hn hn
  unfold walk walkFrom
  rw [extract_of_E (L := []) (acc_nodeSigned_root sk s₁ s₂ hn) nofun
    (decode_encode _ (fits_of_rel hR)) hR]
  dsimp only
  rw [dite_eq_left_of_eq_true (eq_true ⟨rfl, rfl⟩)]
  split
  · rename_i e₁ e₂
    have a₁ := walkFrom_leaf hn (h := chainEnd s₁ n) rfl e₁ nofun
      (decode_encode (.leaf s₁ n) hn64) rfl
    have a₂ := walkFrom_leaf hn (h := chainEnd s₂ n) rfl e₂ nofun
      (decode_encode (.leaf s₂ n) hn64) rfl
    simp only [Outcome.starts?, Option.some.injEq] at a₁ a₂ ⊢
    rw [a₁, a₂]; rfl
  -- the first walk is not the starts (three cases), then the second (three cases)
  all_goals rename_i e
  iterate 3 exact absurd (walkFrom_leaf hn (h := chainEnd s₁ n) rfl e nofun
    (decode_encode (.leaf s₁ n) hn64) rfl) nofun
  all_goals exact absurd (walkFrom_leaf hn (h := chainEnd s₂ n) rfl e nofun
    (decode_encode (.leaf s₂ n) hn64) rfl) nofun

/-- **The witness-sending walk escapes with probability `0`**, under every key and against every
adversary asking at most `Q ≤ logCap` queries. -/
theorem ws_compose_prob (vk : Digest) {n : ℕ} (hn : n ≤ chainCap) (r : ℕ) (hs : List Digest)
    (hr : hs.length = 2 ^ r) (A : OProg Signed) {Q : ℕ} (hA : ∀ H, (A.queries H).length ≤ Q)
    (hQ : Q ≤ logCap) :
    prob (fun p L => ∃ hacc : submission.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true,
      (walk L n hn r hs hr p hacc).Escaped) A [] = 0 :=
  le_antisymm ((compose_prob (ks vk) n hn r hs hr A hA (by simpa [submission] using hQ)).trans
    (by simp [submission])) bot_le

end RecursionFast.Controls.Compose
