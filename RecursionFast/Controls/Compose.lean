/-
# Controls: the composition walk and its probability (`Library/Compose.lean`)

Negative (what the outcome types do not say). `forgery_trivial`, for the capped `Forgery`:
under the key of any known signer and for every log within `logCap`, a `Forgery` exists with no
other hypothesis (a signed one-entry trace whose answer to the empty query is not in the log,
which exists since the log has fewer than `2^256` entries). `collision_nonempty`: a Keccak-256
collision exists (pigeonhole), so `Outcome` and `SignedOutcome` are inhabited with no content.
The content is the compiled `walk` and `walkSigned`, which compute their outcome (the forgery's
membership of the extraction tree included), and the theorems about what they return.

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

Against the service's signed traces (`Forgery.reduce`, `walkSigned`), with `queryLeaf`, the leaf
proof of `(s, n)` carrying the one-entry trace `(qMax, a)` (a query of exactly `queryCap` bytes),
accepted by the one-query verifier `oneQuery qMax` (`Controls/Relation.lean`):
* Positive (the EUF-CMA outcome is reached through the walk): with the empty log and a service
  that signed nothing, `walkSigned` returns an EUF-CMA forgery at the root
  (`walkSigned_queryLeaf_euf`); so the adversary that holds the key, asks nothing and outputs that
  proof makes the EUF-CMA term of `compose_prob_signed` certain (`queryLeaf_euf_prob`). Against a
  service that signed nothing, the reduction returns every forgery as an EUF-CMA forgery
  (`reduce_nil`).
* Positive (`Honest` on a non-empty trace): a log holding `(qMax, a)` accounts for the service
  having signed that trace (`honest_queryLeaf`), and `walkSigned` then extracts the leaf's start
  (`walkSigned_queryLeaf_starts`). On the honest one-leaf witness-sending tree, whose trace is
  empty (so `Honest` holds vacuously, `honest_leaf`), it returns the leaf's start as well
  (`walkSigned_one_leaf`).
* Negative: if the service's signed traces include the forged trace, the forgery is no EUF-CMA
  forgery and `Honest` fails (`forgery_signed_not_euf`), so the hypothesis is what makes the
  forgery an EUF-CMA one; `noExt`'s `walkSigned` escapes (`noExt_walkSigned_escaped`).
Symbolic (`decode_encode`, `sigOk_sign`, `extract_of_E`, `walkFrom_leaf`); no hash is evaluated.
-/
import RecursionFast.Library.Compose
import RecursionFast.Library.WitnessSending
import RecursionFast.Controls.Relation

open scoped NNReal

namespace RecursionFast.Controls.Compose
open RecursionFast RecursionFast.Compose RecursionFast.WitnessSending
open RecursionFast.Controls.Relation (leafSigned acc_leafSigned)

/-! ## Negative: a `Forgery` against a log is free under a known signer's key -/

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

/-- **A forgery is free for a known signer**: under the key of any known signer and for every log
within `logCap`, a forgery against the log exists, with no other hypothesis. -/
theorem forgery_trivial (sk : ℕ → ℕ → Digest) (L : Log) (hlen : L.length ≤ logCap) :
    Nonempty (Forgery (Signer.pk sk) L) := by
  obtain ⟨a, ha⟩ := fresh_answer L hlen
  exact ⟨⟨⟨ByteArray.empty, [(ByteArray.empty, a)],
      Signer.sign sk 0 (traceDigest [(ByteArray.empty, a)])⟩,
    fun e he => List.mem_singleton.mp he ▸ Nat.zero_le _, Signer.sigOk_sign sk 0 (by decide) _,
    fun h => ha (h _ (List.mem_singleton_self _))⟩⟩

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
  have hsize : (encode (nodeWit sk s₁ s₂ n)).size < 2 ^ 64 := by
    rw [size_encode]
    simp [witWords, signedWords, bytesWords, logWords, packBytes_length, sigWords_sign_length,
      leafSigned, size_encode_leaf]
  rw [acc_eq, nodeSigned, decide_eq_true hsize]
  simp [Signer.sigOk_sign sk 2 (by decide),
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

/-! ## The forgery outcome against the service's signed traces -/

/-- **A collision exists**: Keccak-256 maps infinitely many strings to `2^256` digests. So the
outcome types `Outcome` and `SignedOutcome` are inhabited with no content (by their collision
constructor); the content is what the compiled `walk` and `walkSigned` compute, and the theorems
about it. -/
theorem collision_nonempty : Nonempty Collision := by
  by_contra h
  exact not_injective_infinite_finite keccakDigest fun x y heq =>
    by_contra fun hne => h ⟨⟨x, y, hne, heq⟩⟩

/-- **Positive** (the EUF-CMA branch is reached): against a service that signed nothing, the
reduction returns every forgery against the log as an EUF-CMA forgery, in particular the known
signer's of `forgery_trivial`. -/
theorem reduce_nil {vk : Digest} {L : Log} (f : Forgery vk L) :
    (f.reduce [] ⟨nofun, nofun⟩).isLeft = true := by
  unfold Forgery.reduce
  split
  · rename_i h; exact absurd (List.mem_of_find?_eq_some h) List.not_mem_nil
  · rfl

/-- **Negative** (`Honest` is needed): if the service's signed traces include the forged trace,
which the log does not hold, the forgery is no EUF-CMA forgery against them, and the log does not
account for them. -/
theorem forgery_signed_not_euf {vk : Digest} {L : Log} (f : Forgery vk L) :
    ¬ EufForgery (SigOk vk) (issued [(f.p.tr, f.p.σ)]) (traceDigest f.p.tr) f.p.σ ∧
      ¬ Honest [(f.p.tr, f.p.σ)] L :=
  ⟨fun h => h.2 (mem_fst_issued.mpr ⟨_, List.mem_singleton_self _, rfl⟩),
    fun h => f.notIn (h.inLog _ (List.mem_singleton_self _))⟩

/-- The signed traces of the honest one-leaf witness-sending tree: the leaf proof's trace and
signature, which the empty log accounts for (vacuously: the trace is empty). -/
theorem honest_leaf (sk : ℕ → ℕ → Digest) (s : Digest) (n : ℕ) :
    Honest [((leafSigned sk 0 s n).tr, (leafSigned sk 0 s n).σ)] [] :=
  ⟨by simp [leafSigned], by simp [leafSigned]⟩

/-- **Positive**: on the honest one-leaf tree, the walk against its signed traces returns the
leaf's start. -/
theorem walkSigned_one_leaf (sk : ℕ → ℕ → Digest) (s : Digest) {n : ℕ} (hn : n ≤ chainCap) :
    (walkSigned [] _ (honest_leaf sk s n) n hn 0 [chainEnd s n] rfl (leafSigned sk 0 s n)
      (acc_leafSigned sk (by decide) s hn)).starts? = some [s] :=
  (Outcome.starts?_reduce _ _).trans (walk_one_leaf sk s hn)

/-- **Negative**: `noExt`'s walk against the same signed traces escapes at the root, so the
knowledge-soundness term of `compose_prob_signed` is needed. -/
theorem noExt_walkSigned_escaped (sk : ℕ → ℕ → Digest) (s : Digest) {n : ℕ}
    (hn : n ≤ chainCap) :
    (walkSigned [] _ (honest_leaf sk s n) n hn 0 [chainEnd s n] rfl (leafSigned sk 0 s n)
      (noExt_acc_leaf sk s hn)).Escaped :=
  (Outcome.escaped_reduce _ _).mpr (noExt_walk_escaped sk s hn)

/-! ## The forgery outcome through the walk: a one-query leaf proof -/

open RecursionFast.Controls.Relation (oneQuery qMax acc_query_at_cap)

/-- The leaf proof of `(s, n)` with the one-entry trace `(qMax, a)`, signed with key `0`. -/
def queryLeaf (sk : ℕ → ℕ → Digest) (s a : Digest) (n : ℕ) : Signed :=
  ⟨encode (.leaf s n), [(qMax, a)], Signer.sign sk 0 (traceDigest [(qMax, a)])⟩

/-- The one-query verifier accepts it, for the one-leaf tree's root. -/
theorem acc_queryLeaf (sk : ℕ → ℕ → Digest) (s a : Digest) (n : ℕ) :
    (oneQuery qMax).acc (Signer.pk sk) (treeRoot ([chainEnd s n].map fun h => leafStmt h n))
      (queryLeaf sk s a n) = true :=
  acc_query_at_cap sk a _ (by rw [size_encode_leaf]; decide)

/-- **Positive** (the EUF-CMA outcome through the walk): with the empty log and a service that
signed nothing, the walk against its signed traces returns an EUF-CMA forgery at the root. -/
theorem walkSigned_queryLeaf_euf (sk : ℕ → ℕ → Digest) (s a : Digest) {n : ℕ}
    (hn : n ≤ chainCap) :
    (walkSigned [] [] ⟨nofun, nofun⟩ n hn 0 [chainEnd s n] rfl (queryLeaf sk s a n)
      (acc_queryLeaf sk s a n)).IsEuf := by
  unfold walkSigned walk walkFrom
  rw [extract_forgery (L := []) _ fun h => List.not_mem_nil (h _ (List.mem_singleton_self _))]
  exact Outcome.isEuf_reduce_forgery _ _ _ _ _
    ⟨Signer.sigOk_sign sk 0 (by decide) _, fun h => by
      obtain ⟨_, hx, _⟩ := mem_fst_issued.mp h; exact List.not_mem_nil hx⟩

/-- **The EUF-CMA term of `compose_prob_signed` is reached**: against a service that signed
nothing (`T = fun _ _ => []`), the adversary that holds the key, asks nothing and outputs
`queryLeaf` makes the EUF-CMA event certain. -/
theorem queryLeaf_euf_prob (sk : ℕ → ℕ → Digest) (s a : Digest) {n : ℕ} (hn : n ≤ chainCap) :
    prob (fun p L => ∃ hacc : (oneQuery qMax).acc (Signer.pk sk)
        (treeRoot ([chainEnd s n].map fun h => leafStmt h n)) p = true,
      (walkSigned L [] ⟨nofun, nofun⟩ n hn 0 [chainEnd s n] rfl p hacc).IsEuf)
      (.ret (queryLeaf sk s a n)) [] = 1 :=
  (prob_ret _ _ _).trans (ind_of ⟨_, walkSigned_queryLeaf_euf sk s a hn⟩)

/-- **Positive** (`Honest` on a non-empty trace): a log holding `(qMax, a)` accounts for the
service having signed `queryLeaf`'s trace. -/
theorem honest_queryLeaf (sk : ℕ → ℕ → Digest) (s a : Digest) (n : ℕ) :
    Honest [((queryLeaf sk s a n).tr, (queryLeaf sk s a n).σ)] [(qMax, a)] :=
  have hq : qMax.size = queryCap := by simp [qMax, ByteArray.size]
  ⟨by simp [queryLeaf], fun x hx e he => by
    rw [List.mem_singleton.mp hx] at he
    rw [List.mem_singleton.mp he, hq]⟩

/-- **Positive**: with that log and those signed traces, the walk returns the leaf's start. -/
theorem walkSigned_queryLeaf_starts (sk : ℕ → ℕ → Digest) (s a : Digest) {n : ℕ}
    (hn : n ≤ chainCap) :
    (walkSigned [(qMax, a)] _ (honest_queryLeaf sk s a n) n hn 0 [chainEnd s n] rfl
      (queryLeaf sk s a n) (acc_queryLeaf sk s a n)).starts? = some [s] :=
  (Outcome.starts?_reduce _ _).trans (walkFrom_leaf hn rfl rfl (by simp [queryLeaf])
    (decode_encode (.leaf s n) (hn.trans_lt (by decide))) rfl)

end RecursionFast.Controls.Compose
