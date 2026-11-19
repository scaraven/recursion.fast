/-
# Controls: the composition walks and their probability (`Library/Compose.lean`)

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
log, `walk` returns the leaf seeds:
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
  having signed that trace (`honest_queryLeaf`), and `walkSigned` then extracts the leaf's seed
  (`walkSigned_queryLeaf_seeds`). On the honest one-leaf witness-sending tree, whose trace is
  empty (so `Honest` holds vacuously, `honest_leaf`), it returns the leaf's seed as well
  (`walkSigned_one_leaf`).
* Negative: if the service's signed traces include the forged trace, the forgery is no EUF-CMA
  forgery and `Honest` fails (`forgery_signed_not_euf`), so the hypothesis is what makes the
  forgery an EUF-CMA one; `noExt`'s `walkSigned` escapes (`noExt_walkSigned_escaped`).
The stream walk (`walkStream`, over the benchmark's shape `c_1 = L_1`,
`c_i = nodeStmt c_(i-1) L_i`), on the witness-sending submission under the reference signer's
key, with the empty log:
* Positive: `walkStream_one_leaf`, on the one-leaf stream whose proof is the signed leaf proof,
  returns `[s]`; `walkStream_two_leaves`, on the two-leaf stream whose proof is the signed node
  proof over the two signed leaf proofs, returns `[s₁, s₂]`; `walkStream_three_leaves`, on the
  three-leaf stream whose proof is the signed node proof over that node proof and a third signed
  leaf proof (`streamSigned`), returns `[s₁, s₂, s₃]`; `walkStreamSigned_two_leaves`: against a
  service that signed nothing (the traces are empty), the same seeds.
* Negative: `noExt`'s stream walk escapes at the root of the two-leaf stream
  (`noExt_walkStream_escaped`), so the adversary that outputs that proof makes
  `compose_prob_stream`'s event certain (`noExt_stream_escape_prob`). An escape below the root:
  `topOnly`'s extractor opens only proofs longer than the two-leaf node proof, so on the
  three-leaf stream it opens the root and the walk escapes at the root's first child, the path
  `[false]` (`topOnly_walkStream_escaped`).
* `ws_compose_prob_stream`: under every key and against every adversary, the witness-sending
  stream walk escapes with probability `0` (`compose_prob_stream` at `ε = 0`, `qV = 0`).

Symbolic (`decode_encode`, `sigOk_sign`, `extract_of_E`, `walkFrom_leaf`, `walkStreamFrom_one`,
`walkStreamFrom_node`, `walkStreamFrom_succ_succ`, `walkStreamFrom_escape`); no hash is
evaluated.
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
theorem noExt_not_ks (vk s : Digest) {n : ℕ} (hn : n ≤ leafCap) (ε : ℝ≥0) :
    ¬ KS (Rel (noExt.acc vk)) (noExt.V vk) noExt.E ε noExt.qV :=
  not_ks_of_accept (c := leafStmt (leafValue s n) n) (π := encode (.leaf s n))
    (congrArg some (check_encode (vk := vk) (w := .leaf s n) ⟨hn, rfl⟩)) (by simp [noExt])
    (Nat.zero_le _) (by simp [noExt, submission])

/-- Its `acc` is the witness-sending one: the honest leaf proof is accepted. -/
theorem noExt_acc_leaf (sk : ℕ → ℕ → Digest) (s : Digest) {n : ℕ} (hn : n ≤ leafCap) :
    noExt.acc (Signer.pk sk) (treeRoot ([leafValue s n].map fun h => leafStmt h n))
      (leafSigned sk 0 s n) = true :=
  acc_leafSigned (j := 0) sk (Nat.two_pow_pos _) s hn

/-- **The walk escapes**: on an honest one-leaf tree, `noExt`'s walk ends in an escape at the
root. -/
theorem noExt_walk_escaped (sk : ℕ → ℕ → Digest) (s : Digest) {n : ℕ} (hn : n ≤ leafCap) :
    (walk [] n hn 0 [leafValue s n] rfl (leafSigned sk 0 s n)
      (noExt_acc_leaf sk s hn)).Escaped := by
  unfold walk walkFrom
  rw [extract_escape (L := []) (noExt_acc_leaf sk s hn) nofun (by simp [noExt])]
  trivial

/-- **`compose_prob`'s event is certain** for `noExt` and the adversary that outputs the honest
leaf proof. -/
theorem noExt_escape_prob (sk : ℕ → ℕ → Digest) (s : Digest) {n : ℕ} (hn : n ≤ leafCap) :
    prob (fun p L => ∃ hacc : noExt.acc (Signer.pk sk)
        (treeRoot ([leafValue s n].map fun h => leafStmt h n)) p = true,
      (walk L n hn 0 [leafValue s n] rfl p hacc).Escaped) (.ret (leafSigned sk 0 s n)) [] = 1 :=
  (prob_ret _ _ _).trans (ind_of ⟨_, noExt_walk_escaped sk s hn⟩)

/-! ## Positive: the walk on honest witness-sending trees -/

/-- **The walk on a one-leaf tree** returns the leaf's seed. -/
theorem walk_one_leaf (sk : ℕ → ℕ → Digest) (s : Digest) {n : ℕ} (hn : n ≤ leafCap) :
    (walk [] n hn 0 [leafValue s n] rfl (leafSigned sk 0 s n)
      (acc_leafSigned sk (by decide) s hn)).seeds? = some [s] :=
  walkFrom_leaf hn rfl rfl (by simp [leafSigned])
    (decode_encode (.leaf s n) (hn.trans_lt (by decide))) rfl

/-- The signature words of a reference signature: 597 words. -/
theorem sigWords_sign_length (sk : ℕ → ℕ → Digest) (j : ℕ) (m : Digest) :
    (sigWords (Signer.sign sk j m)).length = 597 := by
  simp [sigWords, Signer.sign, List.length_flatMap, packBytes_digest_length,
    Signer.wotsDigits_length, Signer.authPath, Signer.sibs_length, wotsLen, sigHeight]

/-- The witness-sending node witness over two signed leaf proofs of `n` hashes each. -/
abbrev nodeWit (sk : ℕ → ℕ → Digest) (s₁ s₂ : Digest) (n : ℕ) : Wit :=
  .node (leafStmt (leafValue s₁ n) n) (leafStmt (leafValue s₂ n) n) (leafSigned sk 0 s₁ n)
    (leafSigned sk 1 s₂ n)

/-- The signed node proof over two signed leaf proofs: the empty trace, signed with key `2`. -/
def nodeSigned (sk : ℕ → ℕ → Digest) (s₁ s₂ : Digest) (n : ℕ) : Signed :=
  ⟨encode (nodeWit sk s₁ s₂ n), [], Signer.sign sk 2 (traceDigest [])⟩

/-- The signed node proof is accepted for the node statement under the signer's key. -/
theorem acc_nodeSigned (sk : ℕ → ℕ → Digest) (s₁ s₂ : Digest) {n : ℕ} (hn : n ≤ leafCap) :
    submission.acc (Signer.pk sk)
      (nodeStmt (leafStmt (leafValue s₁ n) n) (leafStmt (leafValue s₂ n) n))
      (nodeSigned sk s₁ s₂ n) = true := by
  have hsize : (encode (nodeWit sk s₁ s₂ n)).size < 2 ^ 64 := by
    rw [size_encode]
    simp [witWords, signedWords, bytesWords, logWords, packBytes_length, sigWords_sign_length,
      leafSigned, size_encode_leaf]
  rw [acc_eq, nodeSigned, decide_eq_true hsize]
  simp [Signer.sigOk_sign sk 2 (by decide),
    check_encode (Controls.Relation.node_of_two_leaves sk s₁ s₂ hn hn)]

/-- The same acceptance, stated at the tree's root digest. -/
theorem acc_nodeSigned_root (sk : ℕ → ℕ → Digest) (s₁ s₂ : Digest) {n : ℕ} (hn : n ≤ leafCap) :
    submission.acc (Signer.pk sk)
      (treeRoot ([leafValue s₁ n, leafValue s₂ n].map fun h => leafStmt h n))
      (nodeSigned sk s₁ s₂ n) = true :=
  acc_nodeSigned sk s₁ s₂ hn

/-- **The walk on a two-leaf tree** returns the two leaves' seeds. -/
theorem walk_two_leaves (sk : ℕ → ℕ → Digest) (s₁ s₂ : Digest) {n : ℕ} (hn : n ≤ leafCap) :
    (walk [] n hn 1 [leafValue s₁ n, leafValue s₂ n] rfl (nodeSigned sk s₁ s₂ n)
      (acc_nodeSigned_root sk s₁ s₂ hn)).seeds? = some [s₁, s₂] := by
  have hn64 : n < 2 ^ 64 := hn.trans_lt (by decide)
  have hR := Controls.Relation.node_of_two_leaves sk s₁ s₂ hn hn
  unfold walk walkFrom
  rw [extract_of_E (L := []) (acc_nodeSigned_root sk s₁ s₂ hn) nofun
    (decode_encode _ (fits_of_rel hR)) hR]
  dsimp only
  rw [dite_eq_left_of_eq_true (eq_true ⟨rfl, rfl⟩)]
  split
  · rename_i e₁ e₂
    have a₁ := walkFrom_leaf hn (h := leafValue s₁ n) rfl e₁ nofun
      (decode_encode (.leaf s₁ n) hn64) rfl
    have a₂ := walkFrom_leaf hn (h := leafValue s₂ n) rfl e₂ nofun
      (decode_encode (.leaf s₂ n) hn64) rfl
    simp only [Outcome.seeds?, Option.some.injEq] at a₁ a₂ ⊢
    rw [a₁, a₂]; rfl
  -- the first walk is not the seeds (three cases), then the second (three cases)
  all_goals rename_i e
  iterate 3 exact absurd (walkFrom_leaf hn (h := leafValue s₁ n) rfl e nofun
    (decode_encode (.leaf s₁ n) hn64) rfl) nofun
  all_goals exact absurd (walkFrom_leaf hn (h := leafValue s₂ n) rfl e nofun
    (decode_encode (.leaf s₂ n) hn64) rfl) nofun

/-- **The witness-sending walk escapes with probability `0`**, under every key and against every
adversary asking at most `Q ≤ logCap` queries. -/
theorem ws_compose_prob (vk : Digest) {n : ℕ} (hn : n ≤ leafCap) (r : ℕ) (hs : List Digest)
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
leaf's seed. -/
theorem walkSigned_one_leaf (sk : ℕ → ℕ → Digest) (s : Digest) {n : ℕ} (hn : n ≤ leafCap) :
    (walkSigned [] _ (honest_leaf sk s n) n hn 0 [leafValue s n] rfl (leafSigned sk 0 s n)
      (acc_leafSigned sk (by decide) s hn)).seeds? = some [s] :=
  (Outcome.seeds?_reduce _ _).trans (walk_one_leaf sk s hn)

/-- **Negative**: `noExt`'s walk against the same signed traces escapes at the root, so the
knowledge-soundness term of `compose_prob_signed` is needed. -/
theorem noExt_walkSigned_escaped (sk : ℕ → ℕ → Digest) (s : Digest) {n : ℕ}
    (hn : n ≤ leafCap) :
    (walkSigned [] _ (honest_leaf sk s n) n hn 0 [leafValue s n] rfl (leafSigned sk 0 s n)
      (noExt_acc_leaf sk s hn)).Escaped :=
  (Outcome.escaped_reduce _ _).mpr (noExt_walk_escaped sk s hn)

/-! ## The forgery outcome through the walk: a one-query leaf proof -/

open RecursionFast.Controls.Relation (oneQuery qMax acc_query_at_cap)

/-- The leaf proof of `(s, n)` with the one-entry trace `(qMax, a)`, signed with key `0`. -/
def queryLeaf (sk : ℕ → ℕ → Digest) (s a : Digest) (n : ℕ) : Signed :=
  ⟨encode (.leaf s n), [(qMax, a)], Signer.sign sk 0 (traceDigest [(qMax, a)])⟩

/-- The one-query verifier accepts it, for the one-leaf tree's root. -/
theorem acc_queryLeaf (sk : ℕ → ℕ → Digest) (s a : Digest) (n : ℕ) :
    (oneQuery qMax).acc (Signer.pk sk) (treeRoot ([leafValue s n].map fun h => leafStmt h n))
      (queryLeaf sk s a n) = true :=
  acc_query_at_cap sk a _ (by rw [size_encode_leaf]; decide)

/-- **Positive** (the EUF-CMA outcome through the walk): with the empty log and a service that
signed nothing, the walk against its signed traces returns an EUF-CMA forgery at the root. -/
theorem walkSigned_queryLeaf_euf (sk : ℕ → ℕ → Digest) (s a : Digest) {n : ℕ}
    (hn : n ≤ leafCap) :
    (walkSigned [] [] ⟨nofun, nofun⟩ n hn 0 [leafValue s n] rfl (queryLeaf sk s a n)
      (acc_queryLeaf sk s a n)).IsEuf := by
  unfold walkSigned walk walkFrom
  rw [extract_forgery (L := []) _ fun h => List.not_mem_nil (h _ (List.mem_singleton_self _))]
  exact Outcome.isEuf_reduce_forgery _ _ _ _ _
    ⟨Signer.sigOk_sign sk 0 (by decide) _, fun h => by
      obtain ⟨_, hx, _⟩ := mem_fst_issued.mp h; exact List.not_mem_nil hx⟩

/-- **The EUF-CMA term of `compose_prob_signed` is reached**: against a service that signed
nothing (`T = fun _ _ => []`), the adversary that holds the key, asks nothing and outputs
`queryLeaf` makes the EUF-CMA event certain. -/
theorem queryLeaf_euf_prob (sk : ℕ → ℕ → Digest) (s a : Digest) {n : ℕ} (hn : n ≤ leafCap) :
    prob (fun p L => ∃ hacc : (oneQuery qMax).acc (Signer.pk sk)
        (treeRoot ([leafValue s n].map fun h => leafStmt h n)) p = true,
      (walkSigned L [] ⟨nofun, nofun⟩ n hn 0 [leafValue s n] rfl p hacc).IsEuf)
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

/-- **Positive**: with that log and those signed traces, the walk returns the leaf's seed. -/
theorem walkSigned_queryLeaf_seeds (sk : ℕ → ℕ → Digest) (s a : Digest) {n : ℕ}
    (hn : n ≤ leafCap) :
    (walkSigned [(qMax, a)] _ (honest_queryLeaf sk s a n) n hn 0 [leafValue s n] rfl
      (queryLeaf sk s a n) (acc_queryLeaf sk s a n)).seeds? = some [s] :=
  (Outcome.seeds?_reduce _ _).trans (walkFrom_leaf hn rfl rfl (by simp [queryLeaf])
    (decode_encode (.leaf s n) (hn.trans_lt (by decide))) rfl)

/-! ## The stream walk: `c_1 = L_1`, `c_i = nodeStmt c_(i-1) L_i` -/

/-- **The stream walk on a one-leaf stream** returns the leaf's seed. -/
theorem walkStream_one_leaf (sk : ℕ → ℕ → Digest) (s : Digest) {n : ℕ} (hn : n ≤ leafCap) :
    (walkStream [] n hn [leafValue s n] (leafSigned sk 0 s n)
      (acc_leafSigned sk (by decide) s hn)).seeds? = some [s] :=
  walkStreamFrom_one (L := []) (p := leafSigned sk 0 s n) hn nofun
    (decode_encode (.leaf s n) (hn.trans_lt (by decide))) rfl

/-- The signed node proof over two signed leaf proofs is accepted for the two-leaf stream's
digest (the same digest as the two-leaf tree's root). -/
theorem acc_nodeSigned_stream (sk : ℕ → ℕ → Digest) (s₁ s₂ : Digest) {n : ℕ}
    (hn : n ≤ leafCap) :
    submission.acc (Signer.pk sk) (streamStmt n [leafValue s₁ n, leafValue s₂ n])
      (nodeSigned sk s₁ s₂ n) = true :=
  acc_nodeSigned sk s₁ s₂ hn

/-- **The stream walk on a two-leaf stream** returns the two leaves' seeds. -/
theorem walkStream_two_leaves (sk : ℕ → ℕ → Digest) (s₁ s₂ : Digest) {n : ℕ}
    (hn : n ≤ leafCap) :
    (walkStream [] n hn [leafValue s₁ n, leafValue s₂ n] (nodeSigned sk s₁ s₂ n)
      (acc_nodeSigned_stream sk s₁ s₂ hn)).seeds? = some [s₁, s₂] := by
  have hn64 : n < 2 ^ 64 := hn.trans_lt (by decide)
  have hR := Controls.Relation.node_of_two_leaves sk s₁ s₂ hn hn
  exact walkStreamFrom_succ_succ (L := []) (k := 0) (hs := [leafValue s₁ n, leafValue s₂ n])
    (p := nodeSigned sk s₁ s₂ n) hn (List.cons_ne_nil _ _) nofun
    (decode_encode _ (fits_of_rel hR)) hR
    (fun _ _ _ _ => walkStreamFrom_one (p := leafSigned sk 0 s₁ n) hn nofun
      (decode_encode (.leaf s₁ n) hn64) rfl) nofun
    (s := s₂) (decode_encode (.leaf s₂ n) hn64) rfl

/-- The witness-sending node witness of the three-leaf stream: the signed node proof over the
first two leaves and the signed leaf proof of the third (key `3`). -/
abbrev streamWit (sk : ℕ → ℕ → Digest) (s₁ s₂ s₃ : Digest) (n : ℕ) : Wit :=
  .node (nodeStmt (leafStmt (leafValue s₁ n) n) (leafStmt (leafValue s₂ n) n))
    (leafStmt (leafValue s₃ n) n) (nodeSigned sk s₁ s₂ n) (leafSigned sk 3 s₃ n)

/-- The signed proof of the three-leaf stream: the empty trace, signed with key `4`. -/
def streamSigned (sk : ℕ → ℕ → Digest) (s₁ s₂ s₃ : Digest) (n : ℕ) : Signed :=
  ⟨encode (streamWit sk s₁ s₂ s₃ n), [], Signer.sign sk 4 (traceDigest [])⟩

/-- The three-leaf stream's node witness is in the relation. -/
theorem rel_streamWit (sk : ℕ → ℕ → Digest) (s₁ s₂ s₃ : Digest) {n : ℕ} (hn : n ≤ leafCap) :
    Rel (submission.acc (Signer.pk sk))
      (streamStmt n [leafValue s₁ n, leafValue s₂ n, leafValue s₃ n])
      (streamWit sk s₁ s₂ s₃ n) :=
  ⟨rfl, acc_nodeSigned sk s₁ s₂ hn, acc_leafSigned sk (by decide) s₃ hn⟩

/-- The signed proof of the three-leaf stream is accepted for its digest. -/
theorem acc_streamSigned (sk : ℕ → ℕ → Digest) (s₁ s₂ s₃ : Digest) {n : ℕ} (hn : n ≤ leafCap) :
    submission.acc (Signer.pk sk)
      (streamStmt n [leafValue s₁ n, leafValue s₂ n, leafValue s₃ n])
      (streamSigned sk s₁ s₂ s₃ n) = true := by
  have h₁ : (encode (nodeWit sk s₁ s₂ n)).size < 2 ^ 20 := by
    rw [size_encode]
    simp [witWords, signedWords, bytesWords, logWords, packBytes_length, sigWords_sign_length,
      leafSigned, size_encode_leaf]
  have hsize : (encode (streamWit sk s₁ s₂ s₃ n)).size < 2 ^ 64 := by
    rw [size_encode]
    simp only [witWords, signedWords, bytesWords, logWords, List.length_cons, List.length_append,
      packBytes_length, sigWords_sign_length, nodeSigned, leafSigned, ← size_eq_length,
      size_encode_leaf, Vector.length_toList, List.flatMap_nil, List.length_nil]
    omega
  rw [acc_eq, streamSigned, decide_eq_true hsize]
  simp [Signer.sigOk_sign sk 4 (by decide), check_encode (rel_streamWit sk s₁ s₂ s₃ hn)]

/-- **The stream walk on a three-leaf stream** returns the three leaves' seeds. -/
theorem walkStream_three_leaves (sk : ℕ → ℕ → Digest) (s₁ s₂ s₃ : Digest) {n : ℕ}
    (hn : n ≤ leafCap) :
    (walkStream [] n hn [leafValue s₁ n, leafValue s₂ n, leafValue s₃ n]
      (streamSigned sk s₁ s₂ s₃ n) (acc_streamSigned sk s₁ s₂ s₃ hn)).seeds? =
      some [s₁, s₂, s₃] := by
  have hn64 : n < 2 ^ 64 := hn.trans_lt (by decide)
  have hR := rel_streamWit sk s₁ s₂ s₃ hn
  have hR₂ := Controls.Relation.node_of_two_leaves sk s₁ s₂ hn hn
  exact walkStreamFrom_succ_succ (L := []) (k := 1)
    (hs := [leafValue s₁ n, leafValue s₂ n, leafValue s₃ n]) (p := streamSigned sk s₁ s₂ s₃ n)
    hn (List.cons_ne_nil _ _) nofun (decode_encode _ (fits_of_rel hR)) hR
    (fun _ _ _ _ => walkStreamFrom_succ_succ (L := []) (k := 0)
      (hs := [leafValue s₁ n, leafValue s₂ n]) (p := nodeSigned sk s₁ s₂ n)
      hn (List.cons_ne_nil _ _) nofun (decode_encode _ (fits_of_rel hR₂)) hR₂
      (fun _ _ _ _ => walkStreamFrom_one (p := leafSigned sk 0 s₁ n) hn nofun
      (decode_encode (.leaf s₁ n) hn64) rfl) nofun
      (s := s₂) (decode_encode (.leaf s₂ n) hn64) rfl) nofun
    (s := s₃) (decode_encode (.leaf s₃ n) hn64) rfl

/-- **`noExt`'s stream walk escapes**: on the honest two-leaf stream it ends in an escape at the
root. -/
theorem noExt_walkStream_escaped (sk : ℕ → ℕ → Digest) (s₁ s₂ : Digest) {n : ℕ}
    (hn : n ≤ leafCap) :
    (walkStream (S := noExt) [] n hn [leafValue s₁ n, leafValue s₂ n] (nodeSigned sk s₁ s₂ n)
      (acc_nodeSigned_stream sk s₁ s₂ hn)).Escaped :=
  (walkStreamFrom_escape (S := noExt) (L := []) (k := 0)
    (hs := [leafValue s₁ n, leafValue s₂ n]) (p := nodeSigned sk s₁ s₂ n) hn nofun
    (by simp [noExt])).1

/-- **`compose_prob_stream`'s event is certain** for `noExt` and the adversary that outputs the
honest two-leaf stream's signed proof. -/
theorem noExt_stream_escape_prob (sk : ℕ → ℕ → Digest) (s₁ s₂ : Digest) {n : ℕ}
    (hn : n ≤ leafCap) :
    prob (fun p L => ∃ hacc : noExt.acc (Signer.pk sk)
        (streamStmt n [leafValue s₁ n, leafValue s₂ n]) p = true,
      (walkStream L n hn [leafValue s₁ n, leafValue s₂ n] p hacc).Escaped)
      (.ret (nodeSigned sk s₁ s₂ n)) [] = 1 :=
  (prob_ret _ _ _).trans (ind_of ⟨_, noExt_walkStream_escaped sk s₁ s₂ hn⟩)

/-- **The witness-sending stream walk escapes with probability `0`**, under every key and against
every adversary asking at most `Q ≤ logCap` queries. -/
theorem ws_compose_prob_stream (vk : Digest) {n : ℕ} (hn : n ≤ leafCap) (hs : List Digest)
    (A : OProg Signed) {Q : ℕ} (hA : ∀ H, (A.queries H).length ≤ Q) (hQ : Q ≤ logCap) :
    prob (fun p L => ∃ hacc : submission.acc vk (streamStmt n hs) p = true,
      (walkStream L n hn hs p hacc).Escaped) A [] = 0 :=
  le_antisymm ((compose_prob_stream (ks vk) n hn hs A hA (by simpa [submission] using hQ)).trans
    (by simp [submission])) bot_le

/-- **Positive** (against signed traces): on the honest two-leaf stream, whose traces are empty,
the stream walk against a service that signed nothing returns the two seeds. -/
theorem walkStreamSigned_two_leaves (sk : ℕ → ℕ → Digest) (s₁ s₂ : Digest) {n : ℕ}
    (hn : n ≤ leafCap) :
    (walkStreamSigned [] [] ⟨nofun, nofun⟩ n hn [leafValue s₁ n, leafValue s₂ n]
      (nodeSigned sk s₁ s₂ n) (acc_nodeSigned_stream sk s₁ s₂ hn)).seeds? = some [s₁, s₂] :=
  (Outcome.seeds?_reduce _ _).trans (walkStream_two_leaves sk s₁ s₂ hn)

/-! ## Negative: an escape below the root of the stream -/

/-- The witness-sending submission with an extractor that opens only proofs longer than the
two-leaf node proof `nodeSigned sk s₁ s₂ n`: on the three-leaf stream it opens the root and not
the root's first child. -/
def topOnly (sk : ℕ → ℕ → Digest) (s₁ s₂ : Digest) (n : ℕ) : Submission :=
  { submission with
    E := fun _ π _ => if (nodeSigned sk s₁ s₂ n).π.size < π.size then decode π else none }

/-- **An escape at a non-root member**: on the honest three-leaf stream, `topOnly`'s stream walk
opens the root and escapes at its first child, the path `[false]` (the node over the first two
leaves). -/
theorem topOnly_walkStream_escaped (sk : ℕ → ℕ → Digest) (s₁ s₂ s₃ : Digest) {n : ℕ}
    (hn : n ≤ leafCap) :
    (walkStream (S := topOnly sk s₁ s₂ n) [] n hn
        [leafValue s₁ n, leafValue s₂ n, leafValue s₃ n] (streamSigned sk s₁ s₂ s₃ n)
        (acc_streamSigned sk s₁ s₂ s₃ hn)).Escaped ∧
      (walkStream (S := topOnly sk s₁ s₂ n) [] n hn
        [leafValue s₁ n, leafValue s₂ n, leafValue s₃ n] (streamSigned sk s₁ s₂ s₃ n)
        (acc_streamSigned sk s₁ s₂ s₃ hn)).EscapeIn (· = [false]) := by
  have hR := rel_streamWit sk s₁ s₂ s₃ hn
  have hE : (topOnly sk s₁ s₂ n).E (streamStmt n [leafValue s₁ n, leafValue s₂ n, leafValue s₃ n])
      (streamSigned sk s₁ s₂ s₃ n).π [] = some (streamWit sk s₁ s₂ s₃ n) := by
    have hlt := (size_child_lt
      (nodeStmt (leafStmt (leafValue s₁ n) n) (leafStmt (leafValue s₂ n) n))
      (leafStmt (leafValue s₃ n) n) (nodeSigned sk s₁ s₂ n) (leafSigned sk 3 s₃ n)).1
    simp only [topOnly, streamSigned, hlt, ↓reduceIte]
    exact decode_encode _ (fits_of_rel hR)
  have e := walkStreamFrom_node (S := topOnly sk s₁ s₂ n) (L := []) (M := 3) (k := 1)
    (hs := [leafValue s₁ n, leafValue s₂ n, leafValue s₃ n]) (p := streamSigned sk s₁ s₂ s₃ n)
    (hk := rfl) (j := 0) (hj := rfl) (hacc := acc_streamSigned sk s₁ s₂ s₃ hn) (hmem := .root)
    hn (List.cons_ne_nil _ _) nofun hE hR
  have he := walkStreamFrom_escape (S := topOnly sk s₁ s₂ n) (L := []) (M := 3) (k := 0)
    (hs := [leafValue s₁ n, leafValue s₂ n]) (p := nodeSigned sk s₁ s₂ n) (j := 1) (hj := rfl)
    (hk := rfl) (hacc := acc_nodeSigned_stream sk s₁ s₂ hn) (hmem := InTree.left .root hE) hn
    nofun (by simp [topOnly])
  exact (congrArg (fun o => o.Escaped ∧ o.EscapeIn (· = [false])) e).mpr
    (Outcome.Escaped.append _ he.1 he.2)

end RecursionFast.Controls.Compose
