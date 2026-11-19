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
log, `walk` returns the leaves' data:
* `walk_one_leaf`: a one-leaf tree whose root is the signed leaf proof of the data `xs` gives
  `[xs]`;
* `walk_two_leaves`: a two-leaf tree whose root is the signed node proof over the two signed leaf
  proofs (`n` blocks each) gives `[xs₁, xs₂]`.
And `ws_compose_prob`: under every key and against every adversary, its walk escapes with
probability `0` (`compose_prob` at `ε = 0`, `qV = 0`).

Against the service's signed traces (`Forgery.reduce`, `walkSigned`), with `queryLeaf`, the leaf
proof of the data `xs` carrying the one-entry trace `(qMax, a)` (a query of exactly `queryCap`
bytes), accepted by the one-query verifier `oneQuery qMax` (`Controls/Relation.lean`):
* Positive (the EUF-CMA outcome is reached through the walk): with the empty log and a service
  that signed nothing, `walkSigned` returns an EUF-CMA forgery at the root
  (`walkSigned_queryLeaf_euf`); so the adversary that holds the key, asks nothing and outputs that
  proof makes the EUF-CMA term of `compose_prob_signed` certain (`queryLeaf_euf_prob`). Against a
  service that signed nothing, the reduction returns every forgery as an EUF-CMA forgery
  (`reduce_nil`).
* Positive (`Honest` on a non-empty trace): a log holding `(qMax, a)` accounts for the service
  having signed that trace (`honest_queryLeaf`), and `walkSigned` then extracts the leaf's data
  (`walkSigned_queryLeaf_data`). On the honest one-leaf witness-sending tree, whose trace is
  empty (so `Honest` holds vacuously, `honest_leaf`), it returns the leaf's data as well
  (`walkSigned_one_leaf`).
* Negative: if the service's signed traces include the forged trace, the forgery is no EUF-CMA
  forgery and `Honest` fails (`forgery_signed_not_euf`), so the hypothesis is what makes the
  forgery an EUF-CMA one; `noExt`'s `walkSigned` escapes (`noExt_walkSigned_escaped`).
The stream walk (`walkStream`, over the benchmark's shape `c_1 = L_1`,
`c_i = nodeStmt c_(i-1) L_i`), on the witness-sending submission under the reference signer's
key, with the empty log:
* Positive: `walkStream_one_leaf`, on the one-leaf stream whose proof is the signed leaf proof,
  returns `[xs]`; `walkStream_two_leaves`, on the two-leaf stream whose proof is the signed node
  proof over the two signed leaf proofs, returns `[xs₁, xs₂]`; `walkStream_three_leaves`, on the
  three-leaf stream whose proof is the signed node proof over that node proof and a third signed
  leaf proof (`streamSigned`), returns `[xs₁, xs₂, xs₃]`; `walkStreamSigned_two_leaves`: against
  a service that signed nothing (the traces are empty), the same data.
* The data collision (`dataCollision`): `stream_data_or_collision`, on the two-leaf stream, the
  walk's data are the runner's or a collision over the data tree is exhibited (positive);
  `dataCollision_odd` (three blocks, an odd level whose last digest is carried up): two
  different lists of three blocks with one root give a collision of the two last blocks' hash
  inputs or of the two top nodes' inputs, which carry the third hashes;
  `no_collision_on_runner_data` (negative): when the returned data are the runner's, the collision
  disjunct of `Outcome.data_or_collision` is false (the zip of a list with itself pairs no two
  different lists), so the two disjuncts are exclusive and the honest walk reports no collision.
* Negative: `noExt`'s stream walk escapes at the root of the two-leaf stream
  (`noExt_walkStream_escaped`), so the adversary that outputs that proof makes
  `compose_prob_stream`'s event certain (`noExt_stream_escape_prob`). An escape below the root:
  `topOnly`'s extractor opens only proofs longer than the two-leaf node proof, so on the
  three-leaf stream it opens the root and the walk escapes at the root's first child, the path
  `[false]` (`topOnly_walkStream_escaped`).
* `ws_compose_prob_stream`: under every key and against every adversary, the witness-sending
  stream walk escapes with probability `0` (`compose_prob_stream` at `ε = 0`, `qV = 0`).

The leaves' data are generic: every list of at most `leafCap` blocks, and in the trees and streams
lists of one length `n` (the seeds and sizes of the earlier seed leaf's controls, ported with their
intent).

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

/-- A signed leaf proof is accepted for the statement of its data at its size `n`. -/
theorem acc_leafSigned' (sk : ℕ → ℕ → Digest) {j : ℕ} (hj : j < 2 ^ sigHeight)
    (xs : List Digest) {n : ℕ} (h : xs.length = n) (hn : n ≤ leafCap) :
    submission.acc (Signer.pk sk) (leafStmt (dataRoot xs) n) (leafSigned sk j xs) = true := by
  subst h; exact acc_leafSigned sk hj xs hn

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
theorem noExt_not_ks (vk : Digest) (xs : List Digest) (hn : xs.length ≤ leafCap) (ε : ℝ≥0) :
    ¬ KS (Rel (noExt.acc vk)) (noExt.V vk) noExt.E ε noExt.qV :=
  not_ks_of_accept (c := leafStmt (dataRoot xs) xs.length) (π := encode (.leaf xs))
    (congrArg some (check_encode (vk := vk) (w := .leaf xs) ⟨hn, rfl⟩)) (by simp [noExt])
    (Nat.zero_le _) (by simp [noExt, submission])

/-- Its `acc` is the witness-sending one: the honest leaf proof is accepted. -/
theorem noExt_acc_leaf (sk : ℕ → ℕ → Digest) (xs : List Digest) (hn : xs.length ≤ leafCap) :
    noExt.acc (Signer.pk sk) (treeRoot ([dataRoot xs].map fun h => leafStmt h xs.length))
      (leafSigned sk 0 xs) = true :=
  acc_leafSigned (j := 0) sk (Nat.two_pow_pos _) xs hn

/-- **The walk escapes**: on an honest one-leaf tree, `noExt`'s walk ends in an escape at the
root. -/
theorem noExt_walk_escaped (sk : ℕ → ℕ → Digest) (xs : List Digest)
    (hn : xs.length ≤ leafCap) :
    (walk [] xs.length hn 0 [dataRoot xs] rfl (leafSigned sk 0 xs)
      (noExt_acc_leaf sk xs hn)).Escaped := by
  unfold walk walkFrom
  rw [extract_escape (L := []) (noExt_acc_leaf sk xs hn) nofun (by simp [noExt])]
  trivial

/-- **`compose_prob`'s event is certain** for `noExt` and the adversary that outputs the honest
leaf proof. -/
theorem noExt_escape_prob (sk : ℕ → ℕ → Digest) (xs : List Digest)
    (hn : xs.length ≤ leafCap) :
    prob (fun p L => ∃ hacc : noExt.acc (Signer.pk sk)
        (treeRoot ([dataRoot xs].map fun h => leafStmt h xs.length)) p = true,
      (walk L xs.length hn 0 [dataRoot xs] rfl p hacc).Escaped) (.ret (leafSigned sk 0 xs)) [] =
      1 :=
  (prob_ret _ _ _).trans (ind_of ⟨_, noExt_walk_escaped sk xs hn⟩)

/-! ## Positive: the walk on honest witness-sending trees -/

/-- **The walk on a one-leaf tree** returns the leaf's data. -/
theorem walk_one_leaf (sk : ℕ → ℕ → Digest) (xs : List Digest) (hn : xs.length ≤ leafCap) :
    (walk [] xs.length hn 0 [dataRoot xs] rfl (leafSigned sk 0 xs)
      (acc_leafSigned sk (by decide) xs hn)).data? = some [xs] :=
  walkFrom_leaf hn rfl rfl (by simp [leafSigned])
    (decode_encode (.leaf xs) (hn.trans_lt (by decide))) rfl rfl

/-- The signature words of a reference signature: 597 words. -/
theorem sigWords_sign_length (sk : ℕ → ℕ → Digest) (j : ℕ) (m : Digest) :
    (sigWords (Signer.sign sk j m)).length = 597 := by
  simp [sigWords, Signer.sign, List.length_flatMap, packBytes_digest_length,
    Signer.wotsDigits_length, Signer.authPath, Signer.sibs_length, wotsLen, sigHeight]

/-- The witness-sending node witness over two signed leaf proofs of `n` blocks each. -/
abbrev nodeWit (sk : ℕ → ℕ → Digest) (xs₁ xs₂ : List Digest) (n : ℕ) : Wit :=
  .node (leafStmt (dataRoot xs₁) n) (leafStmt (dataRoot xs₂) n) (leafSigned sk 0 xs₁)
    (leafSigned sk 1 xs₂)

/-- The signed node proof over two signed leaf proofs: the empty trace, signed with key `2`. -/
def nodeSigned (sk : ℕ → ℕ → Digest) (xs₁ xs₂ : List Digest) (n : ℕ) : Signed :=
  ⟨encode (nodeWit sk xs₁ xs₂ n), [], Signer.sign sk 2 (traceDigest [])⟩

/-- The node witness over two leaves of `n` blocks each is in the relation. -/
theorem rel_nodeWit (sk : ℕ → ℕ → Digest) {xs₁ xs₂ : List Digest} {n : ℕ}
    (h₁ : xs₁.length = n) (h₂ : xs₂.length = n) (hn : n ≤ leafCap) :
    Rel (submission.acc (Signer.pk sk))
      (nodeStmt (leafStmt (dataRoot xs₁) n) (leafStmt (dataRoot xs₂) n))
      (nodeWit sk xs₁ xs₂ n) := by
  have := Controls.Relation.node_of_two_leaves sk xs₁ xs₂ (h₁.trans_le hn) (h₂.trans_le hn)
  rwa [h₁, h₂] at this

/-- The node proof over two leaves of `n ≤ leafCap` blocks each: below `2^27` bytes. -/
theorem size_nodeWit (sk : ℕ → ℕ → Digest) {xs₁ xs₂ : List Digest} {n : ℕ}
    (h₁ : xs₁.length = n) (h₂ : xs₂.length = n) (hn : n ≤ leafCap) :
    (encode (nodeWit sk xs₁ xs₂ n)).size < 2 ^ 27 := by
  unfold leafCap at hn
  rw [size_encode]
  simp only [witWords, signedWords, bytesWords, logWords, List.length_cons, List.length_append,
    packBytes_length, sigWords_sign_length, leafSigned, ← size_eq_length, size_encode_leaf,
    Vector.length_toList, List.flatMap_nil, List.length_nil, h₁, h₂]
  omega

/-- The signed node proof is accepted for the node statement under the signer's key. -/
theorem acc_nodeSigned (sk : ℕ → ℕ → Digest) {xs₁ xs₂ : List Digest} {n : ℕ}
    (h₁ : xs₁.length = n) (h₂ : xs₂.length = n) (hn : n ≤ leafCap) :
    submission.acc (Signer.pk sk)
      (nodeStmt (leafStmt (dataRoot xs₁) n) (leafStmt (dataRoot xs₂) n))
      (nodeSigned sk xs₁ xs₂ n) = true := by
  have hsize : (encode (nodeWit sk xs₁ xs₂ n)).size < 2 ^ 64 :=
    (size_nodeWit sk h₁ h₂ hn).trans (by decide)
  rw [acc_eq, nodeSigned, decide_eq_true hsize]
  simp [Signer.sigOk_sign sk 2 (by decide), check_encode (rel_nodeWit sk h₁ h₂ hn)]

/-- The same acceptance, stated at the tree's root digest. -/
theorem acc_nodeSigned_root (sk : ℕ → ℕ → Digest) {xs₁ xs₂ : List Digest} {n : ℕ}
    (h₁ : xs₁.length = n) (h₂ : xs₂.length = n) (hn : n ≤ leafCap) :
    submission.acc (Signer.pk sk)
      (treeRoot ([dataRoot xs₁, dataRoot xs₂].map fun h => leafStmt h n))
      (nodeSigned sk xs₁ xs₂ n) = true :=
  acc_nodeSigned sk h₁ h₂ hn

/-- **The walk on a two-leaf tree** returns the two leaves' data. -/
theorem walk_two_leaves (sk : ℕ → ℕ → Digest) {xs₁ xs₂ : List Digest} {n : ℕ}
    (h₁ : xs₁.length = n) (h₂ : xs₂.length = n) (hn : n ≤ leafCap) :
    (walk [] n hn 1 [dataRoot xs₁, dataRoot xs₂] rfl (nodeSigned sk xs₁ xs₂ n)
      (acc_nodeSigned_root sk h₁ h₂ hn)).data? = some [xs₁, xs₂] := by
  have hn₁ : xs₁.length < 2 ^ 64 := (h₁.trans_le hn).trans_lt (by decide)
  have hn₂ : xs₂.length < 2 ^ 64 := (h₂.trans_le hn).trans_lt (by decide)
  have hR := rel_nodeWit sk h₁ h₂ hn
  unfold walk walkFrom
  rw [extract_of_E (L := []) (acc_nodeSigned_root sk h₁ h₂ hn) nofun
    (decode_encode _ (fits_of_rel hR)) hR]
  dsimp only
  rw [dite_eq_left_of_eq_true (eq_true ⟨rfl, rfl⟩)]
  split
  · rename_i e₁ e₂
    have a₁ := walkFrom_leaf hn (h := dataRoot xs₁) rfl e₁ nofun
      (decode_encode (.leaf xs₁) hn₁) rfl h₁
    have a₂ := walkFrom_leaf hn (h := dataRoot xs₂) rfl e₂ nofun
      (decode_encode (.leaf xs₂) hn₂) rfl h₂
    simp only [Outcome.data?, Option.some.injEq] at a₁ a₂ ⊢
    rw [a₁, a₂]; rfl
  -- the first walk is not data (three cases), then the second (three cases)
  all_goals rename_i e
  iterate 3 exact absurd (walkFrom_leaf hn (h := dataRoot xs₁) rfl e nofun
    (decode_encode (.leaf xs₁) hn₁) rfl h₁) nofun
  all_goals exact absurd (walkFrom_leaf hn (h := dataRoot xs₂) rfl e nofun
    (decode_encode (.leaf xs₂) hn₂) rfl h₂) nofun

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
theorem honest_leaf (sk : ℕ → ℕ → Digest) (xs : List Digest) :
    Honest [((leafSigned sk 0 xs).tr, (leafSigned sk 0 xs).σ)] [] :=
  ⟨by simp [leafSigned], by simp [leafSigned]⟩

/-- **Positive**: on the honest one-leaf tree, the walk against its signed traces returns the
leaf's data. -/
theorem walkSigned_one_leaf (sk : ℕ → ℕ → Digest) (xs : List Digest)
    (hn : xs.length ≤ leafCap) :
    (walkSigned [] _ (honest_leaf sk xs) xs.length hn 0 [dataRoot xs] rfl (leafSigned sk 0 xs)
      (acc_leafSigned sk (by decide) xs hn)).data? = some [xs] :=
  (Outcome.data?_reduce _ _).trans (walk_one_leaf sk xs hn)

/-- **Negative**: `noExt`'s walk against the same signed traces escapes at the root, so the
knowledge-soundness term of `compose_prob_signed` is needed. -/
theorem noExt_walkSigned_escaped (sk : ℕ → ℕ → Digest) (xs : List Digest)
    (hn : xs.length ≤ leafCap) :
    (walkSigned [] _ (honest_leaf sk xs) xs.length hn 0 [dataRoot xs] rfl (leafSigned sk 0 xs)
      (noExt_acc_leaf sk xs hn)).Escaped :=
  (Outcome.escaped_reduce _ _).mpr (noExt_walk_escaped sk xs hn)

/-! ## The forgery outcome through the walk: a one-query leaf proof -/

open RecursionFast.Controls.Relation (oneQuery qMax acc_query_at_cap)

/-- The leaf proof of the data `xs` with the one-entry trace `(qMax, a)`, signed with key `0`. -/
def queryLeaf (sk : ℕ → ℕ → Digest) (xs : List Digest) (a : Digest) : Signed :=
  ⟨encode (.leaf xs), [(qMax, a)], Signer.sign sk 0 (traceDigest [(qMax, a)])⟩

/-- The one-query verifier accepts it, for the one-leaf tree's root. -/
theorem acc_queryLeaf (sk : ℕ → ℕ → Digest) (xs : List Digest) (a : Digest)
    (hn : xs.length ≤ leafCap) :
    (oneQuery qMax).acc (Signer.pk sk)
      (treeRoot ([dataRoot xs].map fun h => leafStmt h xs.length)) (queryLeaf sk xs a) = true :=
  acc_query_at_cap sk a _ (by unfold leafCap at hn; rw [size_encode_leaf]; omega)

/-- **Positive** (the EUF-CMA outcome through the walk): with the empty log and a service that
signed nothing, the walk against its signed traces returns an EUF-CMA forgery at the root. -/
theorem walkSigned_queryLeaf_euf (sk : ℕ → ℕ → Digest) (xs : List Digest) (a : Digest)
    (hn : xs.length ≤ leafCap) :
    (walkSigned [] [] ⟨nofun, nofun⟩ xs.length hn 0 [dataRoot xs] rfl (queryLeaf sk xs a)
      (acc_queryLeaf sk xs a hn)).IsEuf := by
  unfold walkSigned walk walkFrom
  rw [extract_forgery (L := []) _ fun h => List.not_mem_nil (h _ (List.mem_singleton_self _))]
  exact Outcome.isEuf_reduce_forgery _ _ _ _ _
    ⟨Signer.sigOk_sign sk 0 (by decide) _, fun h => by
      obtain ⟨_, hx, _⟩ := mem_fst_issued.mp h; exact List.not_mem_nil hx⟩

/-- **The EUF-CMA term of `compose_prob_signed` is reached**: against a service that signed
nothing (`T = fun _ _ => []`), the adversary that holds the key, asks nothing and outputs
`queryLeaf` makes the EUF-CMA event certain. -/
theorem queryLeaf_euf_prob (sk : ℕ → ℕ → Digest) (xs : List Digest) (a : Digest)
    (hn : xs.length ≤ leafCap) :
    prob (fun p L => ∃ hacc : (oneQuery qMax).acc (Signer.pk sk)
        (treeRoot ([dataRoot xs].map fun h => leafStmt h xs.length)) p = true,
      (walkSigned L [] ⟨nofun, nofun⟩ xs.length hn 0 [dataRoot xs] rfl p hacc).IsEuf)
      (.ret (queryLeaf sk xs a)) [] = 1 :=
  (prob_ret _ _ _).trans (ind_of ⟨_, walkSigned_queryLeaf_euf sk xs a hn⟩)

/-- **Positive** (`Honest` on a non-empty trace): a log holding `(qMax, a)` accounts for the
service having signed `queryLeaf`'s trace. -/
theorem honest_queryLeaf (sk : ℕ → ℕ → Digest) (xs : List Digest) (a : Digest) :
    Honest [((queryLeaf sk xs a).tr, (queryLeaf sk xs a).σ)] [(qMax, a)] :=
  have hq : qMax.size = queryCap := by simp [qMax, ByteArray.size]
  ⟨by simp [queryLeaf], fun x hx e he => by
    rw [List.mem_singleton.mp hx] at he
    rw [List.mem_singleton.mp he, hq]⟩

/-- **Positive**: with that log and those signed traces, the walk returns the leaf's data. -/
theorem walkSigned_queryLeaf_data (sk : ℕ → ℕ → Digest) (xs : List Digest) (a : Digest)
    (hn : xs.length ≤ leafCap) :
    (walkSigned [(qMax, a)] _ (honest_queryLeaf sk xs a) xs.length hn 0 [dataRoot xs] rfl
      (queryLeaf sk xs a) (acc_queryLeaf sk xs a hn)).data? = some [xs] :=
  (Outcome.data?_reduce _ _).trans (walkFrom_leaf hn rfl rfl (by simp [queryLeaf])
    (decode_encode (.leaf xs) (hn.trans_lt (by decide))) rfl rfl)

/-! ## The stream walk: `c_1 = L_1`, `c_i = nodeStmt c_(i-1) L_i` -/

/-- **The stream walk on a one-leaf stream** returns the leaf's data. -/
theorem walkStream_one_leaf (sk : ℕ → ℕ → Digest) (xs : List Digest)
    (hn : xs.length ≤ leafCap) :
    (walkStream [] xs.length hn [dataRoot xs] (leafSigned sk 0 xs)
      (acc_leafSigned sk (by decide) xs hn)).data? = some [xs] :=
  walkStreamFrom_one (L := []) (p := leafSigned sk 0 xs) hn nofun
    (decode_encode (.leaf xs) (hn.trans_lt (by decide))) rfl rfl

/-- The signed node proof over two signed leaf proofs is accepted for the two-leaf stream's
digest (the same digest as the two-leaf tree's root). -/
theorem acc_nodeSigned_stream (sk : ℕ → ℕ → Digest) {xs₁ xs₂ : List Digest} {n : ℕ}
    (h₁ : xs₁.length = n) (h₂ : xs₂.length = n) (hn : n ≤ leafCap) :
    submission.acc (Signer.pk sk) (streamStmt n [dataRoot xs₁, dataRoot xs₂])
      (nodeSigned sk xs₁ xs₂ n) = true :=
  acc_nodeSigned sk h₁ h₂ hn

/-- **The stream walk on a two-leaf stream** returns the two leaves' data. -/
theorem walkStream_two_leaves (sk : ℕ → ℕ → Digest) {xs₁ xs₂ : List Digest} {n : ℕ}
    (h₁ : xs₁.length = n) (h₂ : xs₂.length = n) (hn : n ≤ leafCap) :
    (walkStream [] n hn [dataRoot xs₁, dataRoot xs₂] (nodeSigned sk xs₁ xs₂ n)
      (acc_nodeSigned_stream sk h₁ h₂ hn)).data? = some [xs₁, xs₂] := by
  have hn₁ : xs₁.length < 2 ^ 64 := (h₁.trans_le hn).trans_lt (by decide)
  have hn₂ : xs₂.length < 2 ^ 64 := (h₂.trans_le hn).trans_lt (by decide)
  have hR := rel_nodeWit sk h₁ h₂ hn
  exact walkStreamFrom_succ_succ (L := []) (k := 0) (hs := [dataRoot xs₁, dataRoot xs₂])
    (p := nodeSigned sk xs₁ xs₂ n) hn (List.cons_ne_nil _ _) nofun
    (decode_encode _ (fits_of_rel hR)) hR
    (fun _ _ _ _ => walkStreamFrom_one (p := leafSigned sk 0 xs₁) hn nofun
      (decode_encode (.leaf xs₁) hn₁) rfl h₁) nofun
    (xs := xs₂) (decode_encode (.leaf xs₂) hn₂) rfl h₂

/-- **The extracted data are the runner's, or a collision is exhibited** (positive, on the
two-leaf stream): whatever the walk returns as data is the runner's data `[xs₁, xs₂]`, or two
different block lists of one leaf with one length and one root, from which `dataCollision`
computes a collision over the data tree. On the honest proof it is the runner's
(`walkStream_two_leaves`). -/
theorem stream_data_or_collision (sk : ℕ → ℕ → Digest) {xs₁ xs₂ : List Digest} {n : ℕ}
    (h₁ : xs₁.length = n) (h₂ : xs₂.length = n) (hn : n ≤ leafCap) {L : Log} {p : Signed}
    (hacc : submission.acc (Signer.pk sk) (streamStmt n ([xs₁, xs₂].map dataRoot)) p = true)
    {yss : List (List Digest)} (h : (walkStream L n hn ([xs₁, xs₂].map dataRoot) p hacc).data? =
      some yss) :
    yss = [xs₁, xs₂] ∨ ∃ (ys xs : List Digest) (hne : ys ≠ xs) (hl : ys.length = xs.length)
      (hr : dataRoot ys = dataRoot xs), (ys, xs) ∈ yss.zip [xs₁, xs₂] ∧
        DataPreimage (dataCollision hne hl hr).x ∧ DataPreimage (dataCollision hne hl hr).y :=
  Outcome.data_or_collision h (by simp [h₁, h₂])

/-- **The data collision at an odd size** (three blocks: the third hash is carried up a level):
two different lists of three blocks with one root give a collision of the two lists' block hash
inputs or data node inputs, and when the two lists differ only in their last block, it is that
block's hash input or the top node's, which carries its hash. -/
theorem dataCollision_odd (a b c c' : Digest) (hc : c ≠ c')
    (hr : dataRoot [a, b, c] = dataRoot [a, b, c']) :
    let col := dataCollision (xs := [a, b, c]) (ys := [a, b, c']) (by simpa using hc) rfl hr
    (col.x = tagItem :: c.toList ∧ col.y = tagItem :: c'.toList) ∨
      (col.x = tagData :: (dataNode (leafItem a) (leafItem b)).toList ++ (leafItem c).toList ∧
        col.y = tagData :: (dataNode (leafItem a) (leafItem b)).toList ++
          (leafItem c').toList) := by
  intro col
  simp only [col, dataCollision, List.map_cons, List.map_nil, List.length_cons, List.length_nil]
  split
  · rename_i hm
    left
    simp [itemCollision, hc]
  · rename_i hm
    have hi : leafItem c ≠ leafItem c' := fun h => hm (by rw [h])
    have htop : dataNode (dataNode (leafItem a) (leafItem b)) (leafItem c) =
        dataNode (dataNode (leafItem a) (leafItem b)) (leafItem c') := by
      simpa [dataRoot, dataLevel] using hr
    right
    simp [iterateCollision, levelCollision, dataLevel, hi, htop]

/-- **No collision on the runner's data** (negative): the collision disjunct of
`data_or_collision` (and `Outcome.data_or_collision`, `stream_data_or_collision`) at returned data
`yss = xss` is false, for every list of block lists: the zip of a list with itself pairs each
entry with itself, never two different lists. So the disjuncts are exclusive, and a walk that
returns the runner's data never also exhibits a data collision. -/
theorem no_collision_on_runner_data (xss : List (List Digest)) :
    ¬ ∃ (ys xs : List Digest) (hne : ys ≠ xs) (hl : ys.length = xs.length)
      (hr : dataRoot ys = dataRoot xs), (ys, xs) ∈ xss.zip xss ∧
        DataPreimage (dataCollision hne hl hr).x ∧ DataPreimage (dataCollision hne hl hr).y := by
  rintro ⟨ys, xs, hne, -, -, hm, -⟩
  exact hne ((List.forall₂_iff_zip.mp (List.forall₂_refl xss)).2 hm)

/-- The witness-sending node witness of the three-leaf stream: the signed node proof over the
first two leaves and the signed leaf proof of the third (key `3`). -/
abbrev streamWit (sk : ℕ → ℕ → Digest) (xs₁ xs₂ xs₃ : List Digest) (n : ℕ) : Wit :=
  .node (nodeStmt (leafStmt (dataRoot xs₁) n) (leafStmt (dataRoot xs₂) n))
    (leafStmt (dataRoot xs₃) n) (nodeSigned sk xs₁ xs₂ n) (leafSigned sk 3 xs₃)

/-- The signed proof of the three-leaf stream: the empty trace, signed with key `4`. -/
def streamSigned (sk : ℕ → ℕ → Digest) (xs₁ xs₂ xs₃ : List Digest) (n : ℕ) : Signed :=
  ⟨encode (streamWit sk xs₁ xs₂ xs₃ n), [], Signer.sign sk 4 (traceDigest [])⟩

/-- The three-leaf stream's node witness is in the relation. -/
theorem rel_streamWit (sk : ℕ → ℕ → Digest) {xs₁ xs₂ xs₃ : List Digest} {n : ℕ}
    (h₁ : xs₁.length = n) (h₂ : xs₂.length = n) (h₃ : xs₃.length = n) (hn : n ≤ leafCap) :
    Rel (submission.acc (Signer.pk sk))
      (streamStmt n [dataRoot xs₁, dataRoot xs₂, dataRoot xs₃])
      (streamWit sk xs₁ xs₂ xs₃ n) :=
  ⟨rfl, acc_nodeSigned sk h₁ h₂ hn, acc_leafSigned' sk (by decide) xs₃ h₃ hn⟩

/-- The signed proof of the three-leaf stream is accepted for its digest. -/
theorem acc_streamSigned (sk : ℕ → ℕ → Digest) {xs₁ xs₂ xs₃ : List Digest} {n : ℕ}
    (h₁ : xs₁.length = n) (h₂ : xs₂.length = n) (h₃ : xs₃.length = n) (hn : n ≤ leafCap) :
    submission.acc (Signer.pk sk)
      (streamStmt n [dataRoot xs₁, dataRoot xs₂, dataRoot xs₃])
      (streamSigned sk xs₁ xs₂ xs₃ n) = true := by
  have hb := size_nodeWit sk h₁ h₂ hn
  have hsize : (encode (streamWit sk xs₁ xs₂ xs₃ n)).size < 2 ^ 64 := by
    unfold leafCap at hn
    rw [size_encode]
    simp only [witWords, signedWords, bytesWords, logWords, List.length_cons, List.length_append,
      packBytes_length, sigWords_sign_length, nodeSigned, leafSigned, ← size_eq_length,
      size_encode_leaf, Vector.length_toList, List.flatMap_nil, List.length_nil, h₃]
    omega
  rw [acc_eq, streamSigned, decide_eq_true hsize]
  simp [Signer.sigOk_sign sk 4 (by decide), check_encode (rel_streamWit sk h₁ h₂ h₃ hn)]

/-- **The stream walk on a three-leaf stream** returns the three leaves' data. -/
theorem walkStream_three_leaves (sk : ℕ → ℕ → Digest) {xs₁ xs₂ xs₃ : List Digest} {n : ℕ}
    (h₁ : xs₁.length = n) (h₂ : xs₂.length = n) (h₃ : xs₃.length = n) (hn : n ≤ leafCap) :
    (walkStream [] n hn [dataRoot xs₁, dataRoot xs₂, dataRoot xs₃]
      (streamSigned sk xs₁ xs₂ xs₃ n) (acc_streamSigned sk h₁ h₂ h₃ hn)).data? =
      some [xs₁, xs₂, xs₃] := by
  have hn₁ : xs₁.length < 2 ^ 64 := (h₁.trans_le hn).trans_lt (by decide)
  have hn₂ : xs₂.length < 2 ^ 64 := (h₂.trans_le hn).trans_lt (by decide)
  have hn₃ : xs₃.length < 2 ^ 64 := (h₃.trans_le hn).trans_lt (by decide)
  have hR := rel_streamWit sk h₁ h₂ h₃ hn
  have hR₂ := rel_nodeWit sk h₁ h₂ hn
  exact walkStreamFrom_succ_succ (L := []) (k := 1)
    (hs := [dataRoot xs₁, dataRoot xs₂, dataRoot xs₃]) (p := streamSigned sk xs₁ xs₂ xs₃ n)
    hn (List.cons_ne_nil _ _) nofun (decode_encode _ (fits_of_rel hR)) hR
    (fun _ _ _ _ => walkStreamFrom_succ_succ (L := []) (k := 0)
      (hs := [dataRoot xs₁, dataRoot xs₂]) (p := nodeSigned sk xs₁ xs₂ n)
      hn (List.cons_ne_nil _ _) nofun (decode_encode _ (fits_of_rel hR₂)) hR₂
      (fun _ _ _ _ => walkStreamFrom_one (p := leafSigned sk 0 xs₁) hn nofun
      (decode_encode (.leaf xs₁) hn₁) rfl h₁) nofun
      (xs := xs₂) (decode_encode (.leaf xs₂) hn₂) rfl h₂) nofun
    (xs := xs₃) (decode_encode (.leaf xs₃) hn₃) rfl h₃

/-- **`noExt`'s stream walk escapes**: on the honest two-leaf stream it ends in an escape at the
root. -/
theorem noExt_walkStream_escaped (sk : ℕ → ℕ → Digest) {xs₁ xs₂ : List Digest} {n : ℕ}
    (h₁ : xs₁.length = n) (h₂ : xs₂.length = n) (hn : n ≤ leafCap) :
    (walkStream (S := noExt) [] n hn [dataRoot xs₁, dataRoot xs₂] (nodeSigned sk xs₁ xs₂ n)
      (acc_nodeSigned_stream sk h₁ h₂ hn)).Escaped :=
  (walkStreamFrom_escape (S := noExt) (L := []) (k := 0)
    (hs := [dataRoot xs₁, dataRoot xs₂]) (p := nodeSigned sk xs₁ xs₂ n) hn nofun
    (by simp [noExt])).1

/-- **`compose_prob_stream`'s event is certain** for `noExt` and the adversary that outputs the
honest two-leaf stream's signed proof. -/
theorem noExt_stream_escape_prob (sk : ℕ → ℕ → Digest) {xs₁ xs₂ : List Digest} {n : ℕ}
    (h₁ : xs₁.length = n) (h₂ : xs₂.length = n) (hn : n ≤ leafCap) :
    prob (fun p L => ∃ hacc : noExt.acc (Signer.pk sk)
        (streamStmt n [dataRoot xs₁, dataRoot xs₂]) p = true,
      (walkStream L n hn [dataRoot xs₁, dataRoot xs₂] p hacc).Escaped)
      (.ret (nodeSigned sk xs₁ xs₂ n)) [] = 1 :=
  (prob_ret _ _ _).trans (ind_of ⟨_, noExt_walkStream_escaped sk h₁ h₂ hn⟩)

/-- **The witness-sending stream walk escapes with probability `0`**, under every key and against
every adversary asking at most `Q ≤ logCap` queries. -/
theorem ws_compose_prob_stream (vk : Digest) {n : ℕ} (hn : n ≤ leafCap) (hs : List Digest)
    (A : OProg Signed) {Q : ℕ} (hA : ∀ H, (A.queries H).length ≤ Q) (hQ : Q ≤ logCap) :
    prob (fun p L => ∃ hacc : submission.acc vk (streamStmt n hs) p = true,
      (walkStream L n hn hs p hacc).Escaped) A [] = 0 :=
  le_antisymm ((compose_prob_stream (ks vk) n hn hs A hA (by simpa [submission] using hQ)).trans
    (by simp [submission])) bot_le

/-- **Positive** (against signed traces): on the honest two-leaf stream, whose traces are empty,
the stream walk against a service that signed nothing returns the two leaves' data. -/
theorem walkStreamSigned_two_leaves (sk : ℕ → ℕ → Digest) {xs₁ xs₂ : List Digest} {n : ℕ}
    (h₁ : xs₁.length = n) (h₂ : xs₂.length = n) (hn : n ≤ leafCap) :
    (walkStreamSigned [] [] ⟨nofun, nofun⟩ n hn [dataRoot xs₁, dataRoot xs₂]
      (nodeSigned sk xs₁ xs₂ n) (acc_nodeSigned_stream sk h₁ h₂ hn)).data? = some [xs₁, xs₂] :=
  (Outcome.data?_reduce _ _).trans (walkStream_two_leaves sk h₁ h₂ hn)

/-! ## Negative: an escape below the root of the stream -/

/-- The witness-sending submission with an extractor that opens only proofs longer than the
two-leaf node proof `nodeSigned sk xs₁ xs₂ n`: on the three-leaf stream it opens the root and not
the root's first child. -/
def topOnly (sk : ℕ → ℕ → Digest) (xs₁ xs₂ : List Digest) (n : ℕ) : Submission :=
  { submission with
    E := fun _ π _ => if (nodeSigned sk xs₁ xs₂ n).π.size < π.size then decode π else none }

/-- **An escape at a non-root member**: on the honest three-leaf stream, `topOnly`'s stream walk
opens the root and escapes at its first child, the path `[false]` (the node over the first two
leaves). -/
theorem topOnly_walkStream_escaped (sk : ℕ → ℕ → Digest) {xs₁ xs₂ xs₃ : List Digest} {n : ℕ}
    (h₁ : xs₁.length = n) (h₂ : xs₂.length = n) (h₃ : xs₃.length = n) (hn : n ≤ leafCap) :
    (walkStream (S := topOnly sk xs₁ xs₂ n) [] n hn
        [dataRoot xs₁, dataRoot xs₂, dataRoot xs₃] (streamSigned sk xs₁ xs₂ xs₃ n)
        (acc_streamSigned sk h₁ h₂ h₃ hn)).Escaped ∧
      (walkStream (S := topOnly sk xs₁ xs₂ n) [] n hn
        [dataRoot xs₁, dataRoot xs₂, dataRoot xs₃] (streamSigned sk xs₁ xs₂ xs₃ n)
        (acc_streamSigned sk h₁ h₂ h₃ hn)).EscapeIn (· = [false]) := by
  have hR := rel_streamWit sk h₁ h₂ h₃ hn
  have hE : (topOnly sk xs₁ xs₂ n).E
      (streamStmt n [dataRoot xs₁, dataRoot xs₂, dataRoot xs₃])
      (streamSigned sk xs₁ xs₂ xs₃ n).π [] = some (streamWit sk xs₁ xs₂ xs₃ n) := by
    have hlt := (size_child_lt
      (nodeStmt (leafStmt (dataRoot xs₁) n) (leafStmt (dataRoot xs₂) n))
      (leafStmt (dataRoot xs₃) n) (nodeSigned sk xs₁ xs₂ n) (leafSigned sk 3 xs₃)).1
    simp only [topOnly, streamSigned, hlt, ↓reduceIte]
    exact decode_encode _ (fits_of_rel hR)
  have e := walkStreamFrom_node (S := topOnly sk xs₁ xs₂ n) (L := []) (M := 3) (k := 1)
    (hs := [dataRoot xs₁, dataRoot xs₂, dataRoot xs₃]) (p := streamSigned sk xs₁ xs₂ xs₃ n)
    (hk := rfl) (j := 0) (hj := rfl) (hacc := acc_streamSigned sk h₁ h₂ h₃ hn) (hmem := .root)
    hn (List.cons_ne_nil _ _) nofun hE hR
  have he := walkStreamFrom_escape (S := topOnly sk xs₁ xs₂ n) (L := []) (M := 3) (k := 0)
    (hs := [dataRoot xs₁, dataRoot xs₂]) (p := nodeSigned sk xs₁ xs₂ n) (j := 1) (hj := rfl)
    (hk := rfl) (hacc := acc_nodeSigned_stream sk h₁ h₂ hn) (hmem := InTree.left .root hE) hn
    nofun (by simp [topOnly])
  exact (congrArg (fun o => o.Escaped ∧ o.EscapeIn (· = [false])) e).mpr
    (Outcome.Escaped.append _ he.1 he.2)

end RecursionFast.Controls.Compose
