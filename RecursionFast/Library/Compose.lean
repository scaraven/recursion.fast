/-
  RecursionFast.Library.Compose  (UNTRUSTED, kernel-checked)

  **The composition argument across the benchmark's stream and across balanced trees**
  (CGSY24 Thm 5.1's straight-line argument), from the contract's single-output knowledge
  soundness by a union bound over the extracted proofs. Fix a submission `S` and a public key
  `vk`. The leaves' digests are `leafStmt hᵢ n` (the runner computes them from the leaf values
  `hᵢ = dataRoot xsᵢ` of the data `xsᵢ` it drew, `n` blocks each, with `n ≤ leafCap`). The
  benchmark is a **stream** of `M` steps (plain IVC): `c_1 = L_1`, `c_i = nodeStmt c_(i-1) L_i`
  (`streamStmt`, `Contract/Tree.lean`), a left-leaning chain whose every node's second child is a
  leaf; `walkStream` and `compose_prob_stream` cover it. A **balanced tree** of `2^r` leaves has the
  root digest `treeRoot` of them; `walk` and `compose_prob` cover it (the setting of
  `Contract/Tree.lean` and its known-answer control). The tree walk is described first; the stream
  walk reuses its pieces.

  **The walk** (deterministic and compiled; `walk`). Given one oracle log
  `L` and a root signed proof `p₀` that `S.acc vk` accepts, it returns, computed from `p₀`
  through `S.E` on `L` (`Outcome`):
  * **the leaves' data**: `xsᵢ` of `n` blocks with `dataRoot xsᵢ = hᵢ` for every leaf (where the
    runner drew the data `xssᵢ` with `hs = xss.map dataRoot`, the returned data is the runner's or
    the data collision exhibits a Keccak-256 collision, `Outcome.data_or_collision`);
  * **a Keccak-256 collision** (`Collision`): the tagged preimages of a statement mismatch;
  * **a forgery in the extraction tree of `p₀`**: a signed proof `p` at a path `bs` of the tree
    (`InTree`: the root, or a child of a node witness `S.E` returns for a member) whose trace has
    queries of at most `queryCap` bytes and a valid signature on its digest under `vk`, while the
    trace is not contained in `L` (`Forgery`);
  * **an escape in the extraction tree**, at depth at most `r`: a member that `acc` accepts,
    whose trace is in `L`, and which `S.E` on `L` does not open to a witness of the relation
    (`Escape`).
  At each member the walk checks the signed proof's trace against `L`; if it is contained it asks
  `S.E` on `L`, checks the witness (`Rel` is decidable), and compares its digests with the tree's.
  **The type `Outcome` is not the statement**: it is inhabited with no content (a Keccak-256
  collision exists by pigeonhole, `Controls/Compose.lean`, `collision_nonempty`, and the leaves'
  data exist whenever the harness drew them). The content is the compiled definition of `walk`,
  which computes its outcome from `p₀`, `S.E` and `L`, together with the kernel theorems about what
  it returns: `compose_prob`, `walk_not_escaped`, `extract_of_E`, `walkFrom_leaf`. That the
  definition computes, and so chooses no data classically, is the compiler's check, not a kernel
  statement.

  **The probability** (`compose_prob`), stated on the walk's output. Let `A` be a query program
  asking at most `Q` queries that outputs the root signed proof, run against one lazily sampled
  random oracle, `L` its final log. The probability that the root is accepted and the walk ends in
  an escape (`Outcome.Escaped`: none of the first three outcomes) is at most
  `(2^(r+1) - 1) · (Q + qV) · ε`. On a functional log (every lazily sampled
  log is one) an escape at `(c, p)` is a win of `KS`'s game at `(c, p.π)` on `L` (`Escape.wins`,
  by `runLog_of_runSeq`). For each path `bs` of length at most `r` (`paths r`, `2^(r+1) - 1` of
  them, `card_paths`) the adversary that runs `A` keeping its log and outputs the member at `bs`
  (`memberAt`) asks at most `Q` queries, and `V` run after it on that member asks nothing fresh;
  `KS.union` (`Library/KS.lean`) adds the bounds (`escape_prob_le`). No inner member's verifier
  is run by these adversaries, since `E` reads the log: each member costs `(Q + qV) · ε`.

  **The meter's lossless composition** (`walk_not_escaped`): with a knowledge state
  (`Library/Security.lean`) and one log of potential below `1`, functional and within `logCap`,
  no member escapes (`Escape.not_of_kstate`), so the walk returns one of the first three
  outcomes, and the one event, a potential of at least `1`, has probability at most `n · ε` for a
  game of `n` queries (`PaperTheorem.prob_potential_ge_one`), for the whole tree.

  **The stream walk** (`walkStream`, compiled and deterministic like `walk`). From an accepted
  signed proof of `streamStmt n hs` (`hs` the `M` leaf values, oldest first) it returns, as an
  `Outcome` of depth `M - 1`, the data of **all `M` leaves**, a collision, a forgery in the
  extraction tree, or an escape in it. At a node it extracts the two children, checks that they
  are the digests of the stream without its last leaf and of that leaf (else a collision,
  `nodeCollision`), walks the second child as a one-leaf tree (`walkFrom` at `r = 0`) and the
  first as the shorter stream, and joins the outcomes (`Outcome.append`). Its members lie on the
  stream's comb: the left spine `[false]^j`, `j < M` (the `M - 1` nodes and the oldest leaf), and
  the second children `true :: [false]^j`, `j < M - 1` (the other leaves), `2M - 1` paths
  (`combPaths`, `card_combPaths`); an escape is at one of them (`walkStream_escapeIn`, carried by
  the walk's own result type). So `compose_prob_stream` bounds its escape by
  `(2M - 1) · (Q + qV) · ε` (`escape_prob_le` over `combPaths M`: `2M - 1` members, where
  depth alone would give `2^M - 1`; `M` is the season's, `harness/season.toml`, and nothing here
  fixes it), and `walkStream_not_escaped` is its lossless form.
  `walkStreamSigned`, `compose_prob_stream_signed` and `walkStreamSigned_not_escaped` are the
  signed variants, through `Outcome.reduce`. Returned data are the leaves' data
  (`Outcome.forall₂_of_data?`, `SignedOutcome.forall₂_of_data?`), so off the bounded events the
  data of all `M` leaves are extracted, and they are the runner's or a collision is exhibited
  (`Outcome.data_or_collision`, `SignedOutcome.data_or_collision`, through `dataCollision`: two
  different block lists of one length and one `dataRoot` give a Keccak-256 collision of two
  data-tree preimages, the carry-up included). `Outcome.toRunner` makes that one outcome: returned
  data other than the runner's become the collision (`pairsCollision`), so its data are the
  runner's (`Outcome.toRunner_data?`), and it escapes exactly when the walk does
  (`Outcome.toRunner_escaped`); `compose_prob_stream_runner` bounds that escape by
  `compose_prob_stream`'s bound. `walkStreamFrom_one`, `walkStreamFrom_node`,
  `walkStreamFrom_succ_succ` and `walkStreamFrom_escape` read the walk on known extractor outputs.

  **The forgery outcome against the service's signed traces** (`Forgery.reduce`, `walkSigned`).
  Let `T` list the traces the service signed, with their signatures, and `Honest T L` say that
  the log accounts for them: every answer the service signs is an oracle evaluation it made, so
  in `L`, and its queries are within the wire cap. A forgery against `L` is then, computed:
  * an **EUF-CMA forgery** against the signing record `issued T`
    (`Library/Unforgeability.lean`, `EufForgery`): a valid signature on its trace's digest, a
    message the service never signed; or
  * a **collision** of `traceBytes` encodings, when the service signed some trace of `T` with that
    digest: the two traces differ (one is in `L`, the other is not), and the encoding is injective
    on queries within `queryCap` (`traceBytes_inj`).
  `walkSigned` is `walk` with its forgery so reduced: the leaves' data, a collision, an EUF-CMA
  forgery in the extraction tree, or an escape. As for `walk`, its type `SignedOutcome` is not the
  statement (a collision inhabits it); the content is the compiled definition and the theorems
  about it. `compose_prob_signed` bounds the probability that it returns no leaf data by the
  escape bound plus the probabilities that it returns a collision and an EUF-CMA forgery;
  `walkSigned_not_escaped` is its lossless form. The reduction of one forgery
  (`Forgery.reduce`) does not depend on the tree's shape; the walks around it are for balanced
  trees (`walkSigned`) and for the stream (`walkStreamSigned`).

  **Which signature property, and why not signature-only security.** The original signed-oracle
  construction (Chiesa–Tromer, "Proof-Carrying Data and Hearsay Arguments from Signature Cards",
  ICS 2010, §2) assumes signatures that are EUF-CMA and also secure against **signature-only
  forgery** (`SigOnlyForgery`: "a hitherto-unseen signature that is valid for any message (the
  forger is not required to say which one)"). Its list extractor (§3.5, Algorithm 5) finds, for
  each signature a proof carries, the oracle query whose answer has that signature value, because
  the concise proof does not carry the signed message (instance and witness); its failure is an
  unseen signature on an unnamed message. This walk matches a signed proof to the log by its
  trace, the signed message itself, which a signed proof carries in the clear, and never compares
  signature values (`extract`); the EUF-CMA event reads no signature of the record
  (`Library/Unforgeability.lean`, `eufForgery_issued_iff`). Its failure is a valid signature on a
  named message: **EUF-CMA and collision resistance of Keccak-256 suffice**, as in the soundness
  reduction of Chiesa–Guan–Yildiz 2026 (proof of Theorem 5.2), and signature-only security is not
  used. A second valid signature on a trace the service signed, not issued by the service, is a
  SUF-CMA and signature-only forgery but no EUF-CMA forgery (`Controls/Unforgeability.lean`,
  `resign_not_euf`); it does not affect the walk. (A second signature the service itself issues on
  a trace is in its signing record and no forgery of any kind.)

  A bare forgery against the log is free for a known signer (`Controls/Compose.lean`,
  `forgery_trivial`); the content of the forgery outcome is its membership of the extraction tree
  and, against the service's signed traces, its reduction.

  The EUF-CMA outcome is not left to an EUF-CMA assumption: it is reduced in the kernel to a
  Keccak-256 collision or a chain inversion (`Library/WotsReduce.lean`, `eufReduce`, given that
  `T` is the service's complete transcript, `Transcript`: the reference signer's signatures, one
  message per index), and `compose_prob_wots` and `compose_prob_stream_wots` replace the EUF-CMA
  term by those two. What stays on paper: the
  probabilities of the collision and the chain-inversion outcomes, bounded by
  `Adv_coll + Adv_inv` (`Adv_inv`: tweakable multi-target one-wayness of the chain step with
  pseudorandom chain starts, AGENTS.md §11). The adversaries run the whole evaluation (the prover,
  the service with its `sign` requests answered by the reference signer, the harness's checks),
  keep the signed traces as `T`, which the log accounts for by the service's specification, and
  output the walk's collision or the reduction's collision or chain value; the collision finder
  draws the signing key itself. Also on paper: lazy sampling
  against a random function, randomised adversaries, and the PRF hybrid from the random oracle to
  the keyed deployment (AGENTS.md §12).
-/
import RecursionFast.Library.Trace
import RecursionFast.Library.Tree
import RecursionFast.Library.KS
import RecursionFast.Library.Unforgeability
import RecursionFast.Contract.Certificate

open scoped NNReal

namespace RecursionFast.Compose
open RecursionFast

/-- **The extraction tree** of `S` on the log `L` from the root `(c₀, p₀)`, each member with its
path from the root (last step first; `false` for a first child): the root, and the two children's
signed proofs of every member that the extractor opens, on `L`, to a node witness. -/
inductive InTree (S : Submission) (L : Log) (c₀ : Digest) (p₀ : Signed) :
    List Bool → Digest → Signed → Prop
  /-- The root. -/
  | root : InTree S L c₀ p₀ [] c₀ p₀
  /-- The first child of a member the extractor opens to a node. -/
  | left {bs : List Bool} {c c₁ c₂ : Digest} {p p₁ p₂ : Signed} : InTree S L c₀ p₀ bs c p →
      S.E c p.π L = some (.node c₁ c₂ p₁ p₂) → InTree S L c₀ p₀ (false :: bs) c₁ p₁
  /-- The second child of a member the extractor opens to a node. -/
  | right {bs : List Bool} {c c₁ c₂ : Digest} {p p₁ p₂ : Signed} : InTree S L c₀ p₀ bs c p →
      S.E c p.π L = some (.node c₁ c₂ p₁ p₂) → InTree S L c₀ p₀ (true :: bs) c₂ p₂

/-- The member of the extraction tree of `S` on `L` from the root `x₀` at the path `bs`, if any. -/
def follow (S : Submission) (L : Log) (x₀ : Digest × Signed) :
    List Bool → Option (Digest × Signed)
  | [] => some x₀
  | b :: bs => (follow S L x₀ bs).bind fun x =>
    match S.E x.1 x.2.π L with
    | some (.node c₁ c₂ p₁ p₂) => some (if b then (c₂, p₂) else (c₁, p₁))
    | _ => none

/-- A member of the extraction tree is the one at its path. -/
theorem InTree.follow_eq {S : Submission} {L : Log} {c₀ : Digest} {p₀ : Signed} {bs : List Bool}
    {c : Digest} {p : Signed} (h : InTree S L c₀ p₀ bs c p) :
    follow S L (c₀, p₀) bs = some (c, p) := by
  induction h with
  | root => rfl
  | left _ hE ih => simp only [follow, ih, Option.bind_some, hE, Bool.false_eq_true, ite_false]
  | right _ hE ih => simp only [follow, ih, Option.bind_some, hE, ite_true]

/-- **A forgery against the log `L`**: a signed proof whose trace's queries are within
`queryCap` and whose signature on the trace's digest is valid under `vk`, while its trace is not
contained in `L`. -/
structure Forgery (vk : Digest) (L : Log) where
  /-- The signed proof. -/
  p : Signed
  /-- Its trace's queries are within `queryCap` (so `traceBytes_inj` applies to it). -/
  cap : ∀ e ∈ p.tr, e.1.size ≤ queryCap
  /-- Its signature verifies on its trace's digest. -/
  sig : SigOk vk (traceDigest p.tr) p.σ = true
  /-- Some entry of its trace is not in the log. -/
  notIn : ¬ ∀ e ∈ p.tr, e ∈ L

/-- **An escape at `(c, p)`**: `acc` accepts the signed proof for `c`, its trace is in the log
`L`, and the extractor, on `L`, returns no witness of the relation. -/
def Escape (S : Submission) (vk : Digest) (L : Log) (c : Digest) (p : Signed) : Prop :=
  S.acc vk c p = true ∧ (∀ e ∈ p.tr, e ∈ L) ∧ ¬ ∃ w, S.E c p.π L = some w ∧ Rel (S.acc vk) c w

/-- **What the walk returns** for the leaf values `hs` of size `n`, the root `(c₀, p₀)` and
the depth `d`: the leaves' data, a collision, a forgery in the extraction tree of `S` on `L` from
the root, or an escape in it within depth `d`. -/
inductive Outcome (S : Submission) (vk : Digest) (L : Log) (n : ℕ) (hs : List Digest)
    (c₀ : Digest) (p₀ : Signed) (d : ℕ) where
  /-- The leaves' data: `xss[i]` has `n` blocks and the root `hs[i]`, for every leaf. -/
  | data (xss : List (List Digest))
      (h : List.Forall₂ (fun xs h => dataRoot xs = h ∧ xs.length = n) xss hs)
  /-- A Keccak-256 collision. -/
  | collision (col : Collision)
  /-- A forgery against the log, at the member `(c, f.p)` of the extraction tree. -/
  | forgery (f : Forgery vk L) (c : Digest) (bs : List Bool) (mem : InTree S L c₀ p₀ bs c f.p)
  /-- An escape at the member `(c, p)` of the extraction tree, within depth `d`. -/
  | escape (c : Digest) (p : Signed) (bs : List Bool) (mem : InTree S L c₀ p₀ bs c p)
      (depth : bs.length ≤ d) (h : Escape S vk L c p)

/-- The leaves' data an outcome returns, if it returns them. -/
def Outcome.data? {S : Submission} {vk : Digest} {L : Log} {n : ℕ} {hs : List Digest}
    {c₀ : Digest} {p₀ : Signed} {d : ℕ} :
    Outcome S vk L n hs c₀ p₀ d → Option (List (List Digest))
  | .data xss _ => some xss
  | _ => none

/-- The outcome is an escape: not the leaves' data, a collision or a forgery. -/
def Outcome.Escaped {S : Submission} {vk : Digest} {L : Log} {n : ℕ} {hs : List Digest}
    {c₀ : Digest} {p₀ : Signed} {d : ℕ} : Outcome S vk L n hs c₀ p₀ d → Prop
  | .escape .. => True
  | _ => False

/-- An escaped outcome names a member of the extraction tree within depth `d` that escapes. -/
theorem Outcome.Escaped.exists {S : Submission} {vk : Digest} {L : Log} {n : ℕ}
    {hs : List Digest} {c₀ : Digest} {p₀ : Signed} {d : ℕ} {o : Outcome S vk L n hs c₀ p₀ d}
    (h : o.Escaped) : ∃ (c : Digest) (q : Signed) (bs : List Bool), bs.length ≤ d ∧
      InTree S L c₀ p₀ bs c q ∧ Escape S vk L c q := by
  cases o with
  | escape c q bs m hd he => exact ⟨c, q, bs, hd, m, he⟩
  | _ => exact h.elim

variable {S : Submission} {vk : Digest} {ε : ℝ≥0} {qV : ℕ}

/-! ## Helpers: acceptance, the tree's halves, collisions of the tagged preimages -/

/-- **What an acceptance gives**: the trace within `qV` entries and its queries within
`queryCap`, the signature valid on the trace's digest, and the verifier accepting on the trace. -/
theorem acc_parts {S : Submission} {vk c : Digest} {p : Signed} (h : S.acc vk c p = true) :
    p.tr.length ≤ S.qV ∧ (∀ e ∈ p.tr, e.1.size ≤ queryCap) ∧
      SigOk vk (traceDigest p.tr) p.σ = true ∧ (S.V vk c p.π).runSeq p.tr = some true := by
  simp only [Submission.acc, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- One level over an even-length prefix pairs within the prefix. -/
private theorem treeLevel_append : ∀ (xs ys : List Digest), xs.length % 2 = 0 →
    treeLevel (xs ++ ys) = treeLevel xs ++ treeLevel ys
  | [], _, _ => rfl
  | [_], _, h => by simp at h
  | _ :: _ :: xs, ys, h => by
    simp only [List.cons_append, treeLevel, treeLevel_append xs ys (by simp at h; omega)]

/-- One level over `2^(r+1)` digests leaves `2^r`. -/
private theorem length_treeLevel_pow {r : ℕ} {xs : List Digest} (h : xs.length = 2 ^ (r + 1)) :
    (treeLevel xs).length = 2 ^ r := by
  rw [length_treeLevel, h, pow_succ]; omega

/-- `r` levels over two halves of `2^r` digests act on each half. -/
private theorem iterate_treeLevel_append : ∀ (r : ℕ) (xs ys : List Digest),
    xs.length = 2 ^ r → ys.length = 2 ^ r →
      treeLevel^[r] (xs ++ ys) = treeLevel^[r] xs ++ treeLevel^[r] ys
  | 0, _, _, _, _ => rfl
  | r + 1, xs, ys, hx, hy =>
    (congrArg treeLevel^[r] (treeLevel_append xs ys (by rw [hx, pow_succ]; omega))).trans
      (iterate_treeLevel_append r _ _ (length_treeLevel_pow hx) (length_treeLevel_pow hy))

/-- `r` levels over `2^r` digests leave one. -/
private theorem length_iterate_treeLevel_pow : ∀ (r : ℕ) (xs : List Digest),
    xs.length = 2 ^ r → (treeLevel^[r] xs).length = 1
  | 0, _, h => h
  | r + 1, _, h => length_iterate_treeLevel_pow r _ (length_treeLevel_pow h)

/-- A digest that some number of levels reaches alone is the root. -/
private theorem treeRoot_of_iterate {cs : List Digest} {x : Digest} (k : ℕ)
    (h : treeLevel^[k] cs = [x]) : treeRoot cs = x :=
  (treeRoot_eq cs).trans (root_of_iterate _ k (treeLevel_eq ▸ h))

/-- **The root over two halves of `2^r` digests** is the node statement of the halves' roots. -/
theorem treeRoot_append {r : ℕ} {xs ys : List Digest} (hx : xs.length = 2 ^ r)
    (hy : ys.length = 2 ^ r) : treeRoot (xs ++ ys) = nodeStmt (treeRoot xs) (treeRoot ys) := by
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (length_iterate_treeLevel_pow r xs hx)
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp (length_iterate_treeLevel_pow r ys hy)
  rw [treeRoot_of_iterate r ha, treeRoot_of_iterate r hb]
  apply treeRoot_of_iterate (r + 1)
  rw [Function.iterate_succ_apply', iterate_treeLevel_append r xs ys hx hy, ha, hb]
  rfl

/-- The first half of `2^(r+1)` digests has `2^r`. -/
private theorem length_take_pow {r : ℕ} {hs : List Digest} (hr : hs.length = 2 ^ (r + 1)) :
    (hs.take (2 ^ r)).length = 2 ^ r := by
  rw [List.length_take, hr, pow_succ]; omega

/-- The second half of `2^(r+1)` digests has `2^r`. -/
private theorem length_drop_pow {r : ℕ} {hs : List Digest} (hr : hs.length = 2 ^ (r + 1)) :
    (hs.drop (2 ^ r)).length = 2 ^ r := by
  rw [List.length_drop, hr, pow_succ]; omega

/-- The root over `2^(r+1)` leaf digests is the node statement of its two halves' roots. -/
private theorem treeRoot_map_split {r : ℕ} {hs : List Digest} (hr : hs.length = 2 ^ (r + 1))
    (f : Digest → Digest) :
    treeRoot (hs.map f) =
      nodeStmt (treeRoot ((hs.take (2 ^ r)).map f)) (treeRoot ((hs.drop (2 ^ r)).map f)) := by
  conv_lhs => rw [← List.take_append_drop (2 ^ r) hs, List.map_append]
  exact treeRoot_append ((List.length_map _).trans (length_take_pow hr))
    ((List.length_map _).trans (length_drop_pow hr))

/-- **Two leaf statements**, one digest, different roots or sizes (both at most `leafCap`): a
collision of the tagged preimages. -/
private def leafCollision {h h' : Digest} {n m : ℕ} (hn : n ≤ leafCap) (hm : m ≤ leafCap)
    (hne : ¬ (h' = h ∧ m = n)) (heq : leafStmt h n = leafStmt h' m) : Collision :=
  ⟨tagLeaf :: h.toList ++ enc64 n, tagLeaf :: h'.toList ++ enc64 m, fun hxy => hne (by
    obtain ⟨h1, h2⟩ := List.append_inj hxy (by simp)
    have hc : leafCap < 2 ^ 64 := by unfold leafCap; norm_num
    exact ⟨(Vector.toList_inj.mp (List.cons.inj h1).2).symm,
      (enc64_inj (lt_of_le_of_lt hn hc) (lt_of_le_of_lt hm hc) h2).symm⟩), heq⟩

/-- **A leaf statement equal to a node statement**: a collision (first bytes `L` and `N`). -/
private def leafNodeCollision {h c₁ c₂ : Digest} {n : ℕ} (heq : leafStmt h n = nodeStmt c₁ c₂) :
    Collision :=
  ⟨tagLeaf :: h.toList ++ enc64 n, tagNode :: c₁.toList ++ c₂.toList, by
    simp [tagLeaf, tagNode], heq⟩

/-- **Two node statements**, one digest, different children: a collision. -/
private def nodeCollision {a b c₁ c₂ : Digest} (hne : ¬ (c₁ = a ∧ c₂ = b))
    (heq : nodeStmt a b = nodeStmt c₁ c₂) : Collision :=
  ⟨tagNode :: a.toList ++ b.toList, tagNode :: c₁.toList ++ c₂.toList, fun hxy => hne (by
    obtain ⟨h1, h2⟩ := List.append_inj hxy (by simp)
    exact ⟨(Vector.toList_inj.mp (List.cons.inj h1).2).symm, (Vector.toList_inj.mp h2).symm⟩),
    heq⟩

/-! ## The data collision: one root, one length, two block lists -/

/-- A preimage of the data tree: a block's hash input (`tagItem ‖ x`, `leafItem`) or a data node's
(`tagData ‖ l ‖ r`, `dataNode`). -/
def DataPreimage (b : List UInt8) : Prop :=
  (∃ x : Digest, b = tagItem :: x.toList) ∨ ∃ l r : Digest, b = tagData :: l.toList ++ r.toList

/-- Two different block lists whose block hashes agree: a collision of two `leafItem` preimages,
at the first block where they differ. -/
def itemCollision : (xs ys : List Digest) → xs ≠ ys → xs.map leafItem = ys.map leafItem →
    Collision
  | x :: xs, y :: ys, hne, h =>
    if hxy : x = y then itemCollision xs ys (fun h' => hne (hxy ▸ h' ▸ rfl)) (List.cons.inj h).2
    else ⟨tagItem :: x.toList, tagItem :: y.toList,
      fun hb => hxy (Vector.toList_inj.mp (List.cons.inj hb).2), (List.cons.inj h).1⟩
  | [], [], hne, _ => absurd rfl hne
  | [], _ :: _, _, h => absurd h (by simp)
  | _ :: _, [], _, h => absurd h (by simp)

/-- Two different digest lists of one length with one level above them: a collision of two
`dataNode` preimages, at the first pair where they differ (an odd last digest is carried up
unchanged, so it cannot be where they differ). -/
def levelCollision : (ds es : List Digest) → ds.length = es.length → ds ≠ es →
    dataLevel ds = dataLevel es → Collision
  | a :: b :: ds, c :: d :: es, hl, hne, h =>
    if hab : a = c ∧ b = d then
      levelCollision ds es (by simpa using hl) (fun h' => hne (by rw [hab.1, hab.2, h']))
        (List.cons.inj h).2
    else ⟨tagData :: a.toList ++ b.toList, tagData :: c.toList ++ d.toList, fun hb => hab (by
      obtain ⟨h1, h2⟩ := List.append_inj hb (by simp)
      exact ⟨Vector.toList_inj.mp (List.cons.inj h1).2, Vector.toList_inj.mp h2⟩),
      (List.cons.inj h).1⟩
  | [], [], _, hne, _ => absurd rfl hne
  | [_], [_], _, hne, h => absurd h hne
  | [], _ :: _, hl, _, _ => absurd hl (by simp)
  | _ :: _, [], hl, _, _ => absurd hl (by simp)
  | [_], _ :: _ :: _, hl, _, _ => absurd hl (by simp)
  | _ :: _ :: _, [_], hl, _, _ => absurd hl (by simp)

/-- Two different digest lists of one length that `k` levels bring to one list: a collision of
two `dataNode` preimages, at the lowest level where they agree. -/
def iterateCollision : (k : ℕ) → (ds es : List Digest) → ds.length = es.length → ds ≠ es →
    dataLevel^[k] ds = dataLevel^[k] es → Collision
  | 0, _, _, _, hne, h => absurd h hne
  | k + 1, ds, es, hl, hne, h =>
    if h1 : dataLevel ds = dataLevel es then levelCollision ds es hl hne h1
    else iterateCollision k (dataLevel ds) (dataLevel es)
      (by rw [length_dataLevel, length_dataLevel, hl]) h1
      (by rwa [Function.iterate_succ_apply, Function.iterate_succ_apply] at h)

/-- One root and one length: `|xs|` levels bring the two lists of block hashes to one list. -/
theorem iterate_eq_of_dataRoot_eq {xs ys : List Digest} (hl : xs.length = ys.length)
    (h : dataRoot xs = dataRoot ys) :
    dataLevel^[xs.length] (xs.map leafItem) = dataLevel^[xs.length] (ys.map leafItem) := by
  rw [dataRoot, dataRoot, ← hl] at h
  rw [dataLevel_eq] at h ⊢
  have hlen := length_iterate_level_eq dataNode dataNode
    (show (xs.map leafItem).length = (ys.map leafItem).length by simp [hl]) xs.length
  have h1 := length_iterate_length_le_one' dataNode (xs.map leafItem)
  rw [List.length_map] at h1
  generalize (level dataNode)^[xs.length] (xs.map leafItem) = A at h hlen h1 ⊢
  generalize (level dataNode)^[xs.length] (ys.map leafItem) = B at h hlen h1 ⊢
  match A, B, hlen, h1 with
  | [], [], _, _ => rfl
  | [a], [b], _, _ => simpa using h

/-- **The data collision**: two different block lists of one length and one `dataRoot` give a
Keccak-256 collision of two data-tree preimages (`DataPreimage`, `dataCollision_preimages`):
two blocks' `leafItem` inputs when the block hashes agree, else two `dataNode` inputs at the
lowest level where the lists above agree (the carry-up of an odd last digest included). The
statement binds the length (`leafStmt`), so the two trees have one shape. -/
def dataCollision {xs ys : List Digest} (hne : xs ≠ ys) (hl : xs.length = ys.length)
    (h : dataRoot xs = dataRoot ys) : Collision :=
  if hm : xs.map leafItem = ys.map leafItem then itemCollision xs ys hne hm
  else iterateCollision xs.length (xs.map leafItem) (ys.map leafItem) (by simp [hl]) hm
    (iterate_eq_of_dataRoot_eq hl h)

theorem itemCollision_preimages (xs ys : List Digest) (hne : xs ≠ ys)
    (h : xs.map leafItem = ys.map leafItem) :
    DataPreimage (itemCollision xs ys hne h).x ∧ DataPreimage (itemCollision xs ys hne h).y := by
  fun_induction itemCollision xs ys hne h
  · assumption
  · exact ⟨.inl ⟨_, rfl⟩, .inl ⟨_, rfl⟩⟩

theorem levelCollision_preimages (ds es : List Digest) (hl : ds.length = es.length)
    (hne : ds ≠ es) (h : dataLevel ds = dataLevel es) :
    DataPreimage (levelCollision ds es hl hne h).x ∧
      DataPreimage (levelCollision ds es hl hne h).y := by
  fun_induction levelCollision ds es hl hne h
  · assumption
  · exact ⟨.inr ⟨_, _, rfl⟩, .inr ⟨_, _, rfl⟩⟩

theorem iterateCollision_preimages (k : ℕ) (ds es : List Digest) (hl : ds.length = es.length)
    (hne : ds ≠ es) (h : dataLevel^[k] ds = dataLevel^[k] es) :
    DataPreimage (iterateCollision k ds es hl hne h).x ∧
      DataPreimage (iterateCollision k ds es hl hne h).y := by
  fun_induction iterateCollision k ds es hl hne h
  · exact levelCollision_preimages _ _ _ _ _
  · assumption

/-- **The data collision is over the data tree**: both its preimages are a block's hash input or a
data node's. -/
theorem dataCollision_preimages {xs ys : List Digest} (hne : xs ≠ ys)
    (hl : xs.length = ys.length) (h : dataRoot xs = dataRoot ys) :
    DataPreimage (dataCollision hne hl h).x ∧ DataPreimage (dataCollision hne hl h).y := by
  unfold dataCollision
  split
  · exact itemCollision_preimages _ _ _ _
  · exact iterateCollision_preimages _ _ _ _ _ _

/-- Two different lists of one length differ at a pair of their zip. -/
private theorem exists_mem_zip_ne {α : Type} {l₁ l₂ : List α} (hl : l₁.length = l₂.length)
    (hne : l₁ ≠ l₂) : ∃ q ∈ l₁.zip l₂, q.1 ≠ q.2 := by
  by_contra! hc
  exact hne (List.forall₂_eq_eq_eq ▸ List.forall₂_iff_zip.mpr ⟨hl, fun h => hc _ h⟩)

/-- Returned data with the roots of the runner's data `xss` (`n` blocks each) pair each leaf's
two block lists with one length and one root. -/
theorem zip_pairs_of_forall₂ {n : ℕ} {xss yss : List (List Digest)}
    (h : List.Forall₂ (fun ys h => dataRoot ys = h ∧ ys.length = n) yss (xss.map dataRoot))
    (hlen : ∀ xs ∈ xss, xs.length = n) :
    ∀ q ∈ yss.zip xss, q.1.length = q.2.length ∧ dataRoot q.1 = dataRoot q.2 := fun _ hq =>
  have ⟨hr, hn⟩ := (List.forall₂_iff_zip.mp (List.forall₂_map_right_iff.mp h)).2 hq
  ⟨hn.trans (hlen _ (List.of_mem_zip hq).2).symm, hr⟩

/-- **Returned data against the runner's**: data `yss` of `n` blocks per leaf with the roots of
the runner's data `xss` (`n` blocks each) are the runner's data, or some leaf's two block lists
differ with one length and one root, and `dataCollision` of them is a Keccak-256 collision of two
data-tree preimages. -/
theorem data_or_collision {n : ℕ} {xss yss : List (List Digest)}
    (h : List.Forall₂ (fun ys h => dataRoot ys = h ∧ ys.length = n) yss (xss.map dataRoot))
    (hlen : ∀ xs ∈ xss, xs.length = n) :
    yss = xss ∨ ∃ (ys xs : List Digest) (hne : ys ≠ xs) (hl : ys.length = xs.length)
      (hr : dataRoot ys = dataRoot xs), (ys, xs) ∈ yss.zip xss ∧
        DataPreimage (dataCollision hne hl hr).x ∧ DataPreimage (dataCollision hne hl hr).y := by
  refine or_iff_not_imp_left.mpr fun he => ?_
  obtain ⟨⟨ys, xs⟩, hm, hne⟩ := exists_mem_zip_ne (by simpa using h.length_eq) he
  obtain ⟨hl, hr⟩ := zip_pairs_of_forall₂ h hlen _ hm
  exact ⟨ys, xs, hne, hl, hr, hm, dataCollision_preimages hne hl hr⟩

/-- Membership of the relation is decidable: digests, leaf sizes and acceptance are. -/
instance decRel (acc : Digest → Signed → Bool) (c : Digest) : (w : Wit) → Decidable (Rel acc c w)
  | .leaf xs =>
    inferInstanceAs (Decidable (xs.length ≤ leafCap ∧ c = leafStmt (dataRoot xs) xs.length))
  | .node c₁ c₂ p₁ p₂ =>
    inferInstanceAs (Decidable (c = nodeStmt c₁ c₂ ∧ acc c₁ p₁ = true ∧ acc c₂ p₂ = true))

/-- Whether an extractor output is a witness of the relation is decidable. -/
instance decOpens (acc : Digest → Signed → Bool) (c : Digest) :
    (o : Option Wit) → Decidable (∃ w, o = some w ∧ Rel acc c w)
  | some w => decidable_of_iff (Rel acc c w)
      ⟨fun h => ⟨w, rfl, h⟩, fun ⟨_, hw, h⟩ => (Option.some.inj hw) ▸ h⟩
  | none => isFalse fun ⟨_, hw, _⟩ => nomatch hw

/-! ## The extraction and the walk -/

/-- **One extraction** at an accepted signed proof: a witness of the relation that the extractor
returns on `L`, when the trace is in the log; the signed proof as a forgery when it is not; an
escape when it is and the extractor returns no witness. -/
def extract (L : Log) (c : Digest) (p : Signed) (hacc : S.acc vk c p = true) :
    {w // Rel (S.acc vk) c w ∧ S.E c p.π L = some w} ⊕
      ({f : Forgery vk L // f.p = p} ⊕ PLift (Escape S vk L c p)) :=
  if hin : ∀ e ∈ p.tr, e ∈ L then
    if hex : ∃ w, S.E c p.π L = some w ∧ Rel (S.acc vk) c w then
      have hs : (S.E c p.π L).isSome := hex.elim fun _ ⟨hw, _⟩ => by simp [hw]
      .inl ⟨(S.E c p.π L).get hs, hex.elim fun _ ⟨hw, hR⟩ => by simpa [hw] using hR, by simp⟩
    else .inr (.inr ⟨hacc, hin, hex⟩)
  else .inr (.inl ⟨⟨p, (acc_parts hacc).2.1, (acc_parts hacc).2.2.1, hin⟩, rfl⟩)

/-- **The walk from a member `(treeRoot …, p)` at the path `bs` of the extraction tree of
`(c₀, p₀)`**, over the subtree of `2^r` leaves with leaf values `hs` of size `n`, within depth
`d`. -/
def walkFrom (L : Log) (n : ℕ) (hn : n ≤ leafCap) (c₀ : Digest) (p₀ : Signed) (d : ℕ) :
    (r : ℕ) → (hs : List Digest) → hs.length = 2 ^ r → (p : Signed) → (bs : List Bool) →
      bs.length + r ≤ d → S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true →
      InTree S L c₀ p₀ bs (treeRoot (hs.map fun h => leafStmt h n)) p →
      Outcome S vk L n hs c₀ p₀ d
  | 0, [h], _, p, bs, hd, hacc, hmem =>
    match extract L _ p hacc with
    | .inr (.inl ⟨f, hf⟩) => .forgery f _ bs (hf ▸ hmem)
    | .inr (.inr ⟨he⟩) => .escape _ p bs hmem (by omega) he
    | .inl ⟨.leaf xs, hw, _⟩ =>
      if he : dataRoot xs = h ∧ xs.length = n then .data [xs] (.cons he .nil)
      else .collision (leafCollision (h := h) (n := n) hn hw.1 he hw.2)
    | .inl ⟨.node _ _ _ _, hw, _⟩ => .collision (leafNodeCollision (h := h) (n := n) hw.1)
  | 0, [], hr, _, _, _, _, _ => absurd hr (by simp)
  | 0, _ :: _ :: _, hr, _, _, _, _, _ => absurd hr (by simp)
  | r + 1, hs, hr, p, bs, hd, hacc, hmem =>
    have hroot := treeRoot_map_split hr fun h => leafStmt h n
    match extract L _ p hacc with
    | .inr (.inl ⟨f, hf⟩) => .forgery f _ bs (hf ▸ hmem)
    | .inr (.inr ⟨he⟩) => .escape _ p bs hmem (by omega) he
    | .inl ⟨.leaf _, hw, _⟩ => .collision (leafNodeCollision (hw.2.symm.trans hroot))
    | .inl ⟨.node c₁ c₂ p₁ p₂, hw, hE⟩ =>
      if he : c₁ = treeRoot ((hs.take (2 ^ r)).map fun h => leafStmt h n) ∧
          c₂ = treeRoot ((hs.drop (2 ^ r)).map fun h => leafStmt h n) then
        match walkFrom L n hn c₀ p₀ d r (hs.take (2 ^ r)) (length_take_pow hr) p₁ (false :: bs)
            (by simp only [List.length_cons]; omega) (he.1 ▸ hw.2.1)
            (he.1 ▸ InTree.left hmem hE),
          walkFrom L n hn c₀ p₀ d r (hs.drop (2 ^ r)) (length_drop_pow hr) p₂ (true :: bs)
            (by simp only [List.length_cons]; omega) (he.2 ▸ hw.2.2)
            (he.2 ▸ InTree.right hmem hE) with
        | .data xss₁ h₁, .data xss₂ h₂ =>
          .data (xss₁ ++ xss₂) (List.take_append_drop (2 ^ r) hs ▸ List.rel_append h₁ h₂)
        | .collision col, _ => .collision col
        | .forgery f c bs' m, _ => .forgery f c bs' m
        | .escape c q bs' m hd' h', _ => .escape c q bs' m hd' h'
        | .data _ _, .collision col => .collision col
        | .data _ _, .forgery f c bs' m => .forgery f c bs' m
        | .data _ _, .escape c q bs' m hd' h' => .escape c q bs' m hd' h'
      else .collision (nodeCollision he (hroot.symm.trans hw.1))

/-- **The walk over a balanced tree**: from the log `L` and an accepted root signed
proof, the root's leaf data, an explicit collision, an explicit capped forgery in the extraction
tree of the root signed proof, or an escape in it within depth `r`, computed from it through `S.E`
on `L`. Its type `Outcome` is not the statement (a collision inhabits it); the content is this
compiled definition and the theorems about what it returns (`compose_prob`, `walk_not_escaped`,
`walkFrom_leaf`). -/
def walk (L : Log) (n : ℕ) (hn : n ≤ leafCap) (r : ℕ) (hs : List Digest)
    (hr : hs.length = 2 ^ r) (p : Signed)
    (hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true) :
    Outcome S vk L n hs (treeRoot (hs.map fun h => leafStmt h n)) p r :=
  walkFrom L n hn _ p r r hs hr p [] (by simp) hacc .root

/-! ## An escape is a knowledge-soundness failure -/

/-- **An escape is a win of `KS`'s game** at the member's statement and proof on a functional
log: its trace is in the log, so the verifier accepts on the log (`runLog_of_runSeq`). -/
theorem Escape.wins {L : Log} (hL : L.Functional) {c : Digest} {p : Signed}
    (h : Escape S vk L c p) : Wins (Rel (S.acc vk)) (S.V vk) S.E (c, p.π) L :=
  ⟨OProg.runLog_of_runSeq hL _ _ (acc_parts h.1).2.2.2 h.2.1, h.2.2⟩

/-- **No escape below the potential**: on a functional log within `logCap` whose potential is
below `1`, a knowledge state's `final` law extracts every accepted member. -/
theorem Escape.not_of_kstate (k : KState (Rel (S.acc vk)) (S.V vk) S.E ε) {L : Log}
    (hL : L.Functional) (hlen : L.length ≤ logCap) (hμ : k.μ L < 1) {c : Digest} {p : Signed} :
    ¬ Escape S vk L c p :=
  fun h => h.2.2 (k.final L c p.π hlen hμ (Escape.wins hL h).1)

/-- **The meter's composition** (lossless): from a knowledge state and one functional log within
`logCap` of potential below `1`, the walk does not escape: it returns the leaves' data, a
collision, or a capped forgery in the extraction tree of the root signed proof. -/
theorem walk_not_escaped (k : KState (Rel (S.acc vk)) (S.V vk) S.E ε) {L : Log}
    (hL : L.Functional) (hlen : L.length ≤ logCap) (hμ : k.μ L < 1) (n : ℕ) (hn : n ≤ leafCap)
    (r : ℕ) (hs : List Digest) (hr : hs.length = 2 ^ r) (p : Signed)
    (hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true) :
    ¬ (walk L n hn r hs hr p hacc).Escaped := fun h =>
  have ⟨_, _, _, _, _, he⟩ := h.exists
  Escape.not_of_kstate k hL hlen hμ he

/-! ## The probability: a union bound over the extraction tree -/

/-- The paths of length at most `d`: the members' positions in a binary tree of depth `d`. -/
def paths : ℕ → Finset (List Bool)
  | 0 => {[]}
  | d + 1 => insert [] ((paths d).image (false :: ·) ∪ (paths d).image (true :: ·))

theorem mem_paths : ∀ {d : ℕ} {bs : List Bool}, bs ∈ paths d ↔ bs.length ≤ d
  | 0, bs => by simp [paths, List.length_eq_zero_iff]
  | d + 1, [] => by simp [paths]
  | d + 1, b :: bs => by cases b <;> simp [paths, mem_paths]

/-- **There are `2^(d+1) - 1` paths of length at most `d`.** -/
theorem card_paths : ∀ d, (paths d).card + 1 = 2 ^ (d + 1)
  | 0 => by simp [paths]
  | d + 1 => by
    have h1 : [] ∉ (paths d).image (false :: ·) ∪ (paths d).image (true :: ·) := by simp
    have h2 : Disjoint ((paths d).image (false :: ·)) ((paths d).image (true :: ·)) := by
      rw [Finset.disjoint_left]; simp
    rw [paths, Finset.card_insert_of_notMem h1, Finset.card_union_of_disjoint h2,
      Finset.card_image_of_injective _ (List.cons_injective),
      Finset.card_image_of_injective _ (List.cons_injective), pow_succ]
    have := card_paths d
    omega

/-- The statement and proof of the member at the path `bs` of the extraction tree of `(c₀, p₀)`
on `L`, or the root's if there is none: what the adversary for `bs` outputs. -/
def memberAt (S : Submission) (c₀ : Digest) (bs : List Bool) (p₀ : Signed) (L : Log) :
    Digest × Proof :=
  match follow S L (c₀, p₀) bs with
  | some x => (x.1, x.2.π)
  | none => (c₀, p₀.π)

/-- A fresh answer keeps a log functional. -/
theorem functional_append {L : Log} {q : ByteArray} {a : Digest} (hL : L.Functional)
    (hf : L.find? (fun e => e.1 = q) = none) : (L ++ [(q, a)]).Functional := by
  have hq : ∀ e ∈ L, e.1 ≠ q := fun e he h => List.find?_eq_none.mp hf e he (decide_eq_true h)
  intro e he e' he' h
  simp only [List.mem_append, List.mem_singleton] at he he'
  rcases he with he | rfl <;> rcases he' with he' | rfl
  · exact hL e he e' he' h
  · exact absurd h (hq e he)
  · exact absurd h.symm (hq e' he')
  · rfl

/-- **The union bound over the extraction tree**: for an adversary `A` asking at most `Q`
queries and outputting the root signed proof, the probability that a member at a path in `P` of
the extraction tree of `(c₀, A's output)` on `A`'s final log escapes is at most
`|P| · (Q + qV) · ε`. -/
theorem escape_prob_le (hks : KS (Rel (S.acc vk)) (S.V vk) S.E ε qV) (c₀ : Digest)
    (A : OProg Signed) {Q : ℕ} (hA : ∀ H, (A.queries H).length ≤ Q) (hQ : Q + qV ≤ logCap)
    (P : Finset (List Bool)) :
    prob (fun p L => ∃ bs ∈ P, ∃ c q, InTree S L c₀ p bs c q ∧ Escape S vk L c q) A [] ≤
      P.card * ((Q + qV) * ε) := by
  refine (prob_mono_of_inv Log.Functional (fun _ _ _ => functional_append)
    (B' := fun p L => ∃ bs ∈ P, Wins (Rel (S.acc vk)) (S.V vk) S.E (memberAt S c₀ bs p L) L)
    (fun p L hL ⟨bs, hbs, c, q, hmem, he⟩ => ⟨bs, hbs, ?_⟩) A
    (fun _ h => absurd h List.not_mem_nil)).trans
    (hks.union A hA hQ P fun bs p L => memberAt S c₀ bs p L)
  simp only [memberAt, hmem.follow_eq]
  exact he.wins hL

/-- **The composition theorem with probabilities**: for an adversary `A` asking
at most `Q` queries and outputting the root signed proof, with `Q + qV ≤ logCap`, the probability
over one lazily sampled random oracle that `acc` accepts the root and the walk on `A`'s final log
ends in an escape, returning none of the leaves' data, a collision, or a forgery in the extraction
tree, is at most `(2^(r+1) - 1) · (Q + qV) · ε`. -/
theorem compose_prob (hks : KS (Rel (S.acc vk)) (S.V vk) S.E ε qV) (n : ℕ) (hn : n ≤ leafCap)
    (r : ℕ) (hs : List Digest) (hr : hs.length = 2 ^ r) (A : OProg Signed) {Q : ℕ}
    (hA : ∀ H, (A.queries H).length ≤ Q) (hQ : Q + qV ≤ logCap) :
    prob (fun p L => ∃ hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true,
      (walk L n hn r hs hr p hacc).Escaped) A [] ≤ (2 ^ (r + 1) - 1 : ℕ) * ((Q + qV) * ε) := by
  rw [show 2 ^ (r + 1) - 1 = (paths r).card by have := card_paths r; omega]
  refine (prob_mono (fun p L ⟨_, he⟩ => ?_) A []).trans
    (escape_prob_le hks (treeRoot (hs.map fun h => leafStmt h n)) A hA hQ (paths r))
  obtain ⟨c, q, bs, hd, hmem, h⟩ := he.exists
  exact ⟨bs, mem_paths.mpr hd, c, q, hmem, h⟩

/-! ## The forgery outcome against the service's signed traces: EUF-CMA or a collision -/

/-- A query within `queryCap` is shorter than `2^64` bytes. -/
private theorem lt64 {tr : Trace} (h : ∀ e ∈ tr, e.1.size ≤ queryCap) :
    ∀ e ∈ tr, e.1.size < 2 ^ 64 :=
  fun e he => (h e he).trans_lt (by unfold queryCap; norm_num)

/-- **The reduction of a forgery to EUF-CMA or a collision**, computed. Given signed traces `T`
the log `L` accounts for, a forgery against `L` is an EUF-CMA forgery against the signing record
of `T` (its signature on its trace's digest, which no trace of `T` has), or, for the first trace
of `T` with its trace's digest, a collision of the two traces' encodings. The forgery is
identified by its trace, the message, never by its signature value. -/
def Forgery.reduce {L : Log} (T : List (Trace × Sig)) (hT : Honest T L) (f : Forgery vk L) :
    PLift (EufForgery (SigOk vk) (issued T) (traceDigest f.p.tr) f.p.σ) ⊕
      {col : Collision // ∃ x ∈ T, col.x = tagTrace :: traceBytes x.1 ∧
        col.y = tagTrace :: traceBytes f.p.tr} :=
  match h : T.find? (fun x => decide (traceDigest x.1 = traceDigest f.p.tr)) with
  | some x =>
    have hx := List.mem_of_find?_eq_some h
    have hd := List.find?_some h
    .inr ⟨⟨tagTrace :: traceBytes x.1, tagTrace :: traceBytes f.p.tr, fun hb => f.notIn
        (traceBytes_inj (lt64 (hT.cap x hx)) (lt64 f.cap) (List.cons.inj hb).2 ▸ hT.inLog x hx),
      of_decide_eq_true hd⟩, x, hx, rfl, rfl⟩
  | none => .inl ⟨f.sig, fun hm => by
      obtain ⟨x, hx, hd⟩ := mem_fst_issued.mp hm
      exact List.find?_eq_none.mp h x hx (decide_eq_true hd)⟩

/-- **A forgery against the log is an EUF-CMA forgery or a collision**: given signed traces `T`
the log `L` accounts for, an EUF-CMA forgery against the signing record of `T` on its trace's
digest, or a collision of the encodings of a trace of `T` and its trace. -/
theorem Forgery.euf_or_collision {L : Log} {T : List (Trace × Sig)} (hT : Honest T L)
    (f : Forgery vk L) :
    EufForgery (SigOk vk) (issued T) (traceDigest f.p.tr) f.p.σ ∨
      ∃ x ∈ T, ∃ col : Collision, col.x = tagTrace :: traceBytes x.1 ∧
        col.y = tagTrace :: traceBytes f.p.tr :=
  match f.reduce T hT with
  | .inl ⟨h⟩ => .inl h
  | .inr ⟨col, x, hx, h⟩ => .inr ⟨x, hx, col, h⟩

/-- **What the walk returns against signed traces `T`**: the leaves' data, a collision, an
EUF-CMA forgery against the signing record of `T` in the extraction tree, or an escape in it
within depth `d`. -/
inductive SignedOutcome (S : Submission) (vk : Digest) (L : Log) (T : List (Trace × Sig)) (n : ℕ)
    (hs : List Digest) (c₀ : Digest) (p₀ : Signed) (d : ℕ) where
  /-- The leaves' data: `xss[i]` has `n` blocks and the root `hs[i]`, for every leaf. -/
  | data (xss : List (List Digest))
      (h : List.Forall₂ (fun xs h => dataRoot xs = h ∧ xs.length = n) xss hs)
  /-- A Keccak-256 collision. -/
  | collision (col : Collision)
  /-- An EUF-CMA forgery against the signing record of `T`, at the member `(c, q)` of the
  extraction tree: `q`'s signature on its trace's digest, a message no trace of `T` has. -/
  | euf (c : Digest) (q : Signed) (bs : List Bool) (mem : InTree S L c₀ p₀ bs c q)
      (h : EufForgery (SigOk vk) (issued T) (traceDigest q.tr) q.σ)
  /-- An escape at the member `(c, p)` of the extraction tree, within depth `d`. -/
  | escape (c : Digest) (p : Signed) (bs : List Bool) (mem : InTree S L c₀ p₀ bs c p)
      (depth : bs.length ≤ d) (h : Escape S vk L c p)

namespace SignedOutcome
variable {L : Log} {T : List (Trace × Sig)} {n : ℕ} {hs : List Digest} {c₀ : Digest} {p₀ : Signed}
  {d : ℕ}

/-- The leaves' data the outcome returns, if it returns them. -/
def data? : SignedOutcome S vk L T n hs c₀ p₀ d → Option (List (List Digest))
  | .data xss _ => some xss
  | _ => none

/-- The outcome is a collision. -/
def IsCollision : SignedOutcome S vk L T n hs c₀ p₀ d → Prop
  | .collision _ => True
  | _ => False

/-- The outcome is an EUF-CMA forgery against the signing record of `T`. -/
def IsEuf : SignedOutcome S vk L T n hs c₀ p₀ d → Prop
  | .euf .. => True
  | _ => False

/-- The outcome is an escape. -/
def Escaped : SignedOutcome S vk L T n hs c₀ p₀ d → Prop
  | .escape .. => True
  | _ => False

/-- An outcome with no leaf data is a collision, an EUF-CMA forgery or an escape. -/
theorem cases_of_data?_none {o : SignedOutcome S vk L T n hs c₀ p₀ d} (h : o.data? = none) :
    o.IsCollision ∨ o.IsEuf ∨ o.Escaped := by
  cases o with
  | data => exact absurd h (by simp [data?])
  | collision => exact .inl trivial
  | euf => exact .inr (.inl trivial)
  | escape => exact .inr (.inr trivial)

/-- **Returned data are the leaves' data**: if the outcome returns the data `xss`, `xss[i]` has
`n` blocks and the root `hs[i]`, for every leaf. -/
theorem forall₂_of_data? {o : SignedOutcome S vk L T n hs c₀ p₀ d} {xss : List (List Digest)}
    (h : o.data? = some xss) :
    List.Forall₂ (fun xs h => dataRoot xs = h ∧ xs.length = n) xss hs := by
  cases o <;> cases h
  assumption

/-- **The extracted data are the runner's, or a collision is exhibited** (against signed
traces). -/
theorem data_or_collision {xss : List (List Digest)} {o : SignedOutcome S vk L T n
    (xss.map dataRoot) c₀ p₀ d} {yss : List (List Digest)} (h : o.data? = some yss)
    (hlen : ∀ xs ∈ xss, xs.length = n) :
    yss = xss ∨ ∃ (ys xs : List Digest) (hne : ys ≠ xs) (hl : ys.length = xs.length)
      (hr : dataRoot ys = dataRoot xs), (ys, xs) ∈ yss.zip xss ∧
        DataPreimage (dataCollision hne hl hr).x ∧ DataPreimage (dataCollision hne hl hr).y :=
  Compose.data_or_collision (forall₂_of_data? h) hlen

end SignedOutcome

/-- **The walk's outcome against signed traces `T`** the log accounts for: a forgery is reduced
by `Forgery.reduce` to an EUF-CMA forgery or a collision; the other outcomes are kept. -/
def Outcome.reduce {L : Log} {T : List (Trace × Sig)} (hT : Honest T L) {n : ℕ}
    {hs : List Digest} {c₀ : Digest} {p₀ : Signed} {d : ℕ} :
    Outcome S vk L n hs c₀ p₀ d → SignedOutcome S vk L T n hs c₀ p₀ d
  | .data xss h => .data xss h
  | .collision col => .collision col
  | .forgery f c bs m =>
    match f.reduce T hT with
    | .inl ⟨h⟩ => .euf c f.p bs m h
    | .inr col => .collision col.1
  | .escape c p bs m hd h => .escape c p bs m hd h

/-- **A forgery outcome that is an EUF-CMA forgery is reduced to one**: if no signed trace of `T`
has the forged trace's digest, the reduced outcome is the EUF-CMA outcome. -/
theorem Outcome.isEuf_reduce_forgery {L : Log} {T : List (Trace × Sig)} (hT : Honest T L) {n : ℕ}
    {hs : List Digest} {c₀ : Digest} {p₀ : Signed} {d : ℕ} (f : Forgery vk L) (c : Digest)
    (bs : List Bool) (m : InTree S L c₀ p₀ bs c f.p)
    (h : EufForgery (SigOk vk) (issued T) (traceDigest f.p.tr) f.p.σ) :
    ((Outcome.forgery f c bs m : Outcome S vk L n hs c₀ p₀ d).reduce hT).IsEuf := by
  simp only [Outcome.reduce]
  split
  · trivial
  · rename_i col _
    obtain ⟨⟨x, y, _, heq⟩, t, ht, hx, hy⟩ := col
    simp only at hx hy
    subst hx hy
    exact h.2 (mem_fst_issued.mpr ⟨t, ht, heq⟩)

/-- Reducing a forgery keeps escapes and only them. -/
theorem Outcome.escaped_reduce {L : Log} {T : List (Trace × Sig)} (hT : Honest T L) {n : ℕ}
    {hs : List Digest} {c₀ : Digest} {p₀ : Signed} {d : ℕ} (o : Outcome S vk L n hs c₀ p₀ d) :
    (o.reduce hT).Escaped ↔ o.Escaped := by
  cases o with
  | forgery f c bs m =>
    simp only [Outcome.reduce, Outcome.Escaped]
    split <;> simp [SignedOutcome.Escaped]
  | _ => simp [Outcome.reduce, Outcome.Escaped, SignedOutcome.Escaped]

/-- Reducing a forgery keeps the leaves' data. -/
theorem Outcome.data?_reduce {L : Log} {T : List (Trace × Sig)} (hT : Honest T L) {n : ℕ}
    {hs : List Digest} {c₀ : Digest} {p₀ : Signed} {d : ℕ} (o : Outcome S vk L n hs c₀ p₀ d) :
    (o.reduce hT).data? = o.data? := by
  cases o with
  | forgery f c bs m =>
    simp only [Outcome.reduce, Outcome.data?]
    split <;> rfl
  | _ => rfl

/-- **The walk against the service's signed traces**: from the log `L`, signed traces `T` that
`L` accounts for, and an accepted root signed proof, the root's leaf data, an explicit
collision, an explicit EUF-CMA forgery against the signing record of `T` in the extraction tree
of the root signed proof, or an escape in it within depth `r`. Its type `SignedOutcome` is not the
statement (a collision inhabits it); the content is this compiled definition and the theorems
about what it returns (`compose_prob_signed`, `walkSigned_not_escaped`). No signature-only
forgery is needed. -/
def walkSigned (L : Log) (T : List (Trace × Sig)) (hT : Honest T L) (n : ℕ) (hn : n ≤ leafCap)
    (r : ℕ) (hs : List Digest) (hr : hs.length = 2 ^ r) (p : Signed)
    (hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true) :
    SignedOutcome S vk L T n hs (treeRoot (hs.map fun h => leafStmt h n)) p r :=
  (walk L n hn r hs hr p hacc).reduce hT

/-- **No escape below the potential** for the walk against signed traces (lossless): from a
knowledge state and one functional log within `logCap` of potential below `1`, the walk returns
the leaves' data, a collision or an EUF-CMA forgery against the signing record. -/
theorem walkSigned_not_escaped (k : KState (Rel (S.acc vk)) (S.V vk) S.E ε) {L : Log}
    (hL : L.Functional) (hlen : L.length ≤ logCap) (hμ : k.μ L < 1) (T : List (Trace × Sig))
    (hT : Honest T L) (n : ℕ) (hn : n ≤ leafCap) (r : ℕ) (hs : List Digest)
    (hr : hs.length = 2 ^ r) (p : Signed)
    (hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true) :
    ¬ (walkSigned L T hT n hn r hs hr p hacc).Escaped := fun h =>
  walk_not_escaped k hL hlen hμ n hn r hs hr p hacc ((Outcome.escaped_reduce hT _).mp h)

/-- **The composition theorem with probabilities, against the service's signed traces**: for an
adversary `A` asking at most `Q` queries and outputting the root signed proof, with
`Q + qV ≤ logCap`, and signed traces `T p L` of each run (output `p`, final log `L`) that the
log accounts for, the probability that `acc` accepts the root and the walk against `T p L`
returns no leaf data is at most `(2^(r+1) - 1) · (Q + qV) · ε` plus the probabilities that it
returns a collision and that it returns an EUF-CMA forgery against the signing record of `T p L`.
(`hT` costs nothing here: `accounted` restricts any signed traces to those the log accounts for,
and changes nothing on a run where they all are, `accounted_of_honest`. It is not free for the
chain-inversion term of `compose_prob_wots`: there `T` must be the service's complete transcript,
since an issued signature dropped from `T` can be replayed and is then reported as an
inversion.) -/
theorem compose_prob_signed (hks : KS (Rel (S.acc vk)) (S.V vk) S.E ε qV) (n : ℕ)
    (hn : n ≤ leafCap) (r : ℕ) (hs : List Digest) (hr : hs.length = 2 ^ r) (A : OProg Signed)
    {Q : ℕ} (hA : ∀ H, (A.queries H).length ≤ Q) (hQ : Q + qV ≤ logCap)
    (T : Signed → Log → List (Trace × Sig)) (hT : ∀ p L, Honest (T p L) L) :
    prob (fun p L => ∃ hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true,
      (walkSigned L (T p L) (hT p L) n hn r hs hr p hacc).data? = none) A [] ≤
      (2 ^ (r + 1) - 1 : ℕ) * ((Q + qV) * ε) +
      prob (fun p L => ∃ hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true,
        (walkSigned L (T p L) (hT p L) n hn r hs hr p hacc).IsCollision) A [] +
      prob (fun p L => ∃ hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true,
        (walkSigned L (T p L) (hT p L) n hn r hs hr p hacc).IsEuf) A [] := by
  refine (prob_mono (fun p L ⟨hacc, hno⟩ => ?_) A []).trans
    ((prob_or_le _ _ A []).trans (add_le_add ((prob_or_le _ _ A []).trans
      (add_le_add_left (compose_prob hks n hn r hs hr A hA hQ) _)) le_rfl))
  rcases SignedOutcome.cases_of_data?_none hno with h | h | h
  · exact .inl (.inr ⟨hacc, h⟩)
  · exact .inr ⟨hacc, h⟩
  · exact .inl (.inl ⟨hacc, (Outcome.escaped_reduce (hT p L) _).mp h⟩)

/-! ## Reading the walk: the extraction step on a known extractor output -/

/-- If the trace is in the log and the extractor returns a witness `w` of the relation, the
extraction step returns `w`. -/
theorem extract_of_E {L : Log} {c : Digest} {p : Signed} (hacc : S.acc vk c p = true)
    (hin : ∀ e ∈ p.tr, e ∈ L) {w : Wit} (hE : S.E c p.π L = some w)
    (hR : Rel (S.acc vk) c w) : extract L c p hacc = .inl ⟨w, hR, hE⟩ := by
  unfold extract
  rw [dite_eq_left_of_eq_true (eq_true hin), dite_eq_left_of_eq_true (eq_true ⟨w, hE, hR⟩)]
  exact congrArg Sum.inl (Subtype.ext (by simp [hE]))

/-- If the trace is in the log and the extractor returns no witness of the relation, the
extraction step is an escape. -/
theorem extract_escape {L : Log} {c : Digest} {p : Signed} (hacc : S.acc vk c p = true)
    (hin : ∀ e ∈ p.tr, e ∈ L) (hno : ¬ ∃ w, S.E c p.π L = some w ∧ Rel (S.acc vk) c w) :
    extract L c p hacc = .inr (.inr ⟨hacc, hin, hno⟩) := by
  unfold extract
  rw [dite_eq_left_of_eq_true (eq_true hin), dite_eq_right_of_eq_false (eq_false hno)]

/-- If some entry of the trace is not in the log, the extraction step returns the signed proof
as a forgery. -/
theorem extract_forgery {L : Log} {c : Digest} {p : Signed} (hacc : S.acc vk c p = true)
    (hnot : ¬ ∀ e ∈ p.tr, e ∈ L) :
    extract L c p hacc =
      .inr (.inl ⟨⟨p, (acc_parts hacc).2.1, (acc_parts hacc).2.2.1, hnot⟩, rfl⟩) := by
  unfold extract
  rw [dite_eq_right_of_eq_false (eq_false hnot)]

/-- **The walk at a leaf**: on a one-leaf subtree whose signed proof's trace is in the log and
which the extractor opens to the leaf witness `xs` of `n` blocks with `dataRoot xs` the leaf's
value, the walk's outcome `o` is the data `xs`. -/
theorem walkFrom_leaf {L : Log} {n : ℕ} (hn : n ≤ leafCap) {c₀ : Digest} {p₀ : Signed} {d : ℕ}
    {hs : List Digest} {h : Digest} (hh : hs = [h]) {hr : hs.length = 2 ^ 0} {p : Signed}
    {bs : List Bool} {hd : bs.length + 0 ≤ d}
    {hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true}
    {hmem : InTree S L c₀ p₀ bs (treeRoot (hs.map fun h => leafStmt h n)) p}
    {o : Outcome S vk L n hs c₀ p₀ d}
    (ho : walkFrom L n hn c₀ p₀ d 0 hs hr p bs hd hacc hmem = o) (hin : ∀ e ∈ p.tr, e ∈ L)
    {xs : List Digest} (hE : S.E (treeRoot (hs.map fun h => leafStmt h n)) p.π L = some (.leaf xs))
    (hend : dataRoot xs = h) (hlen : xs.length = n) : o.data? = some [xs] := by
  subst hh ho hend hlen
  unfold walkFrom
  simp only [extract_of_E hacc hin hE ⟨hn, rfl⟩, and_self, dite_true, Outcome.data?]

/-! ## The stream: `c_1 = L_1`, `c_i = nodeStmt c_(i-1) L_i` -/

/-- One more step of a non-empty stream is the node statement of the stream and the new leaf. -/
theorem streamStmt_append (n : ℕ) {hs : List Digest} (hne : hs ≠ []) (h : Digest) :
    streamStmt n (hs ++ [h]) = nodeStmt (streamStmt n hs) (leafStmt h n) := by
  obtain ⟨h₀, hs, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact List.foldl_append

/-- A stream of at least two leaves: the node statement of all but the last and the last. -/
theorem streamStmt_dropLast (n : ℕ) {hs : List Digest} (hne : hs ≠ []) (hne' : hs.dropLast ≠ []) :
    streamStmt n hs = nodeStmt (streamStmt n hs.dropLast) (leafStmt (hs.getLast hne) n) :=
  (congrArg _ (List.dropLast_append_getLast hne)).symm.trans (streamStmt_append n hne' _)

/-- **The paths of the members of a stream of `M` leaves** in its extraction tree: the left
spine `[false]^j` for `j < M` (the `M - 1` nodes and the oldest leaf) and the second children
`true :: [false]^j` for `j < M - 1` (the other leaves). -/
def combPaths (M : ℕ) : Finset (List Bool) :=
  (Finset.range M).image (List.replicate · false) ∪
    (Finset.range (M - 1)).image (true :: List.replicate · false)

theorem mem_combPaths_left {M j : ℕ} (h : j < M) : List.replicate j false ∈ combPaths M :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr h, rfl⟩)

theorem mem_combPaths_right {M j : ℕ} (h : j + 1 < M) :
    true :: List.replicate j false ∈ combPaths M :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩)

/-- **A stream of `M` leaves has `2M - 1` members**: `M - 1` nodes and `M` leaves. -/
theorem card_combPaths (M : ℕ) : (combPaths M).card = 2 * M - 1 := by
  have h : Disjoint ((Finset.range M).image (List.replicate · false))
      ((Finset.range (M - 1)).image (true :: List.replicate · false)) := by
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_range]
    rintro _ ⟨j, -, rfl⟩ ⟨i, -, h⟩
    cases j <;> cases h
  rw [combPaths, Finset.card_union_of_disjoint h,
    Finset.card_image_of_injective _ (List.replicate_left_injective false),
    Finset.card_image_of_injective _ fun _ _ h =>
      List.replicate_left_injective false (List.cons_injective h),
    Finset.card_range, Finset.card_range]
  omega

/-- The outcome's escape, if it is one, is at a path that satisfies `P`. -/
def Outcome.EscapeIn {L : Log} {n : ℕ} {hs : List Digest} {c₀ : Digest} {p₀ : Signed} {d : ℕ}
    (P : List Bool → Prop) : Outcome S vk L n hs c₀ p₀ d → Prop
  | .escape _ _ bs _ _ _ => P bs
  | _ => True

theorem Outcome.EscapeIn.mono {L : Log} {n : ℕ} {hs : List Digest} {c₀ : Digest} {p₀ : Signed}
    {d : ℕ} {P P' : List Bool → Prop} (hP : ∀ bs, P bs → P' bs)
    {o : Outcome S vk L n hs c₀ p₀ d} (h : o.EscapeIn P) : o.EscapeIn P' := by
  cases o with
  | escape _ _ bs _ _ _ => exact hP bs h
  | _ => trivial

/-- An escaped outcome whose escape is at a path satisfying `P` names a member of the extraction
tree at such a path that escapes. -/
theorem Outcome.Escaped.exists_in {L : Log} {n : ℕ} {hs : List Digest} {c₀ : Digest}
    {p₀ : Signed} {d : ℕ} {P : List Bool → Prop} {o : Outcome S vk L n hs c₀ p₀ d}
    (h : o.Escaped) (hP : o.EscapeIn P) : ∃ bs, P bs ∧ ∃ c q,
      InTree S L c₀ p₀ bs c q ∧ Escape S vk L c q := by
  cases o with
  | escape c q bs m _ he => exact ⟨bs, hP, c, q, m, he⟩
  | _ => exact h.elim

/-- **Returned data are the leaves' data**: if the outcome returns the data `xss`, `xss[i]` has
`n` blocks and the root `hs[i]`, for every leaf. -/
theorem Outcome.forall₂_of_data? {L : Log} {n : ℕ} {hs : List Digest} {c₀ : Digest}
    {p₀ : Signed} {d : ℕ} {o : Outcome S vk L n hs c₀ p₀ d} {xss : List (List Digest)}
    (h : o.data? = some xss) :
    List.Forall₂ (fun xs h => dataRoot xs = h ∧ xs.length = n) xss hs := by
  cases o <;> cases h
  assumption

/-- **The extracted data are the runner's, or a collision is exhibited**: if the outcome over the
roots of the runner's data `xss` (`n` blocks each) returns the data `yss`, then `yss = xss`, or
two different block lists of one leaf, of one length and one root, give `dataCollision`. -/
theorem Outcome.data_or_collision {L : Log} {n : ℕ} {xss : List (List Digest)} {c₀ : Digest}
    {p₀ : Signed} {d : ℕ} {o : Outcome S vk L n (xss.map dataRoot) c₀ p₀ d}
    {yss : List (List Digest)} (h : o.data? = some yss) (hlen : ∀ xs ∈ xss, xs.length = n) :
    yss = xss ∨ ∃ (ys xs : List Digest) (hne : ys ≠ xs) (hl : ys.length = xs.length)
      (hr : dataRoot ys = dataRoot xs), (ys, xs) ∈ yss.zip xss ∧
        DataPreimage (dataCollision hne hl hr).x ∧ DataPreimage (dataCollision hne hl hr).y :=
  Compose.data_or_collision (Outcome.forall₂_of_data? h) hlen

/-- The data collision of the first pair of different block lists in `ps`, whose pairs each have
one length and one root. -/
def pairsCollision : (ps : List (List Digest × List Digest)) →
    (∀ q ∈ ps, q.1.length = q.2.length ∧ dataRoot q.1 = dataRoot q.2) →
    (∃ q ∈ ps, q.1 ≠ q.2) → Collision
  | [], _, h => absurd h (by simp)
  | (a, b) :: ps, hp, h =>
    if hab : a = b then
      pairsCollision ps (fun q hq => hp q (List.mem_cons_of_mem _ hq)) (by simpa [hab] using h)
    else dataCollision hab (hp _ (List.mem_cons_self ..)).1 (hp _ (List.mem_cons_self ..)).2

/-- **The outcome against the runner's data**: returned data other than the runner's `xss`
(`n` blocks each) become the data collision of the first leaf whose two block lists differ
(`pairsCollision`, through `dataCollision`); every other outcome is kept. -/
def Outcome.toRunner {L : Log} {n : ℕ} {xss : List (List Digest)} {c₀ : Digest} {p₀ : Signed}
    {d : ℕ} (hlen : ∀ xs ∈ xss, xs.length = n) :
    Outcome S vk L n (xss.map dataRoot) c₀ p₀ d → Outcome S vk L n (xss.map dataRoot) c₀ p₀ d
  | .data yss h =>
    if heq : yss = xss then .data yss h else
      .collision (pairsCollision (yss.zip xss) (zip_pairs_of_forall₂ h hlen)
        (exists_mem_zip_ne (by simpa using h.length_eq) heq))
  | o => o

/-- **Its data are the runner's**: the data `toRunner` returns are `xss`. -/
theorem Outcome.toRunner_data? {L : Log} {n : ℕ} {xss : List (List Digest)} {c₀ : Digest}
    {p₀ : Signed} {d : ℕ} (hlen : ∀ xs ∈ xss, xs.length = n)
    {o : Outcome S vk L n (xss.map dataRoot) c₀ p₀ d} {yss : List (List Digest)}
    (h : (o.toRunner hlen).data? = some yss) : yss = xss := by
  cases o with
  | data zss hz =>
    simp only [Outcome.toRunner] at h
    split at h
    next heq => exact (Option.some.inj h).symm.trans heq
    next => cases h
  | _ => cases h

/-- `toRunner` escapes exactly when the outcome does. -/
theorem Outcome.toRunner_escaped {L : Log} {n : ℕ} {xss : List (List Digest)} {c₀ : Digest}
    {p₀ : Signed} {d : ℕ} (hlen : ∀ xs ∈ xss, xs.length = n)
    {o : Outcome S vk L n (xss.map dataRoot) c₀ p₀ d} : (o.toRunner hlen).Escaped ↔ o.Escaped := by
  cases o with
  | data zss hz =>
    simp only [Outcome.toRunner]
    split <;> simp [Outcome.Escaped]
  | _ => simp [Outcome.toRunner]

/-- **Two outcomes over adjacent leaf ranges, joined**: the data of both, or the first outcome
that is not data. -/
def Outcome.append {L : Log} {n : ℕ} {hs₁ hs₂ hs : List Digest} {c₀ : Digest} {p₀ : Signed}
    {d : ℕ} (hsplit : hs₁ ++ hs₂ = hs) :
    Outcome S vk L n hs₁ c₀ p₀ d → Outcome S vk L n hs₂ c₀ p₀ d → Outcome S vk L n hs c₀ p₀ d
  | .data xss₁ h₁, .data xss₂ h₂ => .data (xss₁ ++ xss₂) (hsplit ▸ List.rel_append h₁ h₂)
  | .collision col, _ => .collision col
  | .forgery f c bs m, _ => .forgery f c bs m
  | .escape c q bs m hd h, _ => .escape c q bs m hd h
  | .data _ _, .collision col => .collision col
  | .data _ _, .forgery f c bs m => .forgery f c bs m
  | .data _ _, .escape c q bs m hd h => .escape c q bs m hd h

theorem Outcome.EscapeIn.append {L : Log} {n : ℕ} {hs₁ hs₂ hs : List Digest} {c₀ : Digest}
    {p₀ : Signed} {d : ℕ} {P : List Bool → Prop} {hsplit : hs₁ ++ hs₂ = hs}
    {o₁ : Outcome S vk L n hs₁ c₀ p₀ d} {o₂ : Outcome S vk L n hs₂ c₀ p₀ d}
    (h₁ : o₁.EscapeIn P) (h₂ : o₂.EscapeIn P) : (o₁.append hsplit o₂).EscapeIn P := by
  cases o₁ <;> cases o₂ <;> trivial

/-- An escape joined with any outcome is that escape. -/
theorem Outcome.Escaped.append {L : Log} {n : ℕ} {hs₁ hs₂ hs : List Digest} {c₀ : Digest}
    {p₀ : Signed} {d : ℕ} {P : List Bool → Prop} {hsplit : hs₁ ++ hs₂ = hs}
    {o₁ : Outcome S vk L n hs₁ c₀ p₀ d} (o₂ : Outcome S vk L n hs₂ c₀ p₀ d) (h : o₁.Escaped)
    (hP : o₁.EscapeIn P) : (o₁.append hsplit o₂).Escaped ∧ (o₁.append hsplit o₂).EscapeIn P := by
  cases o₁ with
  | escape => exact ⟨trivial, hP⟩
  | _ => exact h.elim

theorem Outcome.data?_append {L : Log} {n : ℕ} {hs₁ hs₂ hs : List Digest} {c₀ : Digest}
    {p₀ : Signed} {d : ℕ} {hsplit : hs₁ ++ hs₂ = hs}
    {o₁ : Outcome S vk L n hs₁ c₀ p₀ d} {o₂ : Outcome S vk L n hs₂ c₀ p₀ d}
    {xss₁ xss₂ : List (List Digest)}
    (h₁ : o₁.data? = some xss₁) (h₂ : o₂.data? = some xss₂) :
    (o₁.append hsplit o₂).data? = some (xss₁ ++ xss₂) := by
  cases o₁ <;> cases h₁
  cases o₂ <;> cases h₂
  rfl

/-- The walk at a leaf escapes, if it does, at the leaf itself. -/
theorem walkFrom_zero_escapeIn {L : Log} {n : ℕ} {hn : n ≤ leafCap} {c₀ : Digest} {p₀ : Signed}
    {d : ℕ} {h : Digest} {hr : [h].length = 2 ^ 0} {p : Signed} {bs : List Bool}
    {hd : bs.length + 0 ≤ d}
    {hacc : S.acc vk (treeRoot ([h].map fun h => leafStmt h n)) p = true}
    {hmem : InTree S L c₀ p₀ bs (treeRoot ([h].map fun h => leafStmt h n)) p} :
    (walkFrom L n hn c₀ p₀ d 0 [h] hr p bs hd hacc hmem).EscapeIn (· = bs) := by
  unfold walkFrom
  split <;> (try split) <;> trivial

/-- **The walk from the member `(streamStmt n hs, p)` at the path `[false]^j`** of the
extraction tree of `(c₀, p₀)`, over the stream's first `k` leaves `hs`, in a stream of `M`
leaves (`j + k = M`): at a node it walks the second child as a one-leaf tree (`walkFrom`) and
the first child as the stream of all but the last leaf. The escape it returns, if any, is at a
path of `combPaths M`. -/
def walkStreamFrom (L : Log) (n : ℕ) (hn : n ≤ leafCap) (c₀ : Digest) (p₀ : Signed) (M : ℕ) :
    (k : ℕ) → (hs : List Digest) → hs.length = k → (j : ℕ) → j + k = M → (p : Signed) →
      S.acc vk (streamStmt n hs) p = true →
      InTree S L c₀ p₀ (List.replicate j false) (streamStmt n hs) p →
      {o : Outcome S vk L n hs c₀ p₀ (M - 1) // o.EscapeIn (· ∈ combPaths M)}
  | 0, [], _, _, _, _, _, _ => ⟨.data [] .nil, trivial⟩
  | 0, _ :: _, hk, _, _, _, _, _ => absurd hk (by simp)
  | 1, [h], _, j, hj, p, hacc, hmem =>
    ⟨walkFrom L n hn c₀ p₀ (M - 1) 0 [h] rfl p _ (by simp only [List.length_replicate]; omega)
      hacc hmem,
      walkFrom_zero_escapeIn.mono fun _ (hb : _ = _) => hb ▸ mem_combPaths_left (by omega)⟩
  | 1, [], hk, _, _, _, _, _ => absurd hk (by simp)
  | 1, _ :: _ :: _, hk, _, _, _, _, _ => absurd hk (by simp)
  | k + 2, hs, hk, j, hj, p, hacc, hmem =>
    have hne : hs ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hst := streamStmt_dropLast n hne (List.ne_nil_of_length_pos (by simp [hk]))
    match extract L _ p hacc with
    | .inr (.inl ⟨f, hf⟩) => ⟨.forgery f _ _ (hf ▸ hmem), trivial⟩
    | .inr (.inr ⟨he⟩) =>
      ⟨.escape _ p _ hmem (by simp only [List.length_replicate]; omega) he,
        mem_combPaths_left (by omega)⟩
    | .inl ⟨.leaf _, hw, _⟩ => ⟨.collision (leafNodeCollision (hw.2.symm.trans hst)), trivial⟩
    | .inl ⟨.node c₁ c₂ p₁ p₂, hw, hE⟩ =>
      if he : c₁ = streamStmt n hs.dropLast ∧ c₂ = leafStmt (hs.getLast hne) n then
        let o₁ := walkStreamFrom L n hn c₀ p₀ M (k + 1) hs.dropLast (by simp [hk]) (j + 1)
          (by omega) p₁ (he.1 ▸ hw.2.1) (he.1 ▸ InTree.left hmem hE)
        let o₂ := walkFrom L n hn c₀ p₀ (M - 1) 0 [hs.getLast hne] rfl p₂
          (true :: List.replicate j false)
          (by simp only [List.length_cons, List.length_replicate]; omega)
          (show S.acc vk (leafStmt _ n) p₂ = true from he.2 ▸ hw.2.2)
          (show InTree S L c₀ p₀ _ (leafStmt _ n) p₂ from he.2 ▸ InTree.right hmem hE)
        ⟨o₁.1.append (List.dropLast_append_getLast hne) o₂, o₁.2.append
          (walkFrom_zero_escapeIn.mono fun _ (hb : _ = _) => hb ▸ mem_combPaths_right (by omega))⟩
      else ⟨.collision (nodeCollision he (hst.symm.trans hw.1)), trivial⟩

/-- **The walk over the stream**: from the log `L` and an accepted signed proof of the stream's
digest over the leaf values `hs`, the data of all its leaves, an explicit collision, an
explicit capped forgery in the extraction tree of the signed proof, or an escape in it within
depth `|hs| - 1`, at a path of `combPaths |hs|` (`walkStream_escapeIn`), computed from it through
`S.E` on `L`. -/
def walkStream (L : Log) (n : ℕ) (hn : n ≤ leafCap) (hs : List Digest) (p : Signed)
    (hacc : S.acc vk (streamStmt n hs) p = true) :
    Outcome S vk L n hs (streamStmt n hs) p (hs.length - 1) :=
  (walkStreamFrom L n hn _ p hs.length hs.length hs rfl 0 (Nat.zero_add _) p hacc .root).1

/-- **The stream walk's escape is at one of the stream's `2|hs| - 1` member paths.** -/
theorem walkStream_escapeIn (L : Log) (n : ℕ) (hn : n ≤ leafCap) (hs : List Digest) (p : Signed)
    (hacc : S.acc vk (streamStmt n hs) p = true) :
    (walkStream L n hn hs p hacc).EscapeIn (· ∈ combPaths hs.length) :=
  (walkStreamFrom L n hn _ p hs.length hs.length hs rfl 0 (Nat.zero_add _) p hacc .root).2

/-- **The meter's composition over the stream** (lossless): from a knowledge state and one
functional log within `logCap` of potential below `1`, the stream walk does not escape. -/
theorem walkStream_not_escaped (k : KState (Rel (S.acc vk)) (S.V vk) S.E ε) {L : Log}
    (hL : L.Functional) (hlen : L.length ≤ logCap) (hμ : k.μ L < 1) (n : ℕ) (hn : n ≤ leafCap)
    (hs : List Digest) (p : Signed) (hacc : S.acc vk (streamStmt n hs) p = true) :
    ¬ (walkStream L n hn hs p hacc).Escaped := fun h =>
  have ⟨_, _, _, _, _, he⟩ := h.exists
  Escape.not_of_kstate k hL hlen hμ he

/-- **The composition theorem over the stream, with probabilities**: for an adversary `A` asking
at most `Q` queries and outputting a signed proof of the stream's digest, with
`Q + qV ≤ logCap`, the probability that `acc` accepts it and the stream walk on `A`'s final log
ends in an escape is at most `(2|hs| - 1) · (Q + qV) · ε`: a union bound over the stream's
`|hs| - 1` nodes and `|hs|` leaves. Off that event the walk returns the data of all `|hs|`
leaves (`Outcome.forall₂_of_data?`), a collision or a forgery in the extraction tree. -/
theorem compose_prob_stream (hks : KS (Rel (S.acc vk)) (S.V vk) S.E ε qV) (n : ℕ)
    (hn : n ≤ leafCap) (hs : List Digest) (A : OProg Signed) {Q : ℕ}
    (hA : ∀ H, (A.queries H).length ≤ Q) (hQ : Q + qV ≤ logCap) :
    prob (fun p L => ∃ hacc : S.acc vk (streamStmt n hs) p = true,
      (walkStream L n hn hs p hacc).Escaped) A [] ≤ (2 * hs.length - 1 : ℕ) * ((Q + qV) * ε) := by
  rw [← card_combPaths]
  exact (prob_mono (fun p L ⟨hacc, he⟩ => he.exists_in (walkStream_escapeIn L n hn hs p hacc))
    A []).trans (escape_prob_le hks (streamStmt n hs) A hA hQ (combPaths hs.length))

/-- **The stream walk against the runner's data**: over the roots of the runner's data `xss`
(`n` blocks each), `toRunner` of the walk returns the runner's data (`Outcome.toRunner_data?`), a
Keccak-256 collision (the data collision included) or a forgery, except on an escape, whose
probability is `compose_prob_stream`'s bound. -/
theorem compose_prob_stream_runner (hks : KS (Rel (S.acc vk)) (S.V vk) S.E ε qV) (n : ℕ)
    (hn : n ≤ leafCap) (xss : List (List Digest)) (hlen : ∀ xs ∈ xss, xs.length = n)
    (A : OProg Signed) {Q : ℕ} (hA : ∀ H, (A.queries H).length ≤ Q) (hQ : Q + qV ≤ logCap) :
    prob (fun p L => ∃ hacc : S.acc vk (streamStmt n (xss.map dataRoot)) p = true,
      ((walkStream L n hn (xss.map dataRoot) p hacc).toRunner hlen).Escaped) A [] ≤
      (2 * xss.length - 1 : ℕ) * ((Q + qV) * ε) := by
  refine ((prob_mono (fun p L ⟨hacc, he⟩ => ⟨hacc, (Outcome.toRunner_escaped hlen).mp he⟩)
    A []).trans (compose_prob_stream hks n hn (xss.map dataRoot) A hA hQ)).trans_eq ?_
  rw [List.length_map]

/-- **The stream walk against the service's signed traces**: `walkStream` with its forgery
reduced by `Forgery.reduce`: the data of all the stream's leaves, a collision, an EUF-CMA
forgery against the signing record of `T` in the extraction tree, or an escape in it. -/
def walkStreamSigned (L : Log) (T : List (Trace × Sig)) (hT : Honest T L) (n : ℕ)
    (hn : n ≤ leafCap) (hs : List Digest) (p : Signed)
    (hacc : S.acc vk (streamStmt n hs) p = true) :
    SignedOutcome S vk L T n hs (streamStmt n hs) p (hs.length - 1) :=
  (walkStream L n hn hs p hacc).reduce hT

/-- **No escape below the potential** for the stream walk against signed traces (lossless). -/
theorem walkStreamSigned_not_escaped (k : KState (Rel (S.acc vk)) (S.V vk) S.E ε) {L : Log}
    (hL : L.Functional) (hlen : L.length ≤ logCap) (hμ : k.μ L < 1) (T : List (Trace × Sig))
    (hT : Honest T L) (n : ℕ) (hn : n ≤ leafCap) (hs : List Digest) (p : Signed)
    (hacc : S.acc vk (streamStmt n hs) p = true) :
    ¬ (walkStreamSigned L T hT n hn hs p hacc).Escaped := fun h =>
  walkStream_not_escaped k hL hlen hμ n hn hs p hacc ((Outcome.escaped_reduce hT _).mp h)

/-- **The composition theorem over the stream with probabilities, against the service's signed
traces**: the probability that `acc` accepts the adversary's signed proof of the stream's digest
and the stream walk against `T p L` returns no leaf data is at most
`(2|hs| - 1) · (Q + qV) · ε` plus the probabilities that it returns a collision and that it
returns an EUF-CMA forgery against the signing record of `T p L`. Off these events the walk
returns the data of all `|hs|` leaves (`SignedOutcome.forall₂_of_data?`), the runner's or a
collision (`SignedOutcome.data_or_collision`). -/
theorem compose_prob_stream_signed (hks : KS (Rel (S.acc vk)) (S.V vk) S.E ε qV) (n : ℕ)
    (hn : n ≤ leafCap) (hs : List Digest) (A : OProg Signed) {Q : ℕ}
    (hA : ∀ H, (A.queries H).length ≤ Q) (hQ : Q + qV ≤ logCap)
    (T : Signed → Log → List (Trace × Sig)) (hT : ∀ p L, Honest (T p L) L) :
    prob (fun p L => ∃ hacc : S.acc vk (streamStmt n hs) p = true,
      (walkStreamSigned L (T p L) (hT p L) n hn hs p hacc).data? = none) A [] ≤
      (2 * hs.length - 1 : ℕ) * ((Q + qV) * ε) +
      prob (fun p L => ∃ hacc : S.acc vk (streamStmt n hs) p = true,
        (walkStreamSigned L (T p L) (hT p L) n hn hs p hacc).IsCollision) A [] +
      prob (fun p L => ∃ hacc : S.acc vk (streamStmt n hs) p = true,
        (walkStreamSigned L (T p L) (hT p L) n hn hs p hacc).IsEuf) A [] := by
  refine (prob_mono (fun p L ⟨hacc, hno⟩ => ?_) A []).trans
    ((prob_or_le _ _ A []).trans (add_le_add ((prob_or_le _ _ A []).trans
      (add_le_add_left (compose_prob_stream hks n hn hs A hA hQ) _)) le_rfl))
  rcases SignedOutcome.cases_of_data?_none hno with h | h | h
  · exact .inl (.inr ⟨hacc, h⟩)
  · exact .inr ⟨hacc, h⟩
  · exact .inl (.inl ⟨hacc, (Outcome.escaped_reduce (hT p L) _).mp h⟩)

/-- **The stream walk at its oldest leaf**: on a one-leaf stream whose signed proof's trace is in
the log and which the extractor opens to `xs` of `n` blocks with `dataRoot xs = h`, the data
`xs`. -/
theorem walkStreamFrom_one {L : Log} {n : ℕ} (hn : n ≤ leafCap) {c₀ : Digest} {p₀ : Signed}
    {M : ℕ} {h : Digest} {hk : [h].length = 1} {j : ℕ} {hj : j + 1 = M} {p : Signed}
    {hacc : S.acc vk (streamStmt n [h]) p = true}
    {hmem : InTree S L c₀ p₀ (List.replicate j false) (streamStmt n [h]) p}
    (hin : ∀ e ∈ p.tr, e ∈ L) {xs : List Digest} (hE : S.E (leafStmt h n) p.π L = some (.leaf xs))
    (hend : dataRoot xs = h) (hlen : xs.length = n) :
    (walkStreamFrom L n hn c₀ p₀ M 1 [h] hk j hj p hacc hmem).1.data? = some [xs] :=
  walkFrom_leaf hn (hr := rfl) rfl rfl hin hE hend hlen

/-- **The stream walk at a node, unfolded**: if the signed proof's trace is in the log and the
extractor opens it to a node witness of the relation whose children are the statements of the
stream without its last leaf and of that leaf, the walk joins the walk over the shorter stream at
the first child and the one-leaf walk at the second. -/
theorem walkStreamFrom_node {L : Log} {n : ℕ} (hn : n ≤ leafCap) {c₀ : Digest}
    {p₀ : Signed} {M k : ℕ} {hs : List Digest} (hne : hs ≠ []) {hk : hs.length = k + 2} {j : ℕ}
    {hj : j + (k + 2) = M} {p : Signed} {hacc : S.acc vk (streamStmt n hs) p = true}
    {hmem : InTree S L c₀ p₀ (List.replicate j false) (streamStmt n hs) p}
    (hin : ∀ e ∈ p.tr, e ∈ L) {p₁ p₂ : Signed}
    (hE : S.E (streamStmt n hs) p.π L = some
      (.node (streamStmt n hs.dropLast) (leafStmt (hs.getLast hne) n) p₁ p₂))
    (hR : Rel (S.acc vk) (streamStmt n hs)
      (.node (streamStmt n hs.dropLast) (leafStmt (hs.getLast hne) n) p₁ p₂)) :
    (walkStreamFrom L n hn c₀ p₀ M (k + 2) hs hk j hj p hacc hmem).1 =
      (walkStreamFrom L n hn c₀ p₀ M (k + 1) hs.dropLast (by simp [hk]) (j + 1) (by omega) p₁
        hR.2.1 (InTree.left hmem hE)).1.append (List.dropLast_append_getLast hne)
      (walkFrom L n hn c₀ p₀ (M - 1) 0 [hs.getLast hne] rfl p₂ (true :: List.replicate j false)
        (by simp only [List.length_cons, List.length_replicate]; omega) hR.2.2
        (InTree.right hmem hE)) := by
  rw [walkStreamFrom, extract_of_E hacc hin hE hR]
  exact congrArg Subtype.val (dite_eq_left ⟨rfl, rfl⟩)

/-- **The stream walk at a node**: if the signed proof's trace is in the log, the extractor
opens it to a node witness whose children are the statements of the stream without its last
leaf and of that leaf, the walk over the shorter stream returns the data `xss`, and the last
leaf's signed proof is opened to `xs` of `n` blocks with its value, the walk returns
`xss ++ [xs]`. -/
theorem walkStreamFrom_succ_succ {L : Log} {n : ℕ} (hn : n ≤ leafCap) {c₀ : Digest}
    {p₀ : Signed} {M k : ℕ} {hs : List Digest} (hne : hs ≠ []) {hk : hs.length = k + 2} {j : ℕ}
    {hj : j + (k + 2) = M} {p : Signed} {hacc : S.acc vk (streamStmt n hs) p = true}
    {hmem : InTree S L c₀ p₀ (List.replicate j false) (streamStmt n hs) p}
    (hin : ∀ e ∈ p.tr, e ∈ L) {p₁ p₂ : Signed}
    (hE : S.E (streamStmt n hs) p.π L = some
      (.node (streamStmt n hs.dropLast) (leafStmt (hs.getLast hne) n) p₁ p₂))
    (hR : Rel (S.acc vk) (streamStmt n hs)
      (.node (streamStmt n hs.dropLast) (leafStmt (hs.getLast hne) n) p₁ p₂))
    {xss : List (List Digest)}
    (hrec : ∀ hk' hj' hacc' hmem', (walkStreamFrom (S := S) (vk := vk) L n hn c₀ p₀ M (k + 1)
      hs.dropLast hk' (j + 1) hj' p₁ hacc' hmem').1.data? = some xss)
    (hin₂ : ∀ e ∈ p₂.tr, e ∈ L) {xs : List Digest}
    (hE₂ : S.E (leafStmt (hs.getLast hne) n) p₂.π L = some (.leaf xs))
    (hend : dataRoot xs = hs.getLast hne) (hlen : xs.length = n) :
    (walkStreamFrom L n hn c₀ p₀ M (k + 2) hs hk j hj p hacc hmem).1.data? =
      some (xss ++ [xs]) := by
  rw [walkStreamFrom_node hn hne hin hE hR]
  exact Outcome.data?_append (hsplit := List.dropLast_append_getLast _) (hrec _ _ _ _)
    (walkFrom_leaf hn (hr := rfl) rfl rfl hin₂ hE₂ hend hlen)

/-- **The stream walk escapes at a node** whose signed proof's trace is in the log and which the
extractor opens to no witness of the relation: an escape at that node's path. -/
theorem walkStreamFrom_escape {L : Log} {n : ℕ} (hn : n ≤ leafCap) {c₀ : Digest} {p₀ : Signed}
    {M k : ℕ} {hs : List Digest} {hk : hs.length = k + 2} {j : ℕ} {hj : j + (k + 2) = M}
    {p : Signed} {hacc : S.acc vk (streamStmt n hs) p = true}
    {hmem : InTree S L c₀ p₀ (List.replicate j false) (streamStmt n hs) p}
    (hin : ∀ e ∈ p.tr, e ∈ L)
    (hno : ¬ ∃ w, S.E (streamStmt n hs) p.π L = some w ∧ Rel (S.acc vk) (streamStmt n hs) w) :
    (walkStreamFrom L n hn c₀ p₀ M (k + 2) hs hk j hj p hacc hmem).1.Escaped ∧
      (walkStreamFrom L n hn c₀ p₀ M (k + 2) hs hk j hj p hacc hmem).1.EscapeIn
        (· = List.replicate j false) := by
  rw [walkStreamFrom, extract_escape hacc hin hno]
  exact ⟨trivial, rfl⟩

end RecursionFast.Compose
