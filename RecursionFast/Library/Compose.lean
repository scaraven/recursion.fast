/-
  RecursionFast.Library.Compose  (UNTRUSTED, kernel-checked)

  **The composition argument across the harness tree** (V4-8, V4-A10; CGSY24 Thm 5.1's
  straight-line argument), from the contract's single-output knowledge soundness by a union
  bound over the extracted proofs. Fix a submission `S` and a public key `vk`. The harness's tree
  has `2^r` leaves whose digests are `leafStmt hᵢ n` (the runner computes them from the chain ends
  `hᵢ` it knows, with `n ≤ chainCap`), and its root digest `c₀` is `treeRoot` of them.

  **The walk** (deterministic; `walk`, whose type is the statement, RA-M1). Given one oracle log
  `L` and a root signed proof `p₀` that `S.acc vk` accepts, it returns, computed from `p₀`
  through `S.E` on `L` (`Outcome`):
  * **the leaf starts**: `sᵢ` with `chainEnd sᵢ n = hᵢ` for every leaf;
  * **a BLAKE2s collision** (`Collision`): the tagged preimages of a statement mismatch;
  * **a forgery in the extraction tree of `p₀`**: a signed proof `p` at a path `bs` of the tree
    (`InTree`: the root, or a child of a node witness `S.E` returns for a member) whose trace has
    queries of at most `queryCap` bytes and a valid signature on its digest under `vk`, while the
    trace is not contained in `L` (`Forgery`);
  * **an escape in the extraction tree**, at depth at most `r`: a member that `acc` accepts,
    whose trace is in `L`, and which `S.E` on `L` does not open to a witness of the relation
    (`Escape`).
  At each member the walk checks the signed proof's trace against `L`; if it is contained it asks
  `S.E` on `L`, checks the witness (`Rel` is decidable), and compares its digests with the tree's.
  `compose` states the same as a proposition; its first disjunct, that leaf starts exist, is free
  whenever the harness drew them, so the content is that `walk` computes them (RA-M1).

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

  **The meter's lossless composition** (`compose_of_kstate`): with a knowledge state
  (`Library/Security.lean`) and one log of potential below `1`, functional and within `logCap`,
  no member escapes (`Escape.not_of_kstate`), so the walk returns one of the first three
  outcomes, and the one event, a potential of at least `1`, has probability at most `n · ε` for a
  game of `n` queries (`PaperTheorem.prob_potential_ge_one`), for the whole tree.

  `compose_exists`, the disjunction without the forgery's membership, is **trivially true for
  every key a signer knows** (anyone holding `sk` signs a trace with a fresh answer:
  `Controls/Compose.lean`, `forgery_trivial`) and is kept only as a documented corollary.

  What stays on paper: the probability of the third outcome. A trace not contained in `L` was
  never signed by the service as such (every query a `sign` request evaluates is in `L`), so the
  signature is an EUF-CMA forgery, unless the service signed a different trace with the same
  digest, which is a collision of `traceBytes` encodings (injective on queries of at most
  `queryCap` bytes, `traceBytes_inj`; the forgery carries that cap, and the service's traces have
  it by the wire cap). Collisions and forgeries are then bounded by `Adv_coll + Adv_EUF-CMA`
  (BRIEF §2). Also on paper: lazy sampling against a random function, randomised adversaries,
  and the PRF hybrid (design §2.3).
-/
import RecursionFast.Library.Trace
import RecursionFast.Library.Tree
import RecursionFast.Library.KS
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

/-- **What the walk returns** for the leaf chain ends `hs` of length `n`, the root `(c₀, p₀)` and
the depth `d`: the leaf starts, a collision, a forgery in the extraction tree of `S` on `L` from
the root, or an escape in it within depth `d`. -/
inductive Outcome (S : Submission) (vk : Digest) (L : Log) (n : ℕ) (hs : List Digest)
    (c₀ : Digest) (p₀ : Signed) (d : ℕ) where
  /-- The leaf starts: chain `n` from `ss[i]` ends at `hs[i]`, for every leaf. -/
  | starts (ss : List Digest) (h : List.Forall₂ (fun s h => chainEnd s n = h) ss hs)
  /-- A BLAKE2s collision. -/
  | collision (col : Collision)
  /-- A forgery against the log, at the member `(c, f.p)` of the extraction tree. -/
  | forgery (f : Forgery vk L) (c : Digest) (bs : List Bool) (mem : InTree S L c₀ p₀ bs c f.p)
  /-- An escape at the member `(c, p)` of the extraction tree, within depth `d`. -/
  | escape (c : Digest) (p : Signed) (bs : List Bool) (mem : InTree S L c₀ p₀ bs c p)
      (depth : bs.length ≤ d) (h : Escape S vk L c p)

/-- The leaf starts an outcome returns, if it returns them. -/
def Outcome.starts? {S : Submission} {vk : Digest} {L : Log} {n : ℕ} {hs : List Digest}
    {c₀ : Digest} {p₀ : Signed} {d : ℕ} : Outcome S vk L n hs c₀ p₀ d → Option (List Digest)
  | .starts ss _ => some ss
  | _ => none

/-- The outcome is an escape: not the leaf starts, a collision or a forgery. -/
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

/-- Membership of an entry in a log is decidable, by the entries' decidable equality
(`ByteArray`'s own `BEq` is not known lawful, so the instance is given explicitly). -/
private instance decMemLog (e : ByteArray × Digest) (L : Log) : Decidable (e ∈ L) :=
  @List.instDecidableMemOfLawfulBEq _ instBEqOfDecidableEq _ e L

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
    (h : treeLevel^[k] cs = [x]) : treeRoot cs = x := by
  -- `k` more levels change nothing after `|cs|`, and `|cs|` more change nothing after `k`.
  rw [treeRoot, ← iterate_treeLevel_of_length_le_one (length_iterate_length_le_one cs) k,
    ← Function.iterate_add_apply, Nat.add_comm k, Function.iterate_add_apply, h,
    iterate_treeLevel_of_length_le_one (by simp), List.headD_cons]

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

/-- **Two leaf statements**, one digest, different chain ends or lengths (both at most
`chainCap`): a collision of the tagged preimages. -/
private def leafCollision {h h' : Digest} {n m : ℕ} (hn : n ≤ chainCap) (hm : m ≤ chainCap)
    (hne : ¬ (h' = h ∧ m = n)) (heq : leafStmt h n = leafStmt h' m) : Collision :=
  ⟨tagLeaf :: h.toList ++ enc64 n, tagLeaf :: h'.toList ++ enc64 m, fun hxy => hne (by
    obtain ⟨h1, h2⟩ := List.append_inj hxy (by simp)
    have hc : (2 : ℕ) ^ 20 < 2 ^ 64 := by norm_num
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


/-- Membership of the relation is decidable: digests, chain lengths and acceptance are. -/
instance decRel (acc : Digest → Signed → Bool) (c : Digest) : (w : Wit) → Decidable (Rel acc c w)
  | .leaf s n => inferInstanceAs (Decidable (n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n))
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
`(c₀, p₀)`**, over the subtree of `2^r` leaves with chain ends `hs` of length `n`, within depth
`d`. -/
def walkFrom (L : Log) (n : ℕ) (hn : n ≤ chainCap) (c₀ : Digest) (p₀ : Signed) (d : ℕ) :
    (r : ℕ) → (hs : List Digest) → hs.length = 2 ^ r → (p : Signed) → (bs : List Bool) →
      bs.length + r ≤ d → S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true →
      InTree S L c₀ p₀ bs (treeRoot (hs.map fun h => leafStmt h n)) p →
      Outcome S vk L n hs c₀ p₀ d
  | 0, [h], _, p, bs, hd, hacc, hmem =>
    match extract L _ p hacc with
    | .inr (.inl ⟨f, hf⟩) => .forgery f _ bs (hf ▸ hmem)
    | .inr (.inr ⟨he⟩) => .escape _ p bs hmem (by omega) he
    | .inl ⟨.leaf s m, hw, _⟩ =>
      if he : chainEnd s m = h ∧ m = n then
        .starts [s] (.cons (he.2 ▸ he.1) .nil)
      else .collision (leafCollision (h := h) (n := n) hn hw.1 he hw.2)
    | .inl ⟨.node _ _ _ _, hw, _⟩ => .collision (leafNodeCollision (h := h) (n := n) hw.1)
  | 0, [], hr, _, _, _, _, _ => absurd hr (by simp)
  | 0, _ :: _ :: _, hr, _, _, _, _, _ => absurd hr (by simp)
  | r + 1, hs, hr, p, bs, hd, hacc, hmem =>
    have hroot := treeRoot_map_split hr fun h => leafStmt h n
    match extract L _ p hacc with
    | .inr (.inl ⟨f, hf⟩) => .forgery f _ bs (hf ▸ hmem)
    | .inr (.inr ⟨he⟩) => .escape _ p bs hmem (by omega) he
    | .inl ⟨.leaf _ _, hw, _⟩ => .collision (leafNodeCollision (hw.2.symm.trans hroot))
    | .inl ⟨.node c₁ c₂ p₁ p₂, hw, hE⟩ =>
      if he : c₁ = treeRoot ((hs.take (2 ^ r)).map fun h => leafStmt h n) ∧
          c₂ = treeRoot ((hs.drop (2 ^ r)).map fun h => leafStmt h n) then
        match walkFrom L n hn c₀ p₀ d r (hs.take (2 ^ r)) (length_take_pow hr) p₁ (false :: bs)
            (by simp only [List.length_cons]; omega) (he.1 ▸ hw.2.1)
            (he.1 ▸ InTree.left hmem hE),
          walkFrom L n hn c₀ p₀ d r (hs.drop (2 ^ r)) (length_drop_pow hr) p₂ (true :: bs)
            (by simp only [List.length_cons]; omega) (he.2 ▸ hw.2.2)
            (he.2 ▸ InTree.right hmem hE) with
        | .starts ss₁ h₁, .starts ss₂ h₂ =>
          .starts (ss₁ ++ ss₂) (List.take_append_drop (2 ^ r) hs ▸ List.rel_append h₁ h₂)
        | .collision col, _ => .collision col
        | .forgery f c bs' m, _ => .forgery f c bs' m
        | .escape c q bs' m hd' h', _ => .escape c q bs' m hd' h'
        | .starts _ _, .collision col => .collision col
        | .starts _ _, .forgery f c bs' m => .forgery f c bs' m
        | .starts _ _, .escape c q bs' m hd' h' => .escape c q bs' m hd' h'
      else .collision (nodeCollision he (hroot.symm.trans hw.1))

/-- **The walk over the harness tree** (V4-8): from the log `L` and an accepted root signed
proof, the root's leaf starts, an explicit collision, an explicit capped forgery in the extraction
tree of the root signed proof, or an escape in it within depth `r`, computed from it through `S.E`
on `L`. Its type is the composition statement. -/
def walk (L : Log) (n : ℕ) (hn : n ≤ chainCap) (r : ℕ) (hs : List Digest)
    (hr : hs.length = 2 ^ r) (p : Signed)
    (hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true) :
    Outcome S vk L n hs (treeRoot (hs.map fun h => leafStmt h n)) p r :=
  walkFrom L n hn _ p r r hs hr p [] (by simp) hacc .root

/-- **The composition theorem** (V4-8), the proposition `walk` proves: the leaf starts exist, or
a BLAKE2s collision exists, or a capped forgery against `L` lies in the extraction tree of the
root signed proof, or a member of that tree within depth `r` escapes the extractor on `L`. -/
theorem compose (L : Log) (n : ℕ) (hn : n ≤ chainCap) (r : ℕ) (hs : List Digest)
    (hr : hs.length = 2 ^ r) (p : Signed)
    (hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true) :
    (∃ ss, List.Forall₂ (fun s h => chainEnd s n = h) ss hs) ∨ Nonempty Collision ∨
      (∃ (f : Forgery vk L) (c : Digest) (bs : List Bool),
        InTree S L (treeRoot (hs.map fun h => leafStmt h n)) p bs c f.p) ∨
      ∃ (c : Digest) (q : Signed) (bs : List Bool), bs.length ≤ r ∧
        InTree S L (treeRoot (hs.map fun h => leafStmt h n)) p bs c q ∧ Escape S vk L c q := by
  cases walk L n hn r hs hr p hacc with
  | starts ss h => exact Or.inl ⟨ss, h⟩
  | collision col => exact Or.inr (Or.inl ⟨col⟩)
  | forgery f c bs m => exact Or.inr (Or.inr (Or.inl ⟨f, c, bs, m⟩))
  | escape c q bs m hd h => exact Or.inr (Or.inr (Or.inr ⟨c, q, bs, hd, m, h⟩))

/-- The existential shadow of `compose` without the forgery's tree membership. **Trivially true
for every key a signer knows** (`Controls/Compose.lean`, `compose_exists_free`): it says nothing
beyond `compose` and is kept only as a readability corollary (RA-M1). -/
theorem compose_exists (L : Log) (n : ℕ) (hn : n ≤ chainCap) (r : ℕ) (hs : List Digest)
    (hr : hs.length = 2 ^ r) (p : Signed)
    (hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true) :
    (∃ ss, List.Forall₂ (fun s h => chainEnd s n = h) ss hs) ∨ Nonempty Collision ∨
      Nonempty (Forgery vk L) ∨
      ∃ (c : Digest) (q : Signed) (bs : List Bool), bs.length ≤ r ∧
        InTree S L (treeRoot (hs.map fun h => leafStmt h n)) p bs c q ∧ Escape S vk L c q :=
  (compose L n hn r hs hr p hacc).imp_right
    (Or.imp_right (Or.imp_left fun ⟨f, _, _, _⟩ => ⟨f⟩))

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
`logCap` of potential below `1`, the leaf starts, a collision, or a capped forgery in the
extraction tree of the root signed proof. -/
theorem compose_of_kstate (k : KState (Rel (S.acc vk)) (S.V vk) S.E ε) {L : Log}
    (hL : L.Functional) (hlen : L.length ≤ logCap) (hμ : k.μ L < 1) (n : ℕ) (hn : n ≤ chainCap)
    (r : ℕ) (hs : List Digest) (hr : hs.length = 2 ^ r) (p : Signed)
    (hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true) :
    (∃ ss, List.Forall₂ (fun s h => chainEnd s n = h) ss hs) ∨ Nonempty Collision ∨
      ∃ (f : Forgery vk L) (c : Digest) (bs : List Bool),
        InTree S L (treeRoot (hs.map fun h => leafStmt h n)) p bs c f.p :=
  (compose L n hn r hs hr p hacc).imp_right (Or.imp_right fun h => h.resolve_right
    fun ⟨_, _, _, _, _, he⟩ => Escape.not_of_kstate k hL hlen hμ he)

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

/-- **The composition theorem with probabilities** (V4-8, V4-A10): for an adversary `A` asking
at most `Q` queries and outputting the root signed proof, with `Q + qV ≤ logCap`, the probability
over one lazily sampled random oracle that `acc` accepts the root and the walk on `A`'s final log
ends in an escape, returning none of the leaf starts, a collision, or a forgery in the extraction
tree, is at most `(2^(r+1) - 1) · (Q + qV) · ε`. -/
theorem compose_prob (hks : KS (Rel (S.acc vk)) (S.V vk) S.E ε qV) (n : ℕ) (hn : n ≤ chainCap)
    (r : ℕ) (hs : List Digest) (hr : hs.length = 2 ^ r) (A : OProg Signed) {Q : ℕ}
    (hA : ∀ H, (A.queries H).length ≤ Q) (hQ : Q + qV ≤ logCap) :
    prob (fun p L => ∃ hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true,
      (walk L n hn r hs hr p hacc).Escaped) A [] ≤ (2 ^ (r + 1) - 1 : ℕ) * ((Q + qV) * ε) := by
  rw [show 2 ^ (r + 1) - 1 = (paths r).card by have := card_paths r; omega]
  refine (prob_mono (fun p L ⟨_, he⟩ => ?_) A []).trans
    (escape_prob_le hks (treeRoot (hs.map fun h => leafStmt h n)) A hA hQ (paths r))
  obtain ⟨c, q, bs, hd, hmem, h⟩ := he.exists
  exact ⟨bs, mem_paths.mpr hd, c, q, hmem, h⟩

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

/-- **The walk at a leaf**: on a one-leaf subtree whose signed proof's trace is in the log and
which the extractor opens to the leaf witness `(s, n)` with `chainEnd s n` the leaf's chain end,
the walk's outcome `o` is the start `s`. -/
theorem walkFrom_leaf {L : Log} {n : ℕ} (hn : n ≤ chainCap) {c₀ : Digest} {p₀ : Signed} {d : ℕ}
    {hs : List Digest} {h : Digest} (hh : hs = [h]) {hr : hs.length = 2 ^ 0} {p : Signed}
    {bs : List Bool} {hd : bs.length + 0 ≤ d}
    {hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true}
    {hmem : InTree S L c₀ p₀ bs (treeRoot (hs.map fun h => leafStmt h n)) p}
    {o : Outcome S vk L n hs c₀ p₀ d}
    (ho : walkFrom L n hn c₀ p₀ d 0 hs hr p bs hd hacc hmem = o) (hin : ∀ e ∈ p.tr, e ∈ L)
    {s : Digest} (hE : S.E (treeRoot (hs.map fun h => leafStmt h n)) p.π L = some (.leaf s n))
    (hend : chainEnd s n = h) : o.starts? = some [s] := by
  subst hh ho
  have hR : Rel (S.acc vk) (treeRoot ([h].map fun h => leafStmt h n)) (.leaf s n) :=
    ⟨hn, show leafStmt h n = leafStmt (chainEnd s n) n by rw [hend]⟩
  unfold walkFrom
  simp only [extract_of_E hacc hin hE hR, hend, and_self, dite_true, Outcome.starts?]

end RecursionFast.Compose
