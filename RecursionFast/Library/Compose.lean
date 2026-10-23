/-
  RecursionFast.Library.Compose  (UNTRUSTED, kernel-checked)

  **The composition argument across the harness tree** (V4-8; CGSY24 Thm 5.1's straight-line
  argument, kernel content). Fix a submission `S`, a public key `vk`, a knowledge state for
  `Rel (S.acc vk)` (any error), and one oracle log `L` of the run: functional (an oracle's log),
  at most `logCap` entries, with potential below `1`. The harness's tree has `2^r` leaves whose
  digests are `leafStmt hᵢ n` (the runner computes them from the chain ends `hᵢ` it knows, with
  `n ≤ chainCap`), and its root digest `c₀` is `treeRoot` of them. Given a root signed proof `p₀`
  that `S.acc vk` accepts:

  **The kernel content is the computable `walk`, whose type is the statement** (RA-M1): from
  these hypotheses it returns, computed from `p₀` through `S.E` on `L` (`Outcome`),
  * **the leaf starts**: `sᵢ` with `chainEnd sᵢ n = hᵢ` for every leaf;
  * **a BLAKE2s collision**: two different byte strings with one digest (`Collision`), the
    tagged preimages of a statement mismatch;
  * **a forgery in the extraction tree of `p₀`**: a signed proof `p` with `InTree S L c₀ p₀ c p`
    (the root, or a child of a node witness `S.E` returns for a member, `InTree`) whose trace
    has queries of at most `queryCap` bytes and whose signature on the trace's digest is valid
    under `vk`, while the trace is not contained in `L` (`Forgery`).
  At each node the walk checks the signed proof's trace against `L`; if it is contained, the
  verifier accepts on `L` (`OProg.runLog_of_runSeq`, `Library/Trace.lean`), the knowledge state's
  `final` law extracts a witness with `S.E`, and the witness's digests are compared with the
  tree's. `compose` states the same as a proposition, keeping the membership; `compose_exists`,
  the bare disjunction without it, is **trivially true for every key a signer knows** (anyone
  holding `sk` signs a trace with a fresh answer: `Controls/Compose.lean`, `forgery_trivial`) and
  is kept only as a documented corollary.

  What stays on paper: the probability of the third outcome. A trace not contained in `L` was
  never signed by the service as such (every query a `sign` request evaluates is in `L`), so the
  signature is an EUF-CMA forgery, unless the service signed a different trace with the same
  digest, which is a collision of `traceBytes` encodings (injective on queries of at most
  `queryCap` bytes, `traceBytes_inj`; the forgery carries that cap, and the service's traces have
  it by the wire cap). Collisions and forgeries are then bounded by `Adv_coll + Adv_EUF-CMA`
  (BRIEF §2), and the knowledge state's potential by the paper theorem
  (`Library/PaperTheorem.lean`).
-/
import RecursionFast.Library.Trace
import RecursionFast.Library.Tree
import RecursionFast.Contract.Certificate

open scoped NNReal

namespace RecursionFast.Compose
open RecursionFast

/-- **The extraction tree** of `S` on the log `L` from the root `(c₀, p₀)`: the root, and the
two children's signed proofs of every member that the extractor opens, on `L`, to a node
witness. -/
inductive InTree (S : Submission) (L : Log) (c₀ : Digest) (p₀ : Signed) : Digest → Signed → Prop
  /-- The root. -/
  | root : InTree S L c₀ p₀ c₀ p₀
  /-- The first child of a member the extractor opens to a node. -/
  | left {c c₁ c₂ : Digest} {p p₁ p₂ : Signed} : InTree S L c₀ p₀ c p →
      S.E c p.π L = some (.node c₁ c₂ p₁ p₂) → InTree S L c₀ p₀ c₁ p₁
  /-- The second child of a member the extractor opens to a node. -/
  | right {c c₁ c₂ : Digest} {p p₁ p₂ : Signed} : InTree S L c₀ p₀ c p →
      S.E c p.π L = some (.node c₁ c₂ p₁ p₂) → InTree S L c₀ p₀ c₂ p₂

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

/-- **What the walk returns** for the leaf chain ends `hs` of length `n` and the root `(c₀, p₀)`:
the leaf starts, a collision, or a forgery in the extraction tree of `S` on `L` from the root. -/
inductive Outcome (S : Submission) (vk : Digest) (L : Log) (n : ℕ) (hs : List Digest)
    (c₀ : Digest) (p₀ : Signed) where
  /-- The leaf starts: chain `n` from `ss[i]` ends at `hs[i]`, for every leaf. -/
  | starts (ss : List Digest) (h : List.Forall₂ (fun s h => chainEnd s n = h) ss hs)
  /-- A BLAKE2s collision. -/
  | collision (col : Collision)
  /-- A forgery against the log, at the member `(c, f.p)` of the extraction tree. -/
  | forgery (f : Forgery vk L) (c : Digest) (mem : InTree S L c₀ p₀ c f.p)

/-- The leaf starts an outcome returns, if it returns them. -/
def Outcome.starts? {S : Submission} {vk : Digest} {L : Log} {n : ℕ} {hs : List Digest}
    {c₀ : Digest} {p₀ : Signed} : Outcome S vk L n hs c₀ p₀ → Option (List Digest)
  | .starts ss _ => some ss
  | _ => none

variable {S : Submission} {vk : Digest} {L : Log} {ε : ℝ≥0}

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

/-! ## The extraction and the walk -/

/-- **One extraction**: a witness of the relation that the extractor returns on `L`, for an
accepted signed proof whose trace is in the log; or that signed proof as a forgery. -/
def extract (k : KState (Rel (S.acc vk)) (S.V vk) S.E ε) (hL : L.Functional)
    (hlen : L.length ≤ logCap) (hμ : k.μ L < 1) (c : Digest) (p : Signed)
    (hacc : S.acc vk c p = true) :
    {w // Rel (S.acc vk) c w ∧ S.E c p.π L = some w} ⊕ {f : Forgery vk L // f.p = p} :=
  if hin : ∀ e ∈ p.tr, e ∈ L then
    have hex :=
      k.final L c p.π hlen hμ (OProg.runLog_of_runSeq hL _ _ (acc_parts hacc).2.2.2 hin)
    have hs : (S.E c p.π L).isSome := hex.elim fun _ ⟨hw, _⟩ => by simp [hw]
    .inl ⟨(S.E c p.π L).get hs, hex.elim fun _ ⟨hw, hR⟩ => by simpa [hw] using hR, by simp⟩
  else .inr ⟨⟨p, (acc_parts hacc).2.1, (acc_parts hacc).2.2.1, hin⟩, rfl⟩

/-- **The walk from a member `(treeRoot …, p)` of the extraction tree of `(c₀, p₀)`**, over the
subtree of `2^r` leaves with chain ends `hs` of length `n`. -/
def walkFrom (k : KState (Rel (S.acc vk)) (S.V vk) S.E ε) (hL : L.Functional)
    (hlen : L.length ≤ logCap) (hμ : k.μ L < 1) (n : ℕ) (hn : n ≤ chainCap) (c₀ : Digest)
    (p₀ : Signed) :
    (r : ℕ) → (hs : List Digest) → hs.length = 2 ^ r → (p : Signed) →
      S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true →
      InTree S L c₀ p₀ (treeRoot (hs.map fun h => leafStmt h n)) p → Outcome S vk L n hs c₀ p₀
  | 0, [h], _, p, hacc, hmem =>
    match extract k hL hlen hμ _ p hacc with
    | .inr ⟨f, hf⟩ => .forgery f _ (hf ▸ hmem)
    | .inl ⟨.leaf s m, hw, _⟩ =>
      if he : chainEnd s m = h ∧ m = n then
        .starts [s] (.cons (he.2 ▸ he.1) .nil)
      else .collision (leafCollision (h := h) (n := n) hn hw.1 he hw.2)
    | .inl ⟨.node _ _ _ _, hw, _⟩ => .collision (leafNodeCollision (h := h) (n := n) hw.1)
  | 0, [], hr, _, _, _ => absurd hr (by simp)
  | 0, _ :: _ :: _, hr, _, _, _ => absurd hr (by simp)
  | r + 1, hs, hr, p, hacc, hmem =>
    have hroot := treeRoot_map_split hr fun h => leafStmt h n
    match extract k hL hlen hμ _ p hacc with
    | .inr ⟨f, hf⟩ => .forgery f _ (hf ▸ hmem)
    | .inl ⟨.leaf _ _, hw, _⟩ => .collision (leafNodeCollision (hw.2.symm.trans hroot))
    | .inl ⟨.node c₁ c₂ p₁ p₂, hw, hE⟩ =>
      if he : c₁ = treeRoot ((hs.take (2 ^ r)).map fun h => leafStmt h n) ∧
          c₂ = treeRoot ((hs.drop (2 ^ r)).map fun h => leafStmt h n) then
        match walkFrom k hL hlen hμ n hn c₀ p₀ r (hs.take (2 ^ r)) (length_take_pow hr) p₁
            (he.1 ▸ hw.2.1) (he.1 ▸ InTree.left hmem hE),
          walkFrom k hL hlen hμ n hn c₀ p₀ r (hs.drop (2 ^ r)) (length_drop_pow hr) p₂
            (he.2 ▸ hw.2.2) (he.2 ▸ InTree.right hmem hE) with
        | .starts ss₁ h₁, .starts ss₂ h₂ =>
          .starts (ss₁ ++ ss₂) (List.take_append_drop (2 ^ r) hs ▸ List.rel_append h₁ h₂)
        | .collision col, _ => .collision col
        | .forgery f c m, _ => .forgery f c m
        | .starts _ _, .collision col => .collision col
        | .starts _ _, .forgery f c m => .forgery f c m
      else .collision (nodeCollision he (hroot.symm.trans hw.1))

/-- **The walk over the harness tree** (V4-8): from the hypotheses, the root's leaf starts, an
explicit collision, or an explicit capped forgery in the extraction tree of the root signed
proof, computed from it through `S.E` on `L`. Its type is the composition statement. -/
def walk (k : KState (Rel (S.acc vk)) (S.V vk) S.E ε) (hL : L.Functional)
    (hlen : L.length ≤ logCap) (hμ : k.μ L < 1) (n : ℕ) (hn : n ≤ chainCap) (r : ℕ)
    (hs : List Digest) (hr : hs.length = 2 ^ r) (p : Signed)
    (hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true) :
    Outcome S vk L n hs (treeRoot (hs.map fun h => leafStmt h n)) p :=
  walkFrom k hL hlen hμ n hn _ p r hs hr p hacc .root

/-- **The composition theorem** (V4-8), the proposition `walk` proves: the leaf starts exist, or
a BLAKE2s collision exists, or a capped forgery against `L` lies in the extraction tree of the
root signed proof. -/
theorem compose (k : KState (Rel (S.acc vk)) (S.V vk) S.E ε) (hL : L.Functional)
    (hlen : L.length ≤ logCap) (hμ : k.μ L < 1) (n : ℕ) (hn : n ≤ chainCap) (r : ℕ)
    (hs : List Digest) (hr : hs.length = 2 ^ r) (p : Signed)
    (hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true) :
    (∃ ss, List.Forall₂ (fun s h => chainEnd s n = h) ss hs) ∨ Nonempty Collision ∨
      ∃ (f : Forgery vk L) (c : Digest),
        InTree S L (treeRoot (hs.map fun h => leafStmt h n)) p c f.p := by
  cases walk k hL hlen hμ n hn r hs hr p hacc with
  | starts ss h => exact Or.inl ⟨ss, h⟩
  | collision col => exact Or.inr (Or.inl ⟨col⟩)
  | forgery f c m => exact Or.inr (Or.inr ⟨f, c, m⟩)

/-- The existential shadow of `compose` without the tree membership. **Trivially true for every
key a signer knows** (`Controls/Compose.lean`, `compose_exists_free`): it says nothing beyond
`compose` and is kept only as a readability corollary (RA-M1). -/
theorem compose_exists (k : KState (Rel (S.acc vk)) (S.V vk) S.E ε) (hL : L.Functional)
    (hlen : L.length ≤ logCap) (hμ : k.μ L < 1) (n : ℕ) (hn : n ≤ chainCap) (r : ℕ)
    (hs : List Digest) (hr : hs.length = 2 ^ r) (p : Signed)
    (hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true) :
    (∃ ss, List.Forall₂ (fun s h => chainEnd s n = h) ss hs) ∨ Nonempty Collision ∨
      Nonempty (Forgery vk L) :=
  (compose k hL hlen hμ n hn r hs hr p hacc).imp_right
    (Or.imp_right fun ⟨f, _, _⟩ => ⟨f⟩)

/-! ## Reading the walk: the extraction step on a known extractor output -/

/-- If the trace is in the log and the extractor returns `w`, the extraction step returns `w`. -/
theorem extract_of_E (k : KState (Rel (S.acc vk)) (S.V vk) S.E ε) (hL : L.Functional)
    (hlen : L.length ≤ logCap) (hμ : k.μ L < 1) {c : Digest} {p : Signed}
    (hacc : S.acc vk c p = true) (hin : ∀ e ∈ p.tr, e ∈ L) {w : Wit}
    (hE : S.E c p.π L = some w) :
    ∃ hw, extract k hL hlen hμ c p hacc = .inl ⟨w, hw⟩ := by
  have hex :=
    k.final L c p.π hlen hμ (OProg.runLog_of_runSeq hL _ _ (acc_parts hacc).2.2.2 hin)
  refine ⟨⟨hex.elim fun _ ⟨hw, hR⟩ => Option.some.inj (hE.symm.trans hw) ▸ hR, hE⟩, ?_⟩
  unfold extract
  rw [dite_eq_left_of_eq_true (eq_true hin)]
  exact congrArg Sum.inl (Subtype.ext (by simp [hE]))

/-- **The walk at a leaf**: on a one-leaf subtree whose signed proof's trace is in the log and
which the extractor opens to the leaf witness `(s, n)` with `chainEnd s n` the leaf's chain end,
the walk's outcome `o` is the start `s`. -/
theorem walkFrom_leaf (k : KState (Rel (S.acc vk)) (S.V vk) S.E ε) (hL : L.Functional)
    (hlen : L.length ≤ logCap) (hμ : k.μ L < 1) {n : ℕ} (hn : n ≤ chainCap) {c₀ : Digest}
    {p₀ : Signed} {hs : List Digest} {h : Digest} (hh : hs = [h]) {hr : hs.length = 2 ^ 0}
    {p : Signed} {hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true}
    {hmem : InTree S L c₀ p₀ (treeRoot (hs.map fun h => leafStmt h n)) p}
    {o : Outcome S vk L n hs c₀ p₀} (ho : walkFrom k hL hlen hμ n hn c₀ p₀ 0 hs hr p hacc hmem = o)
    (hin : ∀ e ∈ p.tr, e ∈ L) {s : Digest}
    (hE : S.E (treeRoot (hs.map fun h => leafStmt h n)) p.π L = some (.leaf s n))
    (hend : chainEnd s n = h) : o.starts? = some [s] := by
  subst hh ho
  obtain ⟨hw, hx⟩ := extract_of_E k hL hlen hμ hacc hin hE
  unfold walkFrom
  split
  · rename_i heq; rw [hx] at heq; cases heq
  · rename_i s' m _ _ heq
    rw [hx] at heq
    obtain ⟨rfl, rfl⟩ : s = s' ∧ n = m := by
      have := congrArg (fun x => (Sum.getLeft? x).map Subtype.val) heq
      simpa using this
    rw [dite_eq_left_of_eq_true (eq_true ⟨hend, rfl⟩)]
    rfl
  · rename_i heq; rw [hx] at heq; cases heq

end RecursionFast.Compose
