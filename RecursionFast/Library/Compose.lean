/-
  RecursionFast.Library.Compose  (UNTRUSTED, kernel-checked)

  **The composition argument across the harness tree** (V4-8; CGSY24 Thm 5.1's straight-line
  argument, kernel content). Fix a submission `S`, a public key `vk`, a knowledge state for
  `Rel (S.acc vk)` (any error), and one oracle log `L` of the run: functional (an oracle's log),
  at most `logCap` entries, with potential below `1`. The harness's tree has `2^r` leaves whose
  digests are `leafStmt hᵢ n` (the runner computes them from the chain ends `hᵢ` it knows, with
  `n ≤ chainCap`), and its root digest is `treeRoot` of them. Given a root signed proof that
  `S.acc vk` accepts, the computable walk `walk` returns one of:
  * **the leaf starts**: `sᵢ` with `chainEnd sᵢ n = hᵢ` for every leaf;
  * **a BLAKE2s collision**: two different byte strings with one digest (`Collision`);
  * **a forgery**: a signed proof met on the walk (the root, or a child in a witness the
    extractor returned) whose signature on its trace's digest is valid under `vk` but whose trace
    is not contained in `L` (`Forgery`).
  At each node the walk checks the signed proof's trace against `L`; if it is contained, the
  verifier accepts on `L` (`OProg.runLog_of_runSeq`, `Library/Trace.lean`), the knowledge state's
  `final` law extracts a witness with `S.E`, and the witness's digests are compared with the
  tree's (a mismatch under one digest is a collision of the tagged preimages).

  What stays on paper: the probability of the third outcome. A trace not contained in `L` was
  never signed by the service as such (every query a `sign` request evaluates is in `L`), so the
  signature is an EUF-CMA forgery, unless the service signed a different trace with the same
  digest, which is a collision of `traceBytes` encodings (injective below `queryCap`,
  `traceBytes_inj`). Collisions and forgeries are then bounded by `Adv_coll + Adv_EUF-CMA`
  (BRIEF §2), and the knowledge state's potential by the paper theorem
  (`Library/PaperTheorem.lean`).
-/
import RecursionFast.Library.Trace
import RecursionFast.Library.Tree
import RecursionFast.Contract.Certificate

open scoped NNReal

namespace RecursionFast.Compose
open RecursionFast

/-- **A forgery against the log `L`**: a signed proof whose signature on its trace's digest is
valid under `vk`, while its trace is not contained in `L`. -/
structure Forgery (vk : Digest) (L : Log) where
  /-- The signed proof. -/
  p : Signed
  /-- Its signature verifies on its trace's digest. -/
  sig : SigOk vk (traceDigest p.tr) p.σ = true
  /-- Some entry of its trace is not in the log. -/
  notIn : ¬ ∀ e ∈ p.tr, e ∈ L

/-- **What the walk returns** for the leaf chain ends `hs` of length `n`: the leaf starts, a
collision, or a forgery. -/
inductive Outcome (vk : Digest) (L : Log) (n : ℕ) (hs : List Digest) where
  /-- The leaf starts: chain `n` from `ss[i]` ends at `hs[i]`, for every leaf. -/
  | starts (ss : List Digest) (h : List.Forall₂ (fun s h => chainEnd s n = h) ss hs)
  /-- A BLAKE2s collision. -/
  | collision (c : Collision)
  /-- A forgery against the log. -/
  | forgery (f : Forgery vk L)

variable {S : Submission} {vk : Digest} {L : Log} {ε : ℝ≥0}

/-! ## Helpers: acceptance, the tree's halves, collisions of the tagged preimages -/

/-- The two facts of an acceptance the walk uses: the signature verifies on the trace's digest,
and the verifier accepts on the trace. -/
private theorem acc_parts {S : Submission} {vk c : Digest} {p : Signed}
    (h : S.acc vk c p = true) :
    SigOk vk (traceDigest p.tr) p.σ = true ∧ (S.V vk c p.π).runSeq p.tr = some true := by
  simp only [Submission.acc, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2⟩

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

/-- **One extraction**: a witness of the relation for an accepted signed proof whose trace is in
the log, or a forgery. -/
def extract (k : KState (Rel (S.acc vk)) (S.V vk) S.E ε) (hL : L.Functional)
    (hlen : L.length ≤ logCap) (hμ : k.μ L < 1) (c : Digest) (p : Signed)
    (hacc : S.acc vk c p = true) : {w // Rel (S.acc vk) c w} ⊕ Forgery vk L :=
  if hin : ∀ e ∈ p.tr, e ∈ L then
    have hex := k.final L c p.π hlen hμ (OProg.runLog_of_runSeq hL _ _ (acc_parts hacc).2 hin)
    match hE : S.E c p.π L with
    | some w => .inl ⟨w, hex.elim fun _ ⟨hw, hR⟩ => Option.some.inj (hE.symm.trans hw) ▸ hR⟩
    | none => False.elim (hex.elim fun _ ⟨hw, _⟩ => Option.some_ne_none _ (hw.symm.trans hE))
  else .inr ⟨p, (acc_parts hacc).1, hin⟩

/-- **The walk over the tree** of `2^r` leaves with chain ends `hs` of length `n`. -/
def walk (k : KState (Rel (S.acc vk)) (S.V vk) S.E ε) (hL : L.Functional)
    (hlen : L.length ≤ logCap) (hμ : k.μ L < 1) (n : ℕ) (hn : n ≤ chainCap) :
    (r : ℕ) → (hs : List Digest) → hs.length = 2 ^ r → (p : Signed) →
      S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true → Outcome vk L n hs
  | 0, [h], _, p, hacc =>
    match extract k hL hlen hμ _ p hacc with
    | .inr f => .forgery f
    | .inl ⟨.leaf s m, hw⟩ =>
      if he : chainEnd s m = h ∧ m = n then
        .starts [s] (.cons (he.2 ▸ he.1) .nil)
      else .collision (leafCollision (h := h) (n := n) hn hw.1 he hw.2)
    | .inl ⟨.node _ _ _ _, hw⟩ => .collision (leafNodeCollision (h := h) (n := n) hw.1)
  | 0, [], hr, _, _ => absurd hr (by simp)
  | 0, _ :: _ :: _, hr, _, _ => absurd hr (by simp)
  | r + 1, hs, hr, p, hacc =>
    have hroot := treeRoot_map_split hr fun h => leafStmt h n
    match extract k hL hlen hμ _ p hacc with
    | .inr f => .forgery f
    | .inl ⟨.leaf _ _, hw⟩ => .collision (leafNodeCollision (hw.2.symm.trans hroot))
    | .inl ⟨.node c₁ c₂ p₁ p₂, hw⟩ =>
      if he : c₁ = treeRoot ((hs.take (2 ^ r)).map fun h => leafStmt h n) ∧
          c₂ = treeRoot ((hs.drop (2 ^ r)).map fun h => leafStmt h n) then
        match walk k hL hlen hμ n hn r (hs.take (2 ^ r)) (length_take_pow hr) p₁ (he.1 ▸ hw.2.1),
          walk k hL hlen hμ n hn r (hs.drop (2 ^ r)) (length_drop_pow hr) p₂ (he.2 ▸ hw.2.2) with
        | .starts ss₁ h₁, .starts ss₂ h₂ =>
          .starts (ss₁ ++ ss₂) (List.take_append_drop (2 ^ r) hs ▸ List.rel_append h₁ h₂)
        | .collision c, _ => .collision c
        | .forgery f, _ => .forgery f
        | .starts _ _, .collision c => .collision c
        | .starts _ _, .forgery f => .forgery f
      else .collision (nodeCollision he (hroot.symm.trans hw.1))

/-- **The composition theorem** (V4-8), as a proposition: the leaf starts exist, or a BLAKE2s
collision exists, or a forgery against the log exists. -/
theorem compose (k : KState (Rel (S.acc vk)) (S.V vk) S.E ε) (hL : L.Functional)
    (hlen : L.length ≤ logCap) (hμ : k.μ L < 1) (n : ℕ) (hn : n ≤ chainCap) (r : ℕ)
    (hs : List Digest) (hr : hs.length = 2 ^ r) (p : Signed)
    (hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true) :
    (∃ ss, List.Forall₂ (fun s h => chainEnd s n = h) ss hs) ∨ Nonempty Collision ∨
      Nonempty (Forgery vk L) := by
  cases walk k hL hlen hμ n hn r hs hr p hacc with
  | starts ss h => exact Or.inl ⟨ss, h⟩
  | collision c => exact Or.inr (Or.inl ⟨c⟩)
  | forgery f => exact Or.inr (Or.inr ⟨f⟩)

end RecursionFast.Compose
