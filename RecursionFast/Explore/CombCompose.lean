/-
  RecursionFast.Explore.CombCompose  (UNTRUSTED, kernel-checked; audit probe, not imported)

  **The composition argument over the stream's comb** (V4-A11; design §2.4 table, §6.2), the
  counterpart for the benchmark's pure-IVC stream of `Library/Compose.lean`'s walk over balanced
  trees. The stream draws `M + 1` chains `(sᵢ, nᵢ)` with ends `hᵢ = chainEnd sᵢ nᵢ`, leaf digests
  `dᵢ = leafStmt hᵢ nᵢ`; step 1 proves `nodeStmt d₀ d₁`, step `i ≥ 2` proves
  `nodeStmt stmt_{i-1} dᵢ` (`harness/rfh/bench.py`, `stream_run`; design §3.4 row 6). Step `M`'s
  statement is `combRoot d₀ [d₁, …, d_M]` (`combStmt`): first child the previous statement,
  second child the fresh leaf.

  **The walk** (`combWalk`, whose type is the statement): from one log `L` and an accepted signed
  proof of the comb's statement it returns the leaf starts (`chainEnd sᵢ nᵢ = hᵢ` for every leaf,
  each with its own length), a BLAKE2s collision, a forgery in the extraction tree (`InTree`), or
  an escape at a member whose path lies in `combPaths M`: the `M + 1` spine paths
  `replicate j false` (`j ≤ M`) and the `M` leaf paths `true :: replicate j false` (`j < M`),
  `2M + 1` paths (`card_combPaths`), all of length at most `M`.

  **The probability** (`comb_prob`): `escape_prob_le` over `combPaths M` gives
  `(2M + 1) · (Q + qV) · ε` for "the root is accepted and the walk escapes" (193 members at
  `M = 96`, against `2^97 - 1` for all paths of length at most `M`).
-/
import RecursionFast.Library.Compose
import RecursionFast.Controls.Hex

open scoped NNReal

namespace RecursionFast.CombCompose
open RecursionFast RecursionFast.Compose

/-! ## The comb's statement -/

/-- **The stream's statement after the leaves `d₀, d₁, …, d_k`**: `d₀` alone for `k = 0`, and for
`k ≥ 1` the node statement whose first child is the statement after `d₀, …, d_{k-1}` and whose
second child is `d_k` (step `k` of the stream proves it). -/
def combRoot (d₀ : Digest) (ds : List Digest) : Digest := ds.foldl nodeStmt d₀

/-- **The statement step `M` of the stream proves** for the chains with ends and lengths
`l₀ = (h₀, n₀)` and `ls = [(h₁, n₁), …, (h_M, n_M)]`: the comb over their leaf statements. -/
def combStmt (l₀ : Digest × ℕ) (ls : List (Digest × ℕ)) : Digest :=
  combRoot (leafStmt l₀.1 l₀.2) (ls.map fun x => leafStmt x.1 x.2)

/-- The comb's statement with its leaves listed newest first (the walk's recursion order). -/
def combRev (l₀ : Digest × ℕ) : List (Digest × ℕ) → Digest
  | [] => leafStmt l₀.1 l₀.2
  | x :: rs => nodeStmt (combRev l₀ rs) (leafStmt x.1 x.2)

/-- The harness's loop invariant: one more step nests the previous statement as first child. -/
theorem combRoot_append_singleton (d₀ d : Digest) (ds : List Digest) :
    combRoot d₀ (ds ++ [d]) = nodeStmt (combRoot d₀ ds) d := by
  simp [combRoot, List.foldl_append]

theorem combRev_eq (l₀ : Digest × ℕ) : ∀ rs : List (Digest × ℕ),
    combRev l₀ rs = combStmt l₀ rs.reverse
  | [] => rfl
  | x :: rs => by
    rw [combRev, combRev_eq l₀ rs, List.reverse_cons, combStmt, combStmt, List.map_append,
      List.map_singleton, combRoot_append_singleton]

theorem combRev_reverse (l₀ : Digest × ℕ) (ls : List (Digest × ℕ)) :
    combRev l₀ ls.reverse = combStmt l₀ ls := by
  rw [combRev_eq, List.reverse_reverse]

/-! ## The comb's paths -/

/-- **The paths of the comb with `M` nodes** (last step first, `false` for a first child): the
spine `replicate j false` for `j ≤ M` and the leaves `true :: replicate j false` for `j < M`. -/
def combPaths (M : ℕ) : Finset (List Bool) :=
  (Finset.range (M + 1)).image (List.replicate · false) ∪
    (Finset.range M).image fun j => true :: List.replicate j false

theorem spine_mem {M j : ℕ} (h : j ≤ M) : List.replicate j false ∈ combPaths M :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩)

theorem leaf_mem {M j : ℕ} (h : j < M) : true :: List.replicate j false ∈ combPaths M :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr h, rfl⟩)

/-- **The comb with `M` nodes has `2M + 1` paths.** -/
theorem card_combPaths (M : ℕ) : (combPaths M).card = 2 * M + 1 := by
  have hdis : Disjoint ((Finset.range (M + 1)).image (List.replicate · false))
      ((Finset.range M).image fun j => true :: List.replicate j false) := by
    rw [Finset.disjoint_left]
    rintro _ h₁ h₂
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h₁
    obtain ⟨j, -, h⟩ := Finset.mem_image.mp h₂
    cases i <;> simp [List.replicate_succ] at h
  rw [combPaths, Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ (List.replicate_left_injective false),
    Finset.card_image_of_injective _ fun a b h =>
      List.replicate_left_injective false (List.cons.inj h).2,
    Finset.card_range, Finset.card_range]
  omega

/-- Every comb path has length at most `M`: the comb's paths are among the balanced tree's. -/
theorem combPaths_subset (M : ℕ) : combPaths M ⊆ paths M := by
  intro bs h
  rw [mem_paths]
  rcases Finset.mem_union.mp h with h | h <;> obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h <;>
    simp at hj ⊢ <;> omega

/-! ## The walk -/

variable {S : Submission} {vk : Digest} {ε : ℝ≥0} {qV : ℕ}

/-- **What the comb walk returns** for the leaves `ls` (each `(h, n)`), the root `(c₀, p₀)` and
the path set `P`: the leaf starts, a collision, a forgery in the extraction tree of `S` on `L`
from the root, or an escape in it at a path in `P`. -/
inductive COut (S : Submission) (vk : Digest) (L : Log) (ls : List (Digest × ℕ))
    (c₀ : Digest) (p₀ : Signed) (P : Finset (List Bool)) where
  /-- The leaf starts: chain `ls[i].2` from `ss[i]` ends at `ls[i].1`, for every leaf. -/
  | starts (ss : List Digest) (h : List.Forall₂ (fun s x => chainEnd s x.2 = x.1) ss ls)
  /-- A BLAKE2s collision. -/
  | collision (col : Collision)
  /-- A forgery against the log, at the member `(c, f.p)` of the extraction tree. -/
  | forgery (f : Forgery vk L) (c : Digest) (bs : List Bool) (mem : InTree S L c₀ p₀ bs c f.p)
  /-- An escape at the member `(c, p)` of the extraction tree, at a path in `P`. -/
  | escape (c : Digest) (p : Signed) (bs : List Bool) (mem : InTree S L c₀ p₀ bs c p)
      (path : bs ∈ P) (h : Escape S vk L c p)

/-- The outcome is an escape: not the leaf starts, a collision or a forgery. -/
def COut.Escaped {L : Log} {ls : List (Digest × ℕ)} {c₀ : Digest} {p₀ : Signed}
    {P : Finset (List Bool)} : COut S vk L ls c₀ p₀ P → Prop
  | .escape .. => True
  | _ => False

theorem COut.Escaped.exists {L : Log} {ls : List (Digest × ℕ)} {c₀ : Digest} {p₀ : Signed}
    {P : Finset (List Bool)} {o : COut S vk L ls c₀ p₀ P} (h : o.Escaped) :
    ∃ bs ∈ P, ∃ c q, InTree S L c₀ p₀ bs c q ∧ Escape S vk L c q := by
  cases o with
  | escape c q bs m hp he => exact ⟨bs, hp, c, q, m, he⟩
  | _ => exact h.elim

/-- The same outcome for an equal leaf list. -/
def COut.recast {L : Log} {ls ls' : List (Digest × ℕ)} {c₀ : Digest} {p₀ : Signed}
    {P : Finset (List Bool)} (e : ls = ls') : COut S vk L ls c₀ p₀ P → COut S vk L ls' c₀ p₀ P
  | .starts ss h => .starts ss (e ▸ h)
  | .collision col => .collision col
  | .forgery f c bs m => .forgery f c bs m
  | .escape c q bs m hp he => .escape c q bs m hp he

/-- Two outcomes over consecutive leaf lists: the starts if both return them, else the first
other outcome. -/
def COut.append {L : Log} {ls₁ ls₂ : List (Digest × ℕ)} {c₀ : Digest} {p₀ : Signed}
    {P : Finset (List Bool)} :
    COut S vk L ls₁ c₀ p₀ P → COut S vk L ls₂ c₀ p₀ P → COut S vk L (ls₁ ++ ls₂) c₀ p₀ P
  | .starts ss₁ h₁, .starts ss₂ h₂ => .starts (ss₁ ++ ss₂) (List.rel_append h₁ h₂)
  | .collision col, _ => .collision col
  | .forgery f c bs m, _ => .forgery f c bs m
  | .escape c q bs m hp he, _ => .escape c q bs m hp he
  | .starts _ _, .collision col => .collision col
  | .starts _ _, .forgery f c bs m => .forgery f c bs m
  | .starts _ _, .escape c q bs m hp he => .escape c q bs m hp he

/-- Two leaf statements, one digest, different ends or lengths: a collision (as in `Compose`). -/
def leafCollision {h h' : Digest} {n m : ℕ} (hn : n ≤ chainCap) (hm : m ≤ chainCap)
    (hne : ¬ (h' = h ∧ m = n)) (heq : leafStmt h n = leafStmt h' m) : Collision :=
  ⟨tagLeaf :: h.toList ++ enc64 n, tagLeaf :: h'.toList ++ enc64 m, fun hxy => hne (by
    obtain ⟨h1, h2⟩ := List.append_inj hxy (by simp)
    have hc : (2 : ℕ) ^ 20 < 2 ^ 64 := by norm_num
    exact ⟨(Vector.toList_inj.mp (List.cons.inj h1).2).symm,
      (enc64_inj (lt_of_le_of_lt hn hc) (lt_of_le_of_lt hm hc) h2).symm⟩), heq⟩

/-- A leaf statement equal to a node statement: a collision (as in `Compose`). -/
def leafNodeCollision {h c₁ c₂ : Digest} {n : ℕ} (heq : leafStmt h n = nodeStmt c₁ c₂) :
    Collision :=
  ⟨tagLeaf :: h.toList ++ enc64 n, tagNode :: c₁.toList ++ c₂.toList, by
    simp [tagLeaf, tagNode], heq⟩

/-- Two node statements, one digest, different children: a collision (as in `Compose`). -/
def nodeCollision {a b c₁ c₂ : Digest} (hne : ¬ (c₁ = a ∧ c₂ = b))
    (heq : nodeStmt a b = nodeStmt c₁ c₂) : Collision :=
  ⟨tagNode :: a.toList ++ b.toList, tagNode :: c₁.toList ++ c₂.toList, fun hxy => hne (by
    obtain ⟨h1, h2⟩ := List.append_inj hxy (by simp)
    exact ⟨(Vector.toList_inj.mp (List.cons.inj h1).2).symm, (Vector.toList_inj.mp h2).symm⟩),
    heq⟩

/-- **The walk at one leaf `x = (h, n)`** at the path `bs ∈ P`: its start, a collision, a
forgery or an escape there. -/
def leafOut (L : Log) (x : Digest × ℕ) (hx : x.2 ≤ chainCap) (c₀ : Digest) (p₀ : Signed)
    (P : Finset (List Bool)) (bs : List Bool) (hP : bs ∈ P) (p : Signed)
    (hacc : S.acc vk (leafStmt x.1 x.2) p = true)
    (hmem : InTree S L c₀ p₀ bs (leafStmt x.1 x.2) p) : COut S vk L [x] c₀ p₀ P :=
  match extract L _ p hacc with
  | .inr (.inl ⟨f, hf⟩) => .forgery f _ bs (hf ▸ hmem)
  | .inr (.inr ⟨he⟩) => .escape _ p bs hmem hP he
  | .inl ⟨.leaf s m, hw, _⟩ =>
    if he : chainEnd s m = x.1 ∧ m = x.2 then .starts [s] (.cons (he.2 ▸ he.1) .nil)
    else .collision (leafCollision (h := x.1) (n := x.2) hx hw.1 he hw.2)
  | .inl ⟨.node _ _ _ _, hw, _⟩ => .collision (leafNodeCollision (h := x.1) (n := x.2) hw.1)

/-- **The walk down the comb's spine** from the member at depth `j` (path `replicate j false`),
whose statement is the comb over `l₀` and the leaves `rs` (newest first), with `j + |rs| = M`. -/
def walkRev (L : Log) (l₀ : Digest × ℕ) (h₀ : l₀.2 ≤ chainCap) (c₀ : Digest) (p₀ : Signed)
    (M : ℕ) : (rs : List (Digest × ℕ)) → (∀ x ∈ rs, x.2 ≤ chainCap) → (j : ℕ) →
      j + rs.length = M → (p : Signed) → S.acc vk (combRev l₀ rs) p = true →
      InTree S L c₀ p₀ (List.replicate j false) (combRev l₀ rs) p →
      COut S vk L (l₀ :: rs.reverse) c₀ p₀ (combPaths M)
  | [], _, j, hj, p, hacc, hmem =>
    leafOut L l₀ h₀ c₀ p₀ _ _ (spine_mem (by simp at hj; omega)) p hacc hmem
  | x :: rs, hrs, j, hj, p, hacc, hmem =>
    match extract L _ p hacc with
    | .inr (.inl ⟨f, hf⟩) => .forgery f _ _ (hf ▸ hmem)
    | .inr (.inr ⟨he⟩) =>
      .escape _ p _ hmem (spine_mem (by simp only [List.length_cons] at hj; omega)) he
    | .inl ⟨.leaf _ _, hw, _⟩ =>
      .collision (leafNodeCollision (c₁ := combRev l₀ rs) (c₂ := leafStmt x.1 x.2) hw.2.symm)
    | .inl ⟨.node c₁ c₂ p₁ p₂, hw, hE⟩ =>
      if he : c₁ = combRev l₀ rs ∧ c₂ = leafStmt x.1 x.2 then
        (COut.append
          (walkRev L l₀ h₀ c₀ p₀ M rs (fun y hy => hrs y (.tail _ hy)) (j + 1)
            (by simp only [List.length_cons] at hj; omega) p₁ (he.1 ▸ hw.2.1)
            (he.1 ▸ InTree.left hmem hE))
          (leafOut L x (hrs x (.head _)) c₀ p₀ _ _
            (leaf_mem (by simp only [List.length_cons] at hj; omega)) p₂ (he.2 ▸ hw.2.2)
            (he.2 ▸ InTree.right hmem hE))).recast (by simp)
      else .collision (nodeCollision (a := combRev l₀ rs) (b := leafStmt x.1 x.2) he hw.1)

/-- **The walk over the stream's comb** (V4-A11): from the log `L` and an accepted signed proof
of step `M`'s statement over the chains `l₀ :: ls` (`M = |ls|`), the leaf starts, an explicit
collision, an explicit capped forgery in the extraction tree, or an escape at one of its `2M + 1`
comb paths, computed from it through `S.E` on `L`. Its type is the composition statement. -/
def combWalk (L : Log) (l₀ : Digest × ℕ) (ls : List (Digest × ℕ))
    (hn : ∀ x ∈ l₀ :: ls, x.2 ≤ chainCap) (p : Signed) (hacc : S.acc vk (combStmt l₀ ls) p = true) :
    COut S vk L (l₀ :: ls) (combStmt l₀ ls) p (combPaths ls.length) :=
  (walkRev L l₀ (hn l₀ (.head _)) (combStmt l₀ ls) p ls.length ls.reverse
    (fun x hx => hn x (.tail _ (List.mem_reverse.mp hx))) 0 (by simp) p
    (by rw [combRev_reverse]; exact hacc) (by rw [combRev_reverse]; exact .root)).recast
    (by simp)

/-- **The composition theorem over the comb**, the proposition `combWalk` proves: the leaf starts
exist, or a BLAKE2s collision exists, or a capped forgery against `L` lies in the extraction tree
of the root signed proof, or a member of that tree at a comb path (depth at most `M`) escapes. -/
theorem comb_compose (L : Log) (l₀ : Digest × ℕ) (ls : List (Digest × ℕ))
    (hn : ∀ x ∈ l₀ :: ls, x.2 ≤ chainCap) (p : Signed) (hacc : S.acc vk (combStmt l₀ ls) p = true) :
    (∃ ss, List.Forall₂ (fun s x => chainEnd s x.2 = x.1) ss (l₀ :: ls)) ∨ Nonempty Collision ∨
      (∃ (f : Forgery vk L) (c : Digest) (bs : List Bool), InTree S L (combStmt l₀ ls) p bs c f.p) ∨
      ∃ bs ∈ combPaths ls.length, bs.length ≤ ls.length ∧
        ∃ (c : Digest) (q : Signed), InTree S L (combStmt l₀ ls) p bs c q ∧ Escape S vk L c q := by
  cases combWalk L l₀ ls hn p hacc with
  | starts ss h => exact Or.inl ⟨ss, h⟩
  | collision col => exact Or.inr (Or.inl ⟨col⟩)
  | forgery f c bs m => exact Or.inr (Or.inr (Or.inl ⟨f, c, bs, m⟩))
  | escape c q bs m hp h =>
    exact Or.inr (Or.inr (Or.inr ⟨bs, hp, mem_paths.mp (combPaths_subset _ hp), c, q, m, h⟩))

/-- **The composition theorem over the comb with probabilities**: for an adversary `A` asking at
most `Q` queries and outputting a signed proof, with `Q + qV ≤ logCap`, the probability over one
lazily sampled random oracle that `acc` accepts it for step `M`'s statement and the comb walk on
`A`'s final log escapes is at most `(2M + 1) · (Q + qV) · ε`. -/
theorem comb_prob (hks : KS (Rel (S.acc vk)) (S.V vk) S.E ε qV) (l₀ : Digest × ℕ)
    (ls : List (Digest × ℕ)) (hn : ∀ x ∈ l₀ :: ls, x.2 ≤ chainCap) (A : OProg Signed) {Q : ℕ}
    (hA : ∀ H, (A.queries H).length ≤ Q) (hQ : Q + qV ≤ logCap) :
    prob (fun p L => ∃ hacc : S.acc vk (combStmt l₀ ls) p = true,
      (combWalk L l₀ ls hn p hacc).Escaped) A [] ≤ (2 * ls.length + 1 : ℕ) * ((Q + qV) * ε) := by
  rw [← card_combPaths]
  exact (prob_mono (fun p L ⟨_, he⟩ => he.exists) A []).trans
    (escape_prob_le hks (combStmt l₀ ls) A hA hQ (combPaths ls.length))

/-! ## Controls -/

/-- One leaf: the comb is the leaf's own statement. -/
example (d : Digest) : combRoot d [] = d := rfl
/-- Two leaves (stream step 1): the node statement of the two. -/
example (a b : Digest) : combRoot a [b] = nodeStmt a b := rfl
/-- Three leaves (step 2): the previous statement as first child, the fresh leaf as second. -/
example (a b c : Digest) : combRoot a [b, c] = nodeStmt (nodeStmt a b) c := rfl
/-- At `M = 96` the comb has 193 members. -/
example : (combPaths 96).card = 193 := card_combPaths 96
/-- Negative: the second child's first child is not a comb path (a balanced tree's is). -/
example (M : ℕ) : [false, true] ∉ combPaths M := by
  simp only [combPaths, Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and]
  exact ⟨fun x _ h => by rcases x with _ | _ | _ | x <;> simp [List.replicate_succ] at h,
    fun x _ h => by simp at h⟩
example : [false, true] ∈ paths 2 := mem_paths.mpr (by simp)
/-- Negative: the comb's count is strictly below the balanced count from depth 2 on. -/
example : (combPaths 2).card < (paths 2).card := by
  rw [card_combPaths]; have := card_paths 2; omega

-- Known answer against the harness (`harness/rfh/digest.py`, the loop of `stream_run`): starts
-- `0x00³², 0x01³², 0x02³², 0x00³²`, lengths `0, 1, 2, 3`; step 3's statement.
#guard (combStmt (chainEnd (Vector.replicate 32 0) 0, 0)
    [(chainEnd (Vector.replicate 32 1) 1, 1), (chainEnd (Vector.replicate 32 2) 2, 2),
     (chainEnd (Vector.replicate 32 0) 3, 3)]).toList =
  Controls.Blake2s.hex "ceb1d56f8829e66a6729746fbfa0977436877098a952c52998f8338f4a217fdd"
-- Step 1's statement in the same run.
#guard (combStmt (chainEnd (Vector.replicate 32 0) 0, 0)
    [(chainEnd (Vector.replicate 32 1) 1, 1)]).toList =
  Controls.Blake2s.hex "e8fb8eb6407811c3716d9bd5f6d55e41ac76209f74e69590cc93686f455ade37"
-- Negative: the balanced tree over the same four leaves is not step 3's statement.
#guard (treeRoot [leafStmt (chainEnd (Vector.replicate 32 0) 0) 0,
    leafStmt (chainEnd (Vector.replicate 32 1) 1) 1, leafStmt (chainEnd (Vector.replicate 32 2) 2) 2,
    leafStmt (chainEnd (Vector.replicate 32 0) 3) 3]).toList ≠
  Controls.Blake2s.hex "ceb1d56f8829e66a6729746fbfa0977436877098a952c52998f8338f4a217fdd"

end RecursionFast.CombCompose
