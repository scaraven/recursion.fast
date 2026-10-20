/-
# Exploration: whole-tree extraction from one log                                (UNTRUSTED)

Probe P1, item 2. **A relativized knowledge state composes across every level of a tree, from one
log, with no extra error.** If the potential of a log `L` is below `1` and `V` accepts a root proof
reading `L`, the extractor opens the root on `L`, the children it returns are accepted on the
*same* `L` (that is the relativized node clause), so `final` applies to them with the same `L` and
the same potential, and so on down (`compose`). The tree is extracted from one log at the cost of
one application of the paper theorem, `(Q + qV) · ε`, whatever its depth. When the walk ends in
leaves (`extract`), the leaves form a **flat witness**: chain starts and lengths whose `leafStmt`s,
folded with `nodeStmt` along the extracted shape, give the root digest (`compose_flat`).

**In probability** (`paper_tree`, through `Library/PaperTheorem.lean`, lazily sampled oracle): a
game of at most `n ≤ logCap` queries (the adversary's, then the root verifier's) makes the root
verifier accept a proof whose tree is not extracted on the final log, to some depth, with
probability at most `n · ε`: the bound of one level covers every level.

**Why v3's `Rel Vb` does not give the inductive hypothesis.** v3's `final` concludes `Rel Vb c w`,
whose node clause is `Vb cᵢ πᵢ = true`: the child accepted under **concrete BLAKE2s**. That is a
fact about one fixed function, not about the log `L` the knowledge state controls, so it does not
give `(V cᵢ πᵢ).runLog L = some true`, the hypothesis `final` needs to open the child. A child that
is accepted under BLAKE2s but on no log of small potential escapes. `v3_no_compose` makes this
concrete with the certified backdoor `Controls/Backdoor.lean`: on a good log (potential `0`) it
accepts a node proof whose children are magic proofs (accepted under BLAKE2s only), its knowledge
state opens the root, and the extractor returns nothing for a child: the tree is not extracted to
depth `2`. (Composition is listed as a heuristic v3 does not claim, DESIGN-v3 §5.4.)
-/
import RecursionFast.Explore.Relativized.Defs
import RecursionFast.Controls.Backdoor

open scoped NNReal

namespace RecursionFast.Explore.Relativized

variable {V : Digest → Proof → OProg Bool} {E : Digest → Proof → Log → Option Wit} {ε : ℝ≥0}

/-- **The tree under `(c, π)` is extracted on `L` to depth `d`**: at depth `d + 1` the extractor
opens `(c, π)` on `L` to a leaf witness of the leaf clause, or to a node witness of `c` whose two
children are extracted to depth `d`. -/
def TreeOK (E : Digest → Proof → Log → Option Wit) (L : Log) : ℕ → Digest → Proof → Prop
  | 0, _, _ => True
  | d + 1, c, π => ∃ w, E c π L = some w ∧ RelWith (TreeOK E L d) c w

/-- **Whole-tree extraction from one log**: below potential `1`, every proof `V` accepts on the
log is extracted on that log to every depth. -/
theorem compose (k : KStateRel V E ε) {L : Log} (hL : L.length ≤ logCap) (hμ : k.μ L < 1)
    {c : Digest} {π : Proof} (h : (V c π).runLog L = some true) (d : ℕ) : TreeOK E L d c π := by
  induction d generalizing c π with
  | zero => trivial
  | succ d ih =>
    obtain ⟨w, hE, hw⟩ := k.final L c π hL hμ h
    exact ⟨w, hE, hw.mono ih⟩

open PaperTheorem in
/-- **The whole-tree paper theorem**: the probability that the root verifier accepts on the final
log of a game of at most `n ≤ logCap` queries while the tree is not extracted on that log to every
depth is at most `n · ε`. -/
theorem paper_tree (k : KStateRel V E ε) (G : OProg (Digest × Proof)) (n : ℕ) (hG : DepthLE G n)
    (hn : n ≤ logCap) :
    prob (fun x L => (V x.1 x.2).runLog L = some true ∧ ¬ ∀ d, TreeOK E L d x.1 x.2) G [] ≤
      n * ε :=
  k.paper_of _ (fun _ _ h hl hμ => h.2 (compose k hl hμ h.1)) G n hG hn

/-! ## The flat witness -/

/-- A binary tree of leaf witnesses (chain starts and lengths): the shape of a flat witness. -/
inductive Shape where
  /-- A leaf: a chain start and a chain length. -/
  | leaf (s : Digest) (n : ℕ)
  /-- An inner node over two subtrees. -/
  | node (l r : Shape)

/-- The digest a shape folds to: `leafStmt` of each chain end, combined with `nodeStmt`. -/
def Shape.root : Shape → Digest
  | .leaf s n => leafStmt (chainEnd s n) n
  | .node l r => nodeStmt l.root r.root

/-- The leaf witnesses of a shape, left to right. -/
def Shape.leaves : Shape → List (Digest × ℕ)
  | .leaf s n => [(s, n)]
  | .node l r => l.leaves ++ r.leaves

/-- The shape the extractor's walk from `(c, π)` on `L` reaches within depth `d`, if it ends in
leaves by then. -/
def extract (E : Digest → Proof → Log → Option Wit) (L : Log) : ℕ → Digest → Proof → Option Shape
  | 0, _, _ => none
  | d + 1, c, π =>
    match E c π L with
    | some (.leaf s n) => some (.leaf s n)
    | some (.node c₁ c₂ π₁ π₂) =>
      (extract E L d c₁ π₁).bind fun l => (extract E L d c₂ π₂).map (.node l)
    | none => none

/-- A tree extracted to depth `d` whose walk ends within `d` is a flat witness of its root. -/
theorem extract_root {L : Log} :
    ∀ {d c π t}, TreeOK E L d c π → extract E L d c π = some t →
      t.root = c ∧ ∀ x ∈ t.leaves, x.2 ≤ chainCap
  | 0, _, _, _, _, h => by cases h
  | d + 1, c, π, t, ⟨w, hE, hw⟩, h => by
    simp only [extract, hE] at h
    cases w with
    | leaf s n =>
      cases h
      exact ⟨hw.2.symm, by simp [Shape.leaves, hw.1]⟩
    | node c₁ c₂ π₁ π₂ =>
      obtain ⟨l, hl, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hl1, hl2⟩ := extract_root hw.2.1 hl
      obtain ⟨hr1, hr2⟩ := extract_root hw.2.2 hr
      refine ⟨by rw [Shape.root, hl1, hr1, hw.1], fun x hx => ?_⟩
      rcases List.mem_append.mp hx with hx | hx
      exacts [hl2 x hx, hr2 x hx]

/-- **The flat witness**: below potential `1`, if the extractor's walk from an accepted root ends
in leaves, their `leafStmt`s fold with `nodeStmt` along the walk to the root digest, and every
chain is within `chainCap`. -/
theorem compose_flat (k : KStateRel V E ε) {L : Log} (hL : L.length ≤ logCap) (hμ : k.μ L < 1)
    {c : Digest} {π : Proof} (h : (V c π).runLog L = some true) {d : ℕ} {t : Shape}
    (ht : extract E L d c π = some t) : t.root = c ∧ ∀ x ∈ t.leaves, x.2 ≤ chainCap :=
  extract_root (compose k hL hμ h d) ht

/-! ## v3's knowledge state does not compose -/

namespace V3
open Controls.Backdoor

/-- A digest whose magic proof denotes no witness: its first output word is `0x0202…02`, neither
the leaf tag `0` nor the node tag `1`. -/
def c₀ : Digest := Vector.replicate 32 2

/-- An answer to the backdoor's query other than the deployment value. -/
def a₀ : Digest := if trigger = c₀ then Vector.replicate 32 0 else c₀

/-- The good log: the backdoor's query answered with `a₀`. -/
def L₀ : Log := [(q0, a₀)]

/-- A node proof whose two children are magic proofs of `c₀`. -/
def π₀ : Proof := WitnessSending.encode (.node c₀ c₀ (magic c₀) (magic c₀))

theorem a₀_ne : a₀ ≠ trigger := by
  unfold a₀; split_ifs with h
  · intro h'; rw [← h'] at h; exact absurd (congrArg (·[0]) h) (by decide)
  · exact Ne.symm h

theorem decode_magic : WitnessSending.decode (magic c₀) = none := by
  unfold WitnessSending.decode decodeWit; rfl

/-- **v3's knowledge state does not compose** (the certified backdoor `Controls/Backdoor.lean`):
on a log of potential `0` its verifier accepts a node proof that its knowledge state cannot open
to depth `2`, because the children are accepted under BLAKE2s, not on the log. -/
theorem v3_no_compose :
    L₀.length ≤ logCap ∧ kstate.μ L₀ = 0 ∧
      (Controls.Backdoor.V (nodeStmt c₀ c₀) π₀).runLog L₀ = some true ∧
      ¬ TreeOK WitnessSending.E L₀ 2 (nodeStmt c₀ c₀) π₀ := by
  have hd : WitnessSending.decode π₀ = some (.node c₀ c₀ (magic c₀) (magic c₀)) :=
    WitnessSending.decode_encode _ (by simp [Wit.Fits, magic, proofCap, ByteArray.size])
  refine ⟨by decide, (KState.ofBool_μ_eq_zero _ _ _).mpr ?_, ?_, ?_⟩
  · simp only [boolState, L₀, List.mem_singleton]
    rintro e rfl -; dsimp only; exact a₀_ne
  · have hc : check (nodeStmt c₀ c₀) π₀ = true := by
      unfold check; rw [hd]; simp [π₀, magic, proofCap, ByteArray.size]
    simp [Controls.Backdoor.V, OProg.runLog, L₀, hc]
  · rintro ⟨w, hw, h⟩
    rw [WitnessSending.E, hd, Option.some.injEq] at hw
    subst hw
    obtain ⟨-, ⟨w', hw', -⟩, -⟩ := h
    simp [WitnessSending.E, decode_magic] at hw'

end V3

end RecursionFast.Explore.Relativized
