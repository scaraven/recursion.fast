/-
# Exploration: whole-tree extraction from one attested log                         (UNTRUSTED)

Probe P2, item 3 (`docs/explore/notes/W2-attested-oracle.md` §A.6). P1's `compose` with the
collision disjunct. Below potential `1`, on a well-formed log, `final` opens an accepted proof to
a sound output. A node witness's children are accepted on the **same** log, so `final` applies to
them with the same hypotheses, and so on down. Each opening either gives a witness, and the walk
continues, or gives a list-hash collision, and the walk stops with it.

* `TreeOKA E L d c π`: the extractor opens `(c, π)` on `L` to witnesses to depth `d` (P1's
  `TreeOK` with the witness wrapped in `Out.wit`).
* `collAt E L d c π`: the first collision (left to right) the extractor's walk from `(c, π)` on
  `L` returns within depth `d`, or `none`. A computable walk: the collision is a value.
* **`compose`**: below potential `1` on a well-formed log, for every accepted proof and every
  depth `d`, either the walk finds no collision within `d` and the tree is extracted to depth `d`,
  or the walk returns a pair `(x, y)` with `IsColl x y` (a BLAKE2s collision, `IsColl.blake2s`).
* **`compose_all`**: either the tree is extracted to every depth, or at some depth the walk
  returns a collision.

As in P1, there is one log and one potential for the whole tree, so the error of one application
of the paper theorem covers every level. The kernel-checked paper theorem
(`Library/PaperTheorem.lean`) is for contract games, which have no certification moves; its
extension to games with `certify` (W2 §A.6: the moves do not raise the potential) is not done here.
-/
import RecursionFast.Explore.Attested.KState

open scoped NNReal

namespace RecursionFast.Explore.Attested

open Relativized

variable {V : Digest → Proof → AProg Bool} {E : Digest → Proof → ALog → Option Out} {ε : ℝ≥0}

/-- **The tree under `(c, π)` is extracted on `L` to depth `d`**: at depth `d + 1` the extractor
opens `(c, π)` to a witness that is a leaf witness, or a node witness of `c` whose children are
extracted to depth `d`. -/
def TreeOKA (E : Digest → Proof → ALog → Option Out) (L : ALog) : ℕ → Digest → Proof → Prop
  | 0, _, _ => True
  | d + 1, c, π => ∃ w, E c π L = some (.wit w) ∧ RelWith (TreeOKA E L d) c w

/-- **The first collision of the extractor's walk** from `(c, π)` on `L` within depth `d`: the
pair of a `coll` output, else the first collision under the left child of a node witness, else
under the right child. -/
def collAt (E : Digest → Proof → ALog → Option Out) (L : ALog) :
    ℕ → Digest → Proof → Option (List Item × List Item)
  | 0, _, _ => none
  | d + 1, c, π =>
    match E c π L with
    | some (.coll x y) => some (x, y)
    | some (.wit (.node c₁ c₂ π₁ π₂)) => (collAt E L d c₁ π₁).or (collAt E L d c₂ π₂)
    | _ => none

/-- **Whole-tree extraction from one log, with collisions**: below potential `1` on a
well-formed log, the walk from an accepted proof either finds no collision within depth `d` and
the tree is extracted to depth `d`, or it returns a list-hash collision. -/
theorem compose (k : KStateA V E ε) {L : ALog} (hW : WF L) (hL : L.length ≤ logCap)
    (hμ : k.μ L < 1) {c : Digest} {π : Proof} (h : (V c π).runLog L = some true) (d : ℕ) :
    (collAt E L d c π = none ∧ TreeOKA E L d c π) ∨
      ∃ x y, collAt E L d c π = some (x, y) ∧ IsColl x y := by
  induction d generalizing c π with
  | zero => exact .inl ⟨rfl, trivial⟩
  | succ d ih =>
    obtain ⟨o, hE, hS⟩ := k.final L c π hW hL hμ h
    cases o with
    | coll x y => exact .inr ⟨x, y, by simp [collAt, hE], hS⟩
    | wit w =>
      cases w with
      | leaf s n => exact .inl ⟨by simp [collAt, hE], _, hE, hS⟩
      | node c₁ c₂ π₁ π₂ =>
        obtain ⟨hc, h₁, h₂⟩ := hS
        rcases ih h₁ with ⟨n₁, t₁⟩ | ⟨x, y, e₁, hxy⟩
        · rcases ih h₂ with ⟨n₂, t₂⟩ | ⟨x, y, e₂, hxy⟩
          · exact .inl ⟨by simp [collAt, hE, n₁, n₂], _, hE, hc, t₁, t₂⟩
          · exact .inr ⟨x, y, by simp [collAt, hE, n₁, e₂], hxy⟩
        · exact .inr ⟨x, y, by simp [collAt, hE, e₁], hxy⟩

/-- **Every depth**: below potential `1` on a well-formed log, an accepted proof's tree is
extracted to every depth, or the walk returns a list-hash collision at some depth. -/
theorem compose_all (k : KStateA V E ε) {L : ALog} (hW : WF L) (hL : L.length ≤ logCap)
    (hμ : k.μ L < 1) {c : Digest} {π : Proof} (h : (V c π).runLog L = some true) :
    (∀ d, TreeOKA E L d c π) ∨ ∃ d x y, collAt E L d c π = some (x, y) ∧ IsColl x y := by
  by_cases hc : ∃ d x y, collAt E L d c π = some (x, y)
  · obtain ⟨d, x, y, hd⟩ := hc
    rcases compose k hW hL hμ h d with ⟨hn, -⟩ | ⟨x', y', hd', hxy⟩
    · simp [hn] at hd
    · exact .inr ⟨d, x', y', hd', hxy⟩
  · refine .inl fun d => ?_
    rcases compose k hW hL hμ h d with ⟨-, ht⟩ | ⟨x, y, hd, -⟩
    · exact ht
    · exact absurd ⟨d, x, y, hd⟩ hc

/-- The collision `compose` returns is a BLAKE2s collision between distinct byte strings. -/
theorem compose_blake2s (k : KStateA V E ε) {L : ALog} (hW : WF L) (hL : L.length ≤ logCap)
    (hμ : k.μ L < 1) {c : Digest} {π : Proof} (h : (V c π).runLog L = some true) {d : ℕ}
    {x y : List Item} (hd : collAt E L d c π = some (x, y)) :
    tagList :: encList x ≠ tagList :: encList y ∧
      blake2s256 (tagList :: encList x) = blake2s256 (tagList :: encList y) := by
  rcases compose k hW hL hμ h d with ⟨hn, -⟩ | ⟨x', y', hd', hxy⟩
  · simp [hn] at hd
  · rw [hd, Option.some.injEq, Prod.mk.injEq] at hd'
    obtain ⟨rfl, rfl⟩ := hd'
    exact hxy.blake2s

end RecursionFast.Explore.Attested
