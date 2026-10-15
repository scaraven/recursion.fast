/-
S5 review probe (item 2): `live` and `complete` exclude a constant (or finitely-valued) decoder,
for every protocol. From one accepted node, any accepted child `(K₁, x₁, π₁)` makes, with *every*
recursion key `V` that has a 32-byte root, an accepted two-leaf node (`vkC` of a two-leaf node is
constrained only by its digest). `complete` must decode each of them from a witness of `C`.
-/
import RecursionFast.Library.Recursion

namespace RecursionFast.Probes.S5Review
open RecursionFast

variable (cfg : Cfg) {k : ℕ} (P : Protocol k)

/-- An accepted node has an accepted child proof under one of its keys. -/
theorem accepted_child {x' : Stmt} {nw : NodeWitness P.vkLen} (h : aggOK cfg P x' nw = true) :
    ∃ K₁ x₁ π₁, NARG cfg P K₁ x₁ π₁ = true := by
  obtain ⟨-, -, -, -, -, -, hn, hl, -⟩ := (aggOK_iff cfg P x' nw).mp h
  cases ht : nw.t₁
  · exact ⟨_, _, _, hl ht⟩
  · exact ⟨_, _, _, (hn ht).2.2⟩

/-- **The family**: one accepted node gives an accepted two-leaf node for every recursion key. -/
theorem live_family (hlive : ∃ x' nw, aggOK cfg P x' nw = true) :
    ∃ K₁ x₁ π₁, ∀ V : VKc P.vkLen, V.2.length = 32 →
      aggOK cfg P (nodeStmt cfg V K₁ x₁ x₁) ⟨V, K₁, .leaf, .leaf, x₁, x₁, π₁, π₁⟩ = true := by
  obtain ⟨x', nw, h⟩ := hlive
  obtain ⟨K₁, x₁, π₁, hK⟩ := accepted_child cfg P h
  exact ⟨K₁, x₁, π₁, fun V hV => aggOK_leaves cfg P V K₁ hV x₁ x₁ π₁ π₁ hK hK⟩

/-- **No recursion entry has a constant decoder.** -/
theorem decode_not_const (e : RecursionEntry P cfg) : ¬ ∃ nw₀, ∀ w, e.decode w = nw₀ := by
  rintro ⟨nw₀, hc⟩
  obtain ⟨K₁, x₁, π₁, hf⟩ := live_family cfg P e.live
  let V : Bool → VKc P.vkLen := fun b => (fun _ => 0, List.replicate 32 (if b then 1 else 0))
  have hV : ∀ b, (V b).2.length = 32 := fun b => by simp [V]
  obtain ⟨w₀, -, h₀⟩ := e.complete _ _ (hf (V false) (hV false))
  obtain ⟨w₁, -, h₁⟩ := e.complete _ _ (hf (V true) (hV true))
  have : V false = V true := by
    simpa using congrArg NodeWitness.vkC (((hc w₀).symm.trans h₀).symm.trans ((hc w₁).symm.trans h₁))
  simp [V] at this

end RecursionFast.Probes.S5Review

#print axioms RecursionFast.Probes.S5Review.decode_not_const
