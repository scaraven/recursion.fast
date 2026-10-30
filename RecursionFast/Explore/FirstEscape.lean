import RecursionFast.Library.Compose

/-! Probe (audit, literature.md): CGSY24 Thm 5.1's "first failing vertex" adversary removes the
factor `|P|` from `escape_prob_le`: one `KS.select` with a selector that picks an escaping member
when one exists. -/

open scoped NNReal
namespace RecursionFast.Compose
open RecursionFast
variable {S : Submission} {vk : Digest} {ε : ℝ≥0} {qV : ℕ}

open Classical in
/-- Every path set, one KS application: no factor `|P|`. -/
theorem escape_prob_le_first (hks : KS (Rel (S.acc vk)) (S.V vk) S.E ε qV) (c₀ : Digest)
    (A : OProg Signed) {Q : ℕ} (hA : ∀ H, (A.queries H).length ≤ Q) (hQ : Q + qV ≤ logCap)
    (P : Finset (List Bool)) :
    prob (fun p L => ∃ bs ∈ P, ∃ c q, InTree S L c₀ p bs c q ∧ Escape S vk L c q) A [] ≤
      (Q + qV) * ε := by
  let W : Signed → Log → List Bool → Prop := fun p L bs =>
    bs ∈ P ∧ Wins (Rel (S.acc vk)) (S.V vk) S.E (memberAt S c₀ bs p L) L
  let sel : Signed → Log → Digest × Proof := fun p L =>
    if h : ∃ bs, W p L bs then memberAt S c₀ h.choose p L else (c₀, p.π)
  refine (prob_mono_of_inv Log.Functional (fun _ _ _ => functional_append)
    (B' := fun p L => Wins (Rel (S.acc vk)) (S.V vk) S.E (sel p L) L)
    (fun p L hL ⟨bs, hbs, c, q, hmem, he⟩ => ?_) A
    (fun _ h => absurd h List.not_mem_nil)).trans (hks.select A hA hQ sel)
  have hW : ∃ bs, W p L bs := ⟨bs, hbs, by simp only [memberAt, hmem.follow_eq]; exact he.wins hL⟩
  simp only [sel, dite_cond_eq_true (eq_true hW)]
  exact hW.choose_spec.2

end RecursionFast.Compose
#print axioms RecursionFast.Compose.escape_prob_le_first
