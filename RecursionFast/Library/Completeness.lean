/-
  RecursionFast.Library.Completeness  (UNTRUSTED, kernel-checked)

  Facts about completeness with error (`Contract/Security.lean`, V3-S2R-A2).

  * `failProb`: v3's contract definition of the probability that a program returns `false`
    against a lazily sampled oracle, moved here when the contract stated `CompleteWithError`
    through `prob` (V4-A10). **`failProb_eq_prob`**: it is `prob` of a `false` result, so
    `completeWithError_iff`: `CompleteWithError` means what v3's text said, word for word.
  * `Complete`: perfect completeness over every oracle function, S1's contract definition, moved
    here. **`complete_withError_zero`**: it implies `CompleteWithError` at `δ = 0`, so every
    perfectly complete argument ports with `δ := 0`.
  * `failProb_eq_zero_of_run`: a program that returns `true` under every oracle function
    consistent with the table fails with probability `0`.
  * `failProb_le_one`, `CompleteWithError.mono`.
  * `failProb_bind_false`: a verifier that rejects fails with probability `1`, whatever the
    prover asks.
-/
import RecursionFast.Library.Prob

open scoped NNReal

namespace RecursionFast

/-- The probability that `p` returns `false` when each query not in the table `L` is answered
uniformly at random and recorded, and a repeated query is answered from the table (first match):
a lazily sampled random oracle. -/
noncomputable def failProb : OProg Bool → Log → ℝ≥0
  | .ret b, _ => if b then 0 else 1
  | .query q k, L => match L.find? fun e => e.1 = q with
    | some e => failProb (k e.2) L
    | none => (2 ^ 256)⁻¹ * ∑ a : Digest, failProb (k a) (L ++ [(q, a)])

/-- `failProb` is the lazy-sampling probability of a `false` result. -/
theorem failProb_eq_prob : ∀ (p : OProg Bool) (L : Log),
    failProb p L = prob (fun b _ => b = false) p L
  | .ret b, L => by cases b <;> simp [failProb, prob]
  | .query q k, L => by
    simp only [failProb, prob]
    cases L.find? fun e => decide (e.1 = q) with
    | some e => exact failProb_eq_prob _ _
    | none => simp only [failProb_eq_prob]

/-- **`CompleteWithError` is v3's statement**: the honest prover's proof, produced and verified
against one random oracle, fails with probability (`failProb`) at most `δ`. -/
theorem completeWithError_iff {R : Digest → Wit → Prop} {P : Digest → Wit → OProg Proof}
    {V : Digest → Proof → OProg Bool} {δ : ℝ≥0} :
    CompleteWithError R P V δ ↔ ∀ c w, R c w → failProb ((P c w).bind (V c)) [] ≤ δ := by
  simp only [CompleteWithError, failProb_eq_prob]

/-- **Perfect completeness** over every oracle function: on every statement and witness in `R`,
the verifier accepts the honest prover's proof. -/
def Complete (R : Digest → Wit → Prop) (P : Digest → Wit → OProg Proof)
    (V : Digest → Proof → OProg Bool) : Prop :=
  ∀ (H : ByteArray → Digest) c w, R c w → (V c ((P c w).run H)).run H = true

/-- **A program that returns `true` under every oracle consistent with the table fails with
probability `0`.** -/
theorem failProb_eq_zero_of_run : ∀ (p : OProg Bool) (L : Log),
    (∀ H, Consistent H L → p.run H = true) → failProb p L = 0
  | .ret b, L, h => by
    obtain ⟨H, hH⟩ := exists_consistent L
    have : b = true := h H hH
    simp [failProb, this]
  | .query q k, L, h => by
    simp only [failProb]
    split
    · rename_i e he
      exact failProb_eq_zero_of_run _ L fun H hH => hH q e he ▸ h H hH
    · rename_i hf
      rw [Finset.sum_eq_zero fun a _ => failProb_eq_zero_of_run _ _ fun H hH =>
        (consistent_append hf hH).elim fun hL hq => hq ▸ h H hL]
      simp

/-- **Perfect completeness is completeness with error `0`.** -/
theorem complete_withError_zero {R : Digest → Wit → Prop} {P : Digest → Wit → OProg Proof}
    {V : Digest → Proof → OProg Bool} (h : Complete R P V) : CompleteWithError R P V 0 :=
  completeWithError_iff.mpr fun c w hR => le_of_eq (failProb_eq_zero_of_run _ _ fun H _ =>
    (OProg.run_bind _ _ _).trans (h H c w hR))

theorem CompleteWithError.mono {R : Digest → Wit → Prop} {P : Digest → Wit → OProg Proof}
    {V : Digest → Proof → OProg Bool} {δ δ' : ℝ≥0} (h : CompleteWithError R P V δ)
    (hδ : δ ≤ δ') : CompleteWithError R P V δ' := fun c w hR => (h c w hR).trans hδ

theorem failProb_le_one (p : OProg Bool) (L : Log) : failProb p L ≤ 1 :=
  (failProb_eq_prob p L).trans_le (prob_le_one _ p L)

/-- **Rejecting fails with probability `1`**, whatever the program run before. -/
theorem failProb_bind_false {α : Type} : ∀ (p : OProg α) (L : Log),
    failProb (p.bind fun _ => .ret false) L = 1 := fun p L => by
  rw [failProb_eq_prob, prob_bind, ← expect_const 1 p L]
  exact congrArg (expect · p L) (funext₂ fun _ _ => (prob_ret _ _ _).trans (ind_of rfl))

end RecursionFast
