/-
  RecursionFast.Library.Completeness  (UNTRUSTED, kernel-checked; unchanged from v3)

  Facts about completeness with error (`Contract/Security.lean`, V3-S2R-A2).

  * `Complete`: perfect completeness over every oracle function, S1's contract definition, moved
    here. **`complete_withError_zero`**: it implies `CompleteWithError` at `δ = 0`, so every
    perfectly complete argument ports with `δ := 0`.
  * `failProb_eq_zero_of_run`: a program that returns `true` under every oracle function
    consistent with the table fails with probability `0`.
  * `failProb_le_one`, `CompleteWithError.mono`, `avg_const`.
  * `failProb_bind_false`: a verifier that rejects fails with probability `1`, whatever the
    prover asks.
  * `failProb_eq_prob`: `failProb` is the lazy-sampling probability `PaperTheorem.prob` of a
    `false` result, so "uniformly random oracle" is one notion in the repository.
-/
import RecursionFast.Library.PaperTheorem
import RecursionFast.Library.Oracle

open scoped NNReal

namespace RecursionFast

/-- **Perfect completeness** over every oracle function: on every statement and witness in `R`,
the verifier accepts the honest prover's proof. -/
def Complete (R : Digest → Wit → Prop) (P : Digest → Wit → OProg Proof)
    (V : Digest → Proof → OProg Bool) : Prop :=
  ∀ (H : ByteArray → Digest) c w, R c w → (V c ((P c w).run H)).run H = true

/-- The oracle function `H` agrees with the table `L` (read by first match). -/
def Consistent (H : ByteArray → Digest) (L : Log) : Prop :=
  ∀ q e, L.find? (fun e => e.1 = q) = some e → H q = e.2

theorem exists_consistent (L : Log) : ∃ H, Consistent H L :=
  ⟨fun q => ((L.find? fun e => e.1 = q).map Prod.snd).getD (Vector.replicate 32 0),
    fun _ _ h => by simp [h]⟩

theorem consistent_append {H : ByteArray → Digest} {L : Log} {q : ByteArray} {a : Digest}
    (hf : L.find? (fun e => e.1 = q) = none) (h : Consistent H (L ++ [(q, a)])) :
    Consistent H L ∧ H q = a :=
  ⟨fun q' e he => h q' e (by simp [List.find?_append, he]),
    h q (q, a) (by simp [List.find?_append, hf])⟩

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
  fun c w hR => le_of_eq (failProb_eq_zero_of_run _ _ fun H _ =>
    (OProg.run_bind _ _ _).trans (h H c w hR))

theorem CompleteWithError.mono {R : Digest → Wit → Prop} {P : Digest → Wit → OProg Proof}
    {V : Digest → Proof → OProg Bool} {δ δ' : ℝ≥0} (h : CompleteWithError R P V δ)
    (hδ : δ ≤ δ') : CompleteWithError R P V δ' := fun c w hR => (h c w hR).trans hδ

/-- `failProb` is the lazy-sampling probability of a `false` result. -/
theorem failProb_eq_prob : ∀ (p : OProg Bool) (L : Log),
    failProb p L = PaperTheorem.prob (fun b _ => b = false) p L
  | .ret b, L => by cases b <;> simp [failProb, PaperTheorem.prob]
  | .query q k, L => by
    simp only [failProb, PaperTheorem.prob]
    cases L.find? fun e => decide (e.1 = q) with
    | some e => exact failProb_eq_prob _ _
    | none => simp only [failProb_eq_prob]

theorem failProb_le_one (p : OProg Bool) (L : Log) : failProb p L ≤ 1 :=
  (failProb_eq_prob p L).trans_le (PaperTheorem.prob_le_one _ p L)

/-- The average of a constant over the `2^256` answers. -/
theorem avg_const (x : ℝ≥0) : ((2 : ℝ≥0) ^ 256)⁻¹ * ∑ _a : Digest, x = x := by
  rw [Finset.sum_const, Finset.card_univ, fintype_card_digest, nsmul_eq_mul, Nat.cast_pow,
    Nat.cast_ofNat, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- **Rejecting fails with probability `1`**, whatever the program run before. -/
theorem failProb_bind_false {α : Type} : ∀ (p : OProg α) (L : Log),
    failProb (p.bind fun _ => .ret false) L = 1
  | .ret _, _ => by simp [OProg.bind, failProb]
  | .query q k, L => by
    simp only [OProg.bind, failProb]
    split
    · exact failProb_bind_false _ _
    · simp only [failProb_bind_false, avg_const]

end RecursionFast
