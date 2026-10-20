/-
# Controls: the certificate (`Contract/Certificate.lean`), positive and negative  (DESIGN-v3 §3.2)

Positive:
* `ws_certificate`: the witness-sending submission (`Library/WitnessSending.lean`) has a
  `Certificate`: every clause (knowledge soundness, completeness with error `0`, the program
  computing the extractor within its fuel, the caps) is proved.
* `ws_certificateR`: and against a claim rendered the way a challenge renders it (both errors `0`,
  no verifier query, fuel `8 · t`).
* `blake2sOracle_kat`: the instantiated oracle on the query `01 02 03` against `hashlib`
  (`BLAKE2s-256(tagRO ‖ q)`; the runner, the native prover and the liveness wrapper reproduce it).

Negative:
* `fuel_low_claim`: a claim of constant fuel 25 is not certified (the declared fuel is a bound the
  submission's fuel must meet); `fuel_over_budget_claim`: a declared fuel above the budget is not
  certified either (the harness runs the program with the declared fuel).
* `rejectAll_no_certificate`: a submission whose verifier rejects everything has no certificate
  (completeness, at any error the cap admits), whatever its other fields.
* `acceptAll_no_certificate`: a submission whose verifier accepts everything and whose extractor
  returns nothing has no certificate (knowledge soundness with the named extractor).
* `error_one_no_certificate`, `delta_one_no_certificate`, `fuel_over_budget_no_certificate`,
  `big_program_no_certificate`: a submission declaring knowledge error `1`, completeness error
  `1`, a fuel of `2^49` steps, or a program of `2^20 + 1` statements has no certificate (the four
  caps).
The claim no longer renders an image literal (V3-S2R-A3), so v2's `flipped_image` control has no
counterpart: the program is the submission's own term, and gate rule 4 requires it computable.
The certificate does **not** exclude a verifier that recognises the deployment oracle: see
`Controls/Backdoor.lean` (O-25).
-/
import RecursionFast.Controls.Security
import RecursionFast.Controls.Blake2s

open scoped NNReal

namespace RecursionFast.Controls.Certificate
open RecursionFast RecursionFast.WitnessSending
open RecursionFast.Controls.Blake2s (hex)

theorem ws_certificate : Certificate submission := certificate

/-- `python3 -I -c "import hashlib; print(hashlib.blake2s(b'R'+bytes([1,2,3])).hexdigest())"` -/
theorem blake2sOracle_kat : (blake2sOracle ⟨#[1, 2, 3]⟩).toList =
    hex "5d32eaa721251d8e473bc410cf953591949de810e935f6e06caa3f8d5ae9cf84" := by decide +kernel

/-- The claim of the witness-sending submission, as a challenge renders it. -/
def declared : Declared where
  ε := 0
  δ := 0
  qV := 0
  fuel t := 8 * t

theorem ws_certificateR : CertificateR declared submission :=
  ⟨certificate, le_rfl, le_rfl, le_rfl, fun t => ⟨le_rfl, by
    simp only [declared, extractorBudget]; omega⟩⟩

theorem fuel_low_claim : ¬ CertificateR { declared with fuel := fun _ => 25 } submission :=
  fun h => absurd (h.bounds.2.2.2 4).1 (by simp [submission, fuel])

theorem fuel_over_budget_claim :
    ¬ CertificateR { declared with fuel := fun _ => 2 ^ 49 } submission :=
  fun h => absurd (h.bounds.2.2.2 0).2 (by simp [extractorBudget])

theorem rejectAll_no_certificate (S : Submission) (hV : S.V = Security.rejectAll) :
    ¬ Certificate S := fun h =>
  Security.rejectAll_not_complete S.Vb S.P
    (h.cap.2.1.trans_lt (pow_lt_one₀ (by positivity) (by norm_num) (by norm_num)))
    (hV ▸ h.complete)

theorem acceptAll_no_certificate (S : Submission) (hV : S.V = acceptAll)
    (hE : S.E = fun _ _ _ => none) : ¬ Certificate S := fun h =>
  (Security.acceptAll_no_kstate_none S.Vb S.ε).false (hV ▸ hE ▸ h.secure.1.some)

theorem error_one_no_certificate (S : Submission) (hε : S.ε = 1) : ¬ Certificate S := fun h =>
  (hε ▸ h.cap.1).not_gt errorCap_lt_one

theorem delta_one_no_certificate (S : Submission) (hδ : S.δ = 1) : ¬ Certificate S := fun h =>
  (hδ ▸ h.cap.2.1).not_gt (pow_lt_one₀ (by positivity) (by norm_num) (by norm_num))

theorem fuel_over_budget_no_certificate (S : Submission) (hf : S.fuel = fun _ => 2 ^ 49) :
    ¬ Certificate S := fun h => absurd (hf ▸ h.cap.2.2.2.1 0) (by simp [extractorBudget])

/-- `n + 1` constant statements in a row: `2n + 1` statements in all. -/
def rep : ℕ → XStmt
  | 0 => .const 0 0
  | n + 1 => .seq (.const 0 0) (rep n)

theorem size_rep (n : ℕ) : (rep n).size = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep, XStmt.size, ih]; omega

theorem big_program_no_certificate (S : Submission) (hp : S.ext.body = rep (2 ^ 19)) :
    ¬ Certificate S := fun h => by
  have := h.cap.2.2.2.2
  rw [hp, size_rep, progCap] at this
  omega

end RecursionFast.Controls.Certificate
