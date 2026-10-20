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

What the certificate does not say (V3-S2R review, probes P3 and P4; kept as controls):
* `vb_rejects_all_certified`: a certified submission whose instantiated verifier `Vb` accepts
  nothing. Completeness is about `V` over a random oracle, not about `Vb` (V3-S2R-m1): `V` accepts
  only proofs longer than `proofCap`, which `Vb` rejects. The harness's root check rejects such an
  entry; the certificate does not.
* `choice_certificate`: the witness-sending submission stays certified when its extractor
  specification is a `Classical.choose` of a witness on tapes beyond the `Computes` domain
  (V3-S2R-m2): efficient extraction is claimed only on the domain, `KS` up to `logCap`.
-/
import RecursionFast.Controls.Security
import RecursionFast.Controls.Blake2s
import RecursionFast.Controls.Extractor

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

/-! ## What the certificate does not exclude -/

open Classical in
/-- The witness-sending extractor on the `Computes` domain, a chosen witness beyond it. -/
noncomputable def Echoice (c : Digest) (π : Proof) (L : Log) : Option Wit :=
  if (extractorInput c π L).length ≤ 2 ^ 64 then decode π
  else if h : ∃ w, Rel submission.Vb c w then some (Classical.choose h) else none

/-- The witness-sending submission with that specification. -/
noncomputable def Schoice : Submission := { submission with E := Echoice }

/-- **Beyond the domain the named extractor may be a non-constructive choice.** -/
theorem choice_certificate : Certificate Schoice where
  secure := ⟨⟨KState.zero 0 fun L c π h => by
      have hc : check c π = true := Option.some.inj h
      obtain ⟨w, hd, hR⟩ := check_sound hc
      show ∃ w, Echoice c π L = some w ∧ _
      unfold Echoice
      split
      · exact ⟨w, hd, hR⟩
      · have hw : ∃ w, Rel submission.Vb c w := ⟨w, hR⟩
        simp only [hw, ↓reduceDIte]
        exact ⟨_, rfl, Classical.choose_spec hw⟩⟩,
    fun _ _ _ => le_rfl⟩
  complete := complete
  computes := fun c π L hπ hq ht => by
    obtain ⟨o, ho, hl, hd⟩ := computes c π L hπ hq ht
    exact ⟨o, ho, hl, by rw [hd]; show decode π = Echoice c π L; simp [Echoice, ht]⟩
  cap := certificate.cap

/-- `proofCap + 1` zero bytes. -/
def pad : List UInt8 := List.replicate (proofCap + 1) 0

/-- The bytes after the pad. -/
def strip (π : Proof) : Proof := ⟨(π.data.toList.drop (proofCap + 1)).toArray⟩

/-- Whether a decoded witness is a leaf. -/
def isLeaf : Option Wit → Bool
  | some (.leaf _ _) => true
  | _ => false

/-- Accept only proofs **longer than `proofCap`**: the pad, then a leaf's witness-sending proof. -/
def Vbig (c : Digest) (π : Proof) : OProg Bool :=
  .ret (decide (proofCap < π.size) && isLeaf (decode (strip π)) && check c (strip π))

/-- Pad the witness-sending proof. -/
def Pbig (_ : Digest) (w : Wit) : OProg Proof := .ret ⟨(pad ++ (encode w).data.toList).toArray⟩

/-- The submission whose `V` accepts only padded leaf proofs, with the one-statement program. -/
def Sbig : Submission where
  V := Vbig
  P := Pbig
  E _ π _ := decode (strip π)
  ext := Controls.Extractor.haltProg
  ε := 0
  δ := 0
  qV := 0
  fuel _ := 1

theorem Vb_false (c : Digest) (π : Proof) : Sbig.Vb c π = false := by
  unfold Submission.Vb
  split
  · simp only [Sbig, Vbig, OProg.run]
    simp [show ¬ proofCap < π.size by omega]
  · rfl

theorem strip_small {π : Proof} (h : π.size ≤ proofCap) : strip π = ⟨#[]⟩ := by
  unfold strip
  rw [List.drop_eq_nil_of_le (by rw [Array.length_toList]; exact Nat.le_succ_of_le h)]

theorem pad_length : pad.length = proofCap + 1 := List.length_replicate

theorem strip_pad (b : List UInt8) : strip ⟨(pad ++ b).toArray⟩ = ⟨b.toArray⟩ := by
  unfold strip
  rw [List.drop_left' pad_length]

theorem big_secure : KS (Rel Sbig.Vb) Sbig.V Sbig.E Sbig.ε Sbig.qV :=
  ⟨⟨KState.zero 0 fun L c π h => by
      have hc : (decide (proofCap < π.size) && isLeaf (decode (strip π)) &&
          check c (strip π)) = true := Option.some.inj h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨-, hl⟩, hc⟩ := hc
      obtain ⟨w, hd, hR⟩ := check_sound hc
      refine ⟨w, hd, ?_⟩
      rw [hd] at hl
      cases w with
      | leaf s n => exact hR
      | node => cases hl⟩,
    fun _ _ _ => le_rfl⟩

theorem big_computes : Computes Sbig.ext Sbig.E Sbig.fuel := fun c π L hπ _ _ =>
  ⟨[], Controls.Extractor.halt_run _ 0, by decide, by
    show none = decode (strip π); rw [strip_small hπ]; decide +kernel⟩

theorem Vbig_leaf (c s : Digest) (n : ℕ) (hR : Rel Sbig.Vb c (.leaf s n)) :
    Vbig c ⟨(pad ++ (encode (.leaf s n)).data.toList).toArray⟩ = .ret true := by
  have hn : n < 2 ^ 64 := lt_of_le_of_lt hR.1 (by decide)
  have hsz : proofCap < (⟨(pad ++ (encode (.leaf s n)).data.toList).toArray⟩ : Proof).size := by
    show proofCap < (pad ++ _).toArray.size
    rw [List.size_toArray, List.length_append, pad_length]; omega
  have hck : check c (encode (.leaf s n)) = true := by
    have hR' : n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n := hR
    rw [check_leaf c s hn]; simp [hR'.1, ← hR'.2]
  unfold Vbig
  rw [strip_pad, show (⟨(encode (.leaf s n)).data.toList.toArray⟩ : Proof) = encode (.leaf s n) by
    simp, decode_encode (.leaf s n) hn, hck, decide_eq_true hsz]
  rfl

theorem big_complete : CompleteWithError (Rel Sbig.Vb) Sbig.P Sbig.V Sbig.δ := fun c w hR => by
  cases w with
  | node c₁ c₂ π₁ π₂ => exact absurd hR.2.1 (by rw [Vb_false]; simp)
  | leaf s n =>
    show failProb ((Pbig c (.leaf s n)).bind (Vbig c)) [] ≤ 0
    rw [Pbig, OProg.bind, Vbig_leaf c s n hR]
    simp [failProb]

/-- **A certified submission whose instantiated verifier accepts nothing** (V3-S2R-m1). -/
theorem vb_rejects_all_certified : Certificate Sbig ∧ ∀ c π, Sbig.Vb c π = false :=
  ⟨⟨big_secure, big_complete, big_computes, ⟨zero_le, zero_le, Nat.zero_le _, fun t => by
    show 1 ≤ _; simp only [extractorBudget]; omega, by decide⟩⟩, Vb_false⟩

end RecursionFast.Controls.Certificate
