/-
# Controls: the certificate (`Contract/Certificate.lean`), positive and negative (V4-1, V4-7)

Positive:
* `ws_certificate`: the witness-sending submission (`Library/WitnessSending.lean`) has a
  `Certificate`: knowledge soundness and completeness with error `0` **under every public key**,
  the program computing the extractor within its fuel, the caps.
* `ws_certificateR`: and against a claim rendered the way a challenge renders it (both errors `0`,
  no verifier query, fuel `8 · t`).
* `ws_acc_leaf`: the certified submission's `acc` accepts an honest signed leaf proof under the
  reference signer's key (`Controls/Relation.lean`), so the harness's check is satisfiable too.

Negative:
* `fuel_low_claim`, `fuel_over_budget_claim`: claims the submission does not meet, or that exceed
  the budget, are not certified (v3).
* `rejectAll_no_certificate`, `acceptAll_no_certificate`, `error_one_no_certificate`,
  `delta_one_no_certificate`, `fuel_over_budget_no_certificate`, `big_program_no_certificate`:
  v3's, with the verifier now a function of the key.
* **The `∀ vk` (V4-1, C-m1)**: `sigTrust_no_certificate`: a submission whose verifier accepts any
  proof carrying a signature of the statement valid under `vk` (`Library/SigTrust.lean`'s `Vsig`),
  with an extractor that returns nothing, is **not certified**: the certificate's key quantifier
  reaches `Signer.pk sk`, under which anyone signs every statement. With any extractor,
  `sigTrust_certificate_opens`: a certificate would make the extractor open the signature of every
  statement, on the empty log, to a witness of the relation. **Why the quantifier is what does
  it**: `sigTrust_ks_unsignable` (the same verifier is knowledge-sound at error `0` under any key
  for which no signature verifies), so a certificate stated for one key could not exclude it.
  That no such key can be exhibited (it would need a digest outside the image of a BLAKE2s
  tree) is why the twin is stated for every such key rather than for one.
* The certificate does **not** exclude a verifier that recognises a public function of the
  oracle (`Controls/Backdoor.lean`); the deployment does (V4-2).

What the certificate does not say (v3's, kept):
* `acc_rejects_all_certified`: a certified submission whose `acc` accepts nothing: `V` accepts
  only proofs longer than `proofCap`, which `acc` rejects. Completeness is about `V` over a random
  oracle, not about `acc` (V3-S2R-m1); the harness's root check rejects such an entry.
* `choice_certificate`: the witness-sending submission stays certified when its extractor
  specification is a `Classical.choose` on tapes beyond the `Computes` domain (V3-S2R-m2).
-/
import RecursionFast.Controls.Security
import RecursionFast.Controls.Extractor
import RecursionFast.Controls.Relation
import RecursionFast.Library.SigTrust

open scoped NNReal

namespace RecursionFast.Controls.Certificate
open RecursionFast RecursionFast.WitnessSending

theorem ws_certificate : Certificate submission := certificate

/-- The claim of the witness-sending submission, as a challenge renders it. -/
def declared : Declared where
  ε := 0
  δ := 0
  qV := 0
  fuel t := 8 * t

theorem ws_certificateR : CertificateR declared submission :=
  ⟨certificate, le_rfl, le_rfl, le_rfl, fun t => ⟨le_rfl, certificate.cap.2.2.2.1 t⟩⟩

theorem ws_acc_leaf (seed : List UInt8) (s : Digest) {n : ℕ} (hn : n ≤ chainCap) :
    submission.acc (Signer.pk (Signer.chainStart seed)) (leafStmt (chainEnd s n) n)
      (Controls.Relation.leafSigned (Signer.chainStart seed) 0 s n) = true :=
  Controls.Relation.acc_leafSigned _ (by decide) s hn

theorem fuel_low_claim : ¬ CertificateR { declared with fuel := fun _ => 25 } submission :=
  fun h => absurd (h.bounds.2.2.2 4).1 (by decide)

theorem fuel_over_budget_claim :
    ¬ CertificateR { declared with fuel := fun _ => 2 ^ 49 } submission :=
  fun h => absurd (h.bounds.2.2.2 0).2 (by decide)

theorem rejectAll_no_certificate (S : Submission) (hV : ∀ vk, S.V vk = Security.rejectAll) :
    ¬ Certificate S := fun h =>
  Security.rejectAll_not_complete (S.acc 0) (S.P 0)
    (h.cap.2.1.trans_lt (pow_lt_one₀ (by positivity) (by norm_num) (by norm_num)))
    (hV 0 ▸ h.complete 0)

theorem acceptAll_no_certificate (S : Submission) (hV : ∀ vk, S.V vk = acceptAll)
    (hE : S.E = fun _ _ _ => none) : ¬ Certificate S := fun h =>
  (Security.acceptAll_no_kstate_none (S.acc 0) S.ε).false (hV 0 ▸ hE ▸ (h.secure 0).1.some)

theorem error_one_no_certificate (S : Submission) (hε : S.ε = 1) : ¬ Certificate S := fun h =>
  (hε ▸ h.cap.1).not_gt errorCap_lt_one

theorem delta_one_no_certificate (S : Submission) (hδ : S.δ = 1) : ¬ Certificate S := fun h =>
  (hδ ▸ h.cap.2.1).not_gt (pow_lt_one₀ (by positivity) (by norm_num) (by norm_num))

theorem fuel_over_budget_no_certificate (S : Submission) (hf : S.fuel = fun _ => 2 ^ 49) :
    ¬ Certificate S := fun h => absurd (hf ▸ h.cap.2.2.2.1 0) (by decide)

/-- `n + 1` constant statements in a row: `2n + 1` statements in all. -/
def rep : ℕ → XStmt
  | 0 => .const 0 0
  | n + 1 => .seq (.const 0 0) (rep n)

theorem size_rep (n : ℕ) : (rep n).size = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep, XStmt.size, ih]; omega

theorem big_program_no_certificate (S : Submission) (hp : S.ext.body = rep (2 ^ 19)) :
    ¬ Certificate S := fun h => absurd (size_rep _ ▸ hp ▸ h.cap.2.2.2.2) (by decide)

/-! ## The key quantifier: no certified verifier trusts a signature (C-m1) -/

/-- **A verifier that trusts `vk`-valid signatures is not certified** with an extractor that
returns nothing: the certificate's `∀ vk` reaches the key of a known signer. -/
theorem sigTrust_no_certificate (S : Submission) (hV : ∀ vk, S.V vk = SigTrust.Vsig vk)
    (hE : S.E = fun _ _ _ => none) : ¬ Certificate S := fun h =>
  (SigTrust.sigTrust_no_kstate_none (fun _ _ => 0) _ _).false (hV _ ▸ hE ▸ (h.secure _).1.some)

/-- With any extractor, a certificate would open every statement's signature, on the empty log,
to a witness of the relation. -/
theorem sigTrust_certificate_opens (S : Submission) (hV : ∀ vk, S.V vk = SigTrust.Vsig vk)
    (h : Certificate S) (sk : ℕ → ℕ → Digest) (c : Digest) :
    ∃ w, S.E c (SigTrust.sigProof (Signer.sign sk 0 c)) [] = some w ∧
      Rel (S.acc (Signer.pk sk)) c w :=
  SigTrust.sigTrust_extracts sk (hV _ ▸ (h.secure (Signer.pk sk)).1.some) c

/-- **The twin**: under a key for which no signature verifies, the signature-trusting verifier
is knowledge-sound for the relation of every `acc` and every extractor. -/
theorem sigTrust_ks_unsignable {vk : Digest} (hvk : ∀ m σ, SigOk vk m σ = false)
    (acc : Digest → Signed → Bool) (E : Digest → Proof → Log → Option Wit) :
    KS (Rel acc) (SigTrust.Vsig vk) E 0 0 :=
  SigTrust.sigTrust_ks_of_unsignable hvk _ E

/-! ## What the certificate does not exclude -/

open Classical in
/-- The witness-sending extractor on the `Computes` domain, a chosen witness beyond it. -/
noncomputable def Echoice (c : Digest) (π : Proof) (L : Log) : Option Wit :=
  if (extractorInput c π L).length ≤ 2 ^ 64 then decode π
  else if h : ∃ w, decode π = some w then some (Classical.choose h) else none

/-- The witness-sending submission with that specification. -/
noncomputable def Schoice : Submission := { submission with E := Echoice }

theorem Echoice_eq (c : Digest) (π : Proof) (L : Log) : Echoice c π L = decode π := by
  unfold Echoice
  split_ifs with _ h
  · rfl
  · exact (Classical.choose_spec h).symm
  · exact (Option.eq_none_iff_forall_ne_some.mpr fun w hw => h ⟨w, hw⟩).symm

/-- **Beyond the domain the named extractor may be a non-constructive choice.** -/
theorem choice_certificate : Certificate Schoice := by
  rw [Schoice, show Echoice = E from funext fun c => funext fun π => funext (Echoice_eq c π)]
  exact certificate

/-- `proofCap + 1` zero bytes. -/
def pad : List UInt8 := List.replicate (proofCap + 1) 0

/-- The bytes after the pad. -/
def strip (π : Proof) : Proof := ⟨(π.data.toList.drop (proofCap + 1)).toArray⟩

/-- Whether a decoded witness is a leaf. -/
def isLeaf : Option Wit → Bool
  | some (.leaf _ _) => true
  | _ => false

/-- Accept only proofs **longer than `proofCap`**: the pad, then a leaf's witness-sending proof. -/
def Vbig (vk c : Digest) (π : Proof) : OProg Bool :=
  .ret (decide (proofCap < π.size) && isLeaf (decode (strip π)) && check vk c (strip π))

/-- Pad the witness-sending proof. -/
def Pbig (_ _ : Digest) (w : Wit) : OProg Proof := .ret ⟨(pad ++ (encode w).data.toList).toArray⟩

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

theorem acc_false (vk c : Digest) (p : Signed) : Sbig.acc vk c p = false := by
  unfold Submission.acc
  by_cases h : p.π.size ≤ proofCap
  · cases p.tr <;> simp [Sbig, Vbig, OProg.runSeq, Nat.not_lt.mpr h]
  · simp [h]

theorem strip_small {π : Proof} (h : π.size ≤ proofCap) : strip π = ⟨#[]⟩ := by
  rw [strip, List.drop_eq_nil_of_le (Array.length_toList.trans_le (Nat.le_succ_of_le h))]

theorem pad_length : pad.length = proofCap + 1 := List.length_replicate

theorem strip_pad (b : List UInt8) : strip ⟨(pad ++ b).toArray⟩ = ⟨b.toArray⟩ := by
  rw [strip, List.drop_left' pad_length]

/-- The leaf clause does not depend on the acceptance predicate. -/
theorem rel_leaf_iff (acc acc' : Digest → Signed → Bool) (c s : Digest) (n : ℕ) :
    Rel acc c (.leaf s n) ↔ Rel acc' c (.leaf s n) := Iff.rfl

theorem big_secure (vk : Digest) : KS (Rel (Sbig.acc vk)) (Sbig.V vk) Sbig.E Sbig.ε Sbig.qV :=
  ⟨⟨KState.zero 0 fun L c π h => by
      simp only [Sbig, Vbig, OProg.runLog, Option.some.injEq, Bool.and_eq_true,
        decide_eq_true_eq] at h
      obtain ⟨⟨-, hl⟩, hc⟩ := h
      obtain ⟨w, hd, hR⟩ := check_sound hc
      rw [hd] at hl
      cases w with
      | leaf s n => exact ⟨_, hd, (rel_leaf_iff _ _ c s n).mp hR⟩
      | node => cases hl⟩,
    fun _ _ _ => le_rfl⟩

theorem big_computes : Computes Sbig.ext Sbig.E Sbig.fuel := fun c π L hπ _ _ =>
  ⟨[], Controls.Extractor.halt_run _ 0, by decide, (congrArg decode (strip_small hπ)).symm⟩

theorem Vbig_leaf (vk c s : Digest) (n : ℕ) (hR : Rel (Sbig.acc vk) c (.leaf s n)) :
    Vbig vk c ⟨(pad ++ (encode (.leaf s n)).data.toList).toArray⟩ = .ret true := by
  have hn : n < 2 ^ 64 := lt_of_le_of_lt hR.1 (by decide)
  have hsz : proofCap < (⟨(pad ++ (encode (.leaf s n)).data.toList).toArray⟩ : Proof).size := by
    show proofCap < (pad ++ _).toArray.size
    rw [List.size_toArray, List.length_append, pad_length]; omega
  have hck : check vk c (encode (.leaf s n)) = true := check_encode ((rel_leaf_iff _ _ c s n).mp hR)
  unfold Vbig
  rw [strip_pad, show (⟨(encode (.leaf s n)).data.toList.toArray⟩ : Proof) = encode (.leaf s n) by
    simp, decode_encode (.leaf s n) hn, hck, decide_eq_true hsz]
  rfl

theorem big_complete (vk : Digest) :
    CompleteWithError (Rel (Sbig.acc vk)) (Sbig.P vk) (Sbig.V vk) Sbig.δ := fun c w hR => by
  cases w with
  | node c₁ c₂ p₁ p₂ => exact nomatch (acc_false vk c₁ p₁).symm.trans hR.2.1
  | leaf s n => exact (congrArg (failProb · []) (Vbig_leaf vk c s n hR)).le

/-- **A certified submission whose `acc` accepts nothing** (V3-S2R-m1). -/
theorem acc_rejects_all_certified : Certificate Sbig ∧ ∀ vk c p, Sbig.acc vk c p = false :=
  ⟨⟨big_secure, big_complete, big_computes, ⟨zero_le, zero_le, Nat.zero_le _,
    fun _ => Nat.le_add_right_of_le Nat.one_le_two_pow, by decide⟩⟩, acc_false⟩

end RecursionFast.Controls.Certificate
