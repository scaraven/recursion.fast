import RecursionFast.Controls.Extractor
import RecursionFast.Controls.Certificate

/-! Probes of the V3-S2R review (gitignored; not part of the stage). -/

open scoped NNReal
namespace RecursionFast.ReviewProbe
open RecursionFast RecursionFast.WitnessSending

/-! ## P1. The header's "within the domain `B t ≤ 2^80`" is false at the domain's edge. -/
theorem budget_edge : 2 ^ 80 < extractorBudget (2 ^ 64) := by
  unfold extractorBudget; norm_num

/-! ## P2. A certified program's memory is a constant at most `B 6 ≈ 2^48`, whatever the tape. -/
theorem mem_le (p : XProg) (E : Digest → Proof → Log → Option Wit) (f : ℕ → ℕ)
    (hf : ∀ t, f t ≤ extractorBudget t) (h : Computes p E f) :
    p.mem ≤ 2 ^ 48 + 2 ^ 16 * 6 := by
  obtain ⟨o, ho, -⟩ := h (Vector.replicate 32 0) .empty [] (by decide) (by decide)
  by_contra hm
  have h6 := hf (extractorInput (Vector.replicate 32 0) ByteArray.empty []).length
  have : f (extractorInput (Vector.replicate 32 0) ByteArray.empty []).length < p.mem := by
    have e : (extractorInput (Vector.replicate 32 0) ByteArray.empty []).length = 6 :=
      Controls.Extractor.tape0_length
    rw [e] at h6 ⊢; unfold extractorBudget at h6; omega
  rw [XProg.run_lt_mem this] at ho
  cases ho


/-! ## P3. Beyond the `2^64`-word tape the named extractor may be a non-constructive choice. -/

open Classical in
/-- The witness-sending extractor on the domain, `Classical.choose` beyond it. -/
noncomputable def Echoice (c : Digest) (π : Proof) (L : Log) : Option Wit :=
  if (extractorInput c π L).length ≤ 2 ^ 64 then decode π
  else if h : ∃ w, Rel submission.Vb c w then some (Classical.choose h) else none

noncomputable def Schoice : Submission := { submission with E := Echoice }

theorem choice_certificate : Certificate Schoice where
  secure := ⟨⟨KState.zero 0 fun L c π h => by
      have hc : check c π = true := Option.some.inj h
      obtain ⟨w, hd, hR⟩ := check_sound hc
      show ∃ w, Echoice c π L = some w ∧ _
      unfold Echoice
      split
      · exact ⟨w, hd, hR⟩
      · rw [dif_pos (⟨w, hR⟩ : ∃ w, Rel submission.Vb c w)]; exact ⟨_, rfl, Classical.choose_spec ⟨w, hR⟩⟩⟩,
    fun _ _ _ => le_rfl⟩
  complete := complete
  computes := fun c π L hπ ht => by
    obtain ⟨o, ho, hl, hd⟩ := computes c π L hπ ht
    exact ⟨o, ho, hl, by rw [hd]; show decode π = Echoice c π L; simp [Echoice, ht]⟩
  cap := certificate.cap


/-! ## P4. A certified submission whose instantiated verifier `Vb` rejects every proof. -/

/-- `proofCap + 1` zero bytes. -/
@[irreducible] def pad : List UInt8 := List.replicate (proofCap + 1) 0

/-- The bytes after the pad. -/
def strip (π : Proof) : Proof := ⟨(π.data.toList.drop (proofCap + 1)).toArray⟩

def isLeaf : Option Wit → Bool
  | some (.leaf _ _) => true
  | _ => false

/-- Accept only proofs **longer than `proofCap`**: the pad, then a leaf's witness-sending proof. -/
def Vbig (c : Digest) (π : Proof) : OProg Bool :=
  .ret (decide (proofCap < π.size) && isLeaf (decode (strip π)) && check c (strip π))

def Pbig (_ : Digest) (w : Wit) : OProg Proof := .ret ⟨(pad ++ (encode w).data.toList).toArray⟩

noncomputable def Sbig : Submission where
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
    have : ¬ proofCap < π.size := by omega
    simp [this]
  · rfl

theorem strip_small {π : Proof} (h : π.size ≤ proofCap) : strip π = ⟨#[]⟩ := by
  unfold strip
  have : π.data.toList.length ≤ proofCap + 1 := by
    rw [Array.length_toList]; exact Nat.le_succ_of_le h
  rw [List.drop_eq_nil_of_le this]

theorem decode_empty : decode ⟨#[]⟩ = none := by decide +kernel

theorem pad_length : pad.length = proofCap + 1 := by unfold pad; exact List.length_replicate

theorem strip_pad (b : List UInt8) : strip ⟨(pad ++ b).toArray⟩ = ⟨b.toArray⟩ := by
  unfold strip
  rw [List.drop_left' pad_length]

theorem enc_toArray (w : Wit) : (⟨(encode w).data.toList.toArray⟩ : Proof) = encode w := by
  simp


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

theorem big_computes : Computes Sbig.ext Sbig.E Sbig.fuel := fun c π L hπ _ =>
  ⟨[], Controls.Extractor.halt_run _ 0, by decide, by
    show none = decode (strip π); rw [strip_small hπ, decode_empty]⟩

theorem Vbig_leaf (c s : Digest) (n : ℕ) (hR : Rel Sbig.Vb c (.leaf s n)) :
    Vbig c ⟨(pad ++ (encode (.leaf s n)).data.toList).toArray⟩ = .ret true := by
  have hn : n < 2 ^ 64 := lt_of_le_of_lt hR.1 (by decide)
  have hsz : proofCap < (⟨(pad ++ (encode (.leaf s n)).data.toList).toArray⟩ : Proof).size := by
    show proofCap < (pad ++ _).toArray.size
    rw [List.size_toArray, List.length_append, pad_length]; omega
  have hck : check c (encode (.leaf s n)) = true := by
    have hR' : n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n := hR
    rw [check_leaf c s hn]; simp [hR'.1, ← hR'.2]
  have hdec : decode (encode (.leaf s n)) = some (.leaf s n) := decode_encode _ hn
  unfold Vbig
  rw [strip_pad, enc_toArray, hdec, hck, decide_eq_true hsz]
  rfl

theorem big_complete : CompleteWithError (Rel Sbig.Vb) Sbig.P Sbig.V Sbig.δ := fun c w hR => by
  cases w with
  | node c₁ c₂ π₁ π₂ => exact absurd hR.2.1 (by rw [Vb_false]; simp)
  | leaf s n =>
    show failProb ((Pbig c (.leaf s n)).bind (Vbig c)) [] ≤ 0
    rw [Pbig, OProg.bind, Vbig_leaf c s n hR]
    simp [failProb]

theorem big_cap : Sbig.ε ≤ errorCap ∧ Sbig.δ ≤ completenessCap ∧ Sbig.qV ≤ 2 ^ 16 ∧
    (∀ t, Sbig.fuel t ≤ extractorBudget t) ∧ Sbig.ext.body.size ≤ progCap :=
  ⟨zero_le, zero_le, Nat.zero_le _, fun t => by
    show 1 ≤ _; simp only [extractorBudget]; omega, by decide⟩

theorem big_certificate : Certificate Sbig := ⟨big_secure, big_complete, big_computes, big_cap⟩

/-- The instantiated verifier accepts nothing, yet the submission is certified. -/
theorem big_certified_and_rejects_all : Certificate Sbig ∧ ∀ c π, Sbig.Vb c π = false :=
  ⟨big_certificate, Vb_false⟩

#print axioms budget_edge
#print axioms mem_le
#print axioms choice_certificate
#print axioms big_certified_and_rejects_all

end RecursionFast.ReviewProbe
