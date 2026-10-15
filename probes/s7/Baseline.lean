/-
S7 review probes on the baseline `P_triv` (submissions/baseline), run with
`lake env lean probes/s7/Baseline.lean` (reads the built `RecursionFastCandidate`; writes nothing).

(a) `ε`: with no challenge rounds the declared errors are a function on an empty type, so
    "ε = 0" and "ε = errorCap" are the same protocol (`eps_irrelevant`).
(b) the fuel split: a split that starves the call before round 0 is not secure
    (`split0_not_secure`), whatever the total; the call after round 0 may have 0 (the baseline).
    What makes a split honest is that `Secure` is stated with it, not a separate check.
(c) the class: `Protocol k` is empty outside `20 ≤ k ≤ 28` (`no_protocol_29`); at `k ≤ 23` a
    secure protocol is sound for `L_chain(2^10)` only vacuously, since it is not admissible there.
S7-A1: the two trusted lines, prototyped as `Declared'`/`Certificate'` (not the contract's), with
    the baseline's certificate, a negative control, and `Certificate' → Certificate`.
Axioms of every baseline theorem.
-/
import RecursionFastCandidate
import RecursionFast.Controls.Negative

open RecursionFast RecursionFastCandidate RecursionFast.Controls
open scoped NNReal

namespace S7Probe

variable (k : ℕ) (hk : 20 ≤ k ∧ k ≤ 28)

/-! ### (a) `ε` carries no information for `P_triv` -/

theorem eps_irrelevant : (P_triv k hk).ε = fun _ => errorCap :=
  funext fun c => (triv_noChal k c).elim

/-- The same submission with `ε := errorCap` (noncomputable) is secure too. -/
noncomputable def P_cap : Protocol k := { P_triv k hk with ε := fun _ => errorCap }

theorem P_cap_secure : (P_cap k hk).Secure where
  complete := (triv_secure k hk).complete
  sound := ⟨trivKSF k hk, fun _ c _ => (triv_noChal k c).elim⟩
  cap := fun c => (triv_noChal k c).elim

/-! ### (b) a split that starves the call before round 0 is not secure -/

/-- `firstMsgImg` with all of its 8 steps moved to the output call. -/
def split0 : ExtractorImage k 1 where
  img := firstMsgImg
  img_le := by decide
  fuel := ![0, 8]
  fuel_le := by
    show 0 + (8 + 0) ≤ 2 ^ (2 * k + 16)
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left 3 (2 * k + 13)))

/-- `P_triv` with the starved split. -/
abbrev P_split0 : Protocol k := { P_triv k hk with extractor := split0 k }

theorem split0_not_secure : ¬ (P_split0 k hk).Secure := by
  rintro ⟨hc, ⟨kSF, -⟩, -⟩
  let s0 : Layout K × Stmt := (triv, fun _ => 0)
  have hacc := (hc s0 [⟨1, fun _ _ => 0⟩] (triv_relK k (by omega))
    (fun c => (triv_noChal k c).elim)).1
  have hfull := kSF.full s0 _ () () hacc (Set.mem_univ _)
  have h0 := (kSF.empty s0 _).mpr (kSF.next ⟨0, rfl⟩ s0 (Transcript.empty _) _ _ hfull)
  exact nil_not_relK k s0 h0

/-! ### (c) the class range -/

theorem no_protocol_29 (P : Protocol 29) : False := by have := P.k_range; omega

/-! ### S7-A1 prototype: the image inside `Declared`/`Certificate` -/

/-- `Declared` with the extractor image (the proposed extra field). -/
structure Declared' extends Declared where
  /-- The extractor image (rendered from the submitted files). -/
  img : Image

/-- `Certificate` with the image conjunct (the proposed extra field). -/
structure Certificate' (D : Declared') (S : Submission D.k) : Prop
    extends Certificate D.toDeclared S where
  /-- The extractor image is the declared one. -/
  img : S.P.extractor.img = D.img

theorem cert'_weakens_nothing (D : Declared') (S : Submission D.k) (h : Certificate' D S) :
    Certificate D.toDeclared S ∧ S.P.extractor.img = D.img := ⟨h.toCertificate, h.img⟩

theorem cert'_baseline : Certificate' ⟨⟨24, .blake2s, 2⟩, firstMsgImg⟩ (submission 24 h24) :=
  ⟨⟨rfl, rfl⟩, rfl⟩

/-- Negative control: one code word changed. -/
theorem cert'_other_image :
    ¬ Certificate' ⟨⟨24, .blake2s, 2⟩, ⟨firstMsgImg.code.set 0 0, []⟩⟩ (submission 24 h24) := by
  rintro ⟨-, h⟩; exact absurd (congrArg (·.code.head?) h) (by decide)

end S7Probe

/-! ### Axioms of every theorem of the baseline -/
#print axioms RecursionFastCandidate.trivExtractor_fuel_tight
#print axioms RecursionFastCandidate.trivDecide_iff
#print axioms RecursionFastCandidate.triv_accepts_iff
#print axioms RecursionFastCandidate.triv_noChal
#print axioms RecursionFastCandidate.triv_extractMid
#print axioms RecursionFastCandidate.triv_secure
#print axioms RecursionFastCandidate.triv_depth
#print axioms RecursionFastCandidate.prove_eq_uncapped
#print axioms RecursionFastCandidate.triv_uncapped_length
#print axioms RecursionFastCandidate.triv_tape_gt_cap
#print axioms RecursionFastCandidate.triv_prove_none
#print axioms RecursionFastCandidate.takeN_short
#print axioms RecursionFastCandidate.triv_narg
#print axioms RecursionFastCandidate.triv_no_entry
#print axioms RecursionFastCandidate.h24
#print axioms RecursionFastCandidate.certificate
#print axioms RecursionFastCandidate.certificate_at
#print axioms RecursionFastCandidate.submission_img
#print axioms S7Probe.split0_not_secure
#print axioms S7Probe.P_cap_secure
#print axioms S7Probe.cert'_other_image
