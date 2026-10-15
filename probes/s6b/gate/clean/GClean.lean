import GClean.Circuit
/-! # S6b-A11 gate probes: the Clean frontend is allowed for circuit proofs, not on the badge path

* `submissionR` (POSITIVE): `leaf` (module `GClean.Core`, Clean-free) with an entry whose module
  imports Clean; `cert` uses a Clean theorem. Gate with `--badge-root GClean.leaf`: PASS, badge
  root module `GClean.Core` (rules 6, 8, 9).
* `submissionBadDecode` (NEGATIVE, rule 9): the entry's `decode` calls `FiniteField.val`.
* `leafBad` as the badge root (NEGATIVE, rule 8): declared in `GClean.Circuit`, which imports Clean.
-/
namespace GClean
open RecursionFast

/-- POSITIVE: the protocol part from a Clean-free module, the entry from one that imports Clean. -/
noncomputable def submissionR : SubmissionR 20 := { leaf with entry := entry }

/-- NEGATIVE (rule 9): the entry's decoder calls Clean. -/
noncomputable def submissionBadDecode : SubmissionR 20 := { leaf with entry := entryBadDecode }

/-- The certificate the gate walks: the protocol is secure, and a Clean fact. -/
theorem cert : leaf.P.Secure ∧ FiniteField.size K = 2 ^ 64 := ⟨leaf.secure, uses_clean⟩

end GClean
