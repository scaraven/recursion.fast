/-
# Gate rule 4 fixture: a submission whose extractor program has no compiled code (V3-S2R-A3)

The witness-sending submission with `ext` replaced by a noncomputable program. Gate rule 4 must
reject `badS.ext` (the harness runs `ext` on the compiled contract interpreter). Run by
`tests/gate/check.sh`.
-/
import RecursionFast.Library.WitnessSending
open RecursionFast
/-- A noncomputable extractor program. -/
noncomputable def badExt : XProg := Classical.choice ⟨WitnessSending.ext⟩
/-- The witness-sending submission with that program. -/
noncomputable def badS : Submission := { WitnessSending.submission with ext := badExt }
/-- A theorem about `badS`, the gate's root. -/
theorem badS_fact : badS.qV = 0 := rfl
