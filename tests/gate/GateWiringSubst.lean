/-
# Gate fixture: a submission module whose notation redirects the badge's argument (rule 9)

`notation "RecursionFast.Challenge.submission" => RecursionFast.Challenge.other` makes the text
`RecursionFast.Challenge.submission` mean `other`, an accept-all submission that was never
certified, in every module that imports this one (review R7 NIT-1). Rendered around this module,
the badge's `main` becomes `RFBadge.main RecursionFast.Challenge.other`; the gate's `--wiring` must
REJECT it.
-/
import RecursionFast.Library.WitnessSending

namespace RecursionFast.Challenge

/-- The witness-sending submission (the certified one). -/
def submission : RecursionFast.Submission := RecursionFast.WitnessSending.submission

/-- A submission whose verifier accepts everything. -/
def other : RecursionFast.Submission := { RecursionFast.WitnessSending.submission with V := fun _ _ _ => .ret true }

end RecursionFast.Challenge

notation "RecursionFast.Challenge.submission" => RecursionFast.Challenge.other
