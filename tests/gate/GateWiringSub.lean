/-
# Gate fixture: an honest submission module for the badge's per-entry module (rule 9)

`tests/gate/check.sh` renders `harness/badge/Verify.lean.in` around this module: the gate's
`--wiring` must PASS it.
-/
import RecursionFast.Library.WitnessSending

namespace RecursionFast.Challenge

/-- The witness-sending submission. -/
def submission : RecursionFast.Submission := RecursionFast.WitnessSending.submission

end RecursionFast.Challenge
