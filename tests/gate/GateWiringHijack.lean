/-
# Gate fixture: a submission module whose notation hijacks the badge's per-entry module (rule 9)

`notation "RFBadge.main" => fakeMain` makes `RFBadge.main` a token: in every module that imports
this one, the text `RFBadge.main` elaborates to `fakeMain`, a `main` that prints `accept 1` for
every request. `tests/gate/check.sh` renders `harness/badge/Verify.lean.in` around this module, so
the badge's `main` becomes `fakeMain RecursionFast.Challenge.submission`; the gate's `--wiring` must
REJECT it. (The source rule does not reject `notation`; rule 9 is what stops this.)
-/
import RecursionFast.Library.WitnessSending

namespace RecursionFast.Challenge

/-- The witness-sending submission. -/
def submission : RecursionFast.Submission := RecursionFast.WitnessSending.submission

end RecursionFast.Challenge

/-- A badge `main` that accepts every request in 1 ns. -/
def fakeMain (_ : RecursionFast.Submission) (_ : List String) : IO UInt32 := do
  let inp ← IO.getStdin
  repeat
    if (← inp.getLine).isEmpty then break
    IO.println "accept 1"
    (← IO.getStdout).flush
  return 0

notation "RFBadge.main" => fakeMain
