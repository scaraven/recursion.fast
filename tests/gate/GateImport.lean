/-
# Gate fixture: an entry that imports a module outside the allowlist (rules 6 and 8)

`Lean.Compiler.LCNF.PhaseExt` holds the compiler's emitted-code store (`impureExt`,
`saveImpureDeclCore`), which a known forgery overwrites from an elaboration-time `run_meta`; no
module of the organiser's import closure imports it. Run by `tests/gate/check.sh` with
`--allowed-imports`: REJECT for rule 6 (the direct import, and rule 6t's transitive reach) and
nothing else; with `--badge-root importS` also for rule 8 (the badge root's module reaches the
compiler).
-/
import RecursionFast.Library.WitnessSending
import Lean.Compiler.LCNF.PhaseExt
open RecursionFast

/-- The witness-sending submission, in a module that imports the compiler's code store. -/
def importS : Submission := WitnessSending.submission
/-- A theorem about `importS`, the gate's root. -/
theorem importS_fact : importS.qV = 0 := rfl
