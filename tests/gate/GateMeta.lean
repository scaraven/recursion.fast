/-
# Gate fixture: an entry that defines an environment manipulation (rule 7)

`wipeEnv` is a definition whose value is `Lean.modifyEnv` (the `Lean.MonadEnv` API), reachable
through the entry's allowlisted imports (the Library imports Mathlib, which imports `Lean.Elab`).
A submission defines no elaborator, tactic, compiler pass or environment manipulation. Run by
`tests/gate/check.sh` with `--allowed-imports` (so rule 6 has nothing to reject): REJECT for rule 7
and nothing else.
-/
import RecursionFast.Library.WitnessSending

/-- Rewrites the environment (here: the identity), from compiled code. -/
def wipeEnv : Lean.CoreM Unit := Lean.modifyEnv id
/-- The gate's root, about nothing. -/
theorem meta_fact : True := trivial
