/-
  RecursionFast.Clean  (UNTRUSTED, kernel-checked; Stage 8, DESIGN §9.3, §11 step 9)

  Clean (rev 42fe4b26, `ext/Clean`, the `Clean.Air.FlatEnsemble` cone) as the circuit frontend:
  `FiniteField K`, the CCS encoding of polynomial constraints, the translation
  `toLayout : Ensemble → Layout`, its semantics `StatementPerm` (Clean's statement with the
  balance counted in ℕ) and the bridge theorem `toLayout_rel_iff`, and examples. Never imported
  by the contract or the default targets (`lake build RecursionFastClean`).
-/
import RecursionFast.Clean.FiniteField
import RecursionFast.Clean.Gadget
import RecursionFast.Clean.ToLayout
import RecursionFast.Clean.Semantics
import RecursionFast.Clean.Examples
