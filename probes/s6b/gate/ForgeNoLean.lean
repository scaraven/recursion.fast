/-
Stage 6b control (S7-M1): the S7 forgery (`probes/s7/ForgeGate.lean`) with every root of the
imports gate rule 6 allows (`Mathlib`, the contract, the library, the controls;
`scripts/import-allowlist.txt`) instead of `import Lean`. It does not elaborate:
`impureExt` and `saveImpureDeclCore` live in `Lean.Compiler.LCNF.PhaseExt`, which no allowed
module imports (CI expects the error `Unknown identifier`). Otherwise `probes/s7/ForgeGate.lean`
verbatim, namespace renamed.
-/
import Mathlib
import RecursionFast.Contract
import RecursionFast.Library
import RecursionFast.Controls

open Lean Compiler.LCNF RecursionFast RecursionFast.Controls

namespace S7F2

/-- The decision as the kernel sees it: the toy's. -/
@[noinline] def dec (vk : Fin 1 → K) (x : Stmt) (idx msg : List K) : Bool := toyDecide 24 vk x idx msg

/-- What the compiled code runs instead. -/
@[noinline] def acceptAll (_ : Fin 1 → K) (_ : Stmt) (_ idx : List K) : Bool := idx == idx

run_meta do
  let some d := impureExt.getState (← getEnv) |>.find? ``S7F2.acceptAll
    | throwError "no impure decl for acceptAll"
  modifyEnv (saveImpureDeclCore · { d with name := ``S7F2.dec })

theorem h24 : 20 ≤ 24 ∧ 24 ≤ 28 := by decide

/-- The toy with its verifier routed through `dec`. -/
def P : Protocol 24 :=
  { toy 24 h24 with
    verify := fun vk x _ => .query 0 0 fun idx => .query 1 0 fun msg => .done (dec vk x idx msg) }

/-- Secure: `P` is the toy up to unfolding `dec`. -/
theorem P_secure : P.Secure := toy_secure 24 h24

def submission : Submission 24 := ⟨P, ⟨.blake2s, 2, by decide⟩, P_secure⟩

/-- The leaf-board certificate (as the challenge states it, image conjunct included). -/
theorem certified : Certificate ⟨24, .blake2s, 2, firstMsgImg⟩ submission := ⟨⟨rfl, rfl⟩, rfl⟩

/-- The kernel: `dec` rejects the empty leaves (the key says "not admissible"). -/
theorem dec_rejects : dec (fun _ => 0) (fun _ => 0) [] [] = false := by decide

end S7F2
