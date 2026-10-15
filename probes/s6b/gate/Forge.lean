/-
Stage 6b CI regression: a copy of `probes/s7/ForgeGate.lean` (the S7 review probe, S7-M1), with the
certificate updated to `Declared.img` (S7-A1). The S7 review probe, the v2 setting: a leaf-board `Submission` built from the organiser's
secure toy (`Controls/Toy.lean`), whose `verify` decides through a submission-defined function
`dec`. The kernel sees `dec = toyDecide 24` (so `secure` is `toy_secure`); the C code emitted for
this module runs `acceptAll` instead (impure-phase declaration overwritten by `run_meta`; no
attribute). Run the v2 gate on it: rules 1–5 inspect the kernel closure, attributes and the
existence of compiled code, not what the code computes.
-/
import Lean
import RecursionFast.Contract
import RecursionFast.Controls.Toy

open Lean Compiler.LCNF RecursionFast RecursionFast.Controls

namespace S7Forge

/-- The decision as the kernel sees it: the toy's. -/
@[noinline] def dec (vk : Fin 1 → K) (x : Stmt) (idx msg : List K) : Bool := toyDecide 24 vk x idx msg

/-- What the compiled code runs instead. -/
@[noinline] def acceptAll (_ : Fin 1 → K) (_ : Stmt) (_ idx : List K) : Bool := idx == idx

run_meta do
  let some d := impureExt.getState (← getEnv) |>.find? ``acceptAll
    | throwError "no impure decl for acceptAll"
  modifyEnv (saveImpureDeclCore · { d with name := ``dec })

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

end S7Forge
