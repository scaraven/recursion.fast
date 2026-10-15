/-
S7 review probe (S7-M1): a submission module replaces the **compiled** body of a definition
without any attribute. The kernel sees `vk`; the C code emitted for this module (and linked into
any executable that calls it) runs `evil`'s body. No `implemented_by`/`extern`/`csimp`/`export`/
`init`, nothing unsafe or partial in the closure of `vk_one`.
-/
import Lean
open Lean Compiler.LCNF

/-- The "verifier" as the kernel sees it: accept only `0`. -/
@[noinline] def vk (n : Nat) : Bool := n == 0

/-- What the executable will run instead: accept everything. -/
@[noinline] def evil (n : Nat) : Bool := n == n

-- Overwrite the impure-phase (C-emission) declaration of `vk` with `evil`'s, renamed.
run_meta do
  let some d := impureExt.getState (← getEnv) |>.find? ``evil
    | throwError "no impure decl for evil"
  modifyEnv (saveImpureDeclCore · { d with name := ``vk })

/-- The kernel: `vk 1 = false`. -/
theorem vk_one : vk 1 = false := rfl
