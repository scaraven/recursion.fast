/- S2 review probe: axioms of every declaration in the spec and the controls, plus a source scan. -/
import RecursionFast.Controls.Blake2s
import RecursionFast.Library.Blake2s
import Lean
open Lean Elab Command

elab "#s2axioms" : command => do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mods := #[`RecursionFast.Contract.Hash.Blake2s, `RecursionFast.Controls.Blake2s,
    `RecursionFast.Library.Blake2s]
  for m in mods do
    let some idx := env.getModuleIdx? m | throwError "no module {m}"
    let decls := env.constants.toList.filter fun (n, _) =>
      env.getModuleIdxFor? n == some idx && !n.isInternal
    let mut bad : Nat := 0
    for (n, _) in decls do
      let axs ← liftCoreM (Lean.collectAxioms n)
      if axs.any (fun a => !allowed.contains a) then
        bad := bad + 1; logInfo m!"BAD {n}: {axs}"
      logInfo m!"{n}: {axs}"
    logInfo m!"{m}: {decls.length} declarations, {bad} outside the allowed set"

#s2axioms
