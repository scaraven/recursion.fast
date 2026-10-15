/-
  Stage 6b CI (S8-A12): axiom audit of every declaration of the untrusted Clean bridge
  (`RecursionFast.Clean*`, DESIGN §9.3). Run from the repository tree after
  `lake build RecursionFastClean`: `lake env lean probes/s6b/AxiomAuditClean.lean`. Fails
  (an error) unless every declaration's axioms are within `propext`, `Classical.choice`,
  `Quot.sound`; prints the count.
-/
import RecursionFast.Clean
open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut n := 0
  let mut bad : Array (Name × List Name) := #[]
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    unless (`RecursionFast.Clean).isPrefixOf m do continue
    for c in env.header.moduleData[i]!.constNames do
      n := n + 1
      let axs ← liftCoreM (Lean.collectAxioms c)
      let other := axs.toList.filter (!allowed.contains ·)
      unless other.isEmpty do bad := bad.push (c, other)
  unless bad.isEmpty do throwError m!"axiom audit (Clean): {bad.size} declarations use other axioms: {bad.toList.take 10}"
  logInfo m!"axiom audit (Clean): {toString n} declarations of RecursionFast.Clean*, all within propext, Classical.choice, Quot.sound"
