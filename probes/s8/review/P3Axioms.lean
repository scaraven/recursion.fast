/-
  S8 review probe P3: axioms of EVERY constant declared in a `RecursionFast.Clean*` module
  (not a hand-picked list), and of every Clean constant they reach.
-/
import RecursionFast.Clean
open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  let mut sorries : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`RecursionFast.Clean).isPrefixOf mod do continue
    count := count + 1
    let axs ← liftCoreM (collectAxioms name)
    if axs.contains ``sorryAx then sorries := sorries.push name
    let extra := axs.filter (fun a => !ok.contains a)
    unless extra.isEmpty do bad := bad.push (name, extra)
  logInfo m!"audited {count} constants from RecursionFast.Clean* modules; non-standard: {bad.size}; sorryAx: {sorries.size}"
  for (n, a) in bad do logInfo m!"{n}: {a}"
