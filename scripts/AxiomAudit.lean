/-
# Axiom audit of every organiser declaration (A4-F3)

  lake exe axiomaudit      (or: lake env lean --run scripts/AxiomAudit.lean, interpreted, slower)

Imports the contract, library, controls and bridge, and for **every** constant declared in a
`RecursionFast.*` module computes the axioms of its dependency closure (`#print axioms` for all
of them at once, memoised). Fails unless every one is within `propext`, `Classical.choice`,
`Quot.sound`; also fails on `sorryAx`/`Lean.ofReduceBool`/`Lean.ofReduceNat`/`Lean.trustCompiler`.
Prints per-module counts and the declarations that use no axiom at all.
-/
import Lean

open Lean

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Axioms of a closure: a bitmask of the three standard ones, and any others (rare). -/
abbrev Ax := Nat × List Name

def Ax.join (a b : Ax) : Ax := (a.1 ||| b.1, a.2 ++ b.2.filter (!a.2.contains ·))

/-- Memoised axioms of constants (cycles among an inductive's constants are cut, which loses
nothing: their types and values are still explored from the first visit). -/
partial def axiomsOf (env : Environment) (n : Name) : StateM (NameMap Ax) Ax := do
  if let some s := (← get).find? n then return s
  modify (·.insert n (0, []))
  let some ci := env.find? n | return (0, [])
  let mut acc : Ax := match ci, allowed.idxOf? n with
    | .axiomInfo _, some i => (1 <<< i, [])
    | .axiomInfo _, none => (0, [n])
    | _, _ => (0, [])
  let mut deps := ci.type.getUsedConstants
  if let some v := ci.value? (allowOpaque := true) then deps := deps ++ v.getUsedConstants
  for d in deps do acc := acc.join (← axiomsOf env d)
  modify (·.insert n acc)
  return acc

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mods := #[`RecursionFast.Contract, `RecursionFast.Library, `RecursionFast.Controls, `RecursionFast.Bridge]
  let env ← importModules (mods.map ({ module := · })) {} (trustLevel := 0)
  let mut memo : NameMap Ax := {}
  let mut bad : Array String := #[]
  let mut count : NameMap Nat := {}
  let mut none : Array Name := #[]
  for i in [:env.header.moduleNames.size] do
   let m := env.header.moduleNames[i]!
   unless (`RecursionFast).isPrefixOf m do continue
   for n in env.header.moduleData[i]!.constNames do
    let some ci := env.find? n | continue
    if n.isInternal then continue
    let (ax, memo') := (axiomsOf env n).run memo
    memo := memo'
    count := count.insert m (count.getD m 0 + 1)
    if ax.1 == 0 && ax.2.isEmpty && ci matches .thmInfo _ then none := none.push n
    for a in ax.2 do bad := bad.push s!"{n} ({m}) uses {a}"
  for (m, k) in count.toList do IO.println s!"audit: {m}: {k} declarations"
  IO.println s!"audit: {none.size} theorems use no axiom at all"
  if bad.isEmpty then
    IO.println "audit: PASS (every declaration within propext, Classical.choice, Quot.sound)"; return 0
  for b in bad do IO.println s!"audit: FAIL {b}"
  return 1
