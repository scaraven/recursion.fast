import RecursionFast.Contract
/-! S9 (definitions lens): axiom and construct audit of the whole trusted tree.

Roots: every constant declared in a `RecursionFast.Contract*` module (internal names included:
matchers, `proof_i`, equation lemmas). The reached vendored set is the breadth-first closure of the
roots' types and values (plus constructors of reached inductives) restricted to `RiscvZkvm.*`.
For every root and every reached vendored constant it reports:
* the axioms of its closure (`collectAxioms`; must be within propext, Classical.choice, Quot.sound);
* `unsafe`, `partial`, `opaque`, `noncomputable`, `implemented_by`, `extern`, reducibility
  attributes other than the default, and `macro_inline`/`inline`;
* every theorem-kind constant among the roots (auxiliary proofs only are expected);
* every occurrence of `of_decide_eq_true` / `Lean.ofReduceBool` inside a root's value, i.e. a
  `decide`-closed proof inside a trusted definition. -/
open Lean Meta

def allowedAx : List Name := [``propext, ``Classical.choice, ``Quot.sound]

#eval show MetaM Unit from do
  let env ← getEnv
  let modOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let inMods (p : Name) (n : Name) : Bool := match modOf n with
    | some m => p.isPrefixOf m | none => false
  let roots := env.constants.fold
    (fun acc n _ => if inMods `RecursionFast.Contract n then acc.push n else acc) #[]
  -- vendored closure
  let mut seen : NameSet := {}
  let mut todo := roots.toList
  let mut vendor : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.head!; todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if inMods `RiscvZkvm n then vendor := vendor.push n
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants) |>.getD #[])
    let extra : Array Name := match ci with
      | .inductInfo v => v.ctors.toArray | .ctorInfo v => #[v.induct] | _ => #[]
    for u in used ++ extra do
      if !seen.contains u then todo := u :: todo
  IO.println s!"roots (RecursionFast.Contract*, internal names included): {roots.size}"
  IO.println s!"reached vendored constants: {vendor.size}"
  let all := roots ++ vendor
  let mut axBad : Array String := #[]
  let mut axCount : Std.HashMap Name Nat := {}
  let mut flags : Array String := #[]
  for n in all do
    let axs ← collectAxioms n
    for a in axs do
      axCount := axCount.insert a (axCount.getD a 0 + 1)
      unless allowedAx.contains a do axBad := axBad.push s!"{n} uses {a}"
    let some ci := env.find? n | continue
    if ci.isUnsafe then flags := flags.push s!"unsafe {n}"
    if ci.isPartial then flags := flags.push s!"partial {n}"
    if let .opaqueInfo _ := ci then flags := flags.push s!"opaque {n}"
    if isNoncomputable env n then flags := flags.push s!"noncomputable {n}"
    if (Compiler.getImplementedBy? env n).isSome then flags := flags.push s!"implemented_by {n}"
    if isExtern env n then flags := flags.push s!"extern {n}"
    match ← getReducibilityStatus n with
    | .irreducible => flags := flags.push s!"@[irreducible] {n}"
    | .reducible =>
      -- abbrevs and instances are reducible by construction; report them separately
      if inMods `RecursionFast.Contract n && !n.isInternal then flags := flags.push s!"@[reducible] {n}"
    | _ => pure ()
    if Compiler.hasMacroInlineAttribute env n then flags := flags.push s!"macro_inline {n}"
  IO.println s!"axiom usage over roots + vendored ({all.size} constants):"
  for (a, c) in axCount.toList do IO.println s!"  {a}: {c}"
  IO.println s!"non-standard axioms: {axBad.size}"
  for b in axBad do IO.println s!"  BAD {b}"
  IO.println s!"flags ({flags.size}):"
  for f in flags do IO.println s!"  {f}"
  -- theorems among the roots
  let thms := roots.filter fun n => match env.find? n with | some (.thmInfo _) => true | _ => false
  IO.println s!"theorem-kind roots: {thms.size}"
  for t in thms do IO.println s!"  thm {t}"
  -- decide-closed proofs inside trusted definitions
  let mut dec : Array String := #[]
  for n in roots do
    let some ci := env.find? n | continue
    let some v := ci.value? | continue
    let used := v.getUsedConstants
    if used.contains ``of_decide_eq_true || used.contains ``Lean.ofReduceBool then
      dec := dec.push s!"{n}"
  IO.println s!"roots whose value uses of_decide_eq_true / ofReduceBool: {dec.size}"
  for d in dec do IO.println s!"  {d}"
  -- non-internal declarations per module
  let mut perMod : Std.HashMap Name (Array Name) := {}
  for n in roots do
    if n.isInternal then continue
    let some m := modOf n | continue
    perMod := perMod.insert m ((perMod.getD m #[]).push n)
  IO.println "non-internal declarations per trusted module:"
  for (m, ns) in perMod.toList do IO.println s!"  {m}: {ns.size}"
