import RecursionFast.Contract
/-! Which vendored riscv-zkvm declarations does the v2 contract reach? (Stage 4; adapted from
`contract-v03/probes/TrustedClosure.lean`.) Breadth-first over the constants occurring in the
types and bodies of the declarations of the `RecursionFast.Contract.*` modules, keeping those
defined in a `RiscvZkvm.*` module. Reports each module's reached declarations and the source
lines they span. -/
open Lean Meta in
#eval show MetaM Unit from do
  let env ← getEnv
  let modOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let isVendor (n : Name) : Bool := match modOf n with
    | some m => (`RiscvZkvm).isPrefixOf m | none => false
  let isContract (n : Name) : Bool := match modOf n with
    | some m => (`RecursionFast.Contract).isPrefixOf m | none => false
  let roots := env.constants.fold (fun acc n _ => if isContract n then acc.push n else acc) #[]
  let mut seen : NameSet := {}
  let mut todo := roots.toList
  let mut vendor : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.head!; todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if isVendor n then vendor := vendor.push n
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants) |>.getD #[])
    let extra : Array Name := match ci with
      | .inductInfo v => v.ctors.toArray | .ctorInfo v => #[v.induct] | _ => #[]
    for u in used ++ extra do
      if !seen.contains u then todo := u :: todo
  let mut perMod : Std.HashMap Name (Nat × Std.HashSet Nat) := {}
  for n in vendor do
    let some m := modOf n | continue
    let some r ← findDeclarationRanges? n | continue
    let (k, ls) := perMod.getD m (0, {})
    let ls := (List.range' r.range.pos.line (r.range.endPos.line - r.range.pos.line + 1)).foldl
      (fun s i => s.insert i) ls
    perMod := perMod.insert m (k + 1, ls)
  IO.println s!"contract roots: {roots.size}"
  IO.println s!"reached vendored declarations: {vendor.size}"
  let mut total := 0
  for (m, k, ls) in perMod.toList do
    IO.println s!"  {m}: {k} decls, {ls.size} distinct source lines"
    total := total + ls.size
  IO.println s!"  total distinct source lines: {total}"
  let theorems := vendor.filter fun n => match env.find? n with | some (.thmInfo _) => true | _ => false
  IO.println s!"of which theorems: {theorems.size}"
