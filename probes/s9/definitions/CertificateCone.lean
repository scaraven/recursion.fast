import RecursionFast.Contract
/-! S9 (definitions lens): which trusted declarations does a rendered certificate actually assert?
Roots: the types of the R stub's `certified` (`CertificateR D S ∧ S.entry.C = C ∧
S.toSubmission = leaf`) and of the L stub's, i.e. the constants `CertificateR`, `Certificate`,
`SubmissionR`, `Submission`, `DeclaredR`, `Declared` (with constructors and projections of every
reached structure). Reports the non-internal `RecursionFast.Contract*` declarations NOT in that
cone (trusted text that no certificate states) and the cone's size per module. -/
open Lean Meta

#eval show MetaM Unit from do
  let env ← getEnv
  let modOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let inContract (n : Name) : Bool := match modOf n with
    | some m => (`RecursionFast.Contract).isPrefixOf m | none => false
  let roots := [``RecursionFast.CertificateR, ``RecursionFast.Certificate, ``RecursionFast.SubmissionR,
    ``RecursionFast.Submission, ``RecursionFast.DeclaredR, ``RecursionFast.Declared]
  let mut seen : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    let n := todo.head!; todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants) |>.getD #[])
    let extra : Array Name := match ci with
      | .inductInfo v => v.ctors.toArray ++ ((getStructureInfo? env n).map
          (fun si => si.fieldNames.map (n ++ ·)) |>.getD #[])
      | .ctorInfo v => #[v.induct] | _ => #[]
    for u in used ++ extra do
      if !seen.contains u then todo := u :: todo
  let all := env.constants.fold (fun acc n _ =>
    if inContract n && !n.isInternal then acc.push n else acc) #[]
  let isAux (n : Name) : Bool :=
    let s := n.toString
    s.endsWith ".injEq" || s.endsWith ".inj" || s.endsWith ".sizeOf_spec" || s.endsWith ".noConfusion" ||
    s.endsWith ".noConfusionType" || s.endsWith ".casesOn" || s.endsWith ".recOn" ||
    s.endsWith ".brecOn" || s.endsWith ".below" || s.endsWith ".rec" || s.endsWith ".ctorIdx" ||
    s.endsWith ".elim" || s.endsWith ".ctorElim" || s.endsWith ".ctorElimType" ||
    s.endsWith ".binductionOn" || s.endsWith "ofNat_ctorIdx" || (s.splitOn ".eq_").length > 1 ||
    s.endsWith ".eq_def" || (s.splitOn "._sizeOf").length > 1 || (s.splitOn "sizeOf").length > 1 ||
    s.endsWith ".mk" || (s.splitOn "._unsafe_rec").length > 1 || (s.splitOn "match_").length > 1 ||
    (s.splitOn "Decidable").length > 1 || s.endsWith ".toCtorIdx" || s.endsWith ".ofNat" ||
    s.endsWith ".noConfusion_eq" || (s.splitOn ".brecOn").length > 1 || s.endsWith ".eq"
  let outside := all.filter fun n => !seen.contains n && !isAux n
  let inside := all.filter fun n => seen.contains n && !isAux n
  IO.println s!"non-internal, non-auxiliary contract declarations: {inside.size + outside.size}"
  IO.println s!"  in the certificate cone: {inside.size}"
  IO.println s!"  outside it ({outside.size}):"
  for n in outside.qsort (·.toString < ·.toString) do
    IO.println s!"    {n}  [{(modOf n).getD `_}]"
