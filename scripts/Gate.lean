/-
# Environment-level hygiene and computability gate (A4-F3, A6-G1/G2)   (TRUSTED harness tool)

  lake exe gate MODULE THEOREM --manifest FILE [--computable N1,N2,...]

Loads the **elaborated environment** of `MODULE` (its `.olean` and imports; no source text is
read, so comment/string tricks are irrelevant; no `[init]` code is run, since this process never
enables initializer execution) and walks the transitive dependency closure of the certificate
`THEOREM` (types and values; inductives with their constructors and recursors).

**Trust is by content hash** (A6-G2), never by name, location or import graph: a module is
*trusted* (Lean core, Mathlib and its dependencies, the contract, the vendored `RiscvZkvm`) or
*pinned* (CompPoly, ArkLib, VCVio, PolyFun) iff every one of its `.olean` files
(`.olean`, `.olean.server`, `.olean.private`) hashes (sha256) to the organiser's manifest
`FILE` (`scripts/olean-manifest.py gen` on a clean organiser build, before any solution code ran).
A module whose path is in the manifest but whose files differ is a **tampered organiser module**
and is rejected outright. Every other module (the solution, the organiser's untrusted Library,
anything dropped into a package directory) is untrusted.

It rejects (exit code 1) if:
1. any constant in the closure is `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat` or
   `Lean.trustCompiler`, or is an axiom other than `propext`, `Classical.choice`, `Quot.sound`
   (this is `#print axioms THEOREM`, computed on the certificate itself);
2. a constant of the closure declared in an untrusted or pinned module is `unsafe`, `partial` or
   `opaque` (an `opaque`/`partial` body is invisible to the kernel);
3. **any** untrusted module registers an entry of a compiler-substitution or load-time-code
   attribute, for any target: `implemented_by`, `extern`, `export` (symbol interposition in a
   linked badge executable), `init`/`builtin_init` (code run when a compiled executable starts,
   A6-G1: `@[init f] def x := 0` is an ordinary `def` whose compiled value is `f`'s result),
   `csimp`. Pinned modules may register `csimp` lemmas (kernel-proved equalities) and `init`
   entries (their `initialize` declarations: trace classes, simp sets); these are reported;
4. with `--computable N`, a **badge-path field** of `N` has no compiled code (A7-M2, DESIGN §3).
   The badge path executes only the indexer (`VK`, `IDX`), the honest prover and the extractor
   (`badgeFields`; for `Accumulation`, `VK`/`IDX` and each step's prover and extractor). If `N`
   itself has compiled code, every field has. Otherwise `N` is unfolded (`whnf`, all
   transparency) to its constructor, `Fin k`-indexed families (`Submission*.protocol`/`scheme`)
   are checked member by member, and each badge-path field term is **compiled in this process**
   as an auxiliary definition; it passes iff the compiler emits code for it. Every other field
   (`ε`, `verify`, `qprog`, shapes, `WitMid`, `Racc`, proofs) is specification data: it is never
   executed and may be `noncomputable` (e.g. `ε := fun _ => errorCap`). "Computable" means
   *executable* (Lean has compiled code), not *feasible*: a brute-force indexer is computable.
   Feasibility is enforced only by the badge path's time and memory budget (A7-M1). No imported
   extension code runs: environment extensions keep their initial state except the pure-data
   ones the compiler needs (`pureExts`), and initializer execution is never enabled;
5. an organiser module of the environment does not match the manifest (above).
Options such as `debug.skipKernelTC` leave no trace in an `.olean`; they are defeated by the
comparator's replay through a fresh kernel (and nanoda / `leanchecker`), not by this gate.
The gate must run after the comparator, in a separate tree, with no solution process alive;
the badge executable runs afterwards as its own process (RESULT.md, "Round-3 fixes").
-/
import Lean

open Lean

/-- Manifest packages of the **pinned** class (DESIGN §13); every other manifest entry is trusted. -/
def pinnedPackages : List String := ["CompPoly", "Arklib", "VCVio", "PolyFun"]

def bannedConsts : List Name := [``sorryAx, ``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => `_current

/-- The manifest: module-relative `.olean` path (e.g. `Mathlib/Order/Basic.olean.server`) ↦
(sha256, pinned?). Lines are `<sha256>  <tag>/<path>`, tag `core`, `project` or `packages/<pkg>`. -/
def readManifest (file : System.FilePath) : IO (Std.HashMap String (String × Bool)) := do
  let mut m : Std.HashMap String (String × Bool) := {}
  for line in ← IO.FS.lines file do
    if line.isEmpty || line.startsWith "#" then continue
    let some (h, key) := (match line.splitOn "  " with | [h, k] => some (h, k) | _ => none)
      | throw <| IO.userError s!"gate: malformed manifest line {line}"
    match key.splitOn "/" with
    | "core" :: rel | "project" :: rel => m := m.insert ("/".intercalate rel) (h, false)
    | "packages" :: pkg :: rel => m := m.insert ("/".intercalate rel) (h, pinnedPackages.contains pkg)
    | _ => throw <| IO.userError s!"gate: malformed manifest key {key}"
  return m

/-- sha256 of files, by `sha256sum` in parallel batches. -/
def sha256Files (files : Array String) : IO (Std.HashMap String String) := do
  let mut tasks := #[]
  for i in [:(files.size + 255) / 256] do
    let batch := files.extract (256 * i) (256 * i + 256)
    tasks := tasks.push (← IO.asTask (IO.Process.output { cmd := "sha256sum", args := batch }))
  let mut out : Std.HashMap String String := {}
  for t in tasks do
    let r : IO.Process.Output ← IO.ofExcept t.get
    unless r.exitCode == 0 do throw <| IO.userError "gate: sha256sum failed"
    for line in r.stdout.splitOn "\n" do
      if let [h, f] := line.splitOn "  " then out := out.insert f h
  return out

/-- Trusted and pinned modules of `env` by content hash; errors for tampered organiser modules. -/
def classify (env : Environment) (manifest : Std.HashMap String (String × Bool)) :
    IO (NameSet × NameSet × Array String) := do
  let exts := ["", ".server", ".private"]
  let mut known : Array (Name × List (String × String)) := #[]   -- module, (manifest key, file)
  let mut files : Array String := #[]
  let mut errs : Array String := #[]
  for m in env.header.moduleNames do
    let rel := "/".intercalate (m.components.map (·.toString (escape := false))) ++ ".olean"
    unless manifest.contains rel do continue
    let path := (← findOLean m).toString
    let mut parts := []
    for e in exts do
      let onDisk ← System.FilePath.pathExists (path ++ e)
      if onDisk != manifest.contains (rel ++ e) then
        errs := errs.push s!"organiser module {m}: file {path ++ e} {if onDisk then "is not" else "is missing"} in the manifest"
      if onDisk then
        parts := (rel ++ e, path ++ e) :: parts
        files := files.push (path ++ e)
    known := known.push (m, parts)
  let hashes ← sha256Files files
  let mut trusted : NameSet := {}
  let mut pinned : NameSet := {}
  for (m, parts) in known do
    let ok := parts.all fun (k, f) => (manifest.get? k).map (·.1) == hashes.get? f && hashes.contains f
    if !ok then
      errs := errs.push s!"organiser module {m}: .olean does not match the manifest (tampered or stale build)"
    else if parts.any fun (k, _) => (manifest.get? k).any (·.2) then pinned := pinned.insert m
    else trusted := trusted.insert m
  return (trusted, pinned, errs)

/-- Transitive closure of the constants used by `root`. -/
partial def closure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut next := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then next := next ++ v.getUsedConstants
    match ci with
    | .inductInfo v => next := next ++ v.ctors.toArray ++ #[mkRecName n]
    | .ctorInfo v => next := next.push v.induct
    | .recInfo v => next := next ++ v.all.toArray
    | _ => pure ()
    for m in next do
      unless seen.contains m do todo := todo.push m
  return seen

/-! ### Rule 4: badge-path computability (A7-M2) -/

open Meta

/-- The computational fields the **badge path executes**, per contract structure: the holographic
indexer (`VK`, `IDX`), the honest prover and the named extractor. Fields of a nested structure
listed here are checked recursively. Everything else is specification data (never run). -/
def badgeFields : List (Name × List Name) :=
  [(`RecursionFast.Protocol, [`VK, `IDX, `prover, `extractor]),
   (`RecursionFast.Accumulation, [`VK, `IDX, `embed, `fold, `decide]),
   (`RecursionFast.Reduction, [`prover, `extractor]),
   (`RecursionFast.Submission0, [`protocol]),
   (`RecursionFast.Submission1, [`protocol]),
   (`RecursionFast.Submission2, [`scheme])]

/-- Persistent extensions whose imported state `whnf` and the compiler need here (matcher info,
so that `match` in a field term compiles). Their `addImportedFn` is core code over plain data.
All other extensions keep their initial state: no imported macro, parser, attribute, compiler
pass or `[init]` code is evaluated by the gate (it never enables initializer execution). -/
def pureExts : List Name := [`Lean.Meta.Match.Extension.extension]

def loadPureExts (env : Environment) : IO Environment := do
  let mut env := env
  for d in ← persistentEnvExtensionsRef.get do
    if pureExts.contains d.name then
      let s := d.toEnvExtension.getState (asyncMode := .sync) env
      let st ← d.addImportedFn s.importedEntries { env, opts := {} }
      env := d.toEnvExtension.setState (asyncMode := .sync) env { s with state := st }
  return env

/-- Heartbeat budget (in thousands) for unfolding and compiling the badge-path fields. -/
def gateHeartbeats : Nat := 2000000

/-- `n` has compiled code (an IR declaration). -/
def hasCode (env : Environment) (n : Name) : Bool := (IR.findEnvDecl env n).isSome

/-- Compile the closed term `v` as a fresh auxiliary definition `n` in this process (kernel-checked
first); `none` iff the compiler emitted code for it, otherwise the compiler's error. -/
def compileAux (n : Name) (v : Expr) : MetaM (Option String) := do
  let v ← instantiateMVars v
  tryCatchRuntimeEx (do
      let type ← inferType v
      let lps := (collectLevelParams (collectLevelParams {} type) v).params.toList
      addDecl (.defnDecl { name := n, levelParams := lps, type, value := v, hints := .opaque,
                           safety := .safe })
      compileDecls #[n]
      return if hasCode (← getEnv) n then none else some "the compiler emitted no code")
    fun ex => return some (← ex.toMessageData.toString)

/-- The literal `(⟨i, _⟩ : Fin n)`, proof by `decide`. -/
def finLit (n i : Nat) : Expr :=
  let lt := mkApp4 (mkConst ``LT.lt [0]) (mkConst ``Nat) (mkConst ``instLTNat) (mkRawNatLit i) (mkRawNatLit n)
  mkApp3 (mkConst ``Fin.mk) (mkRawNatLit n) (mkRawNatLit i) <|
    mkApp3 (mkConst ``of_decide_eq_true) lt (mkApp2 (mkConst ``Nat.decLt) (mkRawNatLit i) (mkRawNatLit n))
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))

/-- Field names of a structure constructor (binder names after the parameters). -/
def ctorFields (ty : Expr) (numParams : Nat) : List Name := Id.run do
  let mut out := #[]
  let mut t := ty
  let mut i := 0
  while true do
    match t with
    | .forallE n _ b _ => if i ≥ numParams then out := out.push n
                          i := i + 1; t := b
    | _ => break
  return out.toList

/-- The field argument of `x` if `x` unfolds (all transparency) to a constructor application of
structure `S`, field index `i`. -/
def ctorField? (S : Name) (i : Nat) (x : Expr) : MetaM (Option Expr) := do
  let some (.inductInfo iv) := (← getEnv).find? S | return none
  let [ctor] := iv.ctors | return none
  let x ← withTransparency .all <| whnf x
  unless x.isAppOf ctor do return none
  return x.getAppArgs[iv.numParams + i]?

/-- Replace each projection `s.f` whose structure value `s` unfolds to a constructor by that
field's argument (`{ s with IDX := … }` elaborates to `⟨s.VK, …⟩`, and `s` may itself lack
compiled code, e.g. because of its `ε`). Semantics-preserving (definitional unfolding). -/
def reduceProjs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    match e with
    | .proj S i x => return match ← ctorField? S i x with | some a => .visit a | none => .done e
    | _ =>
      let .const f _ := e.getAppFn | return .done e
      let some info ← getProjectionFnInfo? f | return .done e
      let args := e.getAppArgs
      unless !info.fromClass && args.size > info.numParams do return .done e
      match ← ctorField? info.ctorName.getPrefix info.i args[info.numParams]! with
      | some a => return .visit (mkAppN a args[info.numParams + 1:]).headBeta
      | none => return .done e)

/-- Rule 4 on the term `e` (displayed as `path`): returns the rejections. -/
partial def checkExec (path : String) (e : Expr) : MetaM (Array String) := do
  -- (a) the whole term has compiled code: then so has every field
  let mut err? ← match e with
    | .const n _ => pure (if hasCode (← getEnv) n then none else some s!"{n} has no compiled code")
    | _ => compileAux (Name.mkSimple s!"_gate_badge {path}") e
  if err?.isSome && !e.isConst then
    let e2 ← reduceProjs e
    if e2 != e then err? ← compileAux (Name.mkSimple s!"_gate_badge {path} (projections reduced)") e2
  let some err := err? | IO.println s!"gate: rule 4: {path}: compiled code"; return #[]
  let ty ← whnf (← inferType e)
  -- (b) a family over `Fin k` (`Submission*.protocol`/`scheme`): member by member
  if let .forallE _ d _ _ := ty then
    let d ← whnf d
    if d.isAppOfArity ``Fin 1 then
      if let some k ← evalNat d.appArg! then
        if k ≤ 64 then
          let mut errs := #[]
          for i in [:k] do errs := errs ++ (← checkExec s!"{path}[{i}]" (mkApp e (finLit k i)))
          return errs
  -- (c) a contract structure: unfold to its constructor, check the badge-path fields only
  let some S := ty.getAppFn.constName? | return #[s!"{path}: {err}"]
  let some fields := badgeFields.lookup S | return #[s!"{path}: {err}"]
  let some (.inductInfo iv) := (← getEnv).find? S | return #[s!"{path}: {err}"]
  let [ctor] := iv.ctors | return #[s!"{path}: {err}"]
  let some cinfo := (← getEnv).find? ctor | return #[s!"{path}: {err}"]
  let names := ctorFields cinfo.type iv.numParams
  let e' ← withTransparency .all <| whnf e
  unless e'.isAppOfArity ctor (iv.numParams + names.length) do
    return #[s!"{path}: {err}; it does not unfold to a `{ctor}` application, so its badge-path fields cannot be checked separately"]
  IO.println s!"gate: rule 4: {path}: no compiled code as a whole ({err}); checking its badge-path fields {fields}, the rest is specification data"
  let mut errs := #[]
  for f in fields do
    match names.idxOf? f with
    | some j => errs := errs ++ (← checkExec s!"{path}.{f}" e'.getAppArgs[iv.numParams + j]!)
    | none => errs := errs.push s!"{path}: structure {S} has no field {f}"
  return errs

def parseArgs : List String → Option (String × String × String × String)
  | m :: t :: rest =>
    let rec go (man comp : String) : List String → Option (String × String)
      | [] => some (man, comp)
      | "--manifest" :: f :: r => go f comp r
      | "--computable" :: c :: r => go man c r
      | _ => none
    (go "" "" rest).bind fun (man, comp) => if man.isEmpty then none else some (m, t, man, comp)
  | _ => none

def main (args : List String) : IO UInt32 := do
  let some (modName, thm, manifestFile, comp) := parseArgs args
    | throw <| IO.userError "usage: gate MODULE THEOREM --manifest FILE [--computable N1,N2,...]"
  initSearchPath (← findSysroot)
  let manifest ← readManifest manifestFile
  let env ← importModules #[{ module := modName.toName }] {} (trustLevel := 0)
  let thmName := thm.toName
  unless env.contains thmName do
    IO.eprintln s!"gate: {thm} not found in {modName}"; return 1
  -- 5: organiser modules by content hash
  let (trusted, pinned, hashErrs) ← classify env manifest
  let mut errs : Array String := hashErrs
  -- 1, 2: the closure of the certificate
  let cl := closure env thmName
  let mut axioms : Array Name := #[]
  for n in cl.toList do
    if bannedConsts.contains n then errs := errs.push s!"closure uses {n}"
    let some ci := env.find? n | continue
    if let .axiomInfo _ := ci then
      axioms := axioms.push n
      unless allowedAxioms.contains n do errs := errs.push s!"non-standard axiom {n}"
    let m := moduleOf env n
    unless trusted.contains m do
      if ci.isUnsafe then errs := errs.push s!"unsafe constant {n} (module {m})"
      match ci with
      | .opaqueInfo _ => errs := errs.push s!"opaque (or partial) constant {n} (module {m})"
      | .defnInfo v => if v.safety == .partial then errs := errs.push s!"partial definition {n} (module {m})"
      | _ => pure ()
  -- 3: compiler-substitution and load-time-code attributes registered by untrusted modules
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if trusted.contains m then continue
    let isPinned := pinned.contains m
    let idx : ModuleIdx := i
    for (d, impl) in Compiler.implementedByAttr.ext.getModuleEntries env idx (level := .private) do
      errs := errs.push s!"module {m}: @[implemented_by {impl}] on {d}"
    for (d, _) in externAttr.ext.getModuleEntries env idx (level := .private) do
      errs := errs.push s!"module {m}: @[extern] on {d}"
    for (d, sym) in exportAttr.ext.getModuleEntries env idx (level := .private) do
      errs := errs.push s!"module {m}: @[export {sym}] on {d}"
    let inits := (regularInitAttr.ext.getModuleEntries env idx (level := .private)).map (·.1) ++
      (builtinInitAttr.ext.getModuleEntries env idx (level := .private)).map (·.1)
    if inits.size > 0 then
      if isPinned then IO.println s!"gate: note: pinned dependency {m} registers {inits.size} [init] declaration(s)"
      else for d in inits do errs := errs.push s!"module {m}: [init]/[builtin_init] on {d}"
    let ncs := (Compiler.CSimp.ext.ext.getModuleEntries env idx (level := .private)).size
    if ncs > 0 then
      if isPinned then
        IO.println s!"gate: note: pinned dependency {m} registers {ncs} @[csimp] lemma(s) (proved equalities)"
      else errs := errs.push s!"module {m}: registers @[csimp] lemmas"
  -- 4: the badge-path fields of the named constants have compiled code (A7-M2)
  let comps := (comp.splitOn ",").filter (· ≠ "")
  unless comps.isEmpty do
    let cenv ← loadPureExts env
    let opts : Options := ({} : Options) |>.set `Elab.async false |>.set `maxHeartbeats gateHeartbeats
    let ctx : Core.Context := { fileName := "<gate>", fileMap := default, options := opts,
                                maxHeartbeats := gateHeartbeats * 1000 }
    let act : MetaM (Array String) := comps.foldlM (init := #[]) fun acc c => do
      unless (← getEnv).contains c.toName do return acc.push s!"--computable {c}: not found"
      return acc ++ (← checkExec c (mkConst c.toName))
    let (cerrs, _) ← (act.run' {} {}).toIO ctx { env := cenv }
    errs := errs ++ cerrs
  IO.println s!"gate: {env.header.moduleNames.size} modules, {trusted.size} trusted and {pinned.size} pinned by hash"
  IO.println s!"gate: {thm}: closure of {cl.size} constants, axioms {axioms.qsort (·.lt ·) |>.toList}"
  if errs.isEmpty then
    IO.println "gate: PASS"; return 0
  for e in errs do IO.println s!"gate: REJECT {e}"
  return 1
