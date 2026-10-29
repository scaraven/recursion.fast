/-
# Environment-level hygiene and computability gate (A4-F3, A6-G1/G2; v4 port)   (TRUSTED harness tool)

  lake exe gate MODULE THEOREM --manifest FILE [--computable N1,N2,...] [--allowed-imports FILE]
       [--badge-root CONST]
  lake exe gate --closure ROOT1,ROOT2,... OUT        (writes the import closure of the roots: the
                                                     allowed-imports list, scripts/org-build.sh)

Loads the **elaborated environment** of `MODULE` (its `.olean` and imports; no source text is
read, so comment/string tricks are irrelevant; no `[init]` code is run, since this process never
enables initializer execution) and walks the transitive dependency closure of the certificate
`THEOREM` (types and values; inductives with their constructors and recursors).

**Trust is by content hash** (A6-G2), never by name, location or import graph: a module is
*trusted* (Lean core, Mathlib and its dependencies, the contract) or
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
3. **any** untrusted module registers an entry of an attribute that substitutes compiled code,
   runs code at load time or changes the compiler, for any target. Lean 4.34's attributes with an
   effect on compiled code are: `implemented_by`, `extern`, `export` (symbol interposition in a
   linked badge executable), `init`/`builtin_init` (code run when a compiled executable starts,
   A6-G1: `@[init f] def x := 0` is an ordinary `def` whose compiled value is `f`'s result; also
   every `initialize`, `register_simp_attr`, `register_option`), `csimp` (replacement lemmas),
   `cpass` (a compiler-pass installer, run by every importer's compiler: S7-M1),
   `computed_field` (compiled field implementations); all rejected (`tagged_return` qualifies
   only `extern` declarations, already rejected, and is private to the compiler). `inline`, `noinline`, `macro_inline`,
   `specialize`, `never_extract` and `unbox` steer the compiler without changing what a total
   function computes, and are allowed. Pinned modules may register `csimp` lemmas (kernel-proved
   equalities), `init` entries (their `initialize` declarations: trace classes, simp sets) and the
   others; these are reported;
4. with `--computable N`, a **badge-path field** of `N` has no compiled code (A7-M2, S5-A9;
   v3: V3-S2R-A3; v4: unchanged). The v4 badge executes the compiled `acc` (the field `V`, run on
   the signed trace) and nothing else of the submission; `P` (kept as in v3) and `ext` (run by the
   per-entry liveness check until V4-A9 removed it) are still required to be compiled, a rule
   whose relaxation to `V` alone is an open question of V4-A9.
   `badgeFields`: `Submission`: `V`, `P`, `ext`. If `N` itself has compiled code, every field has.
   Otherwise `N` is unfolded (`whnf`, all transparency) to its constructor, and each badge-path
   field term is **compiled in this process** as an auxiliary definition; it passes iff the
   compiler emits code for it. Every other field (the extractor's specification `E`, `ε`, `δ`,
   `qV`, `fuel`) is specification data: it is never executed and may be `noncomputable` (e.g.
   `ε := errorCap`). "Computable" means *executable* (Lean has compiled code), not *feasible*: a
   brute-force verifier is computable. Feasibility is enforced by the badge path's time and memory
   budget (A7-M1) and, for the extractor, by the certificate's proved step bound. No imported
   extension code runs: environment extensions keep their initial state except the pure-data ones
   the compiler needs (`pureExts`), and initializer execution is never enabled;
5. an organiser module of the environment does not match the manifest (above);
6. (S7-M1, with `--allowed-imports FILE`) an untrusted module **imports** (directly) a module that
   is neither untrusted itself nor in FILE. FILE is the import closure of the organiser's roots
   (`Mathlib`, `RecursionFast.Contract`, `RecursionFast.Library`, `RecursionFast.Controls`; written
   by `gate --closure` in `scripts/org-build.sh`).
   This keeps the compiler's internals out of a submission's reach: the S7-M1 forgery overwrote a
   definition's emitted code from an elaboration-time `run_meta`, which leaves no declaration, but
   needs `Lean.Compiler.LCNF.PhaseExt` (`impureExt`, `saveImpureDeclCore`), which no module of the
   closure imports (nor `Lean` itself). A submission may import any module of Mathlib, the
   contract, the organiser library and controls, and its own modules; nothing else (`Lean`,
   `Lean.Compiler.*` beyond Mathlib's, `Lake`, …). And transitively (S6b fix pass, `rule6t`): every
   module a submission-owned module reaches is its own or in FILE, so an untrusted organiser module
   outside the list (the harness driver imports `Lean`) cannot carry the compiler in. (v3's
   frontend list for Clean, S6b-A11, is gone: v4 has no frontend);
7. (S7-M1) a **definition** declared in an untrusted module refers, in its type or value, to a
   non-theorem constant of the compiler or the environment: under `Lean.Elab`, `Lean.Compiler`,
   `Lean.IR`, `Lean.Meta`, `Lean.Environment`, `Lean.Kernel`, `Lean.Core`, the environment
   extension types, or one of `Lean.modifyEnv`, `Lean.setEnv`, `Lean.persistentEnvExtensionsRef`,
   `Lean.envExtensionsRef`, `Lean.addDecl`, `Lean.compileDecl(s)`, `unsafeCast`. A submission
   defines no elaborator, tactic, compiler pass or environment manipulation (macros, notation and
   `syntax` are fine). Theorems are exempt (their terms are never executed);
8. (S6b-A11, with `--badge-root CONST`) the module that declares `CONST` (the constant the badge
   executables are built from: the rendered challenge's `submission`) imports, transitively, a
   module that is neither untrusted nor in the `--allowed-imports` closure, i.e. it reaches the
   compiler. The badge executables import only that module (the gate prints
   `gate: badge-root-module M`), so no module that can reach the compiler's state is linked into
   them, whatever the submission's proofs import.

Each rule is a function below: `classify` (5), `rules12` over `closure` (1, 2), `rule3`, `rule6`
and `rule6t`, `rule8`, `rule7`, and `rule4` (`checkExec`). `main` runs them in that order, which is
the order of the `REJECT` lines. (v3's rule 9, frontend references, is gone with the frontend.)

**What the gate cannot see (S7-M1, S6b-M3, S6b-A20, open item O-12).** The executed code is the
code Lean's compiler emitted while elaborating the submission's badge-root module and its imports.
A metaprogram run at elaboration time (`run_meta`, `#eval`, …) leaves no declaration. Rules 6 and
8 keep `Lean.Compiler.LCNF.PhaseExt` out of reach, but not the raw route: `persistentEnvExtensionsRef`
(in `Lean.Environment`, which every Mathlib module imports) and `unsafeCast` let a `run_meta` in a
Mathlib-only module rewrite the compiler data its importers inline (`probes/s6b/gate/ForgeRaw.lean`:
the gate PASSES it, its importer's code runs `acceptAll`). The harness's source rule
(`scripts/source-rule.py`, run before any build) rejects the commands such code needs; that raises
the bar. The sound fix is O-12: badge executables regenerated from kernel terms, without linking the
submission's objects, which must ship before any ranked board opens.
-/
import Lean

open Lean

/-- Manifest packages of the **pinned** class (DESIGN §13); every other manifest entry is trusted. -/
def pinnedPackages : List String := ["CompPoly", "Arklib", "VCVio", "PolyFun"]

/-- Rule 1: constants the certificate's closure must not use. -/
def bannedConsts : List Name := [``sorryAx, ``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]
/-- Rule 1: the only axioms allowed. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The module that declares `n` (`_current` for a declaration of this process). -/
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

/-! ### Walks shared by the rules -/

/-- The nodes reachable from `roots` along `succ`, each once, in depth-first visiting order: the
one worklist behind the certificate's closure (rules 1, 2), the badge root's import closure
(rule 8). -/
def reach (roots : Array Name) (succ : Name → Array Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut order := #[]
  let mut todo := roots
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    order := order.push n
    for m in succ n do
      unless seen.contains m do todo := todo.push m
  return order

/-- The constants the type and the value of `ci` refer to. -/
def usedConsts (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]

/-- `c` is a theorem: its term is never executed (rules 7 and 9 exempt it). -/
def isTheorem (env : Environment) (c : Name) : Bool :=
  match env.find? c with | some (.thmInfo _) => true | _ => false

/-- The modules `m` imports directly (none if `m` is not a module of `env`). -/
def moduleImports (env : Environment) (m : Name) : Array Name :=
  match env.getModuleIdx? m with
  | some i => env.header.moduleData[i.toNat]!.imports.map (·.module)
  | none => #[]

/-- Rules 1, 2: the transitive closure of the constants used by `root` (types and values;
inductives with their constructors and recursors). -/
def closure (env : Environment) (root : Name) : NameSet :=
  .ofArray <| reach #[root] fun n => match env.find? n with
    | none => #[]
    | some ci => usedConsts ci ++ match ci with
      | .inductInfo v => v.ctors.toArray.push (mkRecName n)
      | .ctorInfo v => #[v.induct]
      | .recInfo v => v.all.toArray
      | _ => #[]

/-! ### Rule 4: badge-path computability (A7-M2) -/

open Meta

/-- The computational fields **rule 4 requires compiled**, per contract structure (v4, as v3's
V3-S2R-A3): the verifier `V` (the badge `verify` is the compiled `Submission.acc`, which runs `V`
on the signed trace), the prover `P`, and the extractor program `ext` (the last two no longer run
by any badge since V4-A9 removed the liveness check). Everything else (`E`, `ε`, `δ`, `qV`,
`fuel`) is specification data. -/
def badgeFields : List (Name × List Name) :=
  [(`RecursionFast.Submission, [`V, `P, `ext])]

/-- Persistent extensions whose imported state `whnf` and the compiler need here (matcher info,
so that `match` in a field term compiles). Their `addImportedFn` is core code over plain data.
All other extensions keep their initial state: no imported macro, parser, attribute, compiler
pass or `[init]` code is evaluated by the gate (it never enables initializer execution). -/
def pureExts : List Name := [`Lean.Meta.Match.Extension.extension]

/-- `env` with the imported state of the `pureExts` loaded. -/
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
  let some err := err? | do
    IO.println s!"gate: rule 4: {path}: compiled code"
    return #[]
  let ty ← whnf (← inferType e)
  -- (b) a family over `Fin k` (v0.3's `Submission*.protocol`; kept for families): member by member
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

/-! ### Rule 7: the compiler's and the environment's API (S7-M1) -/

/-- Rule 7: name prefixes of the compiler's and the environment's API. -/
def metaPrefixes : List Name :=
  [`Lean.Elab, `Lean.Compiler, `Lean.IR, `Lean.Meta, `Lean.Environment, `Lean.Kernel, `Lean.Core,
   `Lean.EnvExtension, `Lean.EnvExtensionInterfaceUnsafe, `Lean.PersistentEnvExtension,
   `Lean.SimplePersistentEnvExtension, `Lean.ScopedEnvExtension, `Lean.MonadEnv]

/-- Rule 7: single constants of the environment's API. -/
def metaConsts : List Name :=
  [`Lean.modifyEnv, `Lean.setEnv, `Lean.persistentEnvExtensionsRef, `Lean.envExtensionsRef,
   `Lean.addDecl, `Lean.compileDecl, `Lean.compileDecls, `Lean.addAndCompile, `unsafeCast]

/-- Rule 7: `c` is a non-theorem constant of the compiler's or the environment's API. -/
def isMetaConst (env : Environment) (c : Name) : Bool :=
  (metaConsts.contains c || metaPrefixes.any (·.isPrefixOf c)) && !isTheorem env c

/-! ### The rules -/

/-- What the rules read: the environment, its modules classified by content hash (rule 5), and the
module lists of the command line. -/
structure GateCtx where
  env : Environment
  trusted : NameSet
  pinned : NameSet
  /-- `--allowed-imports`: the import closure of the organiser's roots (rules 6, 8). -/
  allowed : NameSet

/-- `m` is neither trusted nor pinned by content hash. -/
def GateCtx.untrusted (g : GateCtx) (m : Name) : Bool := !g.trusted.contains m && !g.pinned.contains m

/-- The modules of the environment with their indices, in the header's order. -/
def GateCtx.modules (g : GateCtx) : Array (Name × ModuleIdx) :=
  g.env.header.moduleNames.mapIdx fun i m => (m, i)

/-- Rule 1 on the constant `n` of the certificate's closure: banned, or a non-standard axiom. -/
def rule1 (n : Name) (ci? : Option ConstantInfo) : Array String :=
  (if bannedConsts.contains n then #[s!"closure uses {n}"] else #[]) ++
  match ci? with
  | some (.axiomInfo _) => if allowedAxioms.contains n then #[] else #[s!"non-standard axiom {n}"]
  | _ => #[]

/-- Rule 2 on the constant `n` of the certificate's closure, declared in the non-trusted module
`m`: `unsafe`, `opaque` or `partial`. -/
def rule2 (n m : Name) (ci : ConstantInfo) : Array String :=
  (if ci.isUnsafe then #[s!"unsafe constant {n} (module {m})"] else #[]) ++
  match ci with
  | .opaqueInfo _ => #[s!"opaque (or partial) constant {n} (module {m})"]
  | .defnInfo v => if v.safety == .partial then #[s!"partial definition {n} (module {m})"] else #[]
  | _ => #[]

/-- Rules 1 and 2 on the closure `cl`, constant by constant; and the closure's axioms. -/
def rules12 (g : GateCtx) (cl : NameSet) : Array String × Array Name := Id.run do
  let mut errs := #[]
  let mut axioms := #[]
  for n in cl.toList do
    let ci? := g.env.find? n
    errs := errs ++ rule1 n ci?
    let some ci := ci? | continue
    if ci matches .axiomInfo _ then axioms := axioms.push n
    let m := moduleOf g.env n
    unless g.trusted.contains m do errs := errs ++ rule2 n m ci
  return (errs, axioms)

/-- Rule 3 on the non-trusted module `m` (index `i`): its entries of the attributes that substitute
compiled code, run code at load time or change the compiler. `implemented_by`, `extern` and
`export` are rejected outright; `[init]`, `@[csimp]`, `@[cpass]` and `@[computed_field]` entries
are reported for a pinned module (`gate: note:`) and rejected for an untrusted one. -/
def rule3 (g : GateCtx) (m : Name) (i : ModuleIdx) : IO (Array String) := do
  let mut errs := #[]
  for (d, impl) in Compiler.implementedByAttr.ext.getModuleEntries g.env i (level := .private) do
    errs := errs.push s!"module {m}: @[implemented_by {impl}] on {d}"
  for (d, _) in externAttr.ext.getModuleEntries g.env i (level := .private) do
    errs := errs.push s!"module {m}: @[extern] on {d}"
  for (d, sym) in exportAttr.ext.getModuleEntries g.env i (level := .private) do
    errs := errs.push s!"module {m}: @[export {sym}] on {d}"
  -- `count` entries described as `what`: a note for a pinned module, the rejections `rej` otherwise
  let pinnedNote (count : Nat) (what : String) (rej : Array String) : IO (Array String) := do
    if count == 0 then return #[]
    unless g.pinned.contains m do return rej
    IO.println s!"gate: note: pinned dependency {m} registers {count} {what}"
    return #[]
  let inits := (regularInitAttr.ext.getModuleEntries g.env i (level := .private)).map (·.1) ++
    (builtinInitAttr.ext.getModuleEntries g.env i (level := .private)).map (·.1)
  errs := errs ++ (← pinnedNote inits.size "[init] declaration(s)"
    (inits.map fun d => s!"module {m}: [init]/[builtin_init] on {d}"))
  errs := errs ++ (← pinnedNote (Compiler.CSimp.ext.ext.getModuleEntries g.env i (level := .private)).size
    "@[csimp] lemma(s) (proved equalities)" #[s!"module {m}: registers @[csimp] lemmas"])
  -- S7-M1: compiler-pass installers, computed fields
  for (a, ds) in [("cpass", Compiler.LCNF.passManagerExt.getModuleEntries g.env i (level := .private)),
      ("computed_field", Elab.ComputedFields.computedFieldAttr.ext.getModuleEntries g.env i (level := .private))] do
    errs := errs ++ (← pinnedNote ds.size s!"@[{a}] entr(y/ies)" (ds.map fun d => s!"module {m}: @[{a}] on {d}"))
  return errs

/-- Rule 6 on the untrusted module `m` (index `i`): each direct import that is neither untrusted
nor in the allowed closure. -/
def rule6 (g : GateCtx) (m : Name) (i : ModuleIdx) : Array String :=
  g.env.header.moduleData[i.toNat]!.imports.filterMap fun imp =>
    if g.untrusted imp.module || g.allowed.contains imp.module then none
    else some s!"module {m} imports {imp.module}, which is outside the allowed imports"

/-- A submission-owned module: untrusted, and not one of the organiser's modules named by the allowed
closure (a submission's module roots are fresh, `harness/evaluate.py`). -/
def GateCtx.submissionOwned (g : GateCtx) (m : Name) : Bool :=
  g.untrusted m && !g.allowed.contains m

/-- Rule 6, transitive (S6b-M3 fix pass) on the submission-owned module `m`: every module it
reaches is submission-owned or in the allowed closure; so an untrusted organiser module outside the
list (e.g. the harness driver, which imports `Lean`) cannot carry the compiler into a submission. -/
def rule6t (g : GateCtx) (m : Name) : Array String :=
  let bad := (reach #[m] (moduleImports g.env)).filter fun n =>
    !(g.submissionOwned n || g.allowed.contains n)
  if bad.isEmpty then #[] else
    #[s!"module {m} reaches (transitively) {bad.size} module(s) outside the allowed imports, " ++
      s!"e.g. {bad.toList.take 3} (rule 6)"]

/-- Rule 7 on the untrusted module `m` (index `i`): each definition (not a theorem) whose type or
value refers to the compiler's or the environment's API. -/
def rule7 (g : GateCtx) (m : Name) (i : ModuleIdx) : Array String :=
  g.env.header.moduleData[i.toNat]!.constNames.filterMap fun n =>
    match g.env.find? n with
    | none | some (.thmInfo _) => none
    | some ci =>
      let bad := (usedConsts ci).filter (isMetaConst g.env)
      if bad.isEmpty then none
      else some s!"module {m}: {n} refers to the compiler/environment API ({bad.toList.take 3})"

/-- Rule 8 on the badge root `r`: its module and that module's transitive imports are untrusted
or in the allowed (compiler-free) closure. On success prints `gate: badge-root-module M`. -/
def rule8 (g : GateCtx) (r : Name) : IO (Array String) := do
  unless g.env.contains r do return #[s!"--badge-root {r}: not found"]
  let m := moduleOf g.env r
  let bad := (reach #[m] (moduleImports g.env)).filter fun n => !(g.untrusted n || g.allowed.contains n)
  if bad.isEmpty then
    IO.println s!"gate: badge-root-module {m}"
    return #[]
  return #[s!"badge root {r} is declared in module {m}, which imports (transitively) " ++
    s!"{bad.size} module(s) outside the compiler-free closure, e.g. {bad.toList.take 3} (rule 8)"]

/-- Rule 4 on the constants `comps`, in this process, over the environment with the `pureExts`
loaded. -/
def rule4 (g : GateCtx) (comps : List String) : IO (Array String) := do
  if comps.isEmpty then return #[]
  let opts : Options := ({} : Options) |>.set `Elab.async false |>.set `maxHeartbeats gateHeartbeats
  let ctx : Core.Context := { fileName := "<gate>", fileMap := default, options := opts,
                              maxHeartbeats := gateHeartbeats * 1000 }
  let act : MetaM (Array String) := comps.foldlM (init := #[]) fun acc c => do
    unless (← getEnv).contains c.toName do return acc.push s!"--computable {c}: not found"
    return acc ++ (← checkExec c (mkConst c.toName))
  return (← (act.run' {} {}).toIO ctx { env := ← loadPureExts g.env }).1

/-! ### Command line -/

/-- The command line, after `MODULE THEOREM`: the options by name. -/
structure GateArgs where
  manifest : String := ""
  computable : String := ""
  allowed : String := ""
  badgeRoot : String := ""

/-- `MODULE THEOREM` and the options; `none` on a malformed command line, without `--manifest`, or
with `--badge-root` but no `--allowed-imports`. -/
def parseArgs : List String → Option (String × String × GateArgs)
  | m :: t :: rest =>
    let rec go (a : GateArgs) : List String → Option GateArgs
      | [] => some a
      | "--manifest" :: f :: r => go { a with manifest := f } r
      | "--computable" :: c :: r => go { a with computable := c } r
      | "--allowed-imports" :: f :: r => go { a with allowed := f } r
      | "--badge-root" :: c :: r => go { a with badgeRoot := c } r
      | _ => none
    (go {} rest).bind fun a =>
      if a.manifest.isEmpty || (!a.badgeRoot.isEmpty && a.allowed.isEmpty) then none else some (m, t, a)
  | _ => none

/-- Module names, one per line. -/
def readNames (file : String) : IO NameSet := do
  if file.isEmpty then return {}
  return (← IO.FS.lines file).foldl (init := {}) fun s l => if l.isEmpty then s else s.insert l.toName

/-- The import closure of `roots`, one module per line (`gate --closure`). -/
def writeClosure (roots : String) (out : String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules ((roots.splitOn ",").toArray.map fun r => { module := r.toName }) {}
    (trustLevel := 0)
  let ms := env.header.moduleNames.map (·.toString) |>.qsort (· < ·)
  IO.FS.writeFile out (String.join (ms.toList.map (· ++ "\n")))
  IO.println s!"gate: wrote the import closure of {roots} ({ms.size} modules) to {out}"
  return 0

/-- The rules in the order of their `REJECT` lines: 5, 1–2, 3, 6, 8, 7, 4. -/
def main (args : List String) : IO UInt32 := do
  if let ["--closure", roots, out] := args then return ← writeClosure roots out
  let some (modName, thm, ga) := parseArgs args
    | throw <| IO.userError ("usage: gate MODULE THEOREM --manifest FILE [--computable N1,N2,...] " ++
        "[--allowed-imports FILE] [--badge-root CONST (needs --allowed-imports)]" ++
        "  |  gate --closure ROOT1,ROOT2,... OUT")
  let allowed ← readNames ga.allowed
  initSearchPath (← findSysroot)
  let manifest ← readManifest ga.manifest
  let env ← importModules #[{ module := modName.toName }] {} (trustLevel := 0)
  let thmName := thm.toName
  unless env.contains thmName do
    IO.eprintln s!"gate: {thm} not found in {modName}"; return 1
  let (trusted, pinned, hashErrs) ← classify env manifest
  let g : GateCtx := { env, trusted, pinned, allowed }
  let cl := closure env thmName
  let (errs12, axioms) := rules12 g cl
  let mut errs := hashErrs ++ errs12
  let mods := g.modules
  for (m, i) in mods do
    unless trusted.contains m do errs := errs ++ (← rule3 g m i)
  if !ga.allowed.isEmpty then
    for (m, i) in mods do
      if g.untrusted m then errs := errs ++ rule6 g m i
    for (m, _) in mods do
      if g.submissionOwned m then errs := errs ++ rule6t g m
  if !ga.badgeRoot.isEmpty then errs := errs ++ (← rule8 g ga.badgeRoot.toName)
  for (m, i) in mods do
    if g.untrusted m then errs := errs ++ rule7 g m i
  errs := errs ++ (← rule4 g ((ga.computable.splitOn ",").filter (· ≠ "")))
  IO.println s!"gate: {env.header.moduleNames.size} modules, {trusted.size} trusted and {pinned.size} pinned by hash"
  IO.println s!"gate: {thm}: closure of {cl.size} constants, axioms {axioms.qsort (·.lt ·) |>.toList}"
  if errs.isEmpty then
    IO.println "gate: PASS"; return 0
  for e in errs do IO.println s!"gate: REJECT {e}"
  return 1
