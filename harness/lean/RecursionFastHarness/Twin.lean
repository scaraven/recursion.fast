/-
# Harness: the executable twin of a submission                         (organiser harness code)

The badge executables (`verify`, `index`) run `NARG cfg P` and `index cfg P` of the submission.
A submission is usually `noncomputable` as a whole: its declared errors `ε` are reals (e.g.
`errorCap`), and its Lean prover may be noncomputable too. The gate's rule 4 allows that and
requires compiled code only for the fields the badge path executes (S5-A9, `scripts/Gate.lean`).
Lean cannot compile `main := … S.P …` when `S` has no code, so the executables use the **twin**:

  `harness_twin P' cfg' := S`

unfolds `S` (all transparency) to its constructor (a `Submission`, a `SubmissionR` through its
`toSubmission`, or any structure with fields `P` and `cfg`), unfolds its `P` to `Protocol.mk`, and
defines `P' : Protocol k` with the same field terms for `k_range`, `n`, `shape`, `vkLen`, `VK`,
`idxShape`, `IDX`, `verify` and the proofs, and executable placeholders for the three fields
`NARG` and `index` never read: the prover (`zeroProver`), the extractor (`zeroExtractor`) and the
errors (`0`); `cfg' := S.cfg`'s term. Projections of structures that unfold to a constructor are
replaced by the field (as the gate's own, Lean-core-only `reduceProjs` does), so
`{ s with ε := … }` compiles even if `s` does not. Both definitions are compiled; the
executable's `main` uses them.

The twin is only an executable copy: the generated main module states, and the kernel checks by
`rfl`, that `NARG cfg' P'` **is** `NARG S.cfg S.P` and `index cfg' P'` **is** `index S.cfg S.P`
(`harness/lean/Main.lean.in`). So the thing timed is the thing the certificate is about, up to the
Lean compiler.
-/
import Lean
import RecursionFast.Contract

namespace RecursionFastHarness
open Lean Meta Elab Command RecursionFast
open scoped NNReal

/-- A value of every round type (all zeros). -/
def Round.zero : (r : Round) → r.Ty
  | .msg _ => fun _ => 0
  | .chal _ _ => (fun _ => ⟨0, 0, 0⟩, fun _ => 0)

/-- The twin's prover: every message all zeros. Never run (the native prover is). -/
def zeroProver {n : ℕ} (sh : Fin n → Round) :
    Strategy sh (Layout K × Stmt) (List (Table K)) Unit Unit where
  next _ _ m _ := Round.zero (sh m.1)
  output _ _ _ := ((), ())

/-- The twin's extractor: the empty image, no fuel. Never run. -/
def zeroExtractor (k n : ℕ) : ExtractorImage k n where
  img := ⟨[], []⟩
  img_le := by decide
  fuel _ := 0
  fuel_le := by simp

/-- The twin's errors: `0` (never read by `NARG` or `index`). -/
def zeroErr {n : ℕ} (sh : Fin n → Round) : ChallengeIdx sh → ℝ≥0 := fun _ => 0

/-- The fields of `x` by name, if `x` unfolds (all transparency) to the constructor of a
structure; with the structure's name and parameters. -/
def ctorApp? (x : Expr) : MetaM (Option (Name × Array Expr × List (Name × Expr))) := do
  let x ← withTransparency .all <| whnf x
  let some (.ctorInfo cv) := (← getEnv).find? x.getAppFn.constName! | return none
  let some (.inductInfo iv) := (← getEnv).find? cv.induct | return none
  unless iv.ctors.length == 1 && x.getAppNumArgs == cv.numParams + cv.numFields do return none
  let some info := getStructureInfo? (← getEnv) cv.induct | return none
  let args := x.getAppArgs
  return some (cv.induct, args[:cv.numParams].toArray,
    (info.fieldNames.toList.zip (args[cv.numParams:].toArray.toList)))

/-- Replace each projection `s.f` whose structure value unfolds to a constructor by that field's
argument (definitional unfolding). The gate's `reduceProjs` does the same with its own matcher
(`ctorField?`: no structure info, no arity check); the kernel's `rfl` in the main module is what
binds this twin to the submission. -/
def reduceProjs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    let field? (S : Name) (i : ℕ) (x : Expr) : MetaM (Option Expr) := do
      let some (S', _, fs) ← ctorApp? x | return none
      unless S' == S do return none
      return (fs[i]?).map (·.2)
    match e with
    | .proj S i x => return match ← field? S i x with | some a => .visit a | none => .done e
    | _ =>
      let .const f _ := e.getAppFn | return .done e
      let some info ← getProjectionFnInfo? f | return .done e
      let args := e.getAppArgs
      unless !info.fromClass && args.size > info.numParams do return .done e
      match ← field? info.ctorName.getPrefix info.i args[info.numParams]! with
      | some a => return .visit (mkAppN a args[info.numParams + 1:]).headBeta
      | none => return .done e)

/-- The submission's protocol and configuration terms: unfold to a constructor, follow
`toSubmission`, read the fields `P` and `cfg`. -/
partial def findPCfg (e : Expr) : MetaM (Expr × Expr) := do
  let some (S, _, fs) ← ctorApp? e | throwError "harness_twin: {e} does not unfold to a structure"
  if let some s := fs.lookup `toSubmission then return ← findPCfg s
  match fs.lookup `P, fs.lookup `cfg with
  | some p, some c => return (p, c)
  | _, _ => throwError "harness_twin: structure {S} has no fields P and cfg (nor toSubmission)"

/-- Add and compile a definition; fail with the compiler's message if it emits no code. -/
def addCompiled (n : Name) (type value : Expr) : MetaM Unit := do
  let value ← instantiateMVars value
  addDecl (.defnDecl { name := n, levelParams := [], type, value, hints := .abbrev, safety := .safe })
  compileDecls #[n]
  unless (IR.findEnvDecl (← getEnv) n).isSome do
    throwError "harness_twin: no compiled code for {n}"

/-- `harness_twin P' cfg' := S`: the executable twin of the submission `S` (module header). -/
syntax (name := harnessTwin) "harness_twin " ident ident " := " term : command

@[command_elab harnessTwin, inherit_doc harnessTwin]
def elabHarnessTwin : CommandElab := fun stx => do
  let `(harness_twin $p:ident $c:ident := $s:term) := stx | throwUnsupportedSyntax
  let ns ← getCurrNamespace
  liftTermElabM do
    let sE ← instantiateMVars (← Term.elabTerm s none)
    Term.synthesizeSyntheticMVarsNoPostponing
    let (pE, cfgE) ← findPCfg (← instantiateMVars sE)
    let some (S, params, fs) ← ctorApp? pE | throwError "harness_twin: the protocol does not unfold to a constructor"
    unless S == ``Protocol do throwError "harness_twin: P is a {S}, not a Protocol"
    let f (n : Name) : MetaM Expr := do
      let some v := fs.lookup n | throwError "harness_twin: Protocol has no field {n}"
      reduceProjs (← instantiateMVars v)
    let k := params[0]!
    let (nE, shE) := (← f `n, ← f `shape)
    let twin := mkAppN (mkConst ``Protocol.mk) #[k, ← f `k_range, nE, ← f `n_le, shE, ← f `vkLen,
      ← f `vkLen_le, ← f `VK, ← f `idxShape, ← f `IDX, ← f `shape_ok,
      mkApp2 (mkConst ``zeroProver) nE shE, ← f `verify, mkApp2 (mkConst ``zeroExtractor) k nE,
      mkApp2 (mkConst ``zeroErr) nE shE]
    check twin
    addCompiled (ns ++ p.getId) (mkApp (mkConst ``Protocol) k) twin
    addCompiled (ns ++ c.getId) (mkConst ``Cfg) (← reduceProjs (← instantiateMVars cfgE))

end RecursionFastHarness
