/-
Stage 6b fix-pass regression (S6b-M3, the review's recommended `ForgeRaw.lean`): the S7-M1
forgery through the RAW route, under Mathlib-only imports (every import is in gate rule 6's
allowlist; no `import Lean`). A `run_meta` finds the compiler's `monoExt`/`baseExt` in
`persistentEnvExtensionsRef` (in `Lean.Environment`, imported by every Mathlib module), casts them
with `unsafeCast`, and replaces the compiler data of `dec` (`@[inline]`) by `acceptAll`'s. The
kernel sees the honest `dec` (`dec_rejects` by `decide`); any module that imports this one and calls
`dec` (the badge executables' main module, which builds the twin) inlines `acceptAll`
(`probes/s6b/gate/UseRaw.lean`: its emitted `useDec` is `msg == msg`).
No gate rule catches it: the imports pass rule 6 (and rule 8 as a badge root), the `run_meta`
leaves no declaration for rules 7 and 3, `@[inline]` is allowed. The harness's source rule
(`scripts/source-rule.py`) rejects it (`run_meta`, `unsafeCast`, `persistentEnvExtensionsRef`).
The sound fix is O-12.
-/
import Mathlib
import RecursionFast.Contract
import RecursionFast.Controls.Toy

/- S9 variant (probes/s9/definitions/srcrule): ForgeRaw with two lines inserted after the imports.
`example : Nat := r#check r` is the identifier `r` and the allowed command `#check r` to Lean, but
`scripts/source-rule.py` reads `r#` as a raw-string opener and skips to the end of the file, so the
`open Lean`, `run_meta`, `unsafeCast` and `persistentEnvExtensionsRef` below are never scanned. -/
def r : Nat := 0
example : Nat := r#check r
open Lean RecursionFast RecursionFast.Controls

namespace S7Raw

/-- The decision as the kernel sees it: the toy's. -/
@[inline] def dec (vk : Fin 1 → K) (x : Stmt) (idx msg : List K) : Bool := toyDecide 24 vk x idx msg

/-- What importers inline instead. -/
@[inline] def acceptAll (_ : Fin 1 → K) (_ : Stmt) (_ idx : List K) : Bool := idx == idx

run_meta do
  for e in (← persistentEnvExtensionsRef.get) do
    if e.name == `Lean.Compiler.LCNF.monoExt || e.name == `Lean.Compiler.LCNF.baseExt then
      let ext : PersistentEnvExtension (Compiler.LCNF.Decl .pure) (Compiler.LCNF.Decl .pure)
          (PersistentHashMap Name (Compiler.LCNF.Decl .pure)) := unsafe unsafeCast e
      let some d := (ext.getState (← getEnv)).find? ``S7Raw.acceptAll | throwError "no decl"
      modifyEnv fun env => ext.addEntry env { d with name := ``S7Raw.dec }

theorem h24 : 20 ≤ 24 ∧ 24 ≤ 28 := by decide

/-- The toy with its verifier routed through `dec`. -/
def P : Protocol 24 :=
  { toy 24 h24 with
    verify := fun vk x _ => .query 0 0 fun idx => .query 1 0 fun msg => .done (dec vk x idx msg) }

/-- Secure: `P` is the toy up to unfolding `dec`. -/
theorem P_secure : P.Secure := toy_secure 24 h24

def submission : Submission 24 := ⟨P, ⟨.blake2s, 2, by decide⟩, P_secure⟩

/-- The leaf-board certificate (image included, S7-A5). -/
theorem certified : Certificate ⟨24, .blake2s, 2, firstMsgImg⟩ submission := ⟨⟨rfl, rfl⟩, rfl⟩

/-- The kernel: `dec` rejects the empty leaves. -/
theorem dec_rejects : dec (fun _ => 0) (fun _ => 0) [] [] = false := by decide

end S7Raw
