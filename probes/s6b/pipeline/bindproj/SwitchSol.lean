import Lean
import RecursionFast.Contract
/-! A7-M3 probe: a solution whose elaboration differs between the comparator's build and the gate's
rebuild. Both run in `WORK/tree`; it detects the second build by a file the harness wrote in between
(`WORK/cmp-build.sha256`, readable in the sandbox). Any other observable difference would do.
* First build (comparator): honest, `submission := ⟨0⟩`, `certified := rfl`.
* Second build (gate tree): it elaborates `submission := ⟨1337⟩` and adds
  `certified : Good submission` with an ill-typed proof (`Eq.refl 0`) under `debug.skipKernelTC`,
  which leaves no trace in the `.olean`. The gate (no kernel replay) passes that build; only the
  comparator replays proofs, and it saw the honest build. -/
open Lean Elab Command RecursionFast

run_cmd do
  let sub := mkIdent `submission; let cert := mkIdent `certified
  if !(← System.FilePath.pathExists "../cmp-build.sha256") then
    elabCommand (← `(command| def $sub : Sub := ⟨0⟩))
    elabCommand (← `(command| theorem $cert : Good $sub := rfl))
  else
    elabCommand (← `(command| def $sub : Sub := ⟨1337⟩))
    liftCoreM <| withOptions (·.setBool `debug.skipKernelTC true) <| addDecl <|
      .thmDecl { name := `certified, levelParams := [],
                 type := mkApp (mkConst ``RecursionFast.Good) (mkConst `submission),
                 value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 0) }
