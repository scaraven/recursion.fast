/-
`TokenSweep`: the token table of the allowed import closure (S9D-M1 fix pass; a test tool, not
part of the badge path or the gate).

  (cd ORG && lake env lean --run SCRIPTS/TokenSweep.lean LIST...)   # ORG: the organiser package

Imports every module named in the LIST files (one per line: `import-allowlist.txt` and
`import-frontend.txt`, so every module a submission may import, transitively) and prints the
parser token table, one token per line, sorted. `tests/source-rule/sweep.py` then requires every
keyword-like token to be rejected by `scripts/source-rule.py` or listed in
`tests/source-rule/reviewed-tokens.txt`, so a toolchain or Mathlib bump that adds a keyword fails
CI until the keyword is reviewed. Non-reserved keywords (`&"run_tac"`) and scoped ones (Qq's
`by_elabq`, `run_tacq`) are not in the table; the source rule lists them from a review of the
packages' syntax declarations.

`unsafe` because importing Mathlib runs its `initialize` declarations
(`enableInitializersExecution`), which the parser extension needs to rebuild the table; this is
what `lean` does for any file that imports these modules.
-/
import Lean
open Lean

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mut mods : Array Import := #[]
  for f in args do
    for l in ← IO.FS.lines f do
      unless l.isEmpty do mods := mods.push { module := l.toName }
  let env ← importModules mods {} (loadExts := true)
  let toks := (Parser.parserExtension.getState env).tokens.values.qsort (· < ·)
  for t in toks do IO.println t
  IO.eprintln s!"TokenSweep: {mods.size} modules, {toks.size} tokens"
  return 0
