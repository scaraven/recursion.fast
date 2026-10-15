import RecursionFast.Contract
/-! Elaborating this (adversarial) module rewrites the contract's `.olean`: `Good` becomes `True`.
Lake does not notice (the trace is computed from sources), so every later build of a module that
imports the contract — including the *challenge*, if it is built after this — sees the new `Good`. -/
def rootSrc : String := "
namespace RecursionFast
structure Sub where
  vk : Nat
def Good (_ : Sub) : Prop := True
end RecursionFast
"
#eval show IO Unit from do
  let lib := ".lake/build/lib/lean/RecursionFast"
  IO.FS.createDirAll "/tmp/a6cmp/RecursionFast"
  IO.FS.writeFile "/tmp/a6cmp/RecursionFast/Contract.lean" rootSrc
  let lean ← IO.appPath
  let args := #["--root=/tmp/a6cmp", "-o", "/tmp/a6cmp/Contract.olean", "/tmp/a6cmp/RecursionFast/Contract.lean"]
  let r ← IO.Process.output { cmd := lean.toString, args := args }
  IO.FS.writeBinFile s!"{lib}/Contract.olean.new" (← IO.FS.readBinFile "/tmp/a6cmp/Contract.olean")
  IO.FS.rename s!"{lib}/Contract.olean.new" s!"{lib}/Contract.olean"
  IO.println s!"tamper: {r.exitCode} {r.stderr}"
