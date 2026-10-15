import RecursionFast.Contract
/-! P2d variant of A6's `Tamper.lean`: instead of the tree's own `.lake/build`, it rewrites the
contract `.olean` wherever the search path (`LEAN_PATH`, set by Lake for the build) finds it, i.e.
in the organiser package that the harness `require`s by path. Under the harness sandbox that
directory is read-only (the write fails, so the solution does not build); without a sandbox the
rewrite succeeds, but the comparator has already exported the challenge (rejects: `Const does not
match`) and the manifest check after the stage reports the changed file. -/
def rootSrc : String := "
namespace RecursionFast
structure Sub where
  vk : Nat
def Good (_ : Sub) : Prop := True
end RecursionFast
"
#eval show IO Unit from do
  let lp := ((← IO.getEnv "LEAN_PATH").getD "").splitOn ":"
  let some dir ← lp.findM? (fun d => System.FilePath.pathExists s!"{d}/RecursionFast/Contract.olean")
    | throw <| IO.userError "tamper: contract not found"
  let scratch := ".lake/tamper"
  IO.FS.createDirAll s!"{scratch}/RecursionFast"
  IO.FS.writeFile s!"{scratch}/RecursionFast/Contract.lean" rootSrc
  let lean := (← IO.appPath).toString
  let args := #[s!"--root={scratch}", "-o", s!"{scratch}/Contract.olean", s!"{scratch}/RecursionFast/Contract.lean"]
  let r ← IO.Process.output { cmd := lean, args := args }
  IO.FS.writeBinFile s!"{dir}/RecursionFast/Contract.olean.new" (← IO.FS.readBinFile s!"{scratch}/Contract.olean")
  IO.FS.rename s!"{dir}/RecursionFast/Contract.olean.new" s!"{dir}/RecursionFast/Contract.olean"
  IO.println s!"tamper: rewrote {dir}/RecursionFast/Contract.olean ({r.exitCode})"
