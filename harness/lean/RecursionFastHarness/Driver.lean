/-
# Harness: the badge executables' entry points                       (organiser harness code)

`verify VKC STMT TAPE` runs the compiled verifier `NARG cfg P` (DESIGN §3.2, §6.3): the key
`VKc.toBytes` (the `vkLen` elements of `VK L`, 8 bytes little-endian each, then the 32-byte index
root), the statement (32 elements, 256 bytes) and the tape are read from files. Exit code 0 and
`ACCEPT` iff `NARG` accepts, 1 and `REJECT` if it rejects, 2 on a malformed key or statement file
(the runner treats 2 as a failure too). A tape file longer than `tapeCap` is rejected without being
read: `NARG`'s first conjunct is `t.length ≤ tapeCap`.

`index LAYOUT.json VKC_OUT` runs the compiled indexer `index cfg P L` (untimed indexing, §6.3 step
2) on a layout JSON (`LayoutJson.parse`), writes the key bytes and prints the key digest
`VKc.digest cfg` (DESIGN §5.1, S3-A8) as hex.

Both are built against a submission module given at build time (`harness/lean/Main.lean.in`,
`harness/badge-main.py`, `harness/README.md`) and take `cfg`, `P` from the twin (`Twin.lean`).
-/
import RecursionFastHarness.LayoutJson
import RecursionFastHarness.Twin

namespace RecursionFastHarness
open RecursionFast

/-- The bytes of a file. -/
def readBytes (path : String) : IO (List UInt8) := return (← IO.FS.readBinFile path).toList

/-- A compiled key from its bytes: `8·vkLen + 32` bytes, read back so that `toBytes` gives them. -/
def parseVKc (vkLen : ℕ) (b : List UInt8) : Option (VKc vkLen) :=
  if b.length = 8 * vkLen + 32 then
    let a := (kList (b.take (8 * vkLen))).toArray
    let vkc : VKc vkLen := (fun i => a.getD i.val 0, b.drop (8 * vkLen))
    if vkc.toBytes == b then some vkc else none
  else none

/-- A statement from its 256 bytes, read back so that `stmtBytes` gives them. -/
def parseStmt (b : List UInt8) : Option Stmt :=
  if b.length = 256 then
    let a := (kList b).toArray
    let x : Stmt := fun i => a.getD i.val 0
    if stmtBytes x == b then some x else none
  else none

/-- Lowercase hex of bytes. -/
def hex (b : List UInt8) : String :=
  String.join (b.map fun c => let s := String.ofList (Nat.toDigits 16 c.toNat)
    if s.length < 2 then "0" ++ s else s)

/-- `verify VKC STMT TAPE`: exit 0 iff `NARG cfg P` accepts. -/
def verifyMain {k : ℕ} (cfg : Cfg) (P : Protocol k) (args : List String) : IO UInt32 := do
  let [vkcF, xF, tapeF] := args
    | IO.eprintln "usage: verify VKC STMT TAPE"; return 2
  let some vkc := parseVKc P.vkLen (← readBytes vkcF)
    | IO.eprintln s!"verify: {vkcF} is not a key of {8 * P.vkLen + 32} bytes"; return 2
  let some x := parseStmt (← readBytes xF)
    | IO.eprintln s!"verify: {xF} is not a statement of 256 bytes"; return 2
  if (← System.FilePath.metadata tapeF).byteSize > tapeCap.toUInt64 then
    IO.println "REJECT"; return 1                -- NARG's first conjunct: |t| ≤ tapeCap
  if NARG cfg P vkc x (← readBytes tapeF) then
    IO.println "ACCEPT"; return 0
  IO.println "REJECT"; return 1

/-- `index LAYOUT.json VKC_OUT`: write `index cfg P L`'s bytes, print its digest. -/
def indexMain {k : ℕ} (cfg : Cfg) (P : Protocol k) (args : List String) : IO UInt32 := do
  let [layoutF, outF] := args
    | IO.eprintln "usage: index LAYOUT.json VKC_OUT"; return 2
  match LayoutJson.parse (← IO.FS.readFile layoutF) with
  | .error e => IO.eprintln s!"index: {layoutF}: {e}"; return 2
  | .ok L =>
    let vkc := index cfg P L
    IO.FS.writeBinFile outF ⟨vkc.toBytes.toArray⟩
    IO.println (hex (vkc.digest cfg))
    return 0

end RecursionFastHarness
