/-
# The badge's glue (TRUSTED harness code)

Everything the badge executable `verify` does around the check. It is compiled with the
organiser's package (`lake build`, `harness/org-setup.sh` step 1) before any entry exists, in a
module that does **not** import the entry's solution, so every instance, notation and name in this
file is resolved against Lean core and the organiser's own modules, and its compiled code (stored
in this module's `.olean`, which the olean manifest hashes) is what the badge links. The per-entry
module (`harness/badge/Verify.lean.in`, rendered and built by `harness/evaluate.py`) imports the
solution and this module and defines only

    def main : List String → IO UInt32 := RFBadge.main RecursionFast.Challenge.submission

so the one thing of the entry that reaches the badge is the value `submission` (its `V` runs inside
`acc`), passed as an ordinary argument. `RFBadge.main` has no instance-implicit or auto-bound
argument, so nothing is resolved in the per-entry module. The compiler may inline or specialise
this module's code there, but it works on the compiled code stored here and never elaborates it
again, so an entry-declared instance (a `HSub Nat Nat Nat` that shrinks the time, a `HOr UInt64`
that changes a length word) or notation cannot change it (`tests/harness/accprobe/`, the hostile
submission). After the badge build the gate checks that the per-entry module declares that `main`
alone, with exactly that value, and registers no attribute (`harness/lean-tools/Gate.lean`,
`--wiring`), which an entry's notation cannot fake either.

What runs:

* `parseSigned`: the signed-proof file (`harness/FORMAT.md`, normative), strictly: `none` unless
  the bytes are exactly one encoding. Lengths are read as little-endian `u64` at byte level (no
  word list), so parsing is linear and cheap.
* `parseHex32`: a statement or key, 64 hexadecimal characters.
* `check`: the contract's `acc` through `Submission.accF`, proved equal to it (`Library/Fast.lean`,
  `accF_eq`), on the parsed file.
* `timedCheck`: one check between two readings of the monotonic clock (the badge's own `NS`). The
  runner also times every request from outside the process and judges `v_cap` on the larger of the
  two (`harness/rfh/checks.py`).

The command line (`main`):

    verify VK_HEX STMT_HEX FILE      prints `accept NS` or `reject NS`; exit 0 iff accepted
    verify --batch LIST              LIST: lines `VK_HEX STMT_HEX FILE`; one `accept NS` or
                                     `reject NS` line per input line; exit 0
    verify --serve                   the same lines as requests on standard input, each answered
                                     (and flushed) before the next is read; exit 0 at the end of
                                     the input (the runner's mode)

A malformed input line is a harness error (exit 2).
-/
import RecursionFast.Library.Fast

namespace RFBadge
open RecursionFast

/-- The number with the 8 little-endian bytes of `b` at offset `o` (zero beyond the end). -/
def u64At (b : ByteArray) (o : Nat) : Nat :=
  let g (i : Nat) : UInt64 := (b.get! (o + i)).toUInt64 <<< (8 * i).toUInt64
  (g 0 ||| g 1 ||| g 2 ||| g 3 ||| g 4 ||| g 5 ||| g 6 ||| g 7).toNat

/-- The 32 bytes of `b` at offset `o`, as a digest (zero bytes beyond the end). -/
def digestAt (b : ByteArray) (o : Nat) : Digest :=
  let a := (b.extract o (o + 32)).data
  if h : a.size = 32 then ⟨a, h⟩ else Vector.ofFn fun i => b.get! (o + i.val)

/-- **The signed proof a file encodes** (`harness/FORMAT.md`): `|π| ‖ π ‖ m ‖ (|q| ‖ q ‖ a)^m ‖
idx ‖ 133 ots ‖ 16 path`, every length a `u64`; `none` if a length runs past the end or bytes
follow the last digest. -/
def parseSigned (b : ByteArray) : Option Signed := Id.run do
  let n := b.size
  let mut o := 0
  if o + 8 > n then return none
  let lp := u64At b o
  o := o + 8
  if lp > n - o then return none
  let π := b.extract o (o + lp)
  o := o + lp
  if o + 8 > n then return none
  let m := u64At b o
  o := o + 8
  if 40 * m > n - o then return none
  let mut tr : Array (ByteArray × Digest) := #[]
  for _ in [:m] do
    if o + 8 > n then return none
    let lq := u64At b o
    o := o + 8
    if lq > n - o then return none
    let q := b.extract o (o + lq)
    o := o + lq
    if o + 32 > n then return none
    tr := tr.push (q, digestAt b o)
    o := o + 32
  if o + 8 + 32 * (wotsLen + sigHeight) ≠ n then return none
  let idx := u64At b o
  o := o + 8
  let ds := (List.range (wotsLen + sigHeight)).map fun k => digestAt b (o + 32 * k)
  return some ⟨π, tr.toList, ⟨idx, ds.take wotsLen, ds.drop wotsLen⟩⟩

/-- A hexadecimal digit's value. -/
def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none

/-- A digest from 64 lowercase hexadecimal characters. -/
def parseHex32 (s : String) : Option Digest := do
  let cs := s.trimAscii.toString.toList.toArray
  if cs.size ≠ 64 then none
  let bs ← (List.range 32).mapM fun i => do
    return ((← hexVal cs[2 * i]!) * 16 + (← hexVal cs[2 * i + 1]!)).toUInt8
  return Vector.ofFn fun i => bs.getD i.val 0

/-- **The check**: the file parses, and `acc vk c` of the submission `S` accepts it (through
`accF = acc`). -/
def check (S : Submission) (vk c : Digest) (bytes : ByteArray) : Bool :=
  match parseSigned bytes with
  | some p => S.accF vk c p
  | none => false

/-- One check, timed. The check's input comes out of a reference read after the first clock
reading, and its result goes into a reference before the second, so the computation is data-
dependent on an effect inside the window and consumed by one inside it: no compiler pass can move
it before or after (`tests/harness/timing/` shows the effect of each half). -/
def timedCheck (S : Submission) (vk c : Digest) (bytes : ByteArray) : IO (Bool × Nat) := do
  let input ← IO.mkRef bytes
  let t0 ← IO.monoNanosNow
  let b ← input.get
  let out ← IO.mkRef (check S vk c b)
  let t1 ← IO.monoNanosNow
  return (← out.get, t1 - t0)

/-- One input line `VK_HEX STMT_HEX FILE`: its result line, or `none` if it is malformed. -/
def runLine (S : Submission) (line : String) : IO (Option (Bool × String)) := do
  match (line.splitOn " ").filter (· ≠ "") with
  | [vkh, ch, path] =>
    let (some vk, some c) := (parseHex32 vkh, parseHex32 ch) | return none
    let bytes ← IO.FS.readBinFile path
    let (ok, ns) ← timedCheck S vk c bytes
    return some (ok, s!"{if ok then "accept" else "reject"} {ns}")
  | _ => return none

/-- `--serve`: one request per line of standard input, each answered and flushed before the next
line is read; exit 0 at the end of the input, 2 on a malformed line. -/
def serve (S : Submission) : IO UInt32 := do
  let inp ← IO.getStdin
  let out ← IO.getStdout
  repeat
    let line ← inp.getLine
    if line.isEmpty then break
    let l := line.trimAscii.toString
    if l.isEmpty then continue
    let some (_, r) ← runLine S l | IO.eprintln s!"verify: malformed line {l}"; return 2
    out.putStrLn r
    out.flush
  return 0

/-- **The badge's `main`** for the submission `S` (the per-entry module passes the entry's). -/
def main (S : Submission) (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  match args with
  | ["--serve"] => serve S
  | ["--batch", list] =>
    for line in ← IO.FS.lines list do
      if line.trimAscii.isEmpty then continue
      let some (_, r) ← runLine S line | IO.eprintln s!"verify: malformed line {line}"; return 2
      out.putStrLn r
      out.flush
    return 0
  | [vk, c, file] =>
    let some (ok, r) ← runLine S s!"{vk} {c} {file}" | IO.eprintln "verify: malformed arguments"; return 2
    out.putStrLn r
    return if ok then 0 else 1
  | _ =>
    IO.eprintln "usage: verify VK_HEX STMT_HEX FILE | verify --batch LIST | verify --serve"
    return 2

end RFBadge
