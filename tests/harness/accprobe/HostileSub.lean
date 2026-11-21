/-
  A hostile probe submission for the badge (`tests/harness/accprobe/run.py`; not an entry, not
  certified). Its verifier asks nothing and accepts a proof of exactly 7 bytes for the statement of
  32 zero bytes after about a hundred milliseconds of work; and the module then declares global,
  high-priority instances of library classes, the levers an entry would use to redirect the badge's
  glue if that glue were elaborated where the entry's instances are in scope (it was, before the
  glue moved to `RecursionFast/Badge.lean`):

  * `HSub Nat Nat Nat`: a difference above 50 ms (in ns) is 1, so a timer `t1 - t0` would report
    the slow check as 1 ns;
  * `HOr UInt64 UInt64 UInt64`: `7 ||| 0 = 1000`, so a length word `07 00 … 00` read with `|||`
    would be 1000 and the 7-byte proof would not parse;
  * `GetElem? (Array Char) Nat Char`: every character reads as `'0'`, so a hex parser using
    `cs[i]!` would turn every key and statement into zeros (the proof's key would not match).

  The badge built around this module must accept the proof for its statement with a time above
  50 ms, and reject it for another statement: the runner checks all three.
-/
import RecursionFast.Library.WitnessSending

namespace RecursionFast.Challenge
open RecursionFast

/-- The statement the probe accepts: 32 zero bytes. -/
def target : Digest := Vector.replicate 32 0

/-- About a hundred milliseconds of work on `x` (`2^27` multiply-adds). -/
def spin (x : UInt64) : UInt64 := Id.run do
  let mut y := x
  for _ in [:134217728] do
    y := y * 6364136223846793005 + 1442695040888963407
  return y

/-- Accept a 7-byte proof for `target`, after the work. -/
def hostileV (c : Digest) (π : Proof) : Bool :=
  c == target && π.size == 7 && spin π.size.toUInt64 != 0

/-- The probe submission. -/
def submission : Submission :=
  { WitnessSending.submission with V := fun _ c π => .ret (hostileV c π), qV := 0 }

end RecursionFast.Challenge

/-- Hostile: a difference above 50,000,000 (50 ms in ns) is 1. -/
instance (priority := high) hostileSub : HSub Nat Nat Nat :=
  ⟨fun a b => if Nat.sub a b > 50000000 then 1 else Nat.sub a b⟩

/-- Hostile: `7 ||| 0 = 1000`. -/
instance (priority := high) hostileOr : HOr UInt64 UInt64 UInt64 :=
  ⟨fun a b => if a = 7 ∧ b = 0 then 1000 else UInt64.lor a b⟩

/-- Hostile: every character of a character array reads as `'0'`. -/
instance (priority := high) hostileGet : GetElem? (Array Char) Nat Char (fun _ _ => True) where
  getElem _ _ _ := '0'
  getElem? _ _ := some '0'
  getElem! _ _ := '0'

-- the instances are the ones elaboration now finds
example : (2000000000 : Nat) - 0 = 1 := by decide
example : ((7 : UInt64) ||| 0) = 1000 := by decide
example : (#['a', 'b'] : Array Char)[1]! = '0' := rfl
