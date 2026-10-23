/-
  A probe submission for timing the badge (`tests/harness/accprobe/run.py`; not an entry, not
  certified): its verifier asks `2^16` fixed queries of 100 bytes (the index in the first 8 bytes)
  and accepts, so `acc` on its signed trace exercises the badge's parser, `traceDigestF` of about
  9.2 MB, `SigOkF` and a `2^16`-step `runSeq`.
-/
import RecursionFast.Library.WitnessSending

namespace RecursionFast.Challenge
open RecursionFast

/-- Query `k`: the 8 little-endian bytes of `k`, then 92 zero bytes. -/
def queryK (k : Nat) : ByteArray :=
  ByteArray.mk ((List.range 100).toArray.map fun j => if j < 8 then (k >>> (8 * j)).toUInt8 else 0)

/-- Ask queries `k, k + 1, …` (`n` of them), then accept. -/
def loopV : Nat → Nat → OProg Bool
  | 0, _ => .ret true
  | n + 1, k => .query (queryK k) fun _ => loopV n (k + 1)

/-- The probe submission. -/
def submission : Submission :=
  { WitnessSending.submission with V := fun _ _ _ => loopV 65536 0, qV := 65536 }

end RecursionFast.Challenge
