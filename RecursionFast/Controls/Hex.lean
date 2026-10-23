/-
# Controls: hex strings, the form in which known answers are published

`hex` and its two helpers, moved out of `Controls/Blake2s.lean` (same names, same namespace) so
that the controls that only read expected digests (`Signature`, `Relation`, `Tree`) do not wait
for the BLAKE2s known answers to be checked. `hex_pos` stays in `Controls/Blake2s.lean`.
-/
import RecursionFast.Contract.Hash.Blake2s

namespace RecursionFast.Controls.Blake2s

/-- The value of a lowercase hex digit. -/
def hexDigit (c : Char) : Nat := if c ≤ '9' then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

/-- The bytes of a list of lowercase hex digits, two digits per byte. -/
def hexBytes : List Char → List UInt8
  | a :: b :: r => (16 * hexDigit a + hexDigit b).toUInt8 :: hexBytes r
  | _ => []

/-- The bytes written by a lowercase hex string, the form in which the vectors are published. -/
def hex (s : String) : List UInt8 := hexBytes s.toList

end RecursionFast.Controls.Blake2s
