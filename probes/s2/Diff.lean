/- S2 review probe: grid differential test of `blake2s` against `hashlib.blake2s`.
Run: `lake env lean --run probes/s2/Diff.lean > logs/S2-review-diff.out`, then
`python3 -I probes/s2/diff.py logs/S2-review-diff.out`. Inputs are deterministic (no RNG):
key byte `i` = `13i + 5`, message byte `i` = `31i + 17 mod 251`. -/
import RecursionFast.Contract.Hash.Blake2s

open RecursionFast

def hexOf (bs : List UInt8) : String :=
  String.join (bs.map fun b =>
    let s := String.ofList (Nat.toDigits 16 b.toNat)
    if s.length = 1 then "0" ++ s else s)

def keyOf (kk : Nat) : List UInt8 := (List.range kk).map fun i => (13 * i + 5).toUInt8
def msgOf (ll : Nat) : List UInt8 := (List.range ll).map fun i => ((31 * i + 17) % 251).toUInt8

def main : IO Unit := do
  let lens := List.range 261 ++ [319, 320, 321, 511, 512, 513, 1023, 1024, 1025, 4096, 4097]
  for kk in [0, 1, 2, 31, 32] do
    for nn in [1, 2, 3, 16, 31, 32] do
      for ll in lens do
        IO.println s!"{kk} {nn} {ll} {hexOf (blake2s (keyOf kk) nn (msgOf ll))}"
  -- `blake2s256` is `blake2s [] 32`
  for ll in lens do
    IO.println s!"256 32 {ll} {hexOf (blake2s256 (msgOf ll))}"
