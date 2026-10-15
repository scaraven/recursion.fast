import RecursionFastHarness.LayoutJson
import S3IdxBench
open RecursionFast S3IdxBench RecursionFast.Controls.Compile

def hex2 (b : List UInt8) : String := String.join (b.map fun c =>
  let s := String.ofList (Nat.toDigits 16 c.toNat); if s.length < 2 then "0" ++ s else s)

/-- usage: harness-idx LAYOUT.json (toy | M): time `index` of `cmpToy`, or of `bench M`. -/
def main (args : List String) : IO UInt32 := do
  let [layoutF, which] := args | IO.eprintln "usage: harness-idx LAYOUT.json (toy|M)"; return 2
  match RecursionFastHarness.LayoutJson.parse (← IO.FS.readFile layoutF) with
  | .error e => IO.eprintln e; return 2
  | .ok L =>
    let t0 ← IO.monoNanosNow
    let (root, len) ← if which == "toy" then
        pure ((index cfg2 cmpToy L).2, (Codec.eLayout L).length)
      else
        let m := which.toNat!
        if h : 4 ≤ m ∧ m ≤ 32 then
          let F := idxFn m L
          pure ((index cfg2 (bench m h.1 h.2 F) L).2, (Codec.eLayout L).length)
        else IO.eprintln "4 ≤ M ≤ 32"; return 2
    IO.println s!"root {hex2 root}"
    let t1 ← IO.monoNanosNow
    IO.println s!"index ({which}; eLayout {len} elements): {(t1 - t0) / 1000000} ms"
    return 0
