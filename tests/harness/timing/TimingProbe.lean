/-
  Probe for the badge's timing barrier (FIXLIST Q10; not a harness tool). `work` is a pure
  computation of about a second; each variant times it between two `IO.monoNanosNow` readings the
  way a badge might. Printed: the measured nanoseconds and the result.

  * `discarded`: the result is not used, so the compiler removes the computation: about 0 ns.
  * `sunk`: the result is used only after the second reading.
  * `ifIdiom`: stage B's first `timedCheck` (`if ok then now else now`).
  * `barrier`: the badge's `timedCheck` now: input read from a reference after the first reading,
    result written to a reference before the second.
-/

/-- About a second of pure work on `b`. -/
def work (b : ByteArray) : UInt64 := Id.run do
  let mut x : UInt64 := b.size.toUInt64
  for i in [:60000000] do
    x := x * 6364136223846793005 + (b.get! (i % b.size)).toUInt64
  return x

def discarded (b : ByteArray) : IO (Nat × UInt64) := do
  let t0 ← IO.monoNanosNow
  let _x := work b
  let t1 ← IO.monoNanosNow
  return (t1 - t0, 0)

def sunk (b : ByteArray) : IO (Nat × UInt64) := do
  let t0 ← IO.monoNanosNow
  let x := work b
  let t1 ← IO.monoNanosNow
  return (t1 - t0, x)

def ifIdiom (b : ByteArray) : IO (Nat × UInt64) := do
  let t0 ← IO.monoNanosNow
  let x := work b
  let t1 ← if x == 0 then IO.monoNanosNow else IO.monoNanosNow
  return (t1 - t0, x)

def barrier (b : ByteArray) : IO (Nat × UInt64) := do
  let input ← IO.mkRef b
  let t0 ← IO.monoNanosNow
  let b' ← input.get
  let out ← IO.mkRef (work b')
  let t1 ← IO.monoNanosNow
  return (t1 - t0, ← out.get)

def main (args : List String) : IO Unit := do
  let b := ByteArray.mk ((List.range (64 + args.length)).toArray.map (·.toUInt8))
  for (name, f) in [("discarded", discarded), ("sunk", sunk), ("ifIdiom", ifIdiom), ("barrier", barrier)] do
    let (ns, x) ← f b
    IO.println s!"{name}: {ns / 1000000} ms (result {x})"
