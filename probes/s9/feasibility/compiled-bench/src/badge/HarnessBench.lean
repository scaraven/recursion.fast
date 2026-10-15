import S9Bench
open RecursionFast S9Bench

def time {α : Type} (f : Unit → α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let a := f ()
  let t1 ← IO.monoNanosNow
  pure (a, t1 - t0)

def main (args : List String) : IO Unit := do
  let n := (args.headD "20").toNat!
  let b := bytes (2 ^ n)
  IO.println s!"input built: {b.length} bytes"
  let t0 ← IO.monoNanosNow
  let d := blake2s256 b
  IO.println s!"digest {d.take 4}"
  let t1 ← IO.monoNanosNow
  let comps := (2 ^ n + 63) / 64
  IO.println s!"blake2s256 of 2^{n} bytes ({comps} compressions): {(t1 - t0) / 1000000} ms, {(t1 - t0) / comps} ns per compression"
  let m := 20000
  let t2 ← IO.monoNanosNow
  let acc := chain64 m (List.replicate 32 7)
  IO.println s!"chain {acc.take 4}"
  let t3 ← IO.monoNanosNow
  IO.println s!"{m} one-block hashes (64-byte inputs): {(t3 - t2) / m} ns each"
  let km := 200000
  let t4 ← IO.monoNanosNow
  let x := kloop km ⟨0x123456789abcdef1⟩ ⟨0x0fedcba987654321⟩
  IO.println s!"k {x.bits}"
  let t5 ← IO.monoNanosNow
  IO.println s!"{km} K multiply-adds: {(t5 - t4) / km} ns each"
