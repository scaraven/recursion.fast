/-
  Speed probe of the badge path (stage A): the contract's reference functions against the
  library's word-level twins (`Library/Blake2sFast.lean`, `Library/Fast.lean`), compiled.

    lake -f scripts/speed/lakefile.toml build speed && .lake/build/bin/speed [seed]

  Inputs are built before the clock starts and depend on a runtime value, so that nothing is
  evaluated at compile time or charged to the function measured. `acc`/`accF` are measured on a
  witness-sending root proof over two signed leaf children, all signatures by the reference
  signer (whose tree is built first and timed).
-/
import RecursionFast.Library.SignerFast
import RecursionFast.Library.WitnessSending

open RecursionFast

/-- Run `f` on each prepared input, print nanoseconds per call and per unit. -/
def bench {α : Type} (name : String) (xs : Array α) (units : Nat) (f : α → Bool) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut acc : Nat := 0
  for x in xs do
    if f x then acc := acc + 1
  let t1 ← IO.monoNanosNow
  let per := (t1 - t0) / xs.size
  IO.println s!"{name}: {xs.size} calls, {per} ns/call, {per / units} ns/unit (true: {acc})"

def main (args : List String) : IO Unit := do
  let seed := (args.headD "7").toNat!
  let msg (k i : Nat) : List UInt8 := (List.range k).map fun j => (i * 31 + j * 7 + seed).toUInt8
  let dig (i : Nat) : Digest := Vector.ofFn fun j => (i + j.val + seed).toUInt8
  -- the hash
  let m64 := (Array.range 20000).map (msg 64)
  let b64 := m64.map fun m => (⟨m.toArray⟩ : ByteArray)
  bench "blake2s256 (reference) 64 B, 1 compression" m64 1 fun m => (blake2s256 m).headD 0 == 1
  bench "digestB (twin) 64 B, 1 compression" b64 1 fun m => (Blake2s.digestB m)[0] == 1
  let blocks := (Array.range 100000).map fun i =>
    (Vector.ofFn fun j => (i + j.val + seed).toUInt32 : Vector UInt32 16)
  bench "compress (reference)" blocks 1 fun b => (Blake2s.compress Blake2s.iv b 64 0 0)[0] == 1
  bench "compressF (twin)" blocks 1 fun b => (Blake2s.compressF Blake2s.iv b 64 0 0)[0] == 1
  let m1M := (Array.range 3).map (msg 1048576)
  let b1M := m1M.map fun m => (⟨m.toArray⟩ : ByteArray)
  bench "blake2s256 (reference) 1 MiB" m1M 16384 fun m => (blake2s256 m).headD 0 == 1
  bench "digestB (twin) 1 MiB" b1M 16384 fun m => (Blake2s.digestB m)[0] == 1
  let xs := (Array.range 20000).map dig
  bench "wotsStep (reference), 43 B" xs 1 fun x => (wotsStep 5 7 1 x)[0] == 1
  bench "wotsStepF (twin), 43 B" xs 1 fun x => (wotsStepF 5 7 1 x)[0] == 1
  -- trace digests: 2^16 queries of 100 bytes (about 1.6 * 2^16 compressions)
  let big (i : Nat) : Trace := (List.range 65536).map fun k =>
    (⟨((List.range 100).map fun j => (i + k + j).toUInt8).toArray⟩, dig (i + k))
  let trs := (Array.range 2).map big
  let units := (1 + 65536 * 140) / 64
  bench "traceDigest (reference), 2^16 x 100 B" trs units fun tr => (traceDigest tr)[0] == 1
  bench "traceDigestF (twin), 2^16 x 100 B" trs units fun tr => (traceDigestF tr)[0] == 1
  -- the reference signer: one tree
  let sk := Signer.chainStartF ((List.range 32).map fun i => (i + seed).toUInt8)
  let t0 ← IO.monoNanosNow
  let T := Signer.buildTree sk
  let vk := Signer.Tree.pk T
  IO.println s!"vk {vk.toList.take 4}"
  let t1 ← IO.monoNanosNow
  IO.println
    s!"buildTree (fast signer, 2^16 keys, about 48M compressions): {(t1 - t0) / 1000000} ms"
  let sigs := (Array.range 200).map fun i => (dig i, Signer.Tree.sign sk T (i % 65536) (dig i))
  bench "SigOk (reference), valid signature" (sigs.extract 0 20) 300 fun p => SigOk vk p.1 p.2
  bench "SigOkF (twin), valid signature" sigs 300 fun p => SigOkF vk p.1 p.2
  -- acc on a witness-sending root over two signed leaves of 2^10 steps
  let s₁ := dig 1
  let s₂ := dig 2
  let n := 1024
  let c₁ := leafStmtF (chainEndF s₁ n) n
  let c₂ := leafStmtF (chainEndF s₂ n) n
  let p₁ : Signed :=
    ⟨WitnessSending.encodeF (.leaf s₁ n), [], Signer.Tree.sign sk T 0 (traceDigestF [])⟩
  let p₂ : Signed :=
    ⟨WitnessSending.encodeF (.leaf s₂ n), [], Signer.Tree.sign sk T 1 (traceDigestF [])⟩
  let root : Signed := ⟨WitnessSending.encodeF (.node c₁ c₂ p₁ p₂), [],
    Signer.Tree.sign sk T 2 (traceDigestF [])⟩
  let c := nodeStmtF c₁ c₂
  let roots := (Array.range 20).map fun _ => root
  bench "acc (reference), ws root over two 2^10-step leaves" (roots.extract 0 3) 1
    fun p => WitnessSending.submission.acc vk c p
  bench "accF (twin), ws root over two 2^10-step leaves" roots 1
    fun p => WitnessSending.submission.accF vk c p
  -- where the witness-sending verifier spends its time: decoding and re-encoding its proof
  let proofs := (Array.range 20).map fun _ => root.π
  bench s!"decodeF of the ws root proof ({root.π.size} B)" proofs 1
    fun π => (WitnessSending.decodeF π).isSome
  bench s!"encodeF == π of the ws root proof ({root.π.size} B)" proofs 1
    fun π => match WitnessSending.decodeF π with
      | some w => WitnessSending.encodeF w == π
      | none => false
  bench "chainEndF, 2^10 steps" (Array.range 20) 1024 fun i => (chainEndF (dig i) 1024)[0] == 1
