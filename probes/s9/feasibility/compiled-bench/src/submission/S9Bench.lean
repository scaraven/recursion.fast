/- S9 feasibility probe (not a submission): compiled cost of the trusted hash and K product, the
   unit costs of the Lean-compiled indexer and verifier (DESIGN §6.3 step 2, O-9). -/
import RecursionFast.Contract.Compile

namespace S9Bench
open RecursionFast

/-- Deterministic test bytes. -/
def bytes (n : Nat) : List UInt8 := (List.range n).map fun i => UInt8.ofNat (i * 2654435761 % 251)

/-- `m` chained one-block hashes (64-byte inputs: one compression each). -/
def chain64 (m : Nat) (s : List UInt8) : List UInt8 :=
  m.fold (fun _ _ acc => blake2s256 (acc ++ acc)) s

/-- `m` multiply-adds in `K`. -/
def kloop (m : Nat) (x y : K) : K := m.fold (fun _ _ acc => acc * y + x) x

end S9Bench
