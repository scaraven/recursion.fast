/-
# Contract: the hash Keccak-256 (FIPS 202 with Ethereum's padding)     (TRUSTED, Lean core only)

The contract's one hash. It is the chain step and the statement hash of the relation
(`Relation.lean`), and the trace digest, the WOTS chain step, leaf and Merkle node of the
signature check (`Signature.lean`); every one of them is public, unkeyed Keccak-256. It is **not**
the oracle: the deployed oracle is Keccak-256 of a secret 32-byte key followed by the query,
computed by the service (`service/PROTOCOL.md` §2). It is pure, total and computable: the
harness runs it in `acc`, through the word-level twin of `Library/KeccakFast.lean`, proved equal.

`keccak256 msg` is Ethereum's Keccak-256: the sponge of FIPS 202 §4 over `Keccak-f[1600]` (§3.3:
24 rounds of `θ, ρ, π, χ, ι`, §3.2), with a rate of 1088 bits (136 bytes), a capacity of 512 bits
and a 256-bit output, and with Keccak's original padding `pad10*1` (§5.1) and no domain suffix: the
first padding byte is `0x01`, where SHA3-256 appends the suffix `01` and so starts with `0x06`; the
last byte of the final block is XORed with `0x80`. Bits are numbered little-endian within a byte
(Appendix B.1), so a lane is the little-endian 64-bit word of 8 state bytes, and lane `x + 5y`
holds `A[x, y]` (§3.1.2). Known answers (OpenSSL's and pycryptodome's `keccak-256`; the padding
edges at 135, 136 and 137 bytes) and the constants re-derived from FIPS 202's definitions are
kernel-checked in `RecursionFast/Controls/Keccak.lean`.

Written from FIPS 202. The constants `rc` and `rhoOffsets` are FIPS 202's (Algorithm 5, Table 2);
they equal leanVM's `RC` and `RHO` (`crates/primitives/src/hash.rs`), the design's reference.
-/

namespace RecursionFast

namespace Keccak

/-- A state of `Keccak-f[1600]` (FIPS 202 §3.1): 25 lanes of 64 bits, lane `x + 5y` holding
`A[x, y]`. -/
abbrev State := Vector UInt64 25

/-- The lane `A[x mod 5, y mod 5]` (FIPS 202 reads every lane coordinate mod 5). -/
def lane (a : State) (x y : Nat) : UInt64 := a[x % 5 + 5 * (y % 5)]'(by omega)

/-- The state whose lane `A[x, y]` is `f x y` (the lanes listed in the order `x + 5y`). -/
def ofLanes (f : Nat → Nat → UInt64) : State :=
  #v[f 0 0, f 1 0, f 2 0, f 3 0, f 4 0, f 0 1, f 1 1, f 2 1, f 3 1, f 4 1, f 0 2, f 1 2, f 2 2,
    f 3 2, f 4 2, f 0 3, f 1 3, f 2 3, f 3 3, f 4 3, f 0 4, f 1 4, f 2 4, f 3 4, f 4 4]

/-- Rotate a lane left by `n < 64` bits (FIPS 202's `rot(W, n)` on a lane). -/
def rotl (w : UInt64) (n : Nat) : UInt64 := w <<< n.toUInt64 ||| w >>> (64 - n).toUInt64

/-- θ (§3.2.1): `A[x, y]` is XORed with `D[x] = C[x − 1] ⊕ rot(C[x + 1], 1)`, where `C[x]` is
the parity of column `x`. -/
def theta (a : State) : State :=
  let c (x : Nat) := lane a x 0 ^^^ lane a x 1 ^^^ lane a x 2 ^^^ lane a x 3 ^^^ lane a x 4
  let d (x : Nat) := c (x + 4) ^^^ rotl (c (x + 1)) 1
  ofLanes fun x y => lane a x y ^^^ d x

/-- The offsets of ρ (§3.2.2, Table 2): lane `x + 5y` is rotated left by `rhoOffsets[x + 5y]`. -/
def rhoOffsets : Vector Nat 25 :=
  #v[0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

/-- ρ (§3.2.2): every lane rotated left by its offset. -/
def rho (a : State) : State := Vector.ofFn fun i => rotl a[i] rhoOffsets[i]

/-- π (§3.2.3): `A'[x, y] = A[x + 3y, x]`. -/
def pi (a : State) : State := ofLanes fun x y => lane a (x + 3 * y) x

/-- χ (§3.2.4): `A'[x, y] = A[x, y] ⊕ (¬A[x + 1, y] ∧ A[x + 2, y])`. -/
def chi (a : State) : State :=
  ofLanes fun x y => lane a x y ^^^ (~~~lane a (x + 1) y &&& lane a (x + 2) y)

/-- The round constants of ι (§3.2.5): `rc[i]` is `RC` of round `i`, the bits `rc(j + 7i)` of
Algorithm 5 placed at the positions `2^j − 1`. -/
def rc : Vector UInt64 24 := #v[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- One round `Rnd(A, i)` (§3.3): θ, ρ, π and χ, then ι XORs the round constant `c` into
`A[0, 0]`. -/
def round (a : State) (c : UInt64) : State :=
  let a := chi (pi (rho (theta a)))
  a.set 0 (a[0] ^^^ c)

/-- **`Keccak-f[1600]`** (§3.3, `Keccak-p[1600, 24]`): the 24 rounds, round `i` with `rc[i]`. -/
def keccakF (a : State) : State := rc.foldl round a

/-- The rate of Keccak-256 in bytes: `1600 − 2 · 256` bits. -/
def rate : Nat := 136

/-- `pad10*1` with Keccak's padding (§5.1, no suffix): the message, then `0x01`, zeros and `0x80`,
to a positive multiple of `rate` bytes; a single padding byte is `0x81`. -/
def pad (msg : List UInt8) : List UInt8 :=
  let p := rate - msg.length % rate    -- the number of padding bytes, `1 … rate`
  msg ++ if p = 1 then [0x81] else 0x01 :: List.replicate (p - 2) 0 ++ [0x80]

/-- Lane `i` of a block: its bytes `8i … 8i + 7` as a little-endian word, `0` past its end. -/
def blockLane (blk : Array UInt8) (i : Nat) : UInt64 :=
  (List.range 8).foldl (fun w k => w ||| (blk.getD (8 * i + k) 0).toUInt64 <<< (8 * k).toUInt64) 0

/-- The absorbing loop of the sponge (§4) on `n` blocks of `d`: the next `rate` bytes are XORed
into the first 17 lanes, then `keccakF` is applied. -/
def absorb (a : State) (d : List UInt8) : Nat → State
  | 0 => a
  | n + 1 =>
    let blk := (d.take rate).toArray
    absorb (keccakF (Vector.ofFn fun i => a[i] ^^^ blockLane blk i)) (d.drop rate) n

end Keccak

open Keccak in
/-- **Keccak-256** (Ethereum's): the padded message absorbed from the all-zero state, then the
first 32 bytes of the state, lane by lane, each lane little-endian. -/
def keccak256 (msg : List UInt8) : List UInt8 :=
  let p := pad msg
  let a := absorb (Vector.replicate 25 0) p (p.length / rate)
  (a.toList.flatMap fun w => (List.range 8).map fun k => (w >>> (8 * k).toUInt64).toUInt8).take 32

end RecursionFast
