/-
# Controls: the hash Keccak-256 (`Contract/Hash/Keccak.lean`), positive and negative

Known answers decided by the kernel (`decide +kernel`) on the word-level twin of
`Library/KeccakFast.lean`, which is proved equal to the contract's `keccak256` and `keccakF`
(`keccak256_eq_digestL`, `keccakF_toVec`): the kernel evaluates the twin's permutation in about
half a second and the contract's own `Vector` form in about 12 s. An expected digest is written
as the hex string of its source and read by `hex` (`Controls/Hex.lean`). General facts (`rotl`
against `BitVec.rotateLeft`, the padded length, the digest length) are theorems of
`Library/Keccak.lean`.

Constants, re-derived from FIPS 202's definitions rather than copied: `rc_spec`, every round
constant from the LFSR of Algorithm 5 (`rc(t)`, the bit `rc(j + 7i)` at position `2^j − 1`);
`rho_spec`, every offset from Algorithm 2 (the walk `(x, y) ↦ (y, 2x + 3y)` from `(1, 0)`, offset
`(t + 1)(t + 2)/2 mod 64` at step `t`, `0` at `(0, 0)`).

The steps, on the contract itself (kernel, no twin): `theta_unit`, `rho_ones` (pins every
offset), `pi_idx`, `chi_unit`, each with a negative control naming a mutant it rejects
(`theta_neg`: neighbouring columns swapped; `rho_neg`: the offset table transposed; `pi_neg`: π
read as `A[y, x + 3y]`; `chi_neg`: χ reading leftwards).

Positive, each digest from OpenSSL 3.5's `openssl dgst -keccak-256` and pycryptodome's
`Crypto.Hash.keccak` (the two agree; `pattern n` is leanVM's test pattern, byte `i` = `7i + 3 mod
256`):
* `keccakF_zero_kat`: `Keccak-f[1600]` of the all-zero state, all 25 lanes (the Keccak team's
  `KeccakF-1600-IntermediateValues.txt`), so the permutation is checked apart from the sponge;
* `empty_kat`: the empty message, one block that is all padding (`0x01 … 0x80`);
* `abc_kat`: "abc";
* `len135_kat`: 135 bytes, so the padding is the single byte `0x81`;
* `len136_kat`: exactly one block of message, then a whole block of padding;
* `len137_kat`: one block and one byte;
* `len272_kat`: two blocks of message, then a block of padding.

Negative:
* `flip_neg`: one bit flipped in the message ("abc" → "abb") changes the digest;
* `sha3_neg`: the digest of the empty message is not SHA3-256's (`a7ffc6f8…434a`, padding `0x06`):
  the padding byte is Keccak's;
* `len_neg`: 135 and 136 bytes of the same pattern have different digests (the length is in the
  padding).

Mutants (checked against these vectors with `harness/rfh/keccak.py` mutated, not here): SHA-3's
padding byte `0x06` fails `empty_kat`; no extra padding block when the message fills a block fails
`len136_kat` and `len272_kat`; a lone padding byte `0x01` instead of `0x81` fails `len135_kat`; a
rate of 144 or 128 bytes fails `len135_kat`, `len136_kat` and `len137_kat`; ρ offsets of the
transposed table, or π read as `A[y, x + 3y]`, fail `keccakF_zero_kat`.
-/
import RecursionFast.Controls.Hex
import RecursionFast.Library.KeccakFast

namespace RecursionFast.Controls.Keccak
open RecursionFast RecursionFast.Keccak

theorem hex_pos : hex "00ff7f80a519" = [0x00, 0xff, 0x7f, 0x80, 0xa5, 0x19] := by decide +kernel

/-- The string "abc". -/
def abc : List UInt8 := [0x61, 0x62, 0x63]

/-- leanVM's test pattern (`crates/primitives/src/hash.rs`): byte `i` is `7i + 3 mod 256`. -/
def pattern (n : Nat) : List UInt8 := (List.range n).map fun i => (7 * i + 3).toUInt8

/-! ## Constants -/

/-- The LFSR of FIPS 202 Algorithm 5 after `t` steps, bit `k` of the result holding `R[k]`:
`R = 0 ‖ R` (a shift), then `R[8]` XORed into `R[0], R[4], R[5], R[6]` (`0x71`), then the first
8 bits kept. -/
def lfsr : Nat → Nat
  | 0 => 1
  | t + 1 => let r := lfsr t <<< 1; (r ^^^ (r >>> 8 &&& 1) * 0x71) &&& 0xFF

/-- `rc(t)` of Algorithm 5: `R[0]` after `t mod 255` steps. -/
def rcBit (t : Nat) : Nat := lfsr (t % 255) &&& 1

/-- `RC` of round `i` (Algorithm 6): the bit `rc(j + 7i)` at position `2^j − 1`, `j = 0 … 6`. -/
def rcOfRound (i : Nat) : UInt64 :=
  (List.range 7).foldl (fun w j => w ||| (rcBit (j + 7 * i)).toUInt64 <<< (2 ^ j - 1).toUInt64) 0

/-- Every round constant is the LFSR's (FIPS 202 Algorithms 5 and 6). -/
theorem rc_spec : ∀ i : Fin 24, rc[i] = rcOfRound i := by decide +kernel

/-- The lane visited at step `t` of FIPS 202 Algorithm 2: `(1, 0)`, then `(x, y) ↦ (y, 2x + 3y)`. -/
def rhoWalk : Nat → Nat × Nat
  | 0 => (1, 0)
  | t + 1 => let p := rhoWalk t; (p.2, (2 * p.1 + 3 * p.2) % 5)

/-- Every ρ offset is Algorithm 2's: `0` at `(0, 0)`, and `(t + 1)(t + 2)/2 mod 64` at the lane of
step `t`, for the 24 steps (which visit the 24 other lanes, `rhoWalk_visits`). -/
theorem rho_spec : rhoOffsets[0] = 0 ∧ ∀ t : Fin 24,
    rhoOffsets.toList.getD ((rhoWalk t).1 + 5 * (rhoWalk t).2) 0 = (t + 1) * (t + 2) / 2 % 64 := by
  decide +kernel

/-- The walk visits every lane but `(0, 0)` once. -/
theorem rhoWalk_visits : ((List.range 24).map fun t => (rhoWalk t).1 + 5 * (rhoWalk t).2).Nodup ∧
    ∀ t < 24, (rhoWalk t).1 + 5 * (rhoWalk t).2 ≠ 0 := by decide +kernel

/-! ## The steps, one at a time (each with a mutant it rejects) -/

/-- The state with the single lane `A[x₀, y₀] = 1`. -/
def unit (x₀ y₀ : Nat) : State := ofLanes fun x y => if x = x₀ ∧ y = y₀ then 1 else 0

/-- θ of `A[0, 0] = 1`: `C[0] = 1`, so `D[1] = 1` (column 1) and `D[4] = rot(1, 1) = 2` (column 4). -/
theorem theta_unit : (theta (unit 0 0)).toList =
    [1, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2] := by decide +kernel

/-- θ with the two neighbouring columns swapped (`C[x + 1] ⊕ rot(C[x − 1], 1)`), a mutant. -/
def thetaSwapped (a : State) : State :=
  let c (x : Nat) := lane a x 0 ^^^ lane a x 1 ^^^ lane a x 2 ^^^ lane a x 3 ^^^ lane a x 4
  ofLanes fun x y => lane a x y ^^^ (c (x + 1) ^^^ rotl (c (x + 4)) 1)

theorem theta_neg : theta (unit 0 0) ≠ thetaSwapped (unit 0 0) := by decide +kernel

/-- ρ of the all-ones state: lane `i` is `2^(rhoOffsets[i])`, which pins every offset. -/
theorem rho_ones : (rho (Vector.replicate 25 1)).toList =
    [1, 2, 4611686018427387904, 268435456, 134217728, 68719476736, 17592186044416, 64,
     36028797018963968, 1048576, 8, 1024, 8796093022208, 33554432, 549755813888, 2199023255552,
     35184372088832, 32768, 2097152, 256, 262144, 4, 2305843009213693952, 72057594037927936,
     16384] := by decide +kernel

/-- ρ with the offset table read transposed (`r[y, x]` for `A[x, y]`), a mutant. -/
def rhoTransposed (a : State) : State :=
  ofLanes fun x y => rotl (lane a x y) (rhoOffsets.toList.getD (y + 5 * x) 0)

theorem rho_neg : rho (Vector.replicate 25 1) ≠ rhoTransposed (Vector.replicate 25 1) := by
  decide +kernel

/-- The state whose lane `i` holds `i`. -/
def idx : State := Vector.ofFn fun i => i.val.toUInt64

/-- π of `idx`: lane `x + 5y` holds `(x + 3y) mod 5 + 5x`. -/
theorem pi_idx : (pi idx).toList =
    [0, 6, 12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20, 4, 5, 11, 17, 23, 2, 8, 14, 15, 21] := by
  decide +kernel

/-- π read as `A'[x, y] = A[y, x + 3y]`, a mutant. -/
def piTransposed (a : State) : State := ofLanes fun x y => lane a y (x + 3 * y)

theorem pi_neg : pi idx ≠ piTransposed idx := by decide +kernel

/-- χ of `A[1, 0] = 1`: lane `(1, 0)` keeps its bit, and lane `(4, 0)` gets `¬A[0, 0] ∧ A[1, 0]`. -/
theorem chi_unit : (chi (unit 1 0)).toList =
    [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel

/-- χ reading the two lanes to the left (`x − 1`, `x − 2`), a mutant. -/
def chiMirrored (a : State) : State :=
  ofLanes fun x y => lane a x y ^^^ (~~~lane a (x + 4) y &&& lane a (x + 3) y)

theorem chi_neg : chi (unit 1 0) ≠ chiMirrored (unit 1 0) := by decide +kernel

/-! ## Known answers -/

/-- `Keccak-f[1600]` of the all-zero state (the Keccak team's intermediate values). -/
theorem keccakF_zero_kat : (keccakF (Vector.replicate 25 0)).toList =
    [0xF1258F7940E1DDE7, 0x84D5CCF933C0478A, 0xD598261EA65AA9EE, 0xBD1547306F80494D,
     0x8B284E056253D057, 0xFF97A42D7F8E6FD4, 0x90FEE5A0A44647C4, 0x8C5BDA0CD6192E76,
     0xAD30A6F71B19059C, 0x30935AB7D08FFC64, 0xEB5AA93F2317D635, 0xA9A6E6260D712103,
     0x81A57C16DBCF555F, 0x43B831CD0347C826, 0x01F22F1A11A5569F, 0x05E5635A21D9AE61,
     0x64BEFEF28CC970F2, 0x613670957BC46611, 0xB87C5A554FD00ECB, 0x8C3EE88A1CCF32C8,
     0x940C7922AE3A2614, 0x1841F924A2C509E4, 0x16F53526E70465C2, 0x75F644E97F30A13B,
     0xEAF1FF7B5CECA249] := by
  rw [show Vector.replicate 25 (0 : UInt64) = zeroS.toVec from rfl, keccakF_toVec]
  decide +kernel

/-- The empty message: one block of padding alone. -/
theorem empty_kat : keccak256 [] =
    hex "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470" := by
  rw [keccak256_eq_digestL]; decide +kernel

/-- "abc". -/
theorem abc_kat : keccak256 abc =
    hex "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45" := by
  rw [keccak256_eq_digestL]; decide +kernel

/-- 135 bytes: the padding is the single byte `0x81`. -/
theorem len135_kat : keccak256 (pattern 135) =
    hex "00ef96af9cf4b24c7f269d922294444a197d0a33638c2e56634c57e892103a8f" := by
  rw [keccak256_eq_digestL]; decide +kernel

/-- 136 bytes: one block of message, then a block of padding. -/
theorem len136_kat : keccak256 (pattern 136) =
    hex "742061bcad767ed4c4f5883b1dcb1aad11afdcc140dc469d953759b127b9f9ed" := by
  rw [keccak256_eq_digestL]; decide +kernel

/-- 137 bytes: one block, then one byte and its padding. -/
theorem len137_kat : keccak256 (pattern 137) =
    hex "e3371f61e770abf254c34239c3b0099ad90594507415bc81dd0a10b9692bbf2a" := by
  rw [keccak256_eq_digestL]; decide +kernel

/-- 272 bytes: two blocks of message, then a block of padding. -/
theorem len272_kat : keccak256 (pattern 272) =
    hex "ac141fd7b0a0ffcd2e967254d508da3ec616596493c36fa304425647d90e6de5" := by
  rw [keccak256_eq_digestL]; decide +kernel

/-! ## Negative -/

/-- One bit flipped in the message (`0x63` → `0x62`, "abc" → "abb") changes the digest. -/
theorem flip_neg : keccak256 [0x61, 0x62, 0x62] ≠ keccak256 abc := by
  rw [keccak256_eq_digestL, keccak256_eq_digestL]; decide +kernel

/-- The hash is not SHA3-256: SHA3-256 of the empty message (padding byte `0x06`) differs. -/
theorem sha3_neg : keccak256 [] ≠
    hex "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a" := by
  rw [keccak256_eq_digestL]; decide +kernel

/-- The length is hashed: 135 and 136 bytes of one pattern have different digests. -/
theorem len_neg : keccak256 (pattern 135) ≠ keccak256 (pattern 136) := by
  rw [len135_kat, len136_kat]; decide

end RecursionFast.Controls.Keccak
