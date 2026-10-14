/- S2 review probe: two plausible wrong specifications that pass every kernel-checked KAT in
`Controls/Blake2s.lean` and are caught only by the boundary vectors of `probes/s2/Boundary.lean`.

* `heldBack`: the number of non-final blocks is `|d| / 64` once `|d| > 64` (the classic
  "held-back buffer" bug: when `|d|` is a multiple of 64 an extra empty final block is hashed).
  Agrees with the spec at |d| ∈ {0, 3, 64, 65, 129}, i.e. on every existing KAT.
* `padNN`: the key is padded with `64 - nn` zeros instead of `64 - kk`. Agrees whenever
  `kk = nn` or `kk = 0`, i.e. on every existing KAT (keyed ones have kk = nn = 32). -/
import RecursionFast.Controls.Blake2s

namespace S2Review
open RecursionFast RecursionFast.Blake2s RecursionFast.Controls.Blake2s

def heldBack (key : List UInt8) (nn : Nat) (msg : List UInt8) : List UInt8 :=
  let kk := key.length
  let d := (if kk = 0 then [] else key ++ List.replicate (64 - kk) 0) ++ msg
  let h := iv.set 0 (iv[0] ^^^ (0x01010000 : UInt32) ^^^ kk.toUInt32 <<< 8 ^^^ nn.toUInt32)
  let h := compressInput h 0 d (if d.length ≤ 64 then 0 else d.length / 64)   -- MUTATED
  let le (w : UInt32) := [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]
  (h.toList.flatMap le).take nn

def padNN (key : List UInt8) (nn : Nat) (msg : List UInt8) : List UInt8 :=
  let kk := key.length
  let d := (if kk = 0 then [] else key ++ List.replicate (64 - nn) 0) ++ msg   -- MUTATED
  let h := iv.set 0 (iv[0] ^^^ (0x01010000 : UInt32) ^^^ kk.toUInt32 <<< 8 ^^^ nn.toUInt32)
  let h := compressInput h 0 d ((d.length - 1) / 64)
  let le (w : UInt32) := [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]
  (h.toList.flatMap le).take nn

/-! `heldBack` passes all seven blake2s KATs of the controls. -/
theorem hb_abc : heldBack [] 32 abc =
    hex "508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982" := by decide +kernel
theorem hb_empty : heldBack [] 32 [] =
    hex "69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9" := by decide +kernel
theorem hb_a64 : heldBack [] 32 (List.replicate 64 0x61) =
    hex "651d2f5f20952eacaea2fba2f2af2bcd633e511ea2d2e4c9ae2ac0d9ffb7b252" := by decide +kernel
theorem hb_a65 : heldBack [] 32 (List.replicate 65 0x61) =
    hex "045f8ae18932119bd051ac7ba5c73db59892055fad5c32f82d79a6543d92a497" := by decide +kernel
theorem hb_keyed_empty : heldBack key32 32 [] =
    hex "48a8997da407876b3d79c0d92325ad3b89cbb754d86ab71aee047ad345fd2c49" := by decide +kernel
theorem hb_keyed_65 : heldBack key32 32 (pattern 65) =
    hex "82e02e62a066f2f3cd7a8a542581cbf441e35cf7a771fc7adb0965d8446b71cb" := by decide +kernel
theorem hb_nn16 : heldBack [] 16 abc = hex "aa4938119b1dc7b87cbad0ffd200d0ae" := by decide +kernel
/-- ... and fails the 128-byte vector. -/
theorem hb_len128 : heldBack [] 32 (pattern 128) ≠
    hex "83470c75afa23d90cd7659906e4b47daa278131fbb225241dd37a40fd5355ac7" := by decide +kernel

/-! `padNN` passes the two keyed KATs (the unkeyed ones never reach the mutated branch). -/
theorem pn_keyed_empty : padNN key32 32 [] =
    hex "48a8997da407876b3d79c0d92325ad3b89cbb754d86ab71aee047ad345fd2c49" := by decide +kernel
theorem pn_keyed_65 : padNN key32 32 (pattern 65) =
    hex "82e02e62a066f2f3cd7a8a542581cbf441e35cf7a771fc7adb0965d8446b71cb" := by decide +kernel
/-- ... and fails the `kk = 1` vector. -/
theorem pn_kk1 : padNN [0x2a] 32 abc ≠
    hex "0c69fe270a3fe7eec19c874b6ce6d86aa72b1a72325749addbdefae817491962" := by decide +kernel

/-- The unkeyed branch of `padNN` is literally the spec's, so the unkeyed KATs carry over. -/
theorem pn_unkeyed (nn : Nat) (msg : List UInt8) : padNN [] nn msg = blake2s [] nn msg := rfl

/-! The single combined vector `kk = 1`, 64-byte message (`probes/s2/Combined.lean`) kills both. -/
theorem hb_kk1len64 : heldBack [0x2a] 32 (pattern 64) ≠
    hex "ac00e6c0bcf8a333106c7f08f68dc06a227a51af0447abb1d099cae263983b85" := by decide +kernel
theorem pn_kk1len64 : padNN [0x2a] 32 (pattern 64) ≠
    hex "ac00e6c0bcf8a333106c7f08f68dc06a227a51af0447abb1d099cae263983b85" := by decide +kernel

/-! ## Fix pass (S2-M1, S2-m1): every mutant fails a vector of `Controls/Blake2s.lean`

`hb_len128` is the vector of `len128_kat`; `hb_kk1len64` and `pn_kk1len64` are the vector of
`kk1_kat`. A third mutant, `wordTrunc`, keeps whole words of the state (`4 ⌈nn/4⌉` bytes): it is
the spec whenever `4 ∣ nn`, so it passes every vector with `nn ∈ {16, 32}`, and fails `nn1_kat`. -/

def wordTrunc (key : List UInt8) (nn : Nat) (msg : List UInt8) : List UInt8 :=
  let kk := key.length
  let d := (if kk = 0 then [] else key ++ List.replicate (64 - kk) 0) ++ msg
  let h := iv.set 0 (iv[0] ^^^ (0x01010000 : UInt32) ^^^ kk.toUInt32 <<< 8 ^^^ nn.toUInt32)
  let h := compressInput h 0 d ((d.length - 1) / 64)
  let le (w : UInt32) := [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]
  (h.toList.flatMap le).take (4 * ((nn + 3) / 4))   -- MUTATED

theorem wt_32 (key msg : List UInt8) : wordTrunc key 32 msg = blake2s key 32 msg := rfl
theorem wt_16 (key msg : List UInt8) : wordTrunc key 16 msg = blake2s key 16 msg := rfl
theorem wt_nn1 : wordTrunc [] 1 abc ≠ hex "0d" := by decide +kernel

end S2Review
