/-
# Controls: the hash BLAKE2s (`Contract/Hash/Blake2s.lean`), positive and negative   (DESIGN §8)

Known-answer tests decided by the kernel (`decide +kernel`; plain `decide` and `rfl` exhaust the
elaborator's recursion depth). An expected digest is written as the hex string of its source and
read by `hex`. The general facts (`rotr` against leanerVM's rotation, digest lengths) are theorems
of `Library/Blake2s.lean`. Outside CI, in v2's probes (git history, tag `v2-archive`): the grid
differential test against `hashlib` (`probes/s2/Diff.lean`, `diff.py`) and RFC 7693's Appendix E
self-test (`probes/s2/SelfTest.lean`, a `#guard`; as a kernel theorem it exceeds 32 GB).

Constants (the checks of leanerVM's tests): every row of `sigma` is a permutation (`sigma_perm`),
and `iv[i] = ⌊2^32 · frac(√pᵢ)⌋` for the first eight primes (`iv_spec`, RFC 7693 §2.6).

Positive, each digest from RFC 7693 Appendix B, `hashlib.blake2s` or the pinned leanVM's tests
(`|d|` is the input length, key block included):
* `abc_kat`: BLAKE2s-256("abc"), RFC 7693 Appendix B: one block, counter 3;
* `empty_kat`: the empty message: one zero block, counter 0;
* `a64_kat`: 64 × "a": exactly one full block (no empty block after it), counter 64;
* `a65_kat`: 65 × "a": two blocks, counter 64 without and 65 with the last-block flag;
* `keyed_empty_kat`: key `0, 1, …, 31` and the empty message: the key block alone, counter 64;
* `keyed_65_kat`: the same key and leanVM's 65-byte pattern: three blocks, counters 64, 128, 129;
* `nn16_kat`: the 16-byte digest of "abc";
* `len128_kat`: `|d| = 128`: a full final block after a non-final one is not followed by an
  empty block (the held-back-block rule; Merkle nodes of arity 4, 8, 16 and `d2` are of this kind);
* `kk1_kat`: a one-byte key (padded with `64 - kk` zeros, `kk ≠ nn`) and 64 bytes, `|d| = 128`;
* `nn1_kat`, `kk1nn16_kat`: `nn = 1` (truncation inside a word); `kk = 1` with `nn = 16`;
* `lastNode_kat`: the vendored `compress` with the last-node flag (unused by `blake2s`) agrees
  with leanerVM's `hashlib` vector;
* `highCounter_kat`: the high counter word, `t = 2^32 + 3`, against an independent model.

Negative:
* `flip_neg`: one bit flipped in the message ("abc" → "abb") changes the digest;
* `key_neg`: the key changes the digest of the empty message;
* `nn_neg`: the 16-byte digest is not the 32-byte digest truncated (`nn` is in the parameter block).

Mutants (v2's `probes/s2/Mutants.lean`, tag `v2-archive`): a block loop that hashes an extra empty
block when `|d|` is a multiple of 64 passes the first seven KATs and fails `len128_kat` and
`kk1_kat`; key padding by `64 - nn` fails `kk1_kat`; truncation to whole words fails `nn1_kat`.
-/
import RecursionFast.Contract.Hash.Blake2s

namespace RecursionFast.Controls.Blake2s
open RecursionFast RecursionFast.Blake2s

/-- The value of a lowercase hex digit. -/
def hexDigit (c : Char) : Nat := if c ≤ '9' then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

/-- The bytes of a list of lowercase hex digits, two digits per byte. -/
def hexBytes : List Char → List UInt8
  | a :: b :: r => (16 * hexDigit a + hexDigit b).toUInt8 :: hexBytes r
  | _ => []

/-- The bytes written by a lowercase hex string, the form in which the vectors are published. -/
def hex (s : String) : List UInt8 := hexBytes s.toList

theorem hex_pos : hex "00ff7f80a519" = [0x00, 0xff, 0x7f, 0x80, 0xa5, 0x19] := by decide +kernel

/-- The string "abc". -/
def abc : List UInt8 := [0x61, 0x62, 0x63]

/-- The key `0, 1, …, 31` of the keyed vectors. -/
def key32 : List UInt8 := (List.range 32).map Nat.toUInt8

/-- leanVM's test pattern (`crates/primitives/src/hash.rs`): byte `i` is `7i + 3 mod 256`. -/
def pattern (n : Nat) : List UInt8 := (List.range n).map fun i => (7 * i + 3).toUInt8

/-! ## Constants -/

/-- Every row of the message schedule is a permutation of the sixteen word indices (§2.7). -/
theorem sigma_perm : ∀ r : Fin 10, ∀ j : Fin 16, ∃ k : Fin 16, sigma[r][k] = j := by decide +kernel

/-- The first eight primes and the integer parts of their square roots. -/
def primes : Vector (Nat × Nat) 8 :=
  #v[(2, 1), (3, 1), (5, 2), (7, 2), (11, 3), (13, 3), (17, 4), (19, 4)]

/-- RFC 7693 §2.6: with `p = pᵢ`, `q = ⌊√p⌋` and `s = 2^32 · q + iv[i]`, the word `iv[i]` is
`⌊2^32 · frac(√p)⌋` exactly when `s = ⌊√(p · 2^64)⌋`, that is `s² ≤ p · 2^64 < (s + 1)²`. -/
theorem iv_spec : ∀ i : Fin 8,
    let p := primes[i].1
    let q := primes[i].2
    let s := 2 ^ 32 * q + iv[i].toNat
    q ^ 2 ≤ p ∧ p < (q + 1) ^ 2 ∧ s ^ 2 ≤ p * 2 ^ 64 ∧ p * 2 ^ 64 < (s + 1) ^ 2 := by decide +kernel

/-! ## Known answers -/

/-- RFC 7693 Appendix B: BLAKE2s-256("abc"). -/
theorem abc_kat : blake2s256 abc =
    hex "508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982" := by decide +kernel

/-- The empty message (`hashlib`; leanVM `crates/primitives/src/hash.rs`). -/
theorem empty_kat : blake2s256 [] =
    hex "69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9" := by decide +kernel

/-- 64 × "a" (`hashlib`; leanVM `crates/flock/src/hash.rs`). -/
theorem a64_kat : blake2s256 (List.replicate 64 0x61) =
    hex "651d2f5f20952eacaea2fba2f2af2bcd633e511ea2d2e4c9ae2ac0d9ffb7b252" := by decide +kernel

/-- 65 × "a" (`hashlib`; leanVM `crates/flock/src/hash.rs`). -/
theorem a65_kat : blake2s256 (List.replicate 65 0x61) =
    hex "045f8ae18932119bd051ac7ba5c73db59892055fad5c32f82d79a6543d92a497" := by decide +kernel

/-- Keyed, empty message (`hashlib`; leanVM `crates/primitives/src/hash.rs`). -/
theorem keyed_empty_kat : blake2s key32 32 [] =
    hex "48a8997da407876b3d79c0d92325ad3b89cbb754d86ab71aee047ad345fd2c49" := by decide +kernel

/-- Keyed, 65-byte pattern (`hashlib`; leanVM `crates/primitives/src/hash.rs`). -/
theorem keyed_65_kat : blake2s key32 32 (pattern 65) =
    hex "82e02e62a066f2f3cd7a8a542581cbf441e35cf7a771fc7adb0965d8446b71cb" := by decide +kernel

/-- The 16-byte digest of "abc" (`hashlib.blake2s(b"abc", digest_size=16)`). -/
theorem nn16_kat : blake2s [] 16 abc = hex "aa4938119b1dc7b87cbad0ffd200d0ae" := by decide +kernel

/-- 128 bytes: the final block is full and follows a non-final one (counters 64, then 128 with
the flag), and no empty block follows it; a 4-ary Merkle node (`hashlib`; leanVM
`crates/primitives/src/hash.rs`, `pattern(128)`). -/
theorem len128_kat : blake2s256 (pattern 128) =
    hex "83470c75afa23d90cd7659906e4b47daa278131fbb225241dd37a40fd5355ac7" := by decide +kernel

/-- A one-byte key, padded with 63 zeros (`kk = 1 ≠ nn = 32`), and 64 bytes, so `|d| = 128`
(`hashlib.blake2s(pattern(64), key=b"\x2a")`). -/
theorem kk1_kat : blake2s [0x2a] 32 (pattern 64) =
    hex "ac00e6c0bcf8a333106c7f08f68dc06a227a51af0447abb1d099cae263983b85" := by decide +kernel

/-- `nn = 1`: the parameter byte `0x01` and a truncation inside a word
(`hashlib.blake2s(b"abc", digest_size=1)`). -/
theorem nn1_kat : blake2s [] 1 abc = hex "0d" := by decide +kernel

/-- A one-byte key and a 16-byte digest (`kk = 1`, `nn = 16`, neither 32) on the message "a"
(`hashlib.blake2s(b"a", digest_size=16, key=b"\x2a")`). -/
theorem kk1nn16_kat : blake2s [0x2a] 16 [0x61] = hex "27729f2e690470d05ce874954a0e09f2" := by
  decide +kernel

/-- `compress` with both flags set, on the empty message's block (leanerVM
`tests/LeanerVMTests/Semantics/Blake2s.lean`, from `hashlib.blake2s(b"", last_node=True)`). -/
theorem lastNode_kat :
    (compress (iv.set 0 (iv[0] ^^^ 0x01010020)) (block []) 0 0xFFFFFFFF 0xFFFFFFFF).toList =
      [0x3c11fc24, 0x848cbe3d, 0x40703c49, 0x680dafae, 0xab7b3bcc, 0x49aecd0d, 0x704abbdb,
       0x365c9d25] := by decide +kernel

/-- The high counter word (`t ≥ 2^32`; no input under the 1 MiB tape cap reaches it): `compress`
of the block of "abc" at `t = 2^32 + 3` with the last-block flag, against an independent Python
model of RFC 7693 §3.1–§3.2 (v2's `probes/s2/compress_model.py`, tag `v2-archive`, itself equal
to `hashlib` on 609 inputs). -/
theorem highCounter_kat :
    (compress (iv.set 0 (iv[0] ^^^ 0x01010020)) (block abc) (2 ^ 32 + 3) 0xFFFFFFFF 0).toList =
      [0xedf58467, 0x5f61f77f, 0xc304857e, 0x7b284348, 0xaea1cac1, 0xc1d78886, 0x0ddcb65a,
       0x74b202fa] := by decide +kernel

/-! ## Negative -/

/-- One bit flipped in the message (`0x63` → `0x62`, "abc" → "abb") changes the digest. -/
theorem flip_neg : blake2s256 [0x61, 0x62, 0x62] ≠ blake2s256 abc := by decide +kernel

/-- The key changes the digest. -/
theorem key_neg : blake2s key32 32 [] ≠ blake2s256 [] := by decide +kernel

/-- The 16-byte digest is not a truncation of the 32-byte one: `nn` is in the parameter block. -/
theorem nn_neg : blake2s [] 16 abc ≠ (blake2s256 abc).take 16 := by decide +kernel

end RecursionFast.Controls.Blake2s
