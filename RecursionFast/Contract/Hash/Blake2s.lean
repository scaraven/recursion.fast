/-
# Contract: the hash BLAKE2s (RFC 7693)                          (TRUSTED, Lean core only)

The contract's hash (DESIGN-v3 §3.4). It is the chain step and the statement hash of the
relation (`Relation.lean`) and the instantiation of the oracle (`Certificate.lean`,
`blake2sOracle`). It is pure, total and computable: the executed verifier runs this function,
compiled by Lean.

`blake2s key nn msg` is BLAKE2s of RFC 7693 §3.3: 32-bit words, ten rounds, rotations
`(16, 12, 8, 7)` (§2.1), an `nn`-byte digest, an optional key. `blake2s256` is the unkeyed
32-byte digest. Bytes are `UInt8`, words `UInt32`, the offset counter `UInt64`. Known-answer
tests (RFC 7693 Appendix B, Python's `hashlib.blake2s`, the pinned leanVM) are kernel-checked in
`RecursionFast/Controls/Blake2s.lean`.

Provenance. Vendored from leanerVM (Apache-2.0, github.com/Verified-zkEVM/leanerVM, commit
`485d0465d1db38a471fb387aa0dd6baf5a5a1ac7`; licence text in `LICENSE-leanerVM`, next to this
file). Modified files carry this notice (Apache-2.0 §4(b)).
* `iv`, `sigma`: `LeanerVM/Parameters/Blake2s.lean` lines 29–47, leanerVM's mechanical dump of the
  RFC 7693 text (Appendix D, `blake2s_iv` and `sigma`; `scripts/dump-blake2s.py constants`, RFC
  text SHA-256 `c943754888364fe29bbd0bb3c71c6658ef392371497eaa4a9d9dde015b0721e5`). The controls
  re-check them against the RFC's definitions (`iv_spec`, `sigma_perm`).
* `rotr`, `mix`, `round`, `initialState`, `compress`: `LeanerVM/Semantics/Blake2s.lean` lines
  64–110.
* Changes: `rotr` uses machine shifts, not `BitVec.rotateRight` (the compiled hash is about 7×
  faster; the two agree below 32, `Blake2s.rotr_eq_rotateRight` in `Library/Blake2s.lean`); all
  of it is in namespace `RecursionFast.Blake2s` (`iv`, `sigma` were in `LeanerVM.Parameters`), so
  `compress` writes `round`, not `Blake2s.round`; the module-system annotations are dropped.
* New here: `block`, `compressInput`, `blake2s`, `blake2s256`.
-/

namespace RecursionFast

namespace Blake2s

/-- The BLAKE2s initialization vector, RFC 7693 §2.6: `IV[i] = ⌊2^32 · frac(√pᵢ₊₁)⌋` for the first
eight primes, the SHA-256 IV. -/
def iv : Vector UInt32 8 := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- The BLAKE2s message schedule, RFC 7693 §2.7: `sigma[r]` is the permutation of the sixteen
message words consumed by round `r`. -/
def sigma : Vector (Vector (Fin 16) 16) 10 := #v[
  #v[ 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15],
  #v[14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3],
  #v[11,  8, 12,  0,  5,  2, 15, 13, 10, 14,  3,  6,  7,  1,  9,  4],
  #v[ 7,  9,  3,  1, 13, 12, 11, 14,  2,  6,  5, 10,  4,  0, 15,  8],
  #v[ 9,  0,  5,  7,  2,  4, 10, 15, 14,  1, 11, 12,  6,  8,  3, 13],
  #v[ 2, 12,  6, 10,  0, 11,  8,  3,  4, 13,  7,  5, 15, 14,  1,  9],
  #v[12,  5,  1, 15, 14, 13,  4, 10,  0,  7,  6,  3,  9,  2,  8, 11],
  #v[13, 11,  7, 14, 12,  1,  3,  9,  5,  0, 15,  4,  8,  6,  2, 10],
  #v[ 6, 15, 14,  9, 11,  3,  0,  8, 12,  2, 13,  7,  1,  4, 10,  5],
  #v[10,  2,  8,  4,  7,  6,  1,  5, 15, 11,  9, 14,  3, 12, 13,  0]]

/-- Rotate a 32-bit word right by `n < 32` bits (RFC 7693 §2.3, `>>>`), with machine shifts
(BLAKE2s uses `n ∈ {16, 12, 8, 7}`). -/
def rotr (x : UInt32) (n : Nat) : UInt32 := x >>> n.toUInt32 ||| x <<< (32 - n).toUInt32

/-- The mixing function `G` (RFC 7693 §3.1) with the BLAKE2s rotations `(16, 12, 8, 7)` (§2.1). -/
def mix (v : Vector UInt32 16) (a b c d : Fin 16) (x y : UInt32) : Vector UInt32 16 :=
  let va := v[a] + v[b] + x
  let vd := rotr (v[d] ^^^ va) 16
  let vc := v[c] + vd
  let vb := rotr (v[b] ^^^ vc) 12
  let va := va + vb + y
  let vd := rotr (vd ^^^ va) 8
  let vc := vc + vd
  let vb := rotr (vb ^^^ vc) 7
  (((v.set a va).set b vb).set c vc).set d vd

/-- One round of `F` (RFC 7693 §3.2): the four column and the four diagonal `G` calls, with the
message words selected by the schedule row `s`. -/
def round (v m : Vector UInt32 16) (s : Vector (Fin 16) 16) : Vector UInt32 16 :=
  let v := mix v 0 4 8 12 m[s[0]] m[s[1]]
  let v := mix v 1 5 9 13 m[s[2]] m[s[3]]
  let v := mix v 2 6 10 14 m[s[4]] m[s[5]]
  let v := mix v 3 7 11 15 m[s[6]] m[s[7]]
  let v := mix v 0 5 10 15 m[s[8]] m[s[9]]
  let v := mix v 1 6 11 12 m[s[10]] m[s[11]]
  let v := mix v 2 7 8 13 m[s[12]] m[s[13]]
  mix v 3 4 9 14 m[s[14]] m[s[15]]

/-- The initial working vector of `F`: `h`, then `iv` with the two counter words and the two
flag words XORed into its last four words (RFC 7693 §3.2; `blake2s-ref.c` for `v[15]`). -/
def initialState (h : Vector UInt32 8) (t : UInt64) (f0 f1 : UInt32) : Vector UInt32 16 :=
  let v : Vector UInt32 16 := h ++ iv
  let v := v.set 12 (v[12] ^^^ t.toUInt32)
  let v := v.set 13 (v[13] ^^^ (t >>> 32).toUInt32)
  let v := v.set 14 (v[14] ^^^ f0)
  v.set 15 (v[15] ^^^ f1)

/-- The BLAKE2s compression function `F` (RFC 7693 §3.2) with the tree-mode last-node flag:
`t` is the 64-bit offset counter, `f0` the last-block flag and `f1` the last-node flag, each
`0xFFFFFFFF` when set. Ten rounds under `sigma`, then `h[i] ^ v[i] ^ v[i + 8]`. -/
def compress (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64) (f0 f1 : UInt32) :
    Vector UInt32 8 :=
  let v := sigma.foldl (fun v s ↦ round v m s) (initialState h t f0 f1)
  #v[h[0] ^^^ v[0] ^^^ v[8], h[1] ^^^ v[1] ^^^ v[9], h[2] ^^^ v[2] ^^^ v[10],
     h[3] ^^^ v[3] ^^^ v[11], h[4] ^^^ v[4] ^^^ v[12], h[5] ^^^ v[5] ^^^ v[13],
     h[6] ^^^ v[6] ^^^ v[14], h[7] ^^^ v[7] ^^^ v[15]]

/-- A message block `m` (RFC 7693 §2.4, §3.3): the first 64 bytes of `d`, zero-padded, as sixteen
little-endian words, `m[j] = d[4j] + 2^8·d[4j+1] + 2^16·d[4j+2] + 2^24·d[4j+3]`. -/
def block (d : List UInt8) : Vector UInt32 16 :=
  let a := (d.take 64).toArray
  let b (i : Nat) : UInt32 := (a.getD i 0).toUInt32
  Vector.ofFn fun j =>
    b (4 * j.val) ||| b (4 * j.val + 1) <<< 8 ||| b (4 * j.val + 2) <<< 16 |||
      b (4 * j.val + 3) <<< 24

/-- The block loop of RFC 7693 §3.3, from the chaining value `h`, with `t` input bytes
compressed before, `d` the input left, and `n` blocks of it before the final one. A non-final
block is the next 64 bytes of `d`, compressed with counter `t + 64` and no flag. The final block
is the rest of `d` (at most 64 bytes when `n = (|d| - 1) / 64`), zero-padded, compressed with
counter `t + |d|` and the last-block flag `0xFFFFFFFF` (`f1 = 0`: no tree mode). -/
def compressInput (h : Vector UInt32 8) (t : Nat) (d : List UInt8) : Nat → Vector UInt32 8
  | 0 => compress h (block d) (t + d.length).toUInt64 0xFFFFFFFF 0
  | n + 1 => compressInput (compress h (block d) (t + 64).toUInt64 0 0) (t + 64) (d.drop 64) n

end Blake2s

open Blake2s in
/-- BLAKE2s with key `key` and an `nn`-byte digest (RFC 7693 §3.3), for `key.length ≤ 32` and
`1 ≤ nn ≤ 32`; outside this range the RFC defines nothing. The parameter block `0x0101kknn`
(§2.5) is XORed into `iv[0]`. The input `d` is the key zero-padded to one block (if `kk > 0`),
then the message. Its `dd = max 1 ⌈|d|/64⌉` blocks are compressed in order, each with the count
of input bytes up to its end, the last one flagged. The digest is the first `nn` bytes of the
state, each word little-endian (§2.4). -/
def blake2s (key : List UInt8) (nn : Nat) (msg : List UInt8) : List UInt8 :=
  let kk := key.length
  let d := (if kk = 0 then [] else key ++ List.replicate (64 - kk) 0) ++ msg
  let h := iv.set 0 (iv[0] ^^^ (0x01010000 : UInt32) ^^^ kk.toUInt32 <<< 8 ^^^ nn.toUInt32)
  let h := compressInput h 0 d ((d.length - 1) / 64)    -- `(|d| - 1) / 64 = dd - 1`
  let le (w : UInt32) := [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]
  (h.toList.flatMap le).take nn

/-- BLAKE2s-256: the unkeyed 32-byte digest (RFC 7693 §3.3 with `kk = 0`, `nn = 32`). -/
def blake2s256 (msg : List UInt8) : List UInt8 := blake2s [] 32 msg

end RecursionFast
