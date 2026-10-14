/- S2 review probe: the RFC 7693 Appendix E self-test (`blake2s_selftest`), evaluated with the spec.
Independent of hashlib: the expected grand hash `blake2s_res` is printed in the RFC. It covers
nn ∈ {16, 20, 28, 32}, ll ∈ {0, 3, 64, 65, 255, 1024}, unkeyed and keyed with kk = nn, and a
final 1152-byte hash (18 blocks). Run: `lake env lean probes/s2/SelfTest.lean` (no output = pass). -/
import RecursionFast.Contract.Hash.Blake2s

open RecursionFast

/-- RFC 7693 Appendix E `selftest_seq`: a Fibonacci sequence, top byte of each term. -/
def selftestSeq (len : Nat) (seed : UInt32) : List UInt8 := Id.run do
  let mut a : UInt32 := 0xDEAD4BAD * seed
  let mut b : UInt32 := 1
  let mut out : Array UInt8 := #[]
  for _ in [0:len] do
    let t := a + b
    a := b
    b := t
    out := out.push (t >>> 24).toUInt8
  return out.toList

/-- The grand hash of RFC 7693 Appendix E. -/
def grand : List UInt8 := Id.run do
  let mut acc : List UInt8 := []
  for outlen in [16, 20, 28, 32] do
    for inlen in [0, 3, 64, 65, 255, 1024] do
      let msg := selftestSeq inlen inlen.toUInt32
      acc := acc ++ blake2s [] outlen msg
      acc := acc ++ blake2s (selftestSeq outlen outlen.toUInt32) outlen msg
  return blake2s256 acc

/-- `blake2s_res` from RFC 7693 Appendix E. -/
def blake2sRes : List UInt8 :=
  [0x6A, 0x41, 0x1F, 0x08, 0xCE, 0x25, 0xAD, 0xCD, 0xFB, 0x02, 0xAB, 0xA6, 0x41, 0x45, 0x1C, 0xEC,
   0x53, 0xC5, 0x98, 0xB2, 0x4F, 0x4F, 0xC7, 0x87, 0xFB, 0xDC, 0x88, 0x79, 0x7F, 0x4C, 0x1D, 0xFE]

/- Evaluated (interpreter), never a kernel theorem: as `decide +kernel` it exceeds 32 GB
(`probes/s2/SelfTestKernel.lean`). Silent on success. -/
#guard grand == blake2sRes
