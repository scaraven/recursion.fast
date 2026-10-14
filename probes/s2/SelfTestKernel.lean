/- S2 review probe: the RFC 7693 Appendix E self-test as a kernel-checked theorem (timing only;
DO NOT RUN casually: aborted after 5 min at 32.9 GB RSS;
too slow for CI). Same computation as `SelfTest.lean`, written with structural recursion. -/
import RecursionFast.Contract.Hash.Blake2s

open RecursionFast

/-- `selftest_seq`, structurally: state `(a, b)`, emit the top byte of `a + b`. -/
def seqGo : Nat → UInt32 → UInt32 → List UInt8
  | 0, _, _ => []
  | n + 1, a, b => ((a + b) >>> 24).toUInt8 :: seqGo n b (a + b)

def selftestSeq (len : Nat) (seed : UInt32) : List UInt8 := seqGo len (0xDEAD4BAD * seed) 1

def grand : List UInt8 :=
  blake2s256 <| [16, 20, 28, 32].flatMap fun outlen =>
    [0, 3, 64, 65, 255, 1024].flatMap fun inlen =>
      let msg := selftestSeq inlen inlen.toUInt32
      blake2s [] outlen msg ++ blake2s (selftestSeq outlen outlen.toUInt32) outlen msg

def blake2sRes : List UInt8 :=
  [0x6A, 0x41, 0x1F, 0x08, 0xCE, 0x25, 0xAD, 0xCD, 0xFB, 0x02, 0xAB, 0xA6, 0x41, 0x45, 0x1C, 0xEC,
   0x53, 0xC5, 0x98, 0xB2, 0x4F, 0x4F, 0xC7, 0x87, 0xFB, 0xDC, 0x88, 0x79, 0x7F, 0x4C, 0x1D, 0xFE]

#eval grand == blake2sRes

theorem rfc_selftest : grand = blake2sRes := by decide +kernel

#print axioms rfc_selftest
