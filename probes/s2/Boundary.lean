/- S2 review probe: boundary vectors missing from `Controls/Blake2s.lean`, kernel-checked.
Expected digests: `python3 -I probes/s2/vectors.py` (hashlib); the unkeyed pattern-128/192 and
keyed pattern-64 values also appear in leanVM `crates/primitives/src/hash.rs` at `a386121f`. -/
import RecursionFast.Controls.Blake2s

namespace S2Review
open RecursionFast RecursionFast.Blake2s RecursionFast.Controls.Blake2s

/-- The reader on all sixteen digits. -/
theorem hex_all : hex "0123456789abcdef" = [0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef] := by
  decide +kernel

/-- One-byte message ("a"): `ll = 1`, the smallest nonempty final block. -/
theorem len1 : blake2s256 [0x61] =
    hex "4a0d129873403037c2cd9b9048203687f6233fb6738956e0349bd4320fec3e90" := by decide +kernel

/-- 128 bytes = exactly two full blocks: the final block is full and follows a non-final one
(leanVM's "held-back-buffer rule"; a 4-ary Merkle node). Counters 64, 128 (flag). -/
theorem len128 : blake2s256 (pattern 128) =
    hex "83470c75afa23d90cd7659906e4b47daa278131fbb225241dd37a40fd5355ac7" := by decide +kernel

/-- 129 bytes, unkeyed: three blocks, counters 64, 128, 129 (flag). -/
theorem len129 : blake2s256 (pattern 129) =
    hex "26fd8892ab0a5f12d4acbff1efd7dcd92b99e2d377f888f07e3cb81b232b11cf" := by decide +kernel

/-- `nn = 1`: smallest digest; parameter byte `0x01` and truncation to one byte. -/
theorem nn1 : blake2s [] 1 abc = hex "0d" := by decide +kernel

/-- `kk = 1`: a one-byte key padded with 63 zeros; parameter block `0x01010120`. -/
theorem kk1 : blake2s [0x2a] 32 abc =
    hex "0c69fe270a3fe7eec19c874b6ce6d86aa72b1a72325749addbdefae817491962" := by decide +kernel

/-- `kk = 1`, `nn = 1`, empty message: every parameter at its minimum. -/
theorem kk1nn1empty : blake2s [0x2a] 1 [] = hex "13" := by decide +kernel

/-- Keyed, 64-byte message: `|d| = 128`, the key block then a full final block, counter 128. -/
theorem kk32len64 : blake2s key32 32 (pattern 64) =
    hex "ce3c22b930e6395797de1e490600d305294ff2e30eb187bb63120e3f5e3fc129" := by decide +kernel

/-- Keyed, one-byte message: key block non-final (counter 64), then 1 byte (counter 65). -/
theorem kk32len1 : blake2s key32 32 [0x61] =
    hex "17157c0b0267627415d490c72861209be87ea201495c7e8d45fc7299fa04e399" := by decide +kernel

end S2Review
