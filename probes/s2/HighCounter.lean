/- S2 review probe: `compress` with a counter whose high word is nonzero (t ≥ 2^32), against the
independent Python model `probes/s2/compress_model.py` (no hashlib input reaches 4 GiB). -/
import RecursionFast.Controls.Blake2s

namespace S2Review
open RecursionFast RecursionFast.Blake2s RecursionFast.Controls.Blake2s

theorem highCounter :
    (compress (iv.set 0 (iv[0] ^^^ 0x01010020)) (block abc) (2 ^ 32 + 3) 0xFFFFFFFF 0).toList =
      [0xedf58467, 0x5f61f77f, 0xc304857e, 0x7b284348, 0xaea1cac1, 0xc1d78886, 0x0ddcb65a,
       0x74b202fa] := by decide +kernel

theorem maxCounter :
    (compress (iv.set 0 (iv[0] ^^^ 0x01010020)) (block abc) (2 ^ 64 - 1) 0xFFFFFFFF 0).toList =
      [0xec4a5130, 0xfb2becd4, 0x57f80f03, 0x00677db8, 0xc0a6811a, 0x4a99224a, 0x899a82f6,
       0x6e870733] := by decide +kernel

end S2Review
