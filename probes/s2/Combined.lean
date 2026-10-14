/- S2 review probe: one vector (`kk = 1`, 64-byte message, so `|d| = 128`) that pins the short-key
padding and the full-final-block rule at once, and kills both mutants of `Mutants.lean`. -/
import RecursionFast.Controls.Blake2s

namespace S2Review
open RecursionFast RecursionFast.Blake2s RecursionFast.Controls.Blake2s

theorem kk1len64 : blake2s [0x2a] 32 (pattern 64) =
    hex "ac00e6c0bcf8a333106c7f08f68dc06a227a51af0447abb1d099cae263983b85" := by decide +kernel

end S2Review
