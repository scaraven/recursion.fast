import RecursionFast.Controls.Extractor
/-! S4 review probe (findings S4-m1, S4-m2): what `extractorFuel k = 2^(2k+16)` admits.
(Fix pass: `extractorFuel k n = B(k) / (n + 1)`; this probe reads `B(k)` as `extractorBudget k`.
The facts are restated over `2^(2k+16)` in `Controls/Extractor.lean`: `oracle_sq`, `cube_gt`,
`budget_24_25`.)

* `oracle_sq`: the square of the longest message oracle (`2^(k+10)` elements, the shape cap) is
  `16 · B(k)`. So `B(k)` is not "quadratic in the oracle length" (`extractorFuel`'s docstring):
  it is `2^16 ·` (witness cells)², i.e. quadratic in `2^(k+8)`.
* `cube_gt`: Gaussian elimination on a system with as many unknowns as the witness has cells
  (`2^k`) needs about `(2^k)^3` field operations, more than `B(k)` steps at every class `k ≥ 17`,
  even at one step per operation. So "admits decoding by Gaussian elimination" is false in the
  whole range `20 ≤ k ≤ 28`; quadratic decoders fit only for short codewords, quasi-linear ones
  (additive-FFT based) for the longest.
* `k24_single_call`: at class 24, enumerating `2^64` candidates in one call needs at most one
  step per candidate, but a loop needs at least a test and a branch: S4-A7's "from `k ≥ 24`" is
  "from `k ≥ 25`" for a single call (and every class for the composed extractor, S4-M1).
-/

namespace RecursionFast.Probe.FuelArith
open RecursionFast

theorem oracle_sq (k : ℕ) : (2 ^ (k + 10)) ^ 2 = 16 * extractorBudget k := by
  rw [extractorBudget, ← pow_mul, show (k + 10) * 2 = 4 + (2 * k + 16) by ring, pow_add]; norm_num

theorem cube_gt {k : ℕ} (hk : 17 ≤ k) : extractorBudget k < (2 ^ k) ^ 3 := by
  rw [extractorBudget, ← pow_mul]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem k24_single_call : extractorBudget 24 < 2 * 2 ^ 64 ∧ 4 * 2 ^ 64 ≤ extractorBudget 25 := by
  simp [extractorBudget]

#print axioms oracle_sq
#print axioms cube_gt
#print axioms k24_single_call

end RecursionFast.Probe.FuelArith
