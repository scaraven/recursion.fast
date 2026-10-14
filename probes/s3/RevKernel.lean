/- S3 review probe (kernel evaluation, one `decide +kernel`): non-vacuity on `cmpToy`.

* `toy_prove`: the honest compiled prover returns `some tape2` in the KERNEL (the control file
  checks it only by `#guard`, i.e. compiled code): the hypothesis of `narg_complete` is inhabited.

S3 fix pass: `toy_consistent` and `toy_local` (with the honest pass and openings) moved into the
CI controls (`Controls/Compile.lean`, kernel-checked in `runs`); this probe keeps `toy_prove`.
-/
import RecursionFast.Controls.Compile

namespace RecursionFast.S3Review
open RecursionFast RecursionFast.Controls.Compile

theorem toy_prove : prove cfg2 cmpToy L0 x0 [] = some tape2 := by
  decide +kernel

end RecursionFast.S3Review

#print axioms RecursionFast.S3Review.toy_prove
