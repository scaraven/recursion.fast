import RecursionFast.Controls.CompileToy
open RecursionFast RecursionFast.Controls.Compile
-- Two runs in one declaration: the kernel's cache shares the hashes they have in common.
theorem h2 : NARG cfg2 cmpToy vkc2 x0 tape2 = true ∧ NARG cfg2 cmpToy vkc2 x0 (tape2 ++ [0]) = false := by
  decide +kernel
