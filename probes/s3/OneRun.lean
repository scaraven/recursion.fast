-- One honest kernel run of the compiled verifier on cmpToy (S3 cost probe).
import RecursionFast.Controls.CompileToy
open RecursionFast RecursionFast.Controls.Compile
theorem h1 : NARG cfg2 cmpToy vkc2 x0 tape2 = true := by decide +kernel
