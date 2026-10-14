/- S1 review probe (S1-m5), updated in the S1 fix pass.

Originally: the library's "R1CS" had no constant wire (`z = (x, w)`), so every instance was
satisfied by `x = 0, w = 0` and no instance expressed `w₀ = 1`; its admissibility was only
claimed. After the fix (S1-A10, view constant cell) `R1CS` is textbook, `z = (1, x, w)`:
1. `oneR_not_zero`: the instance `w₀ · 1 = 1` is *not* satisfied by `x = 0, w = 0`, so the
   homogeneity of the old definition is gone (`R1CS_zero` no longer holds);
2. `oneR_affine`: it has exactly the solutions `w₀ = 1`;
3. `r1csLayout_admissible` is a theorem, and the control instance is in `relK 6`
   (`Controls.r1cs_relK`). -/
import RecursionFast.Controls

open RecursionFast RecursionFast.Controls Matrix

namespace S1Probe

theorem oneR_not_zero : ¬ R1CS (oneR 0) (oneR 1) (oneR 2) 0 0 := by
  rw [r1cs_sel_iff]; decide +kernel

theorem oneR_affine (x : Fin 32 → K) (w : Fin 1 → K) :
    R1CS (oneR 0) (oneR 1) (oneR 2) x w ↔ w 0 = 1 := by
  rw [r1cs_sel_iff, zVec_33, zVec_0]
  constructor <;> intro h
  · simpa using h
  · simp [h]

theorem r1cs_admissible : (r1csLayout (boolR 0) (boolR 1) (boolR 2)).Admissible 6 :=
  r1csLayout_admissible _ _ _ (by norm_num) (by norm_num) (by norm_num)

end S1Probe
