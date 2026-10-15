import RecursionFast.Contract
open RecursionFast
def submission : Sub := ⟨0⟩
theorem certified : Good submission := rfl
/-- A linter warning (unused simp argument): Lean stores it, with the ABSOLUTE source path, in the
`.olean` (`lintLogExt`). So a rebuild is byte-identical only at the same path (harness: WORK/tree). -/
theorem lintMe : (0 : Nat) + 0 = 0 := by simp only [Nat.add_zero, Nat.mul_one]
