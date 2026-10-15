import Lean
/-! v0.3 gate test (A4), v2 port: a false theorem smuggled past the kernel with
`debug.skipKernelTC`. The tactic assigns `Eq.refl 1` to the goal `1 = 2` without the elaborator
checking it; the kernel would reject it. The `.olean` carries no trace of the option, so the gate
passes it; `leanchecker` and the comparator's fresh-kernel replay reject. (v0.3 used the Library
tactic `kernel_rfl`, which v2 does not carry over.) -/
open Lean Elab Tactic in
/-- Close the goal with `Eq.refl 1`, unchecked. -/
elab "unchecked_rfl" : tactic => do
  (← getMainGoal).assign (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 1))
  replaceMainGoal []

set_option debug.skipKernelTC true in
theorem cert : (1 : Nat) = 2 := by unchecked_rfl
