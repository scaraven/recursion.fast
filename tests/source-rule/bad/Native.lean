/- Fixture for scripts/source-rule.py (never compiled): proofs by evaluation of compiled code (the
certificate then depends on an auxiliary `_…decide.ax_…` axiom, which gate rule 1 and the axiom
audits also reject); `decide +kernel` and `decide` are fine. Every line marked `-- REJECT` must be
reported, and no other line. -/
theorem n1 : 2 + 2 = 4 := by native_decide  -- REJECT
theorem n2 : 2 + 2 = 4 := by decide +native  -- REJECT
theorem n3 : 2 + 2 = 4 := by decide (config := { native := true })  -- REJECT
theorem n4 : 2 + 2 = 4 := by decide (native := true)  -- REJECT
def cfg : Lean.Meta.DecideConfig := { Lean.Meta.DecideConfig.native := true }  -- REJECT
theorem n5 : 2 + 2 = 4 := by decide +kernel
theorem n6 : 2 + 2 = 4 := by decide
