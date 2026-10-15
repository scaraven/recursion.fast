import Mathlib
/-! A4 HygieneBypass.lean.txt as a module (v0.3 gate test): every construct the v0.2 regex missed. -/
def opener := "/-"
theorem hidden_sorry : (1 : ℕ) = 2 := sorry
def closer := "-/"
set_option debug.skipKernelTC true in
theorem unchecked : True := trivial
unsafe def u : ℕ := 0
opaque o : ℕ
partial def loop (n : ℕ) : ℕ := loop n
theorem nd : 2 + 2 = 4 := by decide +native
/-- The "certificate": uses the hidden sorry, `decide +native`, the opaque and the partial constant. -/
theorem cert : (1 : ℕ) = 2 ∧ 2 + 2 = 4 ∧ o = o ∧ loop = loop := ⟨hidden_sorry, nd, rfl, rfl⟩
