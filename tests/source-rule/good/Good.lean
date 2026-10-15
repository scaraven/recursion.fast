/- Fixture for scripts/source-rule.py (never compiled): forms a submission may use; no finding.
Comments are skipped: #eval run_meta unsafe /- nested /- #exit -/ unsafeCast -/ initialize -/
import Mathlib.Data.Finset.Card
import RecursionFast.Contract
open Finset Nat in
/-- A docstring may mention `#eval`, `run_cmd`, `unsafe` and `import Lean`. -/
def arr : Array Nat := #[1, 2, 3]  -- #eval in a line comment
def vec : Vector Nat 2 := #v[1, 2]
def str := "run_meta #eval unsafeCast \" initialize"
def ch : Char := '#'
def ch2 : Char := '\''
def raw := r#"#eval "unsafe" run_cmd"#
def interp := s!"value {arr.size} #eval unsafe"
def elabish := 0
def runner := 0
def run := 0
@[simp, inline, specialize] def f (n : Nat) := n
attribute [simp] f
#check f
#print f
#reduce f 1
/-- info: 1 -/ #guard_msgs in #check 1
set_option maxHeartbeats 400000 in
theorem t : f 1 = 1 := by simp [f]
theorem t' {α} (s : Finset α) : #{x ∈ s | True} ≤ s.card := by simp
@[elab_as_elim] theorem rec' {motive : Nat → Prop} (n : Nat) (h : motive n) : motive n := h
notation "‖" x "‖" => f x
infixl:65 " +' " => Nat.add
structure P where
  a : Nat
  deriving Repr, DecidableEq
noncomputable def nc := Classical.choice ⟨0⟩
