/- Fixture for scripts/source-rule.py (never compiled): forms a submission may use. Neither net
reports anything: no rejected word appears even in a comment. -/
import Mathlib.Data.Finset.Card
import RecursionFast.Contract
import LeanSearchClient
open Finset Nat in
/-- A docstring. -/
def arr : Array Nat := #[1, 2, 3]  -- a line comment
/- a block comment /- nested -/ still a comment -/
def vec : Vector Nat 2 := #v[1, 2]
def str := "a string with \" an escaped quote and { braces } that balance"
def ch : Char := '#'
def ch2 : Char := '\''
def ch3 : Char := '"'
def ch4 : Char := '{'
def raw := r#"a raw string with "quotes" and an unbalanced { inside"#
def raw2 := r"plain raw"
def interp := s!"value {arr.size} and {arr.size + 1}"
def interp2 := s!"a nested brace {({ val := 1 } : Fin 2)}"
def interp3 := s!"a comment {1 /- } -/} inside, read the same both ways"
def plain := "balanced { braces } read the same both ways"
def elabish := 0
def runner := 0
def run := 0
def eval := 0
def r : Nat := 0
def rr := r + r
def num := 0x1F + 1_000 + 3
theorem use_library_names : True := by
  have := RecursionFast.Library.run_mono   -- the Library's run_… lemmas are names, not commands
  trivial
@[simp, inline, specialize] def f (n : Nat) := n
attribute [simp] f
attribute [local simp] f
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
def xs := [0, 1].foldl (init := 0) (· + ·)
def g (n : Nat) : Nat := match n with
  | 0 => 1
  | k + 1 => g k
meta def m := 0
