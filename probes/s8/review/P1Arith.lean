/-
  S8 review probe P1: (a) the `Field K` of `FiniteField K` is the contract's arithmetic, by `rfl`
  and on a concrete product that reduces modulo x^64+x^4+x^3+x+1; (b) `readMult` over `K`:
  `(1 : K) * e` is read as a receive, because `(-1 : K) = 1` makes `const 1 * e` and
  `(-1) * e` the same term.
-/
import RecursionFast.Clean
open RecursionFast RecursionFast.Clean Air.Flat

namespace S8Review.P1

/-! (a) instances -/
def fmul {F : Type} [FiniteField F] (a b : F) : F := a * b
def fadd {F : Type} [FiniteField F] (a b : F) : F := a + b
def fneg {F : Type} [FiniteField F] (a : F) : F := -a
def fzero {F : Type} [FiniteField F] : F := 0
def fone {F : Type} [FiniteField F] : F := 1

example (a b : K) : fmul a b = a * b := rfl
example (a b : K) : fadd a b = a + b := rfl
example (a : K) : fneg a = -a := rfl
example : (fzero : K) = 0 := rfl
example : (fone : K) = 1 := rfl

/-- `x^63 · x = x^64 = x^4 + x^3 + x + 1 = 0b11011 = 27`, with the contract's `*`. -/
def a63 : K := ⟨1 <<< 63⟩
def aX : K := ⟨2⟩
example : a63 * aX = ⟨27⟩ := by decide
/-- The same product through Clean's `Expression.eval` (Clean's `Field K` operations). -/
example : Expression.eval (F := K) ⟨fun i => if i = 0 then a63 else aX, fun _ _ => #[]⟩
    (.mul (.var ⟨0⟩) (.var ⟨1⟩)) = ⟨27⟩ := by decide
/-- And through `fmul` (generic `FiniteField` multiplication). -/
example : fmul a63 aX = ⟨27⟩ := by decide

/-! (b) direction from the syntax, over `K` -/

/-- `(1 : K) * e` (Clean's `HMul F (Expression F)`) is `mul (const 1) e`. -/
example (e : Expression K) : ((1 : K) * e : Expression K) = .mul (.const 1) e := rfl

/-- ... and `readMult` reads it as a **receive** with selector `e`: `1 = -1` in `K`. -/
example : readMult ((1 : K) * (Expression.var ⟨0⟩ : Expression K) : Expression K) = (false, .var ⟨0⟩) := by decide

/-- So Clean's `pushedIf ((1 : K) * en)` (a push in Clean's syntax) is read as a pull. -/
def Ch : Channel K field := { name := "c", Guarantees := fun _ _ => True }
example : readMult (pushedIf (channel := Ch) ((1 : K) * (Expression.var ⟨0⟩ : Expression K)) (Expression.var ⟨1⟩ : Expression K)).toRaw.mult
    = (false, .var ⟨0⟩) := by decide
/-- Whereas `pushedIf en` and `pushedIf (en * 1)` are read as sends. -/
example : readMult (pushedIf (channel := Ch) ((Expression.var ⟨0⟩ : Expression K) * (1 : K)) (Expression.var ⟨1⟩ : Expression K)).toRaw.mult
    = (true, .mul (.var ⟨0⟩) (.const 1)) := by decide

/-- Over a prime field the same expression is a send (`1 ≠ -1`): the reading is field-dependent. -/
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
example : (readMult ((1 : F 7) * (Expression.var ⟨0⟩ : Expression (F 7)) : Expression (F 7))).1 = true := by decide

/-- A multiplicity written as the constant `-1` (not through `Neg`): over `K` it is the constant
`1`, i.e. literally `pushed`'s multiplicity, a send; over `F 7` it is a send whose selector
evaluates to `-1 ≠ 1`, i.e. silent, where Clean counts a receive. -/
example : readMult (Expression.const (-1) : Expression K) = (true, .const 1) := by decide
example : readMult (Expression.const (-1) : Expression (F 7)) = (true, .const (-1)) := by decide
example : (Expression.const (-1) : Expression (F 7)).eval ⟨fun _ => 0, fun _ _ => #[]⟩ ≠ 1 := by decide

#synth DecidableEq K

end S8Review.P1
