/- Probe (V3-S2R-H-M1): a step-counting monad whose bind takes a Lean continuation charges
nothing for the work the continuation does. Core Lean only. -/
/-- A shallow step monad: read input word `i` (one charged step), continue with a Lean function. -/
inductive M (α : Type) where
  | ret (a : α)
  | read (i : Nat) (k : UInt64 → M α)

/-- Charged steps: one per `read`. -/
def M.steps {α : Type} (tape : Nat → UInt64) : M α → Nat
  | .ret _ => 0
  | .read i k => 1 + (k (tape i)).steps tape

/-- The value. -/
def M.val {α : Type} (tape : Nat → UInt64) : M α → α
  | .ret a => a
  | .read i k => (k (tape i)).val tape

/-- A search of `2^k` candidates, done by the continuation, uncharged. -/
def search (k : Nat) (t : UInt64) : Option Nat :=
  (List.range (2 ^ k)).find? fun x => (x.toUInt64 * 0x9E3779B97F4A7C15) >>> 44 == t >>> 44

def bruteForce (k : Nat) : M (Option Nat) := .read 0 fun t => .ret (search k t)

/-- One charged step, whatever `k` is. -/
theorem bruteForce_steps (k : Nat) (tape : Nat → UInt64) : (bruteForce k).steps tape = 1 := rfl
