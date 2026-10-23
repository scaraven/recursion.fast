/-
  RecursionFast.Library.Machine  (UNTRUSTED, kernel-checked; unchanged from v3)

  Reasoning about programs of the contract's step-counting machine (`Contract/Machine.lean`).

  * `XStmt.Runs I s M o n M' o'`: the statement `s` runs from memory `M` and output `o` in exactly
    `n` steps to `M'` and `o'`, whatever follows it on the stack. One lemma per statement
    (`runs_op` … `runs_loop_step`) composes runs, so a program's step count is the sum of its
    parts. `XProg.run_of_runs` turns a run of the body into a result of `XProg.run`.
  * `exec_mono`: more fuel does not change a halting run. `exec_none_of_le`: less fuel does not
    make a failing run halt.
  * `XStmt.seqs`: a list of statements run in order (`runs_seqs`).
-/
import RecursionFast.Contract.Machine
import Mathlib.Tactic.Ring

namespace RecursionFast.XStmt
open RecursionFast

variable (I : Array Word)

/-- `s` runs from `(M, o)` in exactly `n` steps to `(M', o')`, whatever statements follow it. -/
def Runs (s : XStmt) (M o : Array Word) (n : ℕ) (M' o' : Array Word) : Prop :=
  ∀ m ks, exec I (n + m) M o (s :: ks) = exec I m M' o' ks

variable {I}

@[simp] theorem exec_nil (n : ℕ) (M o : Array Word) : exec I n M o [] = some o.toList := by
  cases n <;> rfl

@[simp] theorem exec_zero_cons (M o : Array Word) (s : XStmt) (ks : List XStmt) :
    exec I 0 M o (s :: ks) = none := rfl

/-- More fuel does not change a halting run. -/
theorem exec_mono {n : ℕ} {M o : Array Word} {ks : List XStmt} {r : List Word}
    (h : exec I n M o ks = some r) (d : ℕ) : exec I (n + d) M o ks = some r := by
  induction n generalizing M o ks with
  | zero => cases ks with
    | nil => simpa using h
    | cons => cases h
  | succ n ih =>
    cases ks with
    | nil => simpa using h
    | cons s ks =>
      rw [Nat.add_right_comm]
      cases s <;> simp only [exec] at h ⊢ <;> exact ih h

/-- Less fuel does not make a failing run halt. -/
theorem exec_none_of_le {n n' : ℕ} {M o : Array Word} {ks : List XStmt}
    (h : exec I n' M o ks = none) (hn : n ≤ n') : exec I n M o ks = none := by
  cases h' : exec I n M o ks with
  | none => rfl
  | some r =>
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact nomatch (exec_mono h' d).symm.trans h

theorem runs_op (f : XOp) (d a b : ℕ) (M o : Array Word) :
    Runs I (.op f d a b) M o 1 (M.setIfInBounds d (f.eval (M.getD a 0) (M.getD b 0))) o :=
  fun m _ => Nat.add_comm m 1 ▸ rfl

theorem runs_const (d : ℕ) (w : Word) (M o : Array Word) :
    Runs I (.const d w) M o 1 (M.setIfInBounds d w) o :=
  fun m _ => Nat.add_comm m 1 ▸ rfl

theorem runs_load (d a : ℕ) (M o : Array Word) :
    Runs I (.load d a) M o 1 (M.setIfInBounds d (M.getD (M.getD a 0).toNat 0)) o :=
  fun m _ => Nat.add_comm m 1 ▸ rfl

theorem runs_store (a v : ℕ) (M o : Array Word) :
    Runs I (.store a v) M o 1 (M.setIfInBounds (M.getD a 0).toNat (M.getD v 0)) o :=
  fun m _ => Nat.add_comm m 1 ▸ rfl

theorem runs_input (d a : ℕ) (M o : Array Word) :
    Runs I (.input d a) M o 1 (M.setIfInBounds d (I.getD (M.getD a 0).toNat 0)) o :=
  fun m _ => Nat.add_comm m 1 ▸ rfl

theorem runs_out (v : ℕ) (M o : Array Word) : Runs I (.out v) M o 1 M (o.push (M.getD v 0)) :=
  fun m _ => Nat.add_comm m 1 ▸ rfl

theorem runs_seq {p q : XStmt} {M o M₁ o₁ M₂ o₂ : Array Word} {n₁ n₂ : ℕ}
    (hp : Runs I p M o n₁ M₁ o₁) (hq : Runs I q M₁ o₁ n₂ M₂ o₂) :
    Runs I (.seq p q) M o (n₁ + n₂ + 1) M₂ o₂ := fun m ks => by
  rw [show n₁ + n₂ + 1 + m = (n₁ + (n₂ + m)) + 1 by omega]
  simp only [exec]
  rw [hp, hq]

theorem runs_ite_true {c : ℕ} {p q : XStmt} {M o M' o' : Array Word} {n : ℕ}
    (hc : M.getD c 0 ≠ 0) (hp : Runs I p M o n M' o') : Runs I (.ite c p q) M o (n + 1) M' o' :=
  fun m ks => by
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [exec, hc, ↓reduceIte]
    exact hp m ks

theorem runs_ite_false {c : ℕ} {p q : XStmt} {M o M' o' : Array Word} {n : ℕ}
    (hc : M.getD c 0 = 0) (hq : Runs I q M o n M' o') : Runs I (.ite c p q) M o (n + 1) M' o' :=
  fun m ks => by
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [exec, hc, ↓reduceIte]
    exact hq m ks

theorem runs_loop_zero {c : ℕ} {p : XStmt} {M o : Array Word} (hc : M.getD c 0 = 0) :
    Runs I (.loop c p) M o 1 M o := fun m ks => by
  rw [Nat.add_comm]; simp only [exec, hc, ↓reduceIte]

theorem runs_loop_step {c : ℕ} {p : XStmt} {M o M₁ o₁ M₂ o₂ : Array Word} {n n' : ℕ}
    (hc : M.getD c 0 ≠ 0) (hp : Runs I p M o n M₁ o₁) (hl : Runs I (.loop c p) M₁ o₁ n' M₂ o₂) :
    Runs I (.loop c p) M o (n + n' + 1) M₂ o₂ := fun m ks => by
  rw [show n + n' + 1 + m = (n + (n' + m)) + 1 by omega]
  simp only [exec, hc, ↓reduceIte]
  rw [hp, hl]

theorem exec_seq {p q : XStmt} {M o : Array Word} {n : ℕ} {ks : List XStmt} :
    exec I (n + 1) M o (.seq p q :: ks) = exec I n M o (p :: q :: ks) := rfl

theorem exec_out {v : ℕ} {M o : Array Word} {n : ℕ} {ks : List XStmt} :
    exec I (n + 1) M o (.out v :: ks) = exec I n M (o.push (M.getD v 0)) ks := rfl

theorem exec_loop_ne {c : ℕ} {p : XStmt} {M o : Array Word} {n : ℕ} {ks : List XStmt}
    (hc : M.getD c 0 ≠ 0) :
    exec I (n + 1) M o (.loop c p :: ks) = exec I n M o (p :: .loop c p :: ks) := by
  simp only [exec, hc, ↓reduceIte]

theorem exec_loop_eq {c : ℕ} {p : XStmt} {M o : Array Word} {n : ℕ} {ks : List XStmt}
    (hc : M.getD c 0 = 0) : exec I (n + 1) M o (.loop c p :: ks) = exec I n M o ks := by
  simp only [exec, hc, ↓reduceIte]

theorem runs_mono_eq {s : XStmt} {M o M' o' : Array Word} {n n' : ℕ}
    (h : Runs I s M o n M' o') (hn : n = n') : Runs I s M o n' M' o' := hn ▸ h

/-- Statements run in order: `seqs s [t₁, …, tₖ] = seq s (seq t₁ (… tₖ))`. -/
def seqs : XStmt → List XStmt → XStmt
  | s, [] => s
  | s, t :: ts => .seq s (seqs t ts)

end RecursionFast.XStmt

namespace RecursionFast.XProg
open RecursionFast XStmt

/-- **A run of the body is a result of the program**, with any fuel that covers the memory and
the steps. -/
theorem run_of_runs {p : XProg} {input : List Word} {n f : ℕ} {M' o' : Array Word}
    (h : Runs input.toArray p.body (Array.replicate (p.memFor input.length) 0) #[] n M' o')
    (hf : p.memFor input.length + n ≤ f) : p.run input f = some o'.toList := by
  simp only [run, show p.memFor input.length ≤ f by omega, ↓reduceIte]
  rw [show f - p.memFor input.length = n + (f - p.memFor input.length - n) by omega, h]
  simp

/-- With less fuel than the memory, the program does not run. -/
theorem run_lt_mem {p : XProg} {input : List Word} {f : ℕ} (h : f < p.memFor input.length) :
    p.run input f = none := by
  simp only [run, show ¬ p.memFor input.length ≤ f by omega, ↓reduceIte]

/-- The program's run, once its memory is charged. -/
theorem run_eq {p : XProg} {input : List Word} {f : ℕ} (h : p.memFor input.length ≤ f) :
    p.run input f = XStmt.exec input.toArray (f - p.memFor input.length)
      (Array.replicate (p.memFor input.length) 0) #[] [p.body] := by
  simp only [run, h, ↓reduceIte]

end RecursionFast.XProg

namespace RecursionFast

/-- The tape as the interpreter reads it: an array read is the list read. -/
theorem getD_toArray (l : List Word) (k : ℕ) : l.toArray.getD k 0 = l.getD k 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

end RecursionFast
