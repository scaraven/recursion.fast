/-
# Controls: the extractor's machine (`Contract/Machine.lean`), positive and negative

The step-counting word language of V3-S2R-A1 (it replaced v2's RISC-V machine and its controls,
which are at `05fde28`).

Positive:
* `eval_kat`: known answers of the word operations, including the edge cases the docstring names
  (wrap-around, `x / 0 = 0`, `x % 0 = x`, shifts by the low 6 bits, the high words of the integer
  and carry-less products: `clmulh` of `2^64 - 1` with itself is `0x5555…`, as v2's Zbc control).
* `straight_run`: a straight-line program's output, with exactly `mem + statements` fuel
  (`straight_exact`).
* `bounds_run`: a read outside memory is `0`, a write outside it is lost, and an input read past
  the tape's end is `0`.
* `indirect_run`: `store` and `load` address memory through a cell.
* `count_run`: the program that counts a cell down from `k` halts in exactly `2k + 7` steps, for
  every `k < 2^64`.
* `poke_affine`: memory is affine in the tape (V3-S2R-A8): with `memPerWord = 4`, a cell named by
  an input word exists on an 8-word tape and keeps what is written to it.

Negative:
* `straight_short`: with one step less, the straight-line program does not halt.
* `count_short`: **a program that loops `k` times needs more than `2k + 6` steps**, for every
  `k < 2^64`; nothing in the language runs an iteration for free.
* `mem_charged`: a program with `m + r · t` memory words on a tape of `t` words does not run with
  that much fuel, for every `m`, `r` and tape: the zero-initialised memory is charged
  (`mem_charged_run`: one step more suffices for one statement).
* `poke_const`: with constant memory, a cell named by an input word beyond it is lost (the
  separating twin of `poke_affine`).
* `spin_run`: a program whose loop condition never clears halts at no fuel.
-/
import RecursionFast.Library.Machine
import RecursionFast.Library.Words

namespace RecursionFast.Controls.Machine
open RecursionFast XStmt

/-! ## Operations -/

theorem eval_kat :
    XOp.add.eval (-1) 2 = 1 ∧ XOp.sub.eval 0 1 = -1 ∧ XOp.mul.eval (2 ^ 63) 2 = 0 ∧
    XOp.mulhu.eval (2 ^ 63) 4 = 2 ∧ XOp.divu.eval 7 0 = 0 ∧ XOp.remu.eval 7 0 = 7 ∧
    XOp.divu.eval 7 2 = 3 ∧ XOp.remu.eval 7 2 = 1 ∧ XOp.and.eval 6 3 = 2 ∧ XOp.or.eval 6 3 = 7 ∧
    XOp.xor.eval 6 3 = 5 ∧ XOp.shl.eval 1 65 = 2 ∧ XOp.shr.eval (2 ^ 63) 63 = 1 ∧
    XOp.ltu.eval 1 (-1) = 1 ∧ XOp.ltu.eval (-1) 1 = 0 ∧ XOp.eq.eval 5 5 = 1 ∧
    XOp.eq.eval 5 6 = 0 ∧ XOp.clmul.eval 3 3 = 5 ∧
    XOp.clmulh.eval (-1) (-1) = 0x5555555555555555 := by
  decide +kernel

/-! ## Straight-line programs, bounds, indirection -/

/-- `M[0] := 2^64 - 1`, output `M[0] + M[0]` and `clmulh(M[0], M[0])`. -/
def straight : XProg := ⟨3, 0, seqs (.const 0 (-1))
  [.op .add 1 0 0, .out 1, .op .clmulh 2 0 0, .out 2]⟩

theorem straight_run : straight.run [] 100 = some [0xfffffffffffffffe, 0x5555555555555555] := by
  decide +kernel

/-- 3 memory words, 5 statements and 4 `seq` nodes: 12 steps. -/
theorem straight_exact : straight.run [] 12 = some [0xfffffffffffffffe, 0x5555555555555555] := by
  decide +kernel

theorem straight_short : straight.run [] 11 = none := by decide +kernel

/-- One memory word: write `7` to cell 5 (lost), output cell 5 (`0`), read input word 9 of a
two-word tape (`0`) and output it. -/
def bounds : XProg := ⟨1, 0, seqs (.const 5 7) [.out 5, .const 0 9, .input 0 0, .out 0]⟩

theorem bounds_run : bounds.run [1, 2] 100 = some [0, 0] := by decide +kernel

/-- `M[0] := 3; M[1] := 42; M[M[0]] := M[1]; M[2] := M[M[0]]`; output `M[2]` and `M[3]`. -/
def indirect : XProg := ⟨4, 0, seqs (.const 0 3)
  [.const 1 42, .store 0 1, .load 2 0, .out 2, .out 3]⟩

theorem indirect_run : indirect.run [] 100 = some [42, 42] := by decide +kernel

/-! ## Counting down: a loop of `k` iterations costs `2k + 7` steps -/

/-- The loop body: `M[0] := M[0] - M[1]`. -/
def dec : XStmt := .op .sub 0 0 1

/-- Count `M[0]` down from `k` to `0` with `M[1] = 1`. -/
def count (k : ℕ) : XProg := ⟨2, 0, .seq (.const 0 (toWord k)) (.seq (.const 1 1) (.loop 0 dec))⟩

theorem exec_dec {I M o : Array Word} {n : ℕ} {ks : List XStmt} :
    exec I (n + 1) M o (dec :: ks) = exec I n (M.setIfInBounds 0 (M.getD 0 0 - M.getD 1 0)) o ks :=
  rfl

theorem dec_mem {j : ℕ} : (#[toWord (j + 1), 1] : Array Word).setIfInBounds 0
    ((#[toWord (j + 1), 1] : Array Word).getD 0 0 - (#[toWord (j + 1), 1] : Array Word).getD 1 0) =
      #[toWord j, 1] := by
  simp [← toWord_add_one, BitVec.add_sub_cancel]

theorem count_loop (I : Array Word) (o : Array Word) (f : ℕ) :
    ∀ j, j < 2 ^ 64 → exec I (f + 2 * j + 1) #[toWord j, 1] o [.loop 0 dec] = some o.toList := by
  intro j
  induction j with
  | zero => intro _; rw [exec_loop_eq (by decide)]; simp
  | succ j ih =>
    intro hj
    have hne : (#[toWord (j + 1), 1] : Array Word).getD 0 0 ≠ 0 := by
      simpa using (toWord_eq_zero hj).not.mpr (by omega)
    rw [show f + 2 * (j + 1) + 1 = (f + 2 * j + 1 + 1) + 1 by ring, exec_loop_ne hne, exec_dec,
      dec_mem]
    exact ih (by omega)

theorem count_loop_none (I : Array Word) (o : Array Word) :
    ∀ j, j < 2 ^ 64 → exec I (2 * j) #[toWord j, 1] o [.loop 0 dec] = none := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hne : (#[toWord (j + 1), 1] : Array Word).getD 0 0 ≠ 0 := by
      simpa using (toWord_eq_zero hj).not.mpr (by omega)
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, exec_loop_ne hne, exec_dec, dec_mem]
    exact ih (by omega)

theorem count_mem (k : ℕ) (I : Array Word) (n : ℕ) :
    exec I (n + 4) (Array.replicate 2 0) #[] [(count k).body] =
      exec I n #[toWord k, 1] #[] [.loop 0 dec] := by
  rw [show Array.replicate 2 (0 : Word) = #[0, 0] from rfl]
  simp [count, exec]

/-- **Counting down from `k` takes exactly `2k + 7` steps.** -/
theorem count_run (k : ℕ) (hk : k < 2 ^ 64) (t : List Word) :
    (count k).run t (2 * k + 7) = some [] := by
  unfold XProg.run
  simp only [count, XProg.memFor, Nat.zero_mul, Nat.add_zero, show 2 ≤ 2 * k + 7 by omega,
    ↓reduceIte]
  rw [show 2 * k + 7 - 2 = (0 + 2 * k + 1) + 4 by omega]
  exact (count_mem k _ _).trans (count_loop _ _ 0 k hk)

/-- **Not with fewer**: a loop of `k` iterations needs more than `2k + 6` steps. -/
theorem count_short (k : ℕ) (hk : k < 2 ^ 64) (t : List Word) {f : ℕ} (hf : f ≤ 2 * k + 6) :
    (count k).run t f = none := by
  unfold XProg.run
  split
  · apply exec_none_of_le (n' := 2 * k + 4) _ (by simp only [count, XProg.memFor] at *; omega)
    simp only [count, XProg.memFor, Nat.zero_mul, Nat.add_zero]
    exact (count_mem k _ _).trans (count_loop_none _ _ k hk)
  · rfl

/-! ## The memory charge; a loop that never ends -/

/-- **Memory is charged**: `m + r · t` memory words and one statement do not run in `m + r · t`
steps on a tape of `t` words. -/
theorem mem_charged (m r : ℕ) (t : List Word) :
    (⟨m, r, .const 0 0⟩ : XProg).run t (m + r * t.length) = none := by
  simp [XProg.run, XProg.memFor]

/-- With one step more they do. -/
theorem mem_charged_run (m r : ℕ) (t : List Word) :
    (⟨m, r, .const 0 0⟩ : XProg).run t (m + r * t.length + 1) = some [] := by
  simp [XProg.run, XProg.memFor, exec]

/-- Write `1` to the cell named by input word 4 (a proof's byte length on an extractor tape), then
output that cell. -/
def poke (r : ℕ) : XProg := ⟨2, r, seqs (.const 0 4) [.input 1 0, .const 0 1, .store 1 0, .load 0 1,
  .out 0]⟩

/-- An 8-word tape whose word 4 is `16`. -/
def tape8 : List Word := [0, 0, 0, 0, 16, 0, 0, 0]

/-- **Memory grows with the tape**: with `4` words per input word, cell `16` exists on an 8-word
tape (`2 + 4 · 8` words) and keeps the `1`. -/
theorem poke_affine : (poke 4).run tape8 100 = some [1] := by decide +kernel

/-- **Not with constant memory**: with `2` words the write is lost and the read gives `0`. -/
theorem poke_const : (poke 0).run tape8 100 = some [0] := by decide +kernel

/-- `M[0] := 1`, then loop while `M[0] ≠ 0` writing cell 1. -/
def spin : XProg := ⟨1, 0, .seq (.const 0 1) (.loop 0 (.const 1 0))⟩

theorem spin_loop (I : Array Word) (o : Array Word) :
    ∀ n, exec I n #[1] o [.loop 0 (.const 1 0)] = none := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 =>
      rw [exec_loop_ne (by decide)]
      simpa [exec] using ih n (by omega)

/-- **A loop that never ends halts at no fuel**, on every tape. -/
theorem spin_run (t : List Word) (f : ℕ) : spin.run t f = none := by
  unfold XProg.run
  split
  · rename_i h
    simp only [spin, XProg.memFor, Nat.zero_mul, Nat.add_zero] at h ⊢
    obtain ⟨n, hn⟩ : ∃ n, f - 1 = n := ⟨_, rfl⟩
    rw [hn]
    match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 =>
      rw [show Array.replicate 1 (0 : Word) = #[0] from rfl]
      simpa [exec] using spin_loop _ _ n
  · rfl

end RecursionFast.Controls.Machine
