/-
  RecursionFast.Library.Machine  (UNTRUSTED, kernel-checked)

  Symbolic execution of a concrete image on the contract machine (`Contract/Machine.lean`), one
  instruction at a time, on a symbolic tape: simp lemmas on registers and the initial state,
  `execute_step` (an ordinary instruction), `execute_halt` (a `HALT`), `fetch_eq` (the `idx`-th
  instruction), `ordinaryStep_ld`/`ordinaryStep_sd` (aligned doubleword accesses), `readWords_eq`
  (the output as a map over offsets), and fuel monotonicity (`execute_mono`, `run_mono`,
  `run_none_of_le`).

  Copied verbatim from v2's `Library/Extractor.lean`, section "Machine: symbolic execution"
  (git history, tag `v2-archive`), plus `length_readWords` from the same
  file; the machine is unchanged in v3, so the proofs are.
-/
import RecursionFast.Contract.Machine
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.GetD

namespace RecursionFast
open RiscvZkvm.Rv64 (MachineState Instr Reg execInstrBr signExtend12)


@[simp] theorem pc_setPC (s : MachineState) (v : Word) : (s.setPC v).pc = v := rfl
@[simp] theorem getReg_x0 (s : MachineState) : s.getReg .x0 = 0 := rfl
@[simp] theorem getReg_setReg (s : MachineState) (r r' : Reg) (v : Word) :
    (s.setReg r v).getReg r' = if r' = r ∧ r ≠ .x0 then v else s.getReg r' := by
  obtain rfl | h := eq_or_ne r' r
  · cases r' <;> rfl
  · rw [ite_eq_right fun h' => h h'.1, MachineState.getReg_setReg_ne s r r' v h.symm]
@[simp] theorem getReg_initState (img : Image) (t : List Word) (r : Reg) :
    (initState img t).getReg r = if r = .x2 then BitVec.ofNat 64 TAPE_BASE else 0 := by
  cases r <;> rfl
@[simp] theorem pc_initState (img : Image) (t : List Word) :
    (initState img t).pc = BitVec.ofNat 64 CODE_BASE := rfl
/-- The initial memory (not a simp lemma: on a symbolic address `simp` would expand `toNat`). -/
theorem getMem_initState (img : Image) (t : List Word) (a : Word) :
    (initState img t).getMem a = if TAPE_BASE ≤ a.toNat then t.getD ((a.toNat - TAPE_BASE) / 8) 0
      else img.data.getD (a.toNat / 8) 0 := rfl

/-- Tape word `i < 2^60` is at `TAPE_BASE + 8·i`. -/
theorem getMem_initState_tape (img : Image) (t : List Word) {i : ℕ} (hi : i < 2 ^ 60) :
    (initState img t).getMem (BitVec.ofNat 64 (TAPE_BASE + 8 * i)) = t.getD i 0 := by
  rw [getMem_initState, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold TAPE_BASE; omega),
    ite_eq_left (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    Nat.mul_div_cancel_left _ (by omega)]

/-- A step of an ordinary instruction. -/
theorem execute_step {img : Image} {s s' : MachineState} {i : Instruction} (f : ℕ)
    (hf : fetch img s = some i) (hs : ordinaryStep s i = some s') :
    execute img (f + 1) s = execute img f s' := by
  simp only [execute, hf]
  split
  · cases ‹some i = none›
  · cases ‹some i = some (.base .ECALL)›; simp [ordinaryStep] at hs
  · cases ‹some i = some _›; simp [hs]

/-- A `HALT`. -/
theorem execute_halt {img : Image} {s : MachineState} (f : ℕ)
    (hf : fetch img s = some (.base .ECALL)) (h5 : s.getReg .x5 = 0)
    (h10 : (s.getReg .x10).toNat % 8 = 0) : execute img (f + 1) s = some (readOut s) := by
  simp [execute, hf, h5, h10]

/-- More fuel does not change a halting run. -/
theorem execute_mono {img : Image} {s : MachineState} {f : ℕ} {o : List Word}
    (h : execute img f s = some o) (d : ℕ) : execute img (f + d) s = some o := by
  fun_induction execute img f s <;> simp_all [execute, Nat.add_right_comm _ 1 d]

/-- Less fuel does not make a failing run halt. -/
theorem run_none_of_le {img : Image} {t : List Word} {f f' : ℕ}
    (h : run img t f' = none) (hf : f ≤ f') : run img t f = none := by
  cases h' : run img t f with
  | none => rfl
  | some o =>
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hf
    rw [show run img t (f + d) = execute img (f + d) _ from rfl, execute_mono h' d] at h
    cases h

/-- More fuel does not change a halting run of `run`. -/
theorem run_mono {img : Image} {t : List Word} {f f' : ℕ} {o : List Word}
    (h : run img t f = some o) (hf : f ≤ f') : run img t f' = some o := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hf
  exact execute_mono h d

/-- Fetch at the `idx`-th instruction. -/
theorem fetch_eq {img : Image} {s : MachineState} (idx : ℕ) (hi : CODE_BASE + 4 * idx < 2 ^ 64)
    (hpc : s.pc = BitVec.ofNat 64 (CODE_BASE + 4 * idx)) :
    fetch img s = (img.code[idx]?).bind decodeInstruction := by
  have : s.pc.toNat = CODE_BASE + 4 * idx := by rw [hpc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]
  simp only [fetch, this]
  simp [CODE_BASE]

/-- An aligned doubleword load. -/
theorem ordinaryStep_ld {s : MachineState} {rd rs : Reg} {o : BitVec 12}
    (h : (s.getReg rs + signExtend12 o).toNat % 8 = 0) :
    ordinaryStep s (.base (.LD rd rs o)) =
      some ((s.setReg rd (s.getMem (s.getReg rs + signExtend12 o))).setPC (s.pc + 4)) := by
  simp only [ordinaryStep, memAccess, h]
  rfl

/-- An aligned doubleword store below the tape. -/
theorem ordinaryStep_sd {s : MachineState} {rs1 rs2 : Reg} {o : BitVec 12}
    (h : (s.getReg rs1 + signExtend12 o).toNat % 8 = 0)
    (ht : (s.getReg rs1 + signExtend12 o).toNat < TAPE_BASE) :
    ordinaryStep s (.base (.SD rs1 rs2 o)) =
      some ((s.setMem (s.getReg rs1 + signExtend12 o) (s.getReg rs2)).setPC (s.pc + 4)) := by
  simp only [ordinaryStep, memAccess, h, ht]
  rfl

/-- `readWords` as a map over the offsets. -/
theorem readWords_eq (s : MachineState) (base : Word) (n : ℕ) :
    s.readWords base n = (List.range n).map fun j => s.getMem (base + BitVec.ofNat 64 (8 * j)) := by
  induction n generalizing base <;> simp [*, List.range_succ_eq_map, Nat.mul_succ,
    BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_comm 8#64]

/-- `readWords` reads `n` words. -/
theorem length_readWords (s : MachineState) (base : Word) (n : ℕ) :
    (s.readWords base n).length = n := by
  simp [readWords_eq]

end RecursionFast
