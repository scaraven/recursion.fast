/-
# Controls: the machine (`Contract/Machine.lean`), positive and negative

The machine is v2's, unchanged in v3 except that `clmul` moved in from the deleted `Field.lean`
(V3-S1-A2). These controls are v2's machine controls (v2's `Controls/Extractor.lean`, in git history at the
tag `v2-archive`), copied verbatim except `spin_run_100`, whose
v2 tape is now a plain list. Images are assembled from `tests/asm/*.S`.

* Positive: `wzbc_run` (the W-op sign-extends a 32-bit sum; `clmulh` is the high word of the
  carry-less square, so `clmul` moved without change), `tape_below_ok` (a store below the tape),
  `halt_reads` (data words at address 0).
* Negative: `tape_readonly` (a store into the tape faults), `halt_misaligned` (`HALT` with
  `a0 = 4`), `ecall_trap` (`t0 ≠ 0` traps), `spin_run_100` and `spin_run` (an image that loops never
  halts, at any fuel).
-/
import RecursionFast.Library.Machine

namespace RecursionFast.Controls.Machine
open RecursionFast

/-! ## The machine: semantics kept from v0.3, and faults -/

/-- `tests/asm/wzbc.S`: `addw` and `clmulh` of `2^64 - 1` with itself, stored and output. -/
def wzbcImage : Image :=
  ⟨[0xfff00313, 0x00630e3b, 0x0a633eb3, 0x01c03023, 0x01d03423, 0x00200593, 0x00000293,
    0x00000073], []⟩

/-- The W-op sign-extends a 32-bit sum; `clmulh` is the high word of the carry-less square. -/
theorem wzbc_run : run wzbcImage [] 100 = some [0xfffffffffffffffe, 0x5555555555555555] := by
  decide +kernel

/-- A store into the tape faults (`tests/asm/tapestore.S`). -/
theorem tape_readonly :
    run ⟨[0x00100313, 0x03f31313, 0x00033023, 0x00000293, 0x00000073], []⟩ [1, 2] 100 = none := by
  decide +kernel

/-- The same program halts when the store goes below the tape (`slli t1, t1, 62`). -/
theorem tape_below_ok :
    run ⟨[0x00100313, 0x03e31313, 0x00033023, 0x00000293, 0x00000073], []⟩ [1, 2] 100 =
      some [] := by
  decide +kernel

/-- `HALT` with `a0 = 4` (not 8-aligned) faults (`tests/asm/misaligned.S`). -/
theorem halt_misaligned : run ⟨[0x00400513, 0x00000293, 0x00000073], []⟩ [] 100 = none := by
  decide +kernel

/-- `ECALL` with `t0 = 1` (v0.3's QUERY, removed) traps (`tests/asm/trap.S`). -/
theorem ecall_trap : run ⟨[0x00100293, 0x00000073], []⟩ [] 100 = none := by
  decide +kernel

/-- The image's data words are at address 0: output its two data words in place. -/
theorem halt_reads : run ⟨[0x00000293, 0x00200593, 0x00000073], [7, 8]⟩ [] 100 = some [7, 8] := by
  decide +kernel

/-! ## Fuel exhaustion -/

/-- `tests/asm/spin.S`: `j .` -/
def spinImg : Image := ⟨[0x0000006f], []⟩

theorem spin_run_100 : run spinImg [1, 2, 3] 100 = none := by
  decide +kernel

/-- The looping image never halts, at any fuel and on any tape. -/
theorem spin_run (t : List Word) (f : ℕ) : run spinImg t f = none := by
  suffices ∀ f s, s.pc = BitVec.ofNat 64 CODE_BASE → execute spinImg f s = none from
    this f _ rfl
  intro f s hs
  induction f generalizing s with
  | zero => rfl
  | succ f ih =>
    rw [execute_step (i := .base (.JAL .x0 0)) _ ((fetch_eq 0 (by decide) hs).trans rfl) rfl]
    exact ih _ (by simp [RiscvZkvm.Rv64.execInstrBr, hs, RiscvZkvm.Rv64.signExtend21])

end RecursionFast.Controls.Machine
