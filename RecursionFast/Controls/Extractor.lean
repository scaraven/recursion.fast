/-
# Controls: the extractor image (`Contract/Extractor.lean`), positive and negative  (DESIGN-v3 §4.4)

Images are assembled from `tests/asm/*.S` (`riscv64-unknown-elf-as -march=rv64im_zbc`), one word
per instruction. Fuel is a function of the input tape's length (V3-S1-A21).

Positive:
* `ws_computes`: the witness-sending image (`tests/asm/proofwords.S`, 8 instructions) computes the
  witness-sending extractor in 8 steps on every input (`Library/WitnessSending.lean`);
  `ws_run_8` and `ws_run_7`: on the empty proof it halts in exactly 8 steps (7 do not suffice).
* `halt_computes`: the one-instruction image `HALT` (`tests/asm/halt.S`) computes the extractor
  that returns no witness, in 1 step.
* Format known answers (for the runner's Python twins, S3; the expected words are those of the
  module header's format, computed by a 10-line Python reference, `struct.pack('<Q', …)`):
  `extractorInput_kat` (a 3-byte proof and a log of one 9-byte query: padding, length words,
  answer), `decodeWit_kat` (a node with a 3-byte and a 2-byte child proof).

Negative:
* `halt_not_ws`: the `HALT` image does not compute the witness-sending extractor (wrong output:
  on the proof of a leaf witness it outputs nothing).
* `ws_fuel_7`: the witness-sending image does not compute its extractor in 7 steps (fuel
  exhaustion).
* `noCode_computes_nothing`: an image without code computes no extractor at any fuel.
* `toolong_not_computes`: an image that halts with `2^24 + 1` words (`tests/asm/toolong.S`)
  computes no extractor (the output cap).
* `decodeWit_long_child` (V3-S1 review m5): a 10-word output declaring a `2^63`-byte child proof
  denotes nothing.
-/
import RecursionFast.Library.WitnessSending

namespace RecursionFast.Controls.Extractor
open RecursionFast RecursionFast.WitnessSending
open RiscvZkvm.Rv64 (MachineState Instr Reg execInstrBr signExtend12)

/-! ## The witness-sending image -/

theorem ws_computes : ImageComputes img E fuel := computes

/-- The input of the zero statement, the empty proof and the empty log. -/
def tape0 : List Word := extractorInput (Vector.replicate 32 0) ByteArray.empty []

theorem ws_run_8 : run img tape0 8 = some [] := by decide +kernel

theorem ws_run_7 : run img tape0 7 = none := by decide +kernel

/-- **Fuel exhaustion**: 7 steps are not enough. -/
theorem ws_fuel_7 : ¬ ImageComputes img E fun _ => 7 := by
  intro h
  obtain ⟨o, ho, -⟩ := h (Vector.replicate 32 0) .empty [] (by decide) (by decide)
  cases ws_run_7.symm.trans ho

/-! ## The `HALT` image -/

/-- `tests/asm/halt.S`: `HALT` (`t0 = a0 = a1 = 0` initially). -/
def haltImg : Image := ⟨[0x00000073], []⟩

theorem halt_run (t : List Word) (f : ℕ) : run haltImg t (f + 1) = some [] := by
  unfold run
  rw [execute_halt _ (by rw [fetch_eq 0 (by decide) rfl]; rfl) (by simp) (by simp)]
  simp [readOut, readWords_eq]

/-- **The `HALT` image computes the extractor that returns nothing.** -/
theorem halt_computes : ImageComputes haltImg (fun _ _ _ => none) fun _ => 1 :=
  fun _ _ _ _ _ => ⟨[], halt_run _ 0, by decide, rfl⟩

/-- **Wrong output**: the `HALT` image does not compute the witness-sending extractor. -/
theorem halt_not_ws : ¬ ImageComputes haltImg E fun _ => 1 := by
  intro h
  have hs := size_encode_leaf (Vector.replicate 32 0) 0
  obtain ⟨o, ho, -, hd⟩ := h (Vector.replicate 32 0) (encode (.leaf (Vector.replicate 32 0) 0)) []
    (by rw [hs]; decide) (by simp [extractorInput_eq, packBytes_length, hs])
  cases (halt_run _ 0).symm.trans ho
  exact nomatch hd.trans (decode_encode (.leaf _ 0) (by decide : (0 : ℕ) < 2 ^ 64))

/-! ## No code; too long an output -/

theorem noCode_run (t : List Word) (f : ℕ) : run ⟨[], []⟩ t f = none := by
  cases f <;> simp [run, execute, fetch]

/-- **No code, no extractor**, at any fuel. -/
theorem noCode_computes_nothing (E : Digest → Proof → Log → Option Wit) (f : ℕ → ℕ) :
    ¬ ImageComputes ⟨[], []⟩ E f := by
  intro h
  obtain ⟨o, ho, -⟩ := h (Vector.replicate 32 0) .empty [] (by decide) (by decide)
  cases (noCode_run _ _).symm.trans ho

/-- `tests/asm/toolong.S`: `a1 := 2^24 + 1; HALT`. -/
def toolongImg : Image := ⟨[0x010005b7, 0x00158593, 0x00000073], []⟩

/-- The decoded program of `toolongImg`. -/
private def toolongProg : List Instruction :=
  [.base (.LUI .x11 0x1000), .base (.ADDI .x11 .x11 1), .base .ECALL]

private theorem toolong_fetch (s : MachineState) (idx : ℕ) (hidx : idx < 3)
    (hpc : s.pc = BitVec.ofNat 64 (CODE_BASE + 4 * idx)) :
    fetch toolongImg s = toolongProg[idx]? := by
  rw [fetch_eq idx (by simp [CODE_BASE]; omega) hpc]
  interval_cases idx <;> rfl

theorem toolong_run (t : List Word) (f : ℕ) :
    ∃ o, run toolongImg t (f + 3) = some o ∧ o.length = 2 ^ 24 + 1 := by
  unfold run
  rw [execute_step _ (toolong_fetch _ 0 (by omega) rfl) rfl]
  simp [execInstrBr, CODE_BASE]
  rw [execute_step _ (toolong_fetch _ 1 (by omega) (by simp [CODE_BASE])) rfl]
  simp [execInstrBr, signExtend12]
  rw [execute_halt _ (toolong_fetch _ 2 (by omega) (by simp [CODE_BASE])) (by simp) (by simp)]
  exact ⟨_, rfl, (length_readWords _ _ _).trans (by simp)⟩

/-- **The output cap**: an image that halts with `2^24 + 1` words computes no extractor. -/
theorem toolong_not_computes (E : Digest → Proof → Log → Option Wit) :
    ¬ ImageComputes toolongImg E fun _ => 3 := by
  intro h
  obtain ⟨o, ho, hl, -⟩ := h (Vector.replicate 32 0) .empty [] (by decide) (by decide)
  obtain ⟨o', ho', hl'⟩ := toolong_run tape0 0
  cases ho.symm.trans ho'
  exact absurd (hl' ▸ hl) (by decide)

/-! ## Format known answers -/

deriving instance DecidableEq for Wit

/-- The input tape of the statement `01…01`, the proof `aa bb cc` and the log with one entry, the
query `01 02 … 09` and the answer `02…02`. -/
theorem extractorInput_kat :
    extractorInput (Vector.replicate 32 1) ⟨#[0xaa, 0xbb, 0xcc]⟩
        [(⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩, Vector.replicate 32 2)] =
      [0x0101010101010101, 0x0101010101010101, 0x0101010101010101, 0x0101010101010101,
       3, 0xccbbaa, 1, 9, 0x0807060504030201, 9,
       0x0202020202020202, 0x0202020202020202, 0x0202020202020202, 0x0202020202020202] := by
  decide +kernel

/-- The output words of the node with children `01…01`, `02…02` and proofs `aa bb cc`, `dd ee`
denote that node. -/
theorem decodeWit_kat :
    decodeWit [1, 0x0101010101010101, 0x0101010101010101, 0x0101010101010101,
        0x0101010101010101, 0x0202020202020202, 0x0202020202020202, 0x0202020202020202,
        0x0202020202020202, 3, 0xccbbaa, 2, 0xeedd] =
      some (.node (Vector.replicate 32 1) (Vector.replicate 32 2) ⟨#[0xaa, 0xbb, 0xcc]⟩
        ⟨#[0xdd, 0xee]⟩) := by
  decide +kernel

/-- **A long child denotes nothing**: ten words cannot denote a `2^63`-byte proof. -/
theorem decodeWit_long_child : decodeWit [1, 0, 0, 0, 0, 0, 0, 0, 0, 2 ^ 63] = none := by
  decide +kernel

end RecursionFast.Controls.Extractor
