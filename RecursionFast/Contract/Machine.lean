/-
# Contract: the machine of the extractor                                         (TRUSTED)

Trimmed from v0.3 (`contract-v03/RecursionFast/Contract/Machine.lean`, 473 lines; DESIGN §8,
§10). The one contract machine: **RV64IM + all W-ops + Zbc** (`clmul`, `clmulh`, `clmulr`),
decoded by the contract from raw 32-bit words; Harvard code space at `CODE_BASE`; naturally
aligned accesses; every fault stops the run. In v2 it runs only the bounded extractor
(`Extractor.lean`, DESIGN §4 item 3, decision Q1); the verifier is executed as compiled Lean.

* **Kept from v0.3 verbatim:** `Image` (without `harts`), `unpack`, `Image.byteSize`, the
  decoder (`WordOp`, `ClOp`, `Instruction`, `decodeInstruction`), the W-op and Zbc semantics
  (`wordResult`, `clResult`), `memAccess`, `ordinaryStep` (up to the memory check), `fetch`,
  `initState` (up to the memory map). Base instruction semantics (`Instr`, `MachineState`,
  `execInstrBr`) and the base decoder (`decode`) are riscv-zkvm's hand model at `6810fc1`,
  vendored byte-identically (`Vendor/RiscvZkvm`, `scripts/check-vendor.sh`).
* **Changed:** the memory map spans all `2^64` addresses, so v0.3's `inMemory`/`writable` become
  one check (a store lands below the tape); `HALT` returns output words instead of a decision;
  the fuel is an argument of `run`; `readOut` reads the region named by `a0`, `a1`.
* **Removed:** the 18 counters (`CostVec`, `Kind`, `tick`, `kind`, `latency`), first-touch
  accounting (`Acct`, `key`, `touch`), the pipeline timer (`Timer.lean`, `tock`, `opOf`,
  `ecallOp`, `rawAt`), harts (`SPAWN`/`JOIN`, `Region`, `Child`, `Ctx`, `allows`, `access`), the
  QUERY system call (the extractor has no oracles: its inputs are on the tape), `Final`,
  `runFull`, `OUT_BASE`, `FUEL`, `TAPE_CAP`, `MEM_BYTES`, and `deriving DecidableEq` on the
  decoded instructions.

**Memory map.** Image data words from address 0 (then zeros); the read-only **input tape**
from `TAPE_BASE = 2^63`: word `i` of the input at address `TAPE_BASE + 8·i` for `i < 2^60`
(zeros beyond the input; later words are not addressable). As in v0.3 a tape word is one
doubleword (little-endian in memory): a `K` element is its `bits`, an `E` element three limbs
`c0, c1, c2`, an index challenge is zero-extended, a number is its low 64 bits. Stores at or
above `TAPE_BASE` fault. Initially `sp = TAPE_BASE`, all other registers are `0` and
`pc = CODE_BASE`.

**System call** (`ECALL`, selected by `t0` = `x5`): `t0 = 0` is **HALT**; the output is the
`a1` doublewords at address `a0`, which must be 8-aligned (else the run faults). Every other
`t0` traps.
-/
import RiscvZkvm.Rv64.Execution
import RiscvZkvm.Interpreter.Decode
import RecursionFast.Contract.Field

namespace RecursionFast
open RiscvZkvm.Rv64 (MachineState Instr Reg execInstrBr signExtend12)
open RiscvZkvm.Interpreter (decode regOfBits)

/-! ### Memory map and image -/

/-- Address of the first instruction (separate code space: loads and stores never reach it). -/
def CODE_BASE : Nat := 0x1000
/-- Start of the read-only input tape; data memory is `[0, TAPE_BASE)`. -/
def TAPE_BASE : Nat := 2 ^ 63

/-- A program: raw instruction words (at `CODE_BASE`) and data words (at address 0). -/
structure Image where
  code : List (BitVec 32)
  data : List Word

/-- `k` little-endian `w`-bit words packed into the natural `x` (how the challenge renderer
encodes the submitted image files). -/
def unpack (w : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, x => x % 2 ^ w :: unpack w k (x / 2 ^ w)

/-- Size in bytes (contract cap `imageCap`, `Extractor.lean`). -/
def Image.byteSize (img : Image) : Nat := 4 * img.code.length + 8 * img.data.length

/-! ### Decoding (v0.3 verbatim) -/

/-- W-suffixed operations (upstream decodes only `ADDIW`). -/
inductive WordOp where
  | add | sub | sll | srl | sra | mul | div | divu | rem | remu

/-- Zbc carry-less multiplications. -/
inductive ClOp where
  | clmul | clmulh | clmulr

/-- A decoded instruction: upstream's, a W-op (register or immediate shift), or Zbc. -/
inductive Instruction where
  | base (i : Instr)
  | word (op : WordOp) (rd rs1 rs2 : Reg)
  | wordShift (op : WordOp) (rd rs1 : Reg) (shamt : BitVec 5)
  | cl (op : ClOp) (rd rs1 rs2 : Reg)

/-- Decode a raw word: `ECALL` exactly (no `EBREAK`, no CSR), Zbc (`OP`, `funct7 = 5`,
`funct3 = 1/3/2`), the W-ops (`OP-32`, and `OP-IMM-32` shifts), then upstream `decode`. -/
def decodeInstruction (w : BitVec 32) : Option Instruction :=
  let opcode := (w.extractLsb' 0 7).toNat
  let rd := regOfBits (w.extractLsb' 7 5)
  let rs1 := regOfBits (w.extractLsb' 15 5)
  let rs2 := regOfBits (w.extractLsb' 20 5)
  let f3 := (w.extractLsb' 12 3).toNat
  let f7 := (w.extractLsb' 25 7).toNat
  if opcode = 0x73 then (if w = 0x00000073 then some (.base .ECALL) else none)
  else if opcode = 0x33 ∧ f7 = 5 then
    (match f3 with | 1 => some ClOp.clmul | 3 => some .clmulh | 2 => some .clmulr | _ => none).map
      fun op => .cl op rd rs1 rs2
  else if opcode = 0x3b then
    (match f7, f3 with
      | 0, 0 => some WordOp.add | 0x20, 0 => some .sub | 0, 1 => some .sll | 0, 5 => some .srl
      | 0x20, 5 => some .sra | 1, 0 => some .mul | 1, 4 => some .div | 1, 5 => some .divu
      | 1, 6 => some .rem | 1, 7 => some .remu | _, _ => none).map fun op => .word op rd rs1 rs2
  else if opcode = 0x1b ∧ f3 ≠ 0 then
    (match f7, f3 with
      | 0, 1 => some WordOp.sll | 0, 5 => some .srl | 0x20, 5 => some .sra | _, _ => none).map
      fun op => .wordShift op rd rs1 (w.extractLsb' 20 5)
  else (decode w).map .base

/-- 32-bit result of a W-op (RISC-V: shifts use 5 bits; `x/0 = -1`, `x % 0 = x`). -/
def wordResult (op : WordOp) (a b : BitVec 32) : BitVec 32 :=
  match op with
  | .add => a + b | .sub => a - b
  | .sll => a <<< (b.toNat % 32) | .srl => a >>> (b.toNat % 32) | .sra => a.sshiftRight (b.toNat % 32)
  | .mul => a * b
  | .div => if b = 0 then BitVec.allOnes 32 else a.sdiv b
  | .divu => if b = 0 then BitVec.allOnes 32 else a / b
  | .rem => if b = 0 then a else a.srem b
  | .remu => if b = 0 then a else a % b

/-- Zbc: low, high, and reversed (bits 126..63) halves of the 128-bit carry-less product. -/
def clResult (op : ClOp) (a b : Word) : Word :=
  match op with
  | .clmul => (K.clmul a b).setWidth 64
  | .clmulh => (K.clmul a b >>> 64).setWidth 64
  | .clmulr => (K.clmul a b >>> 63).setWidth 64

/-! ### One step -/

/-- Address, width and direction (`true` = store) of each load and store. -/
def memAccess (s : MachineState) : Instr → Option (Word × Nat × Bool)
  | .LD _ r o => some (s.getReg r + signExtend12 o, 8, false)
  | .LW _ r o | .LWU _ r o => some (s.getReg r + signExtend12 o, 4, false)
  | .LH _ r o | .LHU _ r o => some (s.getReg r + signExtend12 o, 2, false)
  | .LB _ r o | .LBU _ r o => some (s.getReg r + signExtend12 o, 1, false)
  | .SD r _ o => some (s.getReg r + signExtend12 o, 8, true)
  | .SW r _ o => some (s.getReg r + signExtend12 o, 4, true)
  | .SH r _ o => some (s.getReg r + signExtend12 o, 2, true)
  | .SB r _ o => some (s.getReg r + signExtend12 o, 1, true)
  | _ => none

/-- One non-`ECALL` instruction; `none` is a fault (misaligned access, store into the tape,
`EBREAK`/CSR/pseudo-instructions, which the decoder never produces anyway). -/
def ordinaryStep (s : MachineState) : Instruction → Option MachineState
  | .base .ECALL | .base .EBREAK | .base (.CSRS _ _) | .base (.LI _ _) | .base (.MV _ _)
  | .base .NOP => none
  | .base i =>
    match memAccess s i with
    | some (a, width, store) =>
      if a.toNat % width = 0 && (!store || a.toNat < TAPE_BASE) then some (execInstrBr s i)
      else none
    | none => some (execInstrBr s i)
  | .word op rd rs1 rs2 =>
    let v := wordResult op ((s.getReg rs1).truncate 32) ((s.getReg rs2).truncate 32)
    some ((s.setReg rd (v.signExtend 64)).setPC (s.pc + 4))
  | .wordShift op rd rs1 sh =>
    let v := wordResult op ((s.getReg rs1).truncate 32) (sh.zeroExtend 32)
    some ((s.setReg rd (v.signExtend 64)).setPC (s.pc + 4))
  | .cl op rd rs1 rs2 => some ((s.setReg rd (clResult op (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4))

/-- Fetch at `pc` (4-aligned, at or above `CODE_BASE`) and decode. -/
def fetch (img : Image) (s : MachineState) : Option Instruction :=
  if CODE_BASE ≤ s.pc.toNat ∧ s.pc.toNat % 4 = 0 then
    (img.code[(s.pc.toNat - CODE_BASE) / 4]?).bind decodeInstruction
  else none

/-! ### Execution -/

/-- The output at `HALT`: the `a1` doublewords from address `a0` upwards. -/
def readOut (s : MachineState) : List Word := s.readWords (s.getReg .x10) (s.getReg .x11).toNat

/-- Run for at most `fuel` steps (an `ECALL` is one step). `some out` iff a `HALT` with an
8-aligned `a0` is reached, `out = readOut`; a fault, a trap (other `t0`, undecodable word, `pc`
off the code) and fuel exhaustion (the `0` case) are all `none`. -/
def execute (img : Image) : Nat → MachineState → Option (List Word)
  | 0, _ => none
  | fuel + 1, s =>
    match fetch img s with
    | none => none
    | some (.base .ECALL) =>
      if s.getReg .x5 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 then some (readOut s) else none
    | some i =>
      match ordinaryStep s i with
      | some s' => execute img fuel s'
      | none => none

/-- Initial state: data words from address 0, the input tape from `TAPE_BASE` (both zero
beyond their length), `sp = TAPE_BASE`, all other registers 0, `pc = CODE_BASE`. -/
def initState (img : Image) (input : List Word) : MachineState where
  regs := fun r => match r with | .x2 => BitVec.ofNat 64 TAPE_BASE | _ => 0
  mem := fun a => if TAPE_BASE ≤ a.toNat then input.getD ((a.toNat - TAPE_BASE) / 8) 0
    else img.data.getD (a.toNat / 8) 0
  pc := BitVec.ofNat 64 CODE_BASE

/-- **The machine**: run `img` on the input tape `input` for at most `fuel` steps; the output
words at `HALT`, or `none` on a fault, a trap or fuel exhaustion. -/
def run (img : Image) (input : List Word) (fuel : Nat) : Option (List Word) :=
  execute img fuel (initState img input)

end RecursionFast
