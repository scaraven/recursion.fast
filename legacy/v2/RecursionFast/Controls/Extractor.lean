/-
# Controls: the bounded extractor (decision Q1)

Kernel-checked controls for `Contract/Machine.lean` and `Contract/Extractor.lean`. The images are
assembled from `tests/asm/*.S` (`riscv64-unknown-elf-as -march=rv64im_zbc`), one word per
instruction, in the order of the source.

* **Positive** (`copy_*`): an image that copies the witness section of its tape into data memory
  and outputs it. On a concrete two-round tape it returns the witness within a few hundred
  steps at its call's fuel (the even split, `2^56 / 3`; `decide +kernel`), so
  `extractMid` through `toExtractor` returns the input witness after round 0, and before round 0
  decodes it as tables that satisfy the relation (`copy_extract_relK`).
* **Machine** (`wzbc_run`, `tape_readonly`, `tape_below_ok`, `halt_misaligned`, `ecall_trap`,
  `halt_reads`): the W-op and Zbc semantics kept from v0.3 give the expected words; a store into
  the tape, a misaligned `HALT` and any `t0 ≠ 0` (v0.3's QUERY included) fail.
* **Fuel exhaustion** (`spin_*`): an image that loops forever returns `none` at fuel 100
  (`decide +kernel`) and at every fuel (a theorem), so `extractMid` is the empty witness.
* **Size cap** (`long_*`): an output of `2^33 > witCap 20` words is discarded; one of exactly
  `2^32` words is kept.
* **Round trip** (`tape_roundTrip`, `layout_roundTrip`): the directory of the input tape returns
  its sections, and the layout section parses back to the layout.
* **Negative, Q1, one call** (`brute_*`): a brute-force image that tries `c = 0, 1, 2, …` until
  `clmul(c, 0x1b) = x₀`. The kernel pins its cost (`15 + 4c` steps to succeed at `c`); a loop
  theorem over the machine shows that within `B(20) = 2^56` steps, so in any one call at class 20,
  it returns `none`, hence the empty witness, whenever no `c < 2^54` works (`brute_none`,
  `brute_extractMid_nil`, for any declared split), and such `x₀` with a preimage exist
  (`brute_nonvacuous`).
* **Negative, Q1, the composed extractor** (S4-M1, S4-A9): calls may share one search through the
  witness words (`resumeImage`, `chain_finds`, `chain_round0`), so `B(k)` is the total over the
  `n + 1` calls, split as the submitter declares. A chained search testing fewer than 256
  candidates per step is not an extractor at class 20, for any split and any number of free
  rounds (`chain_search_fails`); the arithmetic for every class is
  `composed_lt_word`, `composed_lt_two_words`, `budget_24_25`, and what `B(k)` admits is
  `oracle_sq`, `cube_gt`, `quadratic_fits` (S4-M2).

The toy protocol's extractor (`toy_extractMid`) and the control that `Secure` depends on the
image (`toy_spin_not_secure`) are in `Controls/Toy.lean`.
-/
import RecursionFast.Library.Extractor
import RecursionFast.Controls.Negative
import RecursionFast.Library.RbrSound

open scoped NNReal

namespace RecursionFast.Controls
open RecursionFast

/-! ## A concrete two-round tape -/

/-- Two rounds: an oracle of 2 elements (leaves of 1); one E element and one 8-bit index. -/
def sh2 : Fin 2 → Round := ![.msg ⟨1, 0⟩, .chal 1 [8]]

/-- The transcript: the oracle `(5, 6)`, the challenge `7 + 8y + 9y²` and the index `0xab`. -/
def tr2 : FullTranscript sh2 :=
  ((Transcript.empty sh2).concat (m := 0) ![⟨5⟩, ⟨6⟩]).concat (m := 1)
    (fun _ => ⟨⟨7⟩, ⟨8⟩, ⟨9⟩⟩, fun _ => 0xab)

/-- Its first round only. -/
def tr1 : Transcript sh2 (Fin.succ 0) := (Transcript.empty sh2).concat (m := 0) ![⟨5⟩, ⟨6⟩]

/-- The statement: `triv` (one public chip of 32 columns) and `x = (0, 1, …, 31)`. -/
def s2 : Layout K × Stmt := (triv, fun i => ⟨BitVec.ofNat 64 i.val⟩)

/-- A witness after round 1, as words. -/
def w3 : List Word := [7, 8, 9]

/-! ## Positive: copy the witness -/

/-- `tests/asm/copy.S` (21 instructions). -/
def copyImage : ExtractorImage 20 2 := .even ⟨[0x00100313, 0x03f31313, 0x00033383, 0x00439e13, 0x006e0e33, 0x000e3583, 0xff8e3e83,
    0x003e9e93, 0x006e8eb3, 0x10000513, 0x00050f13, 0x00058f93, 0x000f8e63, 0x000eb483,
    0x009f3023, 0x008e8e93, 0x008f0f13, 0xffff8f93, 0xfe9ff06f, 0x00000293, 0x00000073], []⟩
  (by decide) 20 2

/-- The copy image returns the witness `[7, 8, 9]` after round 1 within the class-20 fuel. -/
theorem copy_run :
    run copyImage.img (ExtractorImage.midTape sh2 1 s2 tr2 w3) (copyImage.fuel (Fin.castSucc 1)) =
      some w3 := by
  decide +kernel

/-- It takes 36 steps: 35 are not enough. -/
theorem copy_steps :
    run copyImage.img (ExtractorImage.midTape sh2 1 s2 tr2 w3) 36 = some w3 ∧
    run copyImage.img (ExtractorImage.midTape sh2 1 s2 tr2 w3) 35 = none := by
  decide +kernel

/-- **Through `toExtractor`**: after round 0 the extracted witness is the input witness. -/
theorem copy_extractMid :
    ((copyImage.toExtractor sh2).extractMid 1 s2 tr2 w3 : List Word) = w3 :=
  copyImage.extractMid_eq_of_run sh2 copy_run (by simp [witCap])

/-- The witness of `triv` as words: one table of height 1, 32 zero cells. -/
def trivWords : List Word := 1 :: List.replicate 32 0

/-- Before round 0, on the one-round prefix, the copy image returns `trivWords` (246 steps). -/
theorem copy_run0 :
    run copyImage.img (ExtractorImage.midTape sh2 0 (triv, fun _ => 0) tr1 trivWords)
      (copyImage.fuel (Fin.castSucc 0)) = some trivWords := by
  decide +kernel

/-- **Before round 0 the output is decoded as tables**, and here they satisfy the relation. -/
theorem copy_extract_relK :
    ((triv, fun _ => 0), (copyImage.toExtractor sh2).extractMid 0 (triv, fun _ => 0) tr1
      trivWords) ∈ relK 20 := by
  rw [copyImage.extractMid_eq_of_run sh2 copy_run0 (by simp [trivWords, witCap])]
  have : decMid (n := 2) triv (Fin.castSucc 0) trivWords = [⟨1, fun _ _ => 0⟩] := by
    show decTables [32] trivWords = _
    rw [show decTables [32] trivWords = [⟨1, fun r i => if r < 1 ∧ i < 32 then
      ⟨(List.replicate 32 (0 : Word)).getD (r * 32 + i) 0⟩ else 0⟩] from rfl]
    congr 3
    funext r i
    split
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
    · rfl
  rw [this]; exact triv_relK 20 (by norm_num)


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

/-- The looping image, with the budget split evenly (any split would do). -/
def spinImage (k n : ℕ) : ExtractorImage k n := .even spinImg (by decide) k n

theorem spin_run_100 : run spinImg (ExtractorImage.midTape sh2 1 s2 tr2 w3) 100 =
    none := by
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

/-- **Fuel exhaustion yields the empty witness**, for every class, fuel split, round, statement,
transcript and witness. -/
theorem spin_extractMid {k n : ℕ} (E : ExtractorImage k n) (hE : E.img = spinImg)
    (sh : Fin n → Round) (m : Fin n) (s : Layout K × Stmt) (tr : Transcript sh m.succ)
    (w : Mid n m.succ) : (E.toExtractor sh).extractMid m s tr w = [] :=
  E.extractMid_eq_nil_of_run sh (hE ▸ spin_run _ _)

/-! ## Size bound -/

open RiscvZkvm.Rv64 (MachineState execInstrBr signExtend12)

/-- `tests/asm/long.S`: output `2^33` words from address 0 (budget split evenly). -/
def longImage (n : ℕ) : ExtractorImage 20 n :=
  .even ⟨[0x00100593, 0x02159593, 0x00000293, 0x00000073], []⟩ (by decide) 20 n

/-- `tests/asm/long32.S`: output `2^32` words from address 0. -/
def long32Image : ExtractorImage 20 2 :=
  .even ⟨[0x00100593, 0x02059593, 0x00000293, 0x00000073], []⟩ (by decide) 20 2

/-- Both images halt after 4 steps with `2^sh` zero words, on every tape. -/
private theorem run_long {k n : ℕ} (E : ExtractorImage k n) (sh : BitVec 6)
    (hE : E.img.code.map decodeInstruction =
      [some (.base (.ADDI .x11 .x0 1)), some (.base (.SLLI .x11 .x11 sh)),
        some (.base (.ADDI .x5 .x0 0)), some (.base .ECALL)])
    (hd : E.img.data = []) (hsh : sh.toNat ≤ 60) (t : List Word) (f : ℕ) :
    run E.img t (f + 4) = some (List.replicate (2 ^ sh.toNat) 0) := by
  have fe : ∀ (s : MachineState) (idx : ℕ), idx < 4 → s.pc = BitVec.ofNat 64 (CODE_BASE + 4 * idx) →
      fetch E.img s = (E.img.code.map decodeInstruction)[idx]?.join := by
    intro s idx hi hpc
    rw [fetch_eq idx (by simp [CODE_BASE]; omega) hpc, List.getElem?_map]
    cases E.img.code[idx]? <;> rfl
  unfold run
  rw [execute_step _ ((fe _ 0 (by omega) rfl).trans (by rw [hE]; rfl)) rfl]
  simp [execInstrBr, signExtend12, CODE_BASE]
  rw [execute_step _ ((fe _ 1 (by omega) (by simp [CODE_BASE])).trans (by rw [hE]; rfl)) rfl]
  simp [execInstrBr]
  rw [execute_step _ ((fe _ 2 (by omega) (by simp [CODE_BASE])).trans (by rw [hE]; rfl)) rfl]
  simp [execInstrBr, signExtend12]
  rw [execute_halt _ ((fe _ 3 (by omega) (by simp [CODE_BASE])).trans (by rw [hE]; rfl)) (by simp)
    (by simp)]
  simp [readOut, readWords_eq, getMem_initState, hd, BitVec.toNat_shiftLeft]
  have h1 : 1 <<< sh.toNat % 18446744073709551616 = 2 ^ sh.toNat := by
    rw [Nat.shiftLeft_eq, one_mul, Nat.mod_eq_of_lt
      (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hsh) (by norm_num))]
  rw [h1, List.eq_replicate_iff]
  refine ⟨by simp, fun b hb => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
  rw [List.mem_range] at hj
  have : 8 * j % 18446744073709551616 < TAPE_BASE := by
    have : j < 2 ^ 60 := lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) hsh)
    simp only [TAPE_BASE]; omega
  simp [Nat.not_le.mpr this]

/-- **An output over the cap is discarded**: `longImage` outputs `2^33 > witCap 20` words, so
its extractor returns the empty witness, whatever it is given. -/
theorem long_extractMid {n : ℕ} (hn : n ≤ roundCap) (sh : Fin n → Round) (m : Fin n)
    (s : Layout K × Stmt) (tr : Transcript sh m.succ) (w : Mid n m.succ) :
    ((longImage n).toExtractor sh).extractMid m s tr w = [] := by
  refine (longImage n).call_of_long (o := List.replicate (2 ^ 33) 0) ?_
    (by rw [List.length_replicate, witCap]; norm_num)
  have : 2 ^ (2 * 20 + 1) ≤ (longImage n).fuel m.castSucc := ExtractorImage.even_fuel_ge hn _
  rw [show (longImage n).fuel m.castSucc = ((longImage n).fuel m.castSucc - 4) + 4 by omega]
  exact run_long (longImage n) 33 rfl rfl (by decide) _ _

/-- **An output at the cap is kept**: `long32Image` outputs exactly `2^32 = witCap 20` words. -/
theorem long32_extractMid (w : Mid 2 (Fin.succ 1)) :
    ((long32Image.toExtractor sh2).extractMid 1 s2 tr2 w : List Word) =
      List.replicate (2 ^ 32) (0 : Word) := by
  refine long32Image.extractMid_eq_of_run sh2 (o := List.replicate (2 ^ 32) 0) ?_
    (by rw [List.length_replicate, witCap])
  rw [show long32Image.fuel (Fin.castSucc 1) = (2 ^ 56 / 3 - 4) + 4 from by decide +kernel]
  exact run_long long32Image 32 rfl rfl (by decide) _ _

/-! ## Round trip of the input tape -/

/-- The directory of the concrete tape returns its sections: `[j]`, the layout, `x`, the
oracle's two elements, the challenge's three limbs and its index, the witness. -/
theorem tape_roundTrip :
    unframe (ExtractorImage.midTape sh2 1 s2 tr2 w3) =
      [[1], s2.1.words, (List.range 32).map toWord, [5, 6], [7, 8, 9, 0xab], w3] := by
  decide +kernel

/-- The layout section parses back to the layout (up to what `rel` does not read). -/
theorem layout_roundTrip : (Codec.pLayout (s2.1.words.map K.mk)).1 = triv.normal (2 ^ 8) := by
  have := pLayout_words (k := 20) (L := triv) (by norm_num) (triv_relK 20 (by norm_num)).1 []
  rw [List.append_nil] at this
  exact congrArg Prod.fst this

/-! ## Negative (Q1): brute force -/

/-- `tests/asm/brute.S` (17 instructions): `c := 0`; while `clmul(c, 0x1b) ≠ x₀`, `c := c + 1`;
output `[c]`. -/
def bruteImg : Image :=
  ⟨[0x00100313, 0x03f31313, 0x02833383, 0x00339393, 0x006383b3, 0x0003be03, 0x00000e93,
    0x01b00f13, 0x0bee9fb3, 0x01cf8663, 0x001e8e93, 0xff5ff06f, 0x01d03023, 0x00000513, 0x00100593,
    0x00000293, 0x00000073], []⟩

/-- The brute-force image on the two-round shape, budget split evenly. -/
def bruteImage : ExtractorImage 20 2 := .even bruteImg (by decide) 20 2

/-- The candidate test of the brute-force image: the low word of `c ⊗ 0x1b` (Zbc `clmul`). -/
def bruteHash (c : Word) : Word := clResult .clmul c 0x1b

/-- The statement `x = (0x77, 0, …)`: `0x77 = bruteHash 5`. -/
def s77 : Layout K × Stmt := (triv, fun i => if i = 0 then ⟨0x77⟩ else 0)

/-- **The kernel pins the cost**: the image finds `c = 5` in `15 + 4·5 = 35` steps, not 34
(8 to set up, 4 per failed candidate, 7 to test the last one and halt). -/
theorem brute_cost :
    run bruteImg (ExtractorImage.midTape sh2 1 s77 tr2 w3) 35 = some [5] ∧
    run bruteImg (ExtractorImage.midTape sh2 1 s77 tr2 w3) 34 = none := by
  decide +kernel

/-- The decoded program. -/
private def bruteProg : List Instruction :=
  [.base (.ADDI .x6 .x0 1), .base (.SLLI .x6 .x6 63), .base (.LD .x7 .x6 40),
   .base (.SLLI .x7 .x7 3), .base (.ADD .x7 .x7 .x6), .base (.LD .x28 .x7 0),
   .base (.ADDI .x29 .x0 0), .base (.ADDI .x30 .x0 0x1b), .cl .clmul .x31 .x29 .x30,
   .base (.BEQ .x31 .x28 12), .base (.ADDI .x29 .x29 1), .base (.JAL .x0 0x1ffff4),
   .base (.SD .x0 .x29 0), .base (.ADDI .x10 .x0 0), .base (.ADDI .x11 .x0 1),
   .base (.ADDI .x5 .x0 0), .base .ECALL]

private theorem brute_fetch (s : MachineState) (idx : ℕ) (hidx : idx < 17)
    (hpc : s.pc = BitVec.ofNat 64 (CODE_BASE + 4 * idx)) :
    fetch bruteImg s = bruteProg[idx]? := by
  rw [fetch_eq idx (by simp [CODE_BASE]; omega) hpc]
  interval_cases idx <;> rfl

/-- At the loop head with candidate `c` and target `x`. -/
private def AtLoop (x : Word) (c : ℕ) (s : MachineState) : Prop :=
  s.pc = BitVec.ofNat 64 (CODE_BASE + 4 * 8) ∧ s.getReg .x28 = x ∧
    s.getReg .x29 = BitVec.ofNat 64 c ∧ s.getReg .x30 = 0x1b

/-- One failed candidate: 4 steps back to the loop head with `c + 1`; no halt on the way. -/
private theorem brute_iter {x : Word} {c : ℕ} {s : MachineState} (hs : AtLoop x c s)
    (hc : bruteHash (BitVec.ofNat 64 c) ≠ x) :
    ∃ s', AtLoop x (c + 1) s' ∧
      (∀ f, execute bruteImg (f + 4) s = execute bruteImg f s') ∧
      ∀ f ≤ 3, execute bruteImg f s = none := by
  obtain ⟨hpc, h28, h29, h30⟩ := hs
  have hc' : ¬ (clResult .clmul (BitVec.ofNat 64 c) 27#64 = x) := hc
  let s1 := (s.setReg .x31 (clResult .clmul (s.getReg .x29) (s.getReg .x30))).setPC (s.pc + 4)
  let s2 := execInstrBr s1 (.BEQ .x31 .x28 12)
  let s3 := execInstrBr s2 (.ADDI .x29 .x29 1)
  let s4 := execInstrBr s3 (.JAL .x0 0x1ffff4)
  have p1 : s1.pc = BitVec.ofNat 64 (CODE_BASE + 4 * 9) := by simp [s1, hpc, CODE_BASE]
  have p2 : s2.pc = BitVec.ofNat 64 (CODE_BASE + 4 * 10) := by
    simp [s2, s1, execInstrBr, hpc, h28, h29, h30, hc', CODE_BASE]
  have p3 : s3.pc = BitVec.ofNat 64 (CODE_BASE + 4 * 11) := by
    simp only [s3, execInstrBr, pc_setPC, p2]; simp [CODE_BASE]
  have e1 : ∀ f, execute bruteImg (f + 1) s = execute bruteImg f s1 :=
    fun f => execute_step f (brute_fetch s 8 (by omega) hpc) rfl
  have e2 : ∀ f, execute bruteImg (f + 1) s1 = execute bruteImg f s2 :=
    fun f => execute_step f (brute_fetch s1 9 (by omega) p1) rfl
  have e3 : ∀ f, execute bruteImg (f + 1) s2 = execute bruteImg f s3 :=
    fun f => execute_step f (brute_fetch s2 10 (by omega) p2) rfl
  have e4 : ∀ f, execute bruteImg (f + 1) s3 = execute bruteImg f s4 :=
    fun f => execute_step f (brute_fetch s3 11 (by omega) p3) rfl
  have r2 : s2 = s1.setPC (s1.pc + 4) := by simp [s2, execInstrBr, s1, h28, h29, h30, hc']
  refine ⟨s4, ⟨?_, ?_, ?_, ?_⟩, fun f => by rw [e1, e2, e3, e4], fun f hf => ?_⟩
  · simp [s4, execInstrBr, p3, CODE_BASE, RiscvZkvm.Rv64.signExtend21]
  · simp [s4, s3, execInstrBr, r2, s1, h28]
  · simp [s4, s3, execInstrBr, r2, s1, h29, signExtend12, BitVec.ofNat_add]
  · simp [s4, s3, execInstrBr, r2, s1, h30]
  · interval_cases f
    · rfl
    · rw [e1]; rfl
    · rw [e1, e2]; rfl
    · rw [e1, e2, e3]; rfl

/-- `m` failed candidates from `c` on: no halt within `4·m` steps. -/
private theorem brute_loop (x : Word) (m : ℕ) : ∀ (c : ℕ) (s : MachineState), AtLoop x c s →
    (∀ d < m, bruteHash (BitVec.ofNat 64 (c + d)) ≠ x) →
    ∀ f ≤ 4 * m, execute bruteImg f s = none := by
  induction m with
  | zero => intro c s _ _ f hf; obtain rfl := Nat.le_zero.mp hf; rfl
  | succ m ih =>
    intro c s hs hno f hf
    obtain ⟨s', hs', hstep, hshort⟩ := brute_iter hs (by simpa using hno 0 (by omega))
    by_cases h4 : f ≤ 3
    · exact hshort f h4
    · obtain ⟨g, rfl⟩ : ∃ g, f = g + 4 := ⟨f - 4, by omega⟩
      rw [hstep]
      exact ih (c + 1) s' hs' (fun d hd => by
        simpa [Nat.add_assoc, Nat.add_comm 1 d] using hno (d + 1) (by omega)) g (by omega)

/-- The target the brute-force image loads: the first word of tape section 2 (on an extractor
tape, `x₀`, `bruteTarget_tape`). -/
def bruteTarget (t : List Word) : Word :=
  (initState bruteImg t).getMem ((t.getD 5 0 <<< 3) + 0x8000000000000000)

/-- The 8-step set-up, then `m` failed candidates: no halt within `8 + 4·m` steps. -/
private theorem brute_prologue (t : List Word) (m : ℕ)
    (h : ∀ d < m, bruteHash (BitVec.ofNat 64 d) ≠ bruteTarget t) (f : ℕ) (hf : f ≤ 4 * m) :
    execute bruteImg (f + 8) (initState bruteImg t) = none := by
  rw [execute_step _ (brute_fetch _ 0 (by omega) rfl) rfl]
  simp [execInstrBr, signExtend12, CODE_BASE]
  rw [execute_step _ (brute_fetch _ 1 (by omega) (by simp [CODE_BASE])) rfl]
  simp [execInstrBr]
  rw [execute_step _ (brute_fetch _ 2 (by omega) (by simp [CODE_BASE]))
    (ordinaryStep_ld (by simp [signExtend12]))]
  simp [signExtend12, TAPE_BASE, getMem_initState]
  rw [execute_step _ (brute_fetch _ 3 (by omega) (by simp [CODE_BASE])) rfl]
  simp [execInstrBr]
  rw [execute_step _ (brute_fetch _ 4 (by omega) (by simp [CODE_BASE])) rfl]
  simp [execInstrBr]
  have hal : ∀ (a : Word) (s : MachineState), s.getReg .x7 = a <<< 3 + 9223372036854775808#64 →
      (s.getReg .x7 + signExtend12 0).toNat % 8 = 0 := by
    intro a s hs
    rw [hs, show signExtend12 0 = 0#64 from rfl, BitVec.add_zero, BitVec.toNat_add,
      BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
    omega
  rw [execute_step _ (brute_fetch _ 5 (by omega) (by simp [CODE_BASE]))
    (ordinaryStep_ld (hal (t[5]?.getD 0) _ (by simp)))]
  simp [signExtend12]
  rw [execute_step _ (brute_fetch _ 6 (by omega) (by simp [CODE_BASE])) rfl]
  simp [execInstrBr, signExtend12]
  rw [execute_step _ (brute_fetch _ 7 (by omega) (by simp [CODE_BASE])) rfl]
  simp [execInstrBr, signExtend12]
  refine brute_loop (bruteTarget t) m 0 _ ⟨by simp [CODE_BASE], ?_, by simp, by simp⟩
    (fun d hd => by rw [Nat.zero_add]; exact h d hd) f hf
  simp [bruteTarget, List.getD_eq_getElem?_getD]

/-- **Brute force fails within the class-20 budget**: on any tape, if no candidate `c < 2^54`
hits the target, the image does not halt within `B(20) = 2^56` steps (it reaches only candidate
`2^54 - 2`), so a run with any fuel up to `2^56`, one call's included, is `none`. -/
theorem brute_none (t : List Word) {f : ℕ} (hf : f ≤ 2 ^ 56)
    (h : ∀ c < 2 ^ 54, bruteHash (BitVec.ofNat 64 c) ≠ bruteTarget t) :
    run bruteImg t f = none :=
  run_none_of_le (brute_prologue t (2 ^ 54 - 2) (fun d hd => h d (by omega)) (4 * (2 ^ 54 - 2))
    le_rfl) (by omega)

/-- On an extractor tape whose statement section is addressable, the target is `x₀`. -/
theorem bruteTarget_tape (j : ℕ) (s : Layout K × Stmt) (rounds : List (List Word))
    (w : List Word) (hb : 2 * rounds.length + s.1.words.length + 14 < 2 ^ 60) :
    bruteTarget (extractorTape j s rounds w) = (s.2 0).bits := by
  let secs := [toWord j] :: s.1.words :: List.ofFn (fun i => (s.2 i).bits) :: rounds ++ [w]
  have h2 : 2 < secs.length := by simp [secs]
  have hst : frameStart secs 2 = 2 * rounds.length + s.1.words.length + 10 := by
    simp [frameStart, secs]; omega
  have hsec := frame_getD_sec secs h2 (j := 0) (by simp [secs])
  have haddr : toWord (frameStart secs 2) <<< 3 + 9223372036854775808#64 =
      BitVec.ofNat 64 (TAPE_BASE + 8 * frameStart secs 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft]
    simp only [toWord, BitVec.toNat_ofNat, TAPE_BASE]
    omega
  show (initState bruteImg (frame secs)).getMem ((frame secs).getD 5 0 <<< 3 +
    0x8000000000000000) = _
  rw [show (5 : ℕ) = 1 + 2 * 2 from rfl, frame_getD_start secs h2,
    show (0x8000000000000000 : Word) = 9223372036854775808#64 from rfl, haddr,
    getMem_initState_tape _ _ (by omega), ← Nat.add_zero (frameStart secs 2), hsec]
  simp [secs]

/-- **The Q1 negative control, one call**: at class 20 the brute-force extractor returns the empty
witness for every statement whose `x₀` has no `bruteHash`-preimage below `2^54`, whatever the
number of rounds, the round, transcript and witness. `brute_nonvacuous`: `x₀ = 2^63` has the
preimage `2^63` and none below `2^54`, so it is the fuel that stops it. -/
theorem brute_extractMid_nil {n : ℕ} (E : ExtractorImage 20 n) (hE : E.img = bruteImg)
    (sh : Fin n → Round) (m : Fin n) (s : Layout K × Stmt)
    (tr : Transcript sh m.succ) (w : Mid n m.succ)
    (hb : 2 * m.val + s.1.words.length + 16 < 2 ^ 60)
    (h : ∀ c < 2 ^ 54, bruteHash (BitVec.ofNat 64 c) ≠ (s.2 0).bits) :
    (E.toExtractor sh).extractMid m s tr w = [] := by
  refine E.extractMid_eq_nil_of_run sh (hE ▸ brute_none _ ((E.fuel_le_budget _).trans
    (by simp [extractorBudget])) fun c hc => ?_)
  rw [bruteTarget_tape m s _ w (by rw [List.length_ofFn, Fin.val_succ]; omega)]
  exact h c hc

/-! ### Non-vacuity of the one-call control (S4-m1) -/

private theorem foldl_inv {α β : Type} (P : α → Prop) (f : α → β → α) (l : List β) (x : α)
    (hx : P x) (hf : ∀ a b, b ∈ l → P a → P (f a b)) : P (l.foldl f x) := by
  induction l generalizing x with
  | nil => exact hx
  | cons b l ih =>
    exact ih (f x b) (hf x b (by simp) hx) (fun a b' hb => hf a b' (by simp [hb]))

/-- Degree bound for the carry-less product: `a < 2^p`, `b < 2^q` give `a ⊗ b < 2^(p+q)`. -/
theorem clmul_lt {a b : Word} {p q : ℕ} (ha : a.toNat < 2 ^ p) (hb : b.toNat < 2 ^ q) :
    (K.clmul a b).toNat < 2 ^ (p + q) := by
  unfold K.clmul
  rw [Fin.foldl_eq_finRange_foldl]
  refine foldl_inv (fun acc : BitVec 128 => acc.toNat < 2 ^ (p + q)) _ _ _
    (by simp) fun acc i _ hacc => ?_
  split
  · rename_i hbit
    rw [BitVec.toNat_xor]
    refine Nat.xor_lt_two_pow hacc ?_
    have hip : i.val < p := by
      by_contra h
      have : a.toNat < 2 ^ i.val :=
        lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [BitVec.getLsbD, Nat.testBit_eq_false_of_lt this] at hbit
      exact absurd hbit (by simp)
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth]
    have hb' : b.toNat % 2 ^ 128 = b.toNat := Nat.mod_eq_of_lt (by omega)
    rw [hb', Nat.shiftLeft_eq]
    calc b.toNat * 2 ^ i.val % 2 ^ 128 ≤ b.toNat * 2 ^ i.val := Nat.mod_le _ _
      _ < 2 ^ q * 2 ^ i.val := Nat.mul_lt_mul_of_pos_right hb (by positivity)
      _ ≤ 2 ^ (p + q) := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · exact hacc

/-- `bruteHash c < 2^59` for `c < 2^54`. -/
theorem bruteHash_lt {c : ℕ} (hc : c < 2 ^ 54) :
    (bruteHash (BitVec.ofNat 64 c)).toNat < 2 ^ 59 := by
  have h1 : (BitVec.ofNat 64 c).toNat < 2 ^ 54 := by simp; omega
  have h2 : (0x1b : Word).toNat < 2 ^ 5 := by decide
  show ((K.clmul (BitVec.ofNat 64 c) 0x1b).setWidth 64).toNat < 2 ^ 59
  rw [BitVec.toNat_setWidth]
  exact lt_of_le_of_lt (Nat.mod_le _ _) (clmul_lt h1 h2)

/-- A preimage of `2^63` exists: `2^63` itself (`x^63 · (x^4+x^3+x+1)` truncated to 64 bits). -/
theorem bruteHash_top : bruteHash (BitVec.ofNat 64 (2 ^ 63)) = BitVec.ofNat 64 (2 ^ 63) := by
  decide +kernel

/-- ... and none below `2^54`. -/
theorem bruteHash_ne_top (c : ℕ) (hc : c < 2 ^ 54) :
    bruteHash (BitVec.ofNat 64 c) ≠ BitVec.ofNat 64 (2 ^ 63) := fun h => by
  have := bruteHash_lt hc
  rw [h] at this
  simp at this

/-- The statement `x₀ = 2^63` over `triv`. -/
def sTop : Layout K × Stmt := (triv, fun i => if i = 0 then ⟨BitVec.ofNat 64 (2 ^ 63)⟩ else 0)

/-- **The one-call control fires on a statement with a preimage**: `x₀ = 2^63` has one, yet the
brute-force extractor at class 20 returns `[]`. -/
theorem brute_nonvacuous :
    (∃ c : Word, bruteHash c = (sTop.2 0).bits) ∧
      ((bruteImage.toExtractor sh2).extractMid 1 sTop tr2 w3 : List Word) = [] := by
  refine ⟨⟨_, bruteHash_top⟩, ?_⟩
  refine brute_extractMid_nil bruteImage rfl sh2 1 sTop tr2 w3 ?_ (fun c hc => bruteHash_ne_top c hc)
  have : triv.words.length = 264 := by decide +kernel
  simp [sTop, this]

/-! ## The composed budget (S4-M1, S4-A9)

The fuel bounds each call, but knowledge is delivered by the `n + 1` calls of the round-by-round
extractor (`Library/RbrSound.lean`'s `chain`), which may pass state through the witness words.
So `B(k)` is the total: the submitter splits it over the calls, and the contract bounds the sum
(`ExtractorImage.fuel_le`, `composed_fuel_le`; S4-A14).

* **The mechanism** (`resumeImage`, `chain_finds`, `chain_round0`, after the review's
  `probes/s4/ChainBudget.lean`): a brute force made resumable keeps `[flag, c]` in the witness
  section; at class 20 on three rounds its four calls do one search and the composed extractor
  returns the secret `9`, which the first call alone (candidates `0 … 3`) does not reach.
* **The bound** (`chain_search_fails`): for any declared split of `B(20) = 2^56` and any number
  of free (empty challenge) rounds, a chained search whose calls test at most `c < 256`
  candidates per step of their fuel (bit-slicing included) is **not** an extractor for any
  injective `f`: the calls cover at most `255 · 2^56` candidates, and the secret `2^64 - 1` lies
  beyond. Under the per-call reading (`2^56` steps per call) the review's `chain_secure` (kept in
  `probes/s4/ChainBudget.lean`) made it secure with `2^10` padding rounds.
-/

/-- `probes/s4/asm/resume.S` (34 instructions): brute force over `x₀`, `T = 4` candidates per
call, the state `[flag, c]` in the witness section (`[]`: start at 0; `[0, c]`: resume at `c`;
`[1, c]`: found `c`, pass it on); outputs `[1, c]` or `[0, c + 4]` from address 0. -/
def resumeImage : ExtractorImage 20 3 := .even ⟨[0x00100313, 0x03f31313, 0x02833383, 0x00339393, 0x006383b3, 0x0003be03, 0x00033383,
    0x00439613, 0x00660633, 0x00063683, 0x00000e93, 0x00068e63, 0xff863883, 0x00389893,
    0x006888b3, 0x0008b803, 0x0088be83, 0x02081063, 0x01b00f13, 0x004e8713, 0x00ee8e63,
    0x0bee9fb3, 0x01cf8663, 0x001e8e93, 0xff1ff06f, 0x00100793, 0x0080006f, 0x00000793,
    0x00f03023, 0x01d03423, 0x00000513, 0x00200593, 0x00000293, 0x00000073], []⟩
  (by decide) 20 3

/-- Three one-element message rounds. -/
def sh3 : Fin 3 → Round := fun _ => .msg ⟨0, 0⟩

/-- The statement `x₀ = 0xc3 = bruteHash 9`. -/
def sC3 : Layout K × Stmt := (triv, fun i => if i = 0 then ⟨0xc3⟩ else 0)

theorem secret_9 : bruteHash 9 = 0xc3 := by decide +kernel

private theorem fuel_100 (j : Fin 4) : 100 ≤ resumeImage.fuel j :=
  le_trans (by norm_num) (ExtractorImage.even_fuel_ge (k := 20) (by decide) j)

/-- Call 1 (`extractOut`, `w = []`): candidates `0 … 3` fail; state `[0, 4]`. -/
theorem call1 : ((resumeImage.toExtractor sh3).extractOut sC3 (fun _ _ => 0) () : List Word) =
    ([0, 4] : List Word) := by
  have h : run resumeImage.img (ExtractorImage.outTape sh3 sC3 (fun _ _ => 0)) 100 =
      some [0, 4] := by decide +kernel
  rw [resumeImage.extractOut_eq_of_run sh3 (run_mono h (fuel_100 _)) (by simp [witCap])]; rfl

/-- Call 2 (`extractMid 2`, `w = [0, 4]`): candidates `4 … 7` fail; state `[0, 8]`. -/
theorem call2 : ((resumeImage.toExtractor sh3).extractMid 2 sC3 (fun _ _ => 0)
    ([0, 4] : List Word) : List Word) = ([0, 8] : List Word) := by
  have h : run resumeImage.img (ExtractorImage.midTape sh3 2 sC3 (fun _ _ => 0) [0, 4]) 100 =
      some [0, 8] := by decide +kernel
  rw [resumeImage.extractMid_eq_of_run sh3 (run_mono h (fuel_100 _)) (by simp [witCap])]; rfl

/-- Call 3 (`extractMid 1`, `w = [0, 8]`): candidate `9` hits; state `[1, 9]`. -/
theorem call3 : ((resumeImage.toExtractor sh3).extractMid 1 sC3 (fun _ _ => 0)
    ([0, 8] : List Word) : List Word) = ([1, 9] : List Word) := by
  have h : run resumeImage.img (ExtractorImage.midTape sh3 1 sC3 (fun _ _ => 0) [0, 8]) 100 =
      some [1, 9] := by decide +kernel
  rw [resumeImage.extractMid_eq_of_run sh3 (run_mono h (fuel_100 _)) (by simp [witCap])]; rfl

/-- Call 4 (`extractMid 0`, `w = [1, 9]`): passes `9` on, decoded before round 0 as one table of
height 1 whose first cell is `9`. -/
theorem call4 : ((resumeImage.toExtractor sh3).extractMid 0 sC3 (fun _ _ => 0)
    ([1, 9] : List Word) : List (Table K)) = decTables [32] [1, 9] := by
  have h : run resumeImage.img (ExtractorImage.midTape sh3 0 sC3 (fun _ _ => 0) [1, 9]) 100 =
      some [1, 9] := by decide +kernel
  rw [resumeImage.extractMid_eq_of_run sh3 (run_mono h (fuel_100 _)) (by simp [witCap])]; rfl

/-- **The calls share one search**: the first call (the only one that starts from nothing) gives
up at `4`; the third returns the preimage `9` of `x₀`. -/
theorem chain_finds :
    ((resumeImage.toExtractor sh3).extractOut sC3 (fun _ _ => 0) () : List Word) =
      ([0, 4] : List Word) ∧
    ((resumeImage.toExtractor sh3).extractMid 1 sC3 (fun _ _ => 0)
      ((resumeImage.toExtractor sh3).extractMid 2 sC3 (fun _ _ => 0)
        ((resumeImage.toExtractor sh3).extractOut sC3 (fun _ _ => 0) ())) : List Word) =
      ([1, 9] : List Word) ∧
    bruteHash 9 = (sC3.2 0).bits := by
  refine ⟨call1, ?_, secret_9⟩
  have e : ((resumeImage.toExtractor sh3).extractMid 2 sC3 (fun _ _ => 0)
      ((resumeImage.toExtractor sh3).extractOut sC3 (fun _ _ => 0) ()) : List Word) =
      ([0, 8] : List Word) := by
    rw [call1]; exact call2
  rw [e]; exact call3

/-- **The composed extractor** (`chain`, which `chain_extracts` turns into a witness) of this image
returns, before round 0, the tables holding the preimage `9`. -/
theorem chain_round0 :
    (chain (resumeImage.toExtractor sh3) sC3 (fun _ _ => 0) () 0 : List (Table K)) =
      decTables [32] [1, 9] := by
  let E := resumeImage.toExtractor sh3
  let tr : FullTranscript sh3 := fun _ _ => 0
  have step : ∀ m : Fin 3, chain E sC3 tr () m.castSucc =
      E.extractMid m sC3 (pre tr m.succ) (chain E sC3 tr () m.succ) := fun m => by
    unfold chain; exact Fin.reverseInduction_castSucc (i := m)
  have last : chain E sC3 tr () (Fin.last 3) = E.extractOut sC3 tr () := by
    unfold chain; exact Fin.reverseInduction_last
  have e3 : (chain E sC3 tr () (Fin.succ 2) : List Word) = ([0, 4] : List Word) :=
    last.trans call1
  have e2 : (chain E sC3 tr () (Fin.succ 1) : List Word) = ([0, 8] : List Word) := by
    refine (step 2).trans ?_
    rw [e3]; exact call2
  have e1 : (chain E sC3 tr () (Fin.succ 0) : List Word) = ([1, 9] : List Word) := by
    refine (step 1).trans ?_
    rw [e2]; exact call3
  refine (step 0).trans ?_
  rw [e1]; exact call4

section ChainSearch
variable (f : Word → Word) (n : ℕ)

/-- `n` **empty** challenge rounds: admissible, one value each, so free for the verifier and for
the error budget; each adds an extractor call. -/
def padShape : Fin n → Round := fun _ => .chal 0 []

/-- `padShape` rounds are admissible at every class. -/
theorem padShape_admissible (k : ℕ) (j : Fin n) : (padShape n j).Admissible k := by
  simp [padShape, Round.Admissible]

/-- The search state: `inl c` (candidates below `c` tried) or `inr w` (found `w`). -/
abbrev St := ℕ ⊕ Word

/-- One call: test the `t` candidates `c, …, c + t - 1`. -/
def step (t : ℕ) (x : Word) : St → St
  | .inr w => .inr w
  | .inl c => match (List.range t).find? (fun i => f (BitVec.ofNat 64 (c + i)) == x) with
    | some i => .inr (BitVec.ofNat 64 (c + i))
    | none => .inl (c + t)

/-- The last call: one more step, then the witness found (`0` if none). -/
def finish (t : ℕ) (x : Word) (s : St) : Word := match step f t x s with
  | .inr w => w
  | .inl _ => 0

/-- Witness types: the input witness before round 0, the search state after it. -/
def WM : Fin (n + 1) → Type := Fin.cases (motive := fun _ => Type) Word (fun _ => St)

/-- The call before round `j`, testing `T j` candidates: `finish` before round 0, `step` after. -/
def callAt (T : Fin (n + 1) → ℕ) (x : Word) (j : Fin (n + 1)) : St → WM n j :=
  Fin.cases (motive := fun j => St → WM n j) (finish f (T 0) x) (fun i => step f (T i.succ) x) j

/-- The chained-search extractor on any round shapes: its `n + 1` calls continue one search, the
call before round `j` testing `T j` candidates. -/
def chainE (T : Fin (n + 1) → ℕ) (sh : Fin n → Round) : Extractor sh Word Word Unit (WM n) where
  eqIn := rfl
  extractMid m x _ s := callAt f n T x m.castSucc s
  extractOut x _ _ := callAt f n T x (Fin.last n) (.inl 0)

/-- A call that tests only candidates below the secret's index finds nothing. -/
private theorem step_miss (hf : Function.Injective f) {p : Word} {c t : ℕ}
    (hc : c + t ≤ p.toNat) : step f t (f p) (.inl c) = .inl (c + t) := by
  simp only [step]
  rw [List.find?_eq_none.mpr fun i hi => by
    have hi' := List.mem_range.mp hi
    simp only [beq_iff_eq]
    intro h
    have := congrArg BitVec.toNat (hf h)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.isLt; omega)] at this
    omega]

/-- The candidates of the calls before rounds `j, j + 1, …, n`. -/
private def tail (T : Fin (n + 1) → ℕ) (j : ℕ) : ℕ := ((List.ofFn T).drop j).sum

private theorem tail_succ (T : Fin (n + 1) → ℕ) (j : Fin (n + 1)) :
    tail n T j = T j + tail n T (j + 1) := by
  rw [tail, List.drop_eq_getElem_cons (by rw [List.length_ofFn]; exact j.isLt), List.sum_cons,
    List.getElem_ofFn]; rfl

private theorem tail_le (T : Fin (n + 1) → ℕ) (j : ℕ) : tail n T j ≤ (List.ofFn T).sum := by
  conv_rhs => rw [← List.take_append_drop j (List.ofFn T), List.sum_append]
  exact Nat.le_add_left _ _

/-- What the chain holds: `0` before round 0; after round `i + 1`, the calls before rounds
`i + 1, …, n` done. -/
private def Missed (T : Fin (n + 1) → ℕ) (j : Fin (n + 1)) : WM n j → Prop :=
  Fin.cases (motive := fun j => WM n j → Prop) (fun w : Word => w = 0)
    (fun i s => s = .inl (tail n T (i.val + 1))) j

private theorem missed_back (hf : Function.Injective f) {p : Word} (T : Fin (n + 1) → ℕ)
    (hp : (List.ofFn T).sum ≤ p.toNat) (m : Fin n) (s : WM n m.succ)
    (h : Missed n T m.succ s) : Missed n T m.castSucc (callAt f n T (f p) m.castSucc s) := by
  obtain ⟨m, hm⟩ := m
  have hs : s = .inl (tail n T (m + 1)) := h
  have e := tail_succ n T ⟨m, by omega⟩
  have hle := tail_le n T m
  cases m with
  | zero =>
    have e' : tail n T 0 = T 0 + tail n T (0 + 1) := e
    show finish f (T 0) (f p) s = 0
    rw [hs, finish, step_miss f hf (by omega)]
  | succ m =>
    show step f (T ⟨m + 1, by omega⟩) (f p) s = .inl (tail n T (m + 1))
    rw [hs, step_miss f hf (by simp only at e; omega)]
    simp only at e
    rw [e, Nat.add_comm]

private theorem missed_last (hf : Function.Injective f) {p : Word} (T : Fin (n + 1) → ℕ)
    (hp : (List.ofFn T).sum ≤ p.toNat) :
    Missed n T (Fin.last n) (callAt f n T (f p) (Fin.last n) (.inl 0)) := by
  have e := tail_succ n T (Fin.last n)
  have h0 : tail n T (n + 1) = 0 := by rw [tail, List.drop_eq_nil_of_le (by simp)]; rfl
  have hle := tail_le n T n
  simp only [Fin.val_last, h0, Nat.add_zero] at e
  cases n with
  | zero =>
    show finish f (T 0) (f p) (.inl 0) = 0
    rw [finish, step_miss f hf (by simp only [Fin.last_zero] at e; omega)]
  | succ n =>
    show step f (T (Fin.last (n + 1))) (f p) (.inl 0) = .inl (tail (n + 1) T (n + 1))
    rw [step_miss f hf (by omega), e, Nat.zero_add]

/-- **The composed enumeration fails at class 20, for any split.** Let `E` be any image at class
20 for `n` rounds (any declared split of `B(20) = 2^56`), and let a chained search test, in the
call before round `j`, at most `c` candidates per step of that call's fuel (`c = 1` for one test
per step; bit-slicing gives up to `c = 64`). If `c < 256`, it is not a knowledge extractor for
"`f c = x`", for any injective `f`, prover and errors, on any number `n` of free padding rounds:
the calls test at most `255 · 2^56 < 2^64 - 1` candidates, and the secret `2^64 - 1` lies beyond.
Reaching `2^64` candidates would take 256 per step. -/
theorem chain_search_fails (hf : Function.Injective f) (E : ExtractorImage 20 n) {c : ℕ}
    (hc : c < 256) (T : Fin (n + 1) → ℕ) (hT : ∀ j, T j ≤ c * E.fuel j)
    (P : Strategy (padShape n) Word Word Unit Unit) (ε : ChallengeIdx (padShape n) → ℝ≥0) :
    ¬ SecureWith {q : Word × Word | f q.2 = q.1} Set.univ P (fun _ _ => some ())
      (chainE f n T (padShape n)) ε := by
  rintro ⟨-, ⟨kSF, hrbr⟩, hcap⟩
  let p : Word := BitVec.allOnes 64
  have hsum : (List.ofFn T).sum ≤ c * 2 ^ 56 := by
    have h1 : (List.ofFn T).sum ≤ (List.ofFn fun j => c * E.fuel j).sum := by
      simp only [List.sum_ofFn]; exact Finset.sum_le_sum fun j _ => hT j
    have h2 : (List.ofFn fun j => c * E.fuel j).sum = c * (List.ofFn E.fuel).sum := by
      simp only [List.sum_ofFn, Finset.mul_sum]
    have h3 := E.fuel_le
    simp only [extractorBudget] at h3
    calc (List.ofFn T).sum ≤ c * (List.ofFn E.fuel).sum := h2 ▸ h1
      _ ≤ c * 2 ^ (2 * 20 + 16) := Nat.mul_le_mul_left _ h3
  have hp : (List.ofFn T).sum ≤ p.toNat := by
    simp only [p, BitVec.toNat_allOnes]
    have : c * 2 ^ 56 ≤ 255 * 2 ^ 56 := Nat.mul_le_mul_right _ (by omega)
    omega
  let tr : FullTranscript (padShape n) := fun _ => (fun i => i.elim0, fun j => j.elim0)
  have hgood : ∀ c : ChallengeIdx (padShape n),
      ¬ kSF.Bad c (f p) (pre tr c.1.castSucc) (tr c.1) := fun c hb => by
    have h1 := hrbr (f p) c (pre tr c.1.castSucc)
    have hcard : Nat.card (padShape n c.1).Ty = 1 := by
      show Nat.card (Round.chal 0 []).Ty = 1
      rw [natCard_chal]; simp
    rw [hcard, Nat.cast_one, mul_one] at h1
    have hpos : 0 < Nat.card {ch // kSF.Bad c (f p) (pre tr c.1.castSucc) ch} := by
      have : Nonempty {ch // kSF.Bad c (f p) (pre tr c.1.castSucc) ch} := ⟨⟨_, hb⟩⟩
      exact Nat.card_pos
    have : (1 : ℝ≥0) ≤ ε c := le_trans (by exact_mod_cast hpos) h1
    exact absurd (lt_of_le_of_lt (hcap c) errorCap_lt_one) (not_lt.mpr this)
  have hext := chain_extracts kSF (f p) tr () () rfl (Set.mem_univ _) hgood
  have h0 : Missed n T 0 (chain (chainE f n T (padShape n)) (f p) tr () 0) := by
    have : ∀ j, Missed n T j (chain (chainE f n T (padShape n)) (f p) tr () j) := by
      intro j
      induction j using Fin.reverseInduction with
      | last => rw [chain, Fin.reverseInduction_last]; exact missed_last f n hf T hp
      | cast m ih =>
        rw [chain, Fin.reverseInduction_castSucc, ← chain]
        exact missed_back f n hf T hp m _ ih
    exact this 0
  have h1 : f (show Word from chain (chainE f n T (padShape n)) (f p) tr () 0) = f p := hext
  have hz : (show Word from chain (chainE f n T (padShape n)) (f p) tr () 0) = 0 := h0
  rw [hz] at h1
  have := congrArg BitVec.toNat (hf h1)
  simp [p] at this

end ChainSearch

/-! ### The arithmetic of the bound (S4-A9, S4-A14) -/

/-- Up to class 23 a whole extraction (all calls, any split) has fewer than `2^64` steps: no
extractor tests all values of one word, even at one step per candidate. -/
theorem composed_lt_word {k n : ℕ} (E : ExtractorImage k n) (hk : k ≤ 23) :
    (List.ofFn E.fuel).sum < 2 ^ 64 :=
  lt_of_le_of_lt E.fuel_le (Nat.pow_lt_pow_right (by norm_num) (by omega))

/-- At every class of the range a whole extraction has fewer than `2^128` steps: no extractor
tests all values of two words (a witness of two or more `K` elements, such as a 256-bit chain
start). -/
theorem composed_lt_two_words {k n : ℕ} (E : ExtractorImage k n) (hk : k ≤ 28) :
    (List.ofFn E.fuel).sum < 2 ^ 128 :=
  lt_of_le_of_lt E.fuel_le (Nat.pow_lt_pow_right (by norm_num) (by omega))

/-- From class 24 on the total budget reaches `2^64`: a one-element secret is enumerable when a
candidate costs at most `2^(2k-48)` steps, loop control included; that is one step at `k = 24`,
which no loop achieves (`budget_24_25`), and four at `k = 25`. -/
theorem word_le_budget {k : ℕ} (hk : 24 ≤ k) : 2 ^ 64 ≤ extractorBudget k :=
  Nat.pow_le_pow_right (by norm_num) (by omega)

theorem budget_24_25 : extractorBudget 24 < 2 * 2 ^ 64 ∧ 4 * 2 ^ 64 ≤ extractorBudget 25 := by
  simp [extractorBudget]

/-- The brute-force image needs `15 + 4c` steps to succeed at `c` (`brute_cost`): more than
`B(20)`, hence more than any call has, from `c = 2^54 - 3`. -/
theorem brute_steps_exceed {n c : ℕ} (E : ExtractorImage 20 n) (j : Fin (n + 1))
    (hc : 2 ^ 54 - 3 ≤ c) : E.fuel j < 15 + 4 * c :=
  lt_of_le_of_lt (E.fuel_le_budget j) (by simp [extractorBudget]; omega)

/-- What `B(k)` admits (S4-M2): it is a sixteenth of the square of the longest admissible oracle
(`2^(k+10)` elements); ... -/
theorem oracle_sq (k : ℕ) : (2 ^ (k + 10)) ^ 2 = 16 * 2 ^ (2 * k + 16) := by
  rw [← pow_mul, show (k + 10) * 2 = 4 + (2 * k + 16) by ring, pow_add]; norm_num

/-- ... cubic elimination on as many unknowns as the witness has cells exceeds it from `k = 17`;
... -/
theorem cube_gt {k : ℕ} (hk : 17 ≤ k) : 2 ^ (2 * k + 16) < (2 ^ k) ^ 3 := by
  rw [← pow_mul]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- ... and a quadratic decoder at 10 steps per operation fits it up to `2^(k+6)` elements. -/
theorem quadratic_fits (k : ℕ) : 10 * (2 ^ (k + 6)) ^ 2 ≤ 2 ^ (2 * k + 16) := by
  rw [← pow_mul, show 2 * k + 16 = 4 + (k + 6) * 2 by ring, pow_add]
  exact Nat.mul_le_mul_right _ (by norm_num)

end RecursionFast.Controls
