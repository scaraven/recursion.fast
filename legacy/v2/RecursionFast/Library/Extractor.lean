/-
  RecursionFast.Library.Extractor  (UNTRUSTED, kernel-checked)

  The submitter's interface to the bounded extractor (`Contract/Extractor.lean`, decision Q1).

  * **Refinement** (`extractMid_eq_of_run`, `extractMid_eq_nil_of_run`, `extractOut_eq_of_run`,
    `extractOut_eq_nil_of_run`): the extractor of an image returns the decoded output of the
    image's run when the run halts with an output of at most `witCap k` words, and the empty
    witness when the run fails. A `KSF` proof therefore reduces to facts about `run`. Before
    round 0 the empty witness is never in `relK` (`nil_not_relK`).
  * **Fuel** (`composed_fuel_le`, `fuel_le_budget`, `even`, `atZero`, `even_fuel_ge`): the
    `n + 1` calls of an extraction share `B(k) = 2^(2k+16)` steps, split as the submitter
    declares; `even` and `atZero` are two ready-made splits.
  * **Machine** (`execute_step`, `execute_halt`, `execute_mono`, `fetch_eq`, `ordinaryStep_ld`,
    `readWords_eq`, simp lemmas on registers and the initial state): symbolic execution of a
    concrete image on a symbolic tape, one instruction at a time.
  * **Tape** (`frameStart`, `frame_getD_count`, `frame_getD_start`, `frame_getD_len`,
    `frame_getD_sec`, `unframe_frame`): where each section of the input tape lies, and that the
    directory determines the sections.
  * **Codec bridge** (`Layout.words_eq`, `decTables_map_bits`): the contract's word encodings are
    `Library/Codec.lean`'s `K` encodings read as words, so `pLayout_eLayout` and `pWit_eWit` are
    their round trips (`pLayout_words`).
  * **The first-message image** (`firstMsgImage`, `run_firstMsgImage_tape`,
    `firstMsg_extractMid`): an 8-instruction image that outputs the first transcript round in
    place; the extractor of the toy protocol and of the trivial baseline (DESIGN §7.3), which
    send the witness tables in round 0.
-/
import RecursionFast.Contract.Protocol
import RecursionFast.Library.Codec
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.GetD

namespace RecursionFast
open RiscvZkvm.Rv64 (MachineState Instr Reg execInstrBr signExtend12)

/-! ## Refinement: the extractor is the image's run -/

namespace ExtractorImage
variable {k n : ℕ} (E : ExtractorImage k n)

theorem call_of_run {L : Layout K} {j : Fin (n + 1)} {t o : List Word}
    (h : run E.img t (E.fuel j) = some o) (ho : o.length ≤ witCap k) :
    E.call L j t = decMid L j o := by
  unfold call; rw [h]; exact ite_eq_left ho

theorem call_of_run_none {L : Layout K} {j : Fin (n + 1)} {t : List Word}
    (h : run E.img t (E.fuel j) = none) : E.call L j t = [] := by
  unfold call; rw [h]

theorem call_of_long {L : Layout K} {j : Fin (n + 1)} {t o : List Word}
    (h : run E.img t (E.fuel j) = some o) (ho : witCap k < o.length) :
    E.call L j t = [] := by
  unfold call; rw [h]; exact ite_eq_right (Nat.not_le.mpr ho)

variable (sh : Fin n → Round)

/-- The tape of `extractMid m s tr w`. -/
abbrev midTape (m : Fin n) (s : Layout K × Stmt) (tr : Transcript sh m.succ) (w : List Word) :
    List Word :=
  extractorTape m s (List.ofFn fun i => Round.words _ (tr i)) w

/-- The tape of `extractOut s tr ()`. -/
abbrev outTape (s : Layout K × Stmt) (tr : FullTranscript sh) : List Word :=
  extractorTape n s (List.ofFn fun i => (sh i).words (tr i)) []

theorem extractMid_eq (m : Fin n) (s : Layout K × Stmt) (tr : Transcript sh m.succ)
    (w : Mid n m.succ) :
    (E.toExtractor sh).extractMid m s tr w = E.call s.1 m.castSucc (midTape sh m s tr w) :=
  rfl

theorem extractOut_eq (s : Layout K × Stmt) (tr : FullTranscript sh) :
    (E.toExtractor sh).extractOut s tr () = E.call s.1 (Fin.last n) (outTape sh s tr) := rfl

/-- **Refinement, `extractMid`**: if the image halts on `⟦m, s, tr, w⟧` within the fuel with an
output `o` of at most `witCap k` words, the extracted witness is `o` decoded. -/
theorem extractMid_eq_of_run {m : Fin n} {s : Layout K × Stmt} {tr : Transcript sh m.succ}
    {w : Mid n m.succ} {o : List Word}
    (h : run E.img (midTape sh m s tr w) (E.fuel m.castSucc) = some o)
    (ho : o.length ≤ witCap k) :
    (E.toExtractor sh).extractMid m s tr w = decMid s.1 m.castSucc o :=
  E.call_of_run h ho

/-- **Refinement, failure**: if the run fails (fault, trap, fuel exhaustion), the extracted
witness is empty. -/
theorem extractMid_eq_nil_of_run {m : Fin n} {s : Layout K × Stmt} {tr : Transcript sh m.succ}
    {w : Mid n m.succ} (h : run E.img (midTape sh m s tr w) (E.fuel m.castSucc) = none) :
    (E.toExtractor sh).extractMid m s tr w = [] :=
  E.call_of_run_none h

/-- **Refinement, `extractOut`**. -/
theorem extractOut_eq_of_run {s : Layout K × Stmt} {tr : FullTranscript sh} {o : List Word}
    (h : run E.img (outTape sh s tr) (E.fuel (Fin.last n)) = some o) (ho : o.length ≤ witCap k) :
    (E.toExtractor sh).extractOut s tr () = decMid s.1 (Fin.last n) o :=
  E.call_of_run h ho

theorem extractOut_eq_nil_of_run {s : Layout K × Stmt} {tr : FullTranscript sh}
    (h : run E.img (outTape sh s tr) (E.fuel (Fin.last n)) = none) :
    (E.toExtractor sh).extractOut s tr () = [] :=
  E.call_of_run_none h

end ExtractorImage

/-- Before round 0 an output is decoded as tables. -/
theorem decMid_zero {n : ℕ} (L : Layout K) (o : List Word) :
    decMid (n := n) L 0 o = decTables (L.chips.map Chip.cols) o := rfl

/-- After round 0 an output is its own words. -/
theorem decMid_succ {n : ℕ} (L : Layout K) (j : Fin n) (o : List Word) :
    decMid L j.succ o = o := rfl

/-- `[]` is never a witness of an admissible layout: there is a chip, and `rel` needs one table
per chip. So a failed call before round 0 never satisfies a `KSF`'s `empty` law. -/
theorem nil_not_relK (k : ℕ) (s : Layout K × Stmt) : (s, ([] : List (Table K))) ∉ relK k := by
  rintro ⟨⟨-, ⟨C, hC, -⟩, -⟩, hlen, -⟩
  have : s.1.chips ≠ [] := by rintro h; simp [h] at hC
  exact this (List.eq_nil_of_length_eq_zero hlen.symm)

/-! ## Fuel: `B(k)` split over the `n + 1` calls -/

namespace ExtractorImage
variable {k n : ℕ}

/-- **The composed budget**: the `n + 1` calls of an extraction have at most `B(k)` steps in
all, whatever `n` and the split. -/
theorem composed_fuel_le (E : ExtractorImage k n) : (List.ofFn E.fuel).sum ≤ extractorBudget k :=
  E.fuel_le

/-- One call has at most `B(k)` steps. -/
theorem fuel_le_budget (E : ExtractorImage k n) (j : Fin (n + 1)) :
    E.fuel j ≤ extractorBudget k :=
  le_trans (List.le_sum_of_mem (List.mem_ofFn.mpr ⟨j, rfl⟩)) E.fuel_le

/-- An image with the budget split evenly over the calls. -/
def even (img : Image) (h : img.byteSize ≤ imageCap) (k n : ℕ) : ExtractorImage k n where
  img := img
  img_le := h
  fuel _ := extractorBudget k / (n + 1)
  fuel_le := by
    rw [List.sum_ofFn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact Nat.mul_div_le _ _

/-- An image with the whole budget on the call before round 0 (the decoding call). -/
def atZero (img : Image) (h : img.byteSize ≤ imageCap) (k n : ℕ) : ExtractorImage k n where
  img := img
  img_le := h
  fuel j := if j = 0 then extractorBudget k else 0
  fuel_le := by
    rw [List.sum_ofFn, Finset.sum_ite_eq' Finset.univ (0 : Fin (n + 1))]
    simp

/-- Within the round cap, each call of the even split has at least `2^(2k+1) = B(k) / 2^15`
steps. -/
theorem even_fuel_ge {img : Image} {h : img.byteSize ≤ imageCap} (hn : n ≤ roundCap)
    (j : Fin (n + 1)) : 2 ^ (2 * k + 1) ≤ (even img h k n).fuel j := by
  show 2 ^ (2 * k + 1) ≤ 2 ^ (2 * k + 16) / (n + 1)
  rw [Nat.le_div_iff_mul_le (Nat.succ_pos n)]
  calc 2 ^ (2 * k + 1) * (n + 1) ≤ 2 ^ (2 * k + 1) * 2 ^ 15 :=
        Nat.mul_le_mul_left _ (by unfold roundCap at hn; omega)
    _ = 2 ^ (2 * k + 16) := by rw [← Nat.pow_add]

end ExtractorImage

/-! ## Machine: symbolic execution -/

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

/-! ## The input tape -/

/-- Index of the first word of section `i` in `frame secs`. -/
def frameStart (secs : List (List Word)) (i : ℕ) : ℕ :=
  1 + 2 * secs.length + ((secs.take i).map List.length).sum

private theorem foldl_add_eq (a : ℕ) (l : List ℕ) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a <;> simp [*, Nat.add_assoc]

private theorem flatMap_pair_getD {α β : Type} (f g : α → β) (d : β) (l : List α) (i : ℕ)
    (hi : i < l.length) :
    (l.flatMap fun p => [f p, g p]).getD (2 * i) d = f l[i] ∧
      (l.flatMap fun p => [f p, g p]).getD (2 * i + 1) d = g l[i] := by
  induction l generalizing i with
  | nil => nomatch hi
  | cons a l ih =>
    cases i with
    | zero => exact ⟨rfl, rfl⟩
    | succ i => exact ih i (Nat.lt_of_succ_lt_succ hi)

private theorem frame_eq (secs : List (List Word)) :
    frame secs = toWord secs.length ::
      (((secs.map List.length).scanl (· + ·) (1 + 2 * secs.length)).zip secs).flatMap
        (fun p => [toWord p.1, toWord p.2.length]) ++ secs.flatten := rfl

private theorem dir_length (secs : List (List Word)) :
    ((((secs.map List.length).scanl (· + ·) (1 + 2 * secs.length)).zip secs).flatMap
      (fun p => [toWord p.1, toWord p.2.length])).length = 2 * secs.length := by
  simp [List.length_flatMap, List.length_zip, List.length_scanl]
  omega

/-- Word 0 of the tape: the number of sections. -/
theorem frame_getD_count (secs : List (List Word)) : (frame secs).getD 0 0 = toWord secs.length :=
  rfl

private theorem frame_dir (secs : List (List Word)) {i : ℕ} (hi : i < secs.length) :
    (frame secs).getD (1 + 2 * i) 0 = toWord (frameStart secs i) ∧
      (frame secs).getD (2 + 2 * i) 0 = toWord secs[i].length := by
  have hz : i < (((secs.map List.length).scanl (· + ·) (1 + 2 * secs.length)).zip secs).length := by
    simp [List.length_zip, List.length_scanl]; omega
  obtain ⟨h1, h2⟩ := flatMap_pair_getD (fun p : ℕ × List Word => toWord p.1)
    (fun p => toWord p.2.length) 0 _ i hz
  have hd := dir_length secs
  rw [frame_eq, List.cons_append]
  constructor
  · rw [show 1 + 2 * i = 2 * i + 1 by ring, List.getD_cons_succ,
      List.getD_append _ _ _ _ (by omega),
      h1, List.getElem_zip, List.getElem_scanl, foldl_add_eq, ← List.map_take]
    rfl
  · rw [show 2 + 2 * i = 2 * i + 1 + 1 by ring, List.getD_cons_succ,
      List.getD_append _ _ _ _ (by omega),
      h2, List.getElem_zip]

/-- Words `1 + 2i` of the tape: where section `i` starts. -/
theorem frame_getD_start (secs : List (List Word)) {i : ℕ} (hi : i < secs.length) :
    (frame secs).getD (1 + 2 * i) 0 = toWord (frameStart secs i) := (frame_dir secs hi).1

/-- Words `2 + 2i` of the tape: the length of section `i`. -/
theorem frame_getD_len (secs : List (List Word)) {i : ℕ} (hi : i < secs.length) :
    (frame secs).getD (2 + 2 * i) 0 = toWord secs[i].length := (frame_dir secs hi).2

private theorem drop_sum_flatten (secs : List (List Word)) (i : ℕ) :
    secs.flatten.drop ((secs.take i).map List.length).sum = (secs.drop i).flatten := by
  rw [List.map_take, List.drop_sum_flatten]

/-- The tape from the start of section `i` on. -/
theorem frame_drop (secs : List (List Word)) (i : ℕ) :
    (frame secs).drop (frameStart secs i) = (secs.drop i).flatten := by
  rw [frame_eq, frameStart, ← List.drop_drop,
    List.drop_left' (by rw [List.length_cons, dir_length]; omega), drop_sum_flatten]

/-- Word `j` of section `i`. -/
theorem frame_getD_sec (secs : List (List Word)) {i j : ℕ} (hi : i < secs.length)
    (hj : j < secs[i].length) : (frame secs).getD (frameStart secs i + j) 0 = secs[i][j] := by
  have h1 : (frame secs).getD (frameStart secs i + j) 0 =
      ((frame secs).drop (frameStart secs i)).getD j 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [h1, frame_drop, List.drop_eq_getElem_cons hi, List.flatten_cons,
    List.getD_append _ _ _ _ hj, List.getD_eq_getElem]

/-- The tape's length. -/
theorem frame_length (secs : List (List Word)) :
    (frame secs).length = 1 + 2 * secs.length + (secs.map List.length).sum := by
  rw [frame_eq]; simp [List.length_flatten]; omega

theorem frameStart_add_le (secs : List (List Word)) {i : ℕ} (hi : i < secs.length) :
    frameStart secs i + secs[i].length ≤ (frame secs).length := by
  have e := List.sum_take_add_sum_drop (secs.map List.length) i
  rw [List.drop_eq_getElem_cons (by rwa [List.length_map]), List.sum_cons, List.getElem_map] at e
  rw [frame_length, frameStart, List.map_take]
  omega

/-- Read the sections back through the directory. -/
def unframe (t : List Word) : List (List Word) :=
  (List.range (t.getD 0 0).toNat).map fun i =>
    ((t.drop (t.getD (1 + 2 * i) 0).toNat).take (t.getD (2 + 2 * i) 0).toNat)

/-- **The directory determines the sections** (for a tape shorter than `2^64` words). -/
theorem unframe_frame (secs : List (List Word)) (h : (frame secs).length < 2 ^ 64) :
    unframe (frame secs) = secs := by
  have hN : secs.length < 2 ^ 64 := by rw [frame_length] at h; omega
  have toNat_toWord : ∀ a, a < 2 ^ 64 → (toWord a).toNat = a := fun _ => Nat.mod_eq_of_lt
  refine List.ext_getElem (by simp only [unframe, List.length_map, List.length_range,
    frame_getD_count, toNat_toWord _ hN]) fun i h1 h2 => ?_
  have hb := frameStart_add_le secs h2
  simp only [unframe, frame_getD_count, List.getElem_map, List.getElem_range]
  rw [frame_getD_start secs h2, frame_getD_len secs h2, toNat_toWord _ (by omega),
    toNat_toWord _ (by omega), frame_drop, List.drop_eq_getElem_cons h2, List.flatten_cons,
    List.take_left' rfl]

/-- **Round trip of the extractor's input tape**: its directory returns the sections `[j]`, `L`,
`x`, the rounds and `w` (for a tape shorter than `2^64` words). -/
theorem unframe_extractorTape (j : ℕ) (s : Layout K × Stmt) (rounds : List (List Word))
    (w : List Word) (h : (extractorTape j s rounds w).length < 2 ^ 64) :
    unframe (extractorTape j s rounds w) =
      [toWord j] :: s.1.words :: List.ofFn (fun i => (s.2 i).bits) :: rounds ++ [w] :=
  unframe_frame _ h

/-- `readWords` reads `n` words. -/
theorem length_readWords (s : MachineState) (base : Word) (n : ℕ) :
    (s.readWords base n).length = n := by
  simp [readWords_eq]

/-! ## Codec bridge: the contract's word encodings are `Library/Codec.lean`'s -/

section Codec
open Codec

theorem Table.words_eq (c : ℕ) (T : Table K) : T.words c = (eTable c T).map K.bits := by
  simp [Table.words, eTable, toWord, Codec.ofNat]

private theorem eMat_bits {m n : ℕ} (M : List (Fin m × Fin n × K)) :
    (eMat M).map K.bits =
      toWord M.length :: M.flatMap fun e => [toWord e.1, toWord e.2.1, e.2.2.bits] := by
  simp only [eMat, List.map_cons, List.map_flatten, List.map_map, List.flatMap_def]
  rfl

private theorem eS_bits {t : ℕ} (S : List (Fin t)) :
    (eS S).map K.bits = toWord S.length :: S.map fun j => toWord j.val := by
  simp only [eS, List.map_cons, List.map_map]; rfl

private theorem ePort_bits (p : Port) :
    (ePort p).map K.bits =
      [p.bus, if p.send then 1 else 0, p.sel, p.msg.length].map toWord ++ p.msg.map toWord := by
  cases h : p.send <;> simp only [ePort, h, List.map_append, List.map_cons, List.map_map] <;> rfl

private theorem eFixed_bits (c : ℕ) (f : Option (Table K)) :
    (eFixed c f).map K.bits = f.elim [0] fun T => 1 :: T.words c := by
  cases f <;> simp only [eFixed, Option.elim, List.map_cons, Table.words_eq] <;> rfl

theorem Chip.words_eq (C : Chip K) : C.words = (eChip C).map K.bits := by
  simp only [Chip.words, eChip, eGadget, List.map_cons, List.map_append, List.map_flatten,
    List.map_map, List.cons_append, List.nil_append, List.append_assoc, List.flatMap_def,
    Function.comp_def, eMat_bits, eS_bits, ePort_bits, eFixed_bits]
  rfl

/-- The layout's words are `eLayout`'s elements. -/
theorem Layout.words_eq (L : Layout K) : L.words = (eLayout L).map K.bits := by
  simp only [Layout.words, eLayout, List.map_append, List.map_cons, List.map_nil, List.map_map,
    List.flatMap_def, List.map_flatten, Function.comp_def, ← Chip.words_eq]
  congr 2
  refine List.map_congr_left fun b _ => ?_
  split <;> rfl

/-- **Round trip of the layout section**: an admissible layout of class `k ≤ 28` parses back
from its words to itself, up to what `rel` does not read (`Codec.pLayout_eLayout`). -/
theorem pLayout_words {k : ℕ} (hk : k ≤ 28) {L : Layout K} (h : L.Admissible k) (rest : List K) :
    pLayout (L.words.map K.mk ++ rest) = (L.normal (2 ^ 8), rest) := by
  rw [Layout.words_eq, List.map_map, show K.mk ∘ K.bits = id from rfl, List.map_id]
  exact pLayout_eLayout hk h rest

/-- The layout section has at most `2^(k+8)` words (`Codec.eLayout_length`). -/
theorem Layout.words_length {k : ℕ} (hk : 20 ≤ k) {L : Layout K} (h : L.Admissible k) :
    L.words.length ≤ 2 ^ (k + 8) := by
  rw [Layout.words_eq, List.length_map]; exact eLayout_length hk h

private theorem pMany_pK_eq (n : ℕ) (l : List K) :
    pMany pK n l = (List.ofFn fun i : Fin n => l.getD i 0, l.drop n) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => cases l <;> simp [pMany, pK, ih, List.ofFn_succ]

/-- **The round-0 decoder is `Codec.pWit`** on the elements the words denote. -/
theorem decTables_map_bits (cols : List ℕ) (l : List K) :
    decTables cols (l.map K.bits) = (pWit cols l).1 := by
  have hget : ∀ (l' : List K) (n : ℕ), (⟨(l'.map K.bits).getD n 0⟩ : K) = l'.getD n 0 := by
    intro l' n; simp only [List.getD_eq_getElem?_getD, List.getElem?_map]; cases l'[n]? <;> rfl
  induction cols generalizing l with
  | nil => rfl
  | cons c cs ih =>
    cases l with
    | nil => simpa [decTables, pWit, pTable, pNat, pMany_pK_eq] using ih []
    | cons a l =>
      simp only [decTables, pWit, pTable, pNat, pMany_pK_eq, List.map_cons, List.headD_cons,
        List.tail_cons, ← List.map_drop]
      refine congrArg₂ _ (congrArg (Table.mk _) (funext₂ fun r i => ite_congr rfl (fun h => ?_)
        fun _ => rfl)) (ih _)
      have hq : r * c + i < toNat a * c := by
        have := Nat.mul_le_mul_right c (h.1 : r + 1 ≤ toNat a)
        rw [Nat.succ_mul] at this; omega
      rw [hget, List.getD_eq_getElem (List.ofFn _) _ (by simpa using hq), List.getElem_ofFn]

end Codec

/-! ## The first-message image -/

/-- `tests/asm/section3.S`: output tape section 3, the first transcript round, in place (8
instructions). The extractor of a protocol that sends the witness tables in round 0, in the
format `Table.words` (the toy, `Controls/Toy.lean`; the trivial baseline, DESIGN §7.3). -/
def firstMsgImg : Image :=
  ⟨[0x00100313, 0x03f31313, 0x03833503, 0x04033583, 0x00351513, 0x00650533, 0x00000293,
    0x00000073], []⟩

/-- The first-message image with the whole budget on the call before round 0, which is the only
call it needs. -/
def firstMsgImage (k n : ℕ) : ExtractorImage k n := .atZero firstMsgImg (by decide) k n

/-- The decoded program: `t1 := 2^63; a0 := tape[7]; a1 := tape[8]; a0 := 8·a0 + t1; HALT`. -/
private def fmProg : List Instruction :=
  [.base (.ADDI .x6 .x0 1), .base (.SLLI .x6 .x6 63), .base (.LD .x10 .x6 56),
   .base (.LD .x11 .x6 64), .base (.SLLI .x10 .x10 3), .base (.ADD .x10 .x10 .x6),
   .base (.ADDI .x5 .x0 0), .base .ECALL]

private theorem fm_fetch (s : MachineState) (idx : ℕ) (hidx : idx < 8)
    (hpc : s.pc = BitVec.ofNat 64 (CODE_BASE + 4 * idx)) :
    fetch firstMsgImg s = fmProg[idx]? := by
  rw [fetch_eq idx (by simp [CODE_BASE]; omega) hpc]
  interval_cases idx <;> rfl

/-- **The first-message image on any tape**: it outputs the `tape[8]` words from tape word
`tape[7]` on, in 8 steps, if they are addressable. -/
theorem run_firstMsgImage (t : List Word) (f : ℕ)
    (h : (t.getD 7 0).toNat + (t.getD 8 0).toNat < 2 ^ 60) :
    run firstMsgImg t (f + 8) =
      some ((List.range (t.getD 8 0).toNat).map fun j => t.getD ((t.getD 7 0).toNat + j) 0) := by
  unfold run
  rw [execute_step _ (fm_fetch _ 0 (by omega) rfl) rfl]
  simp [execInstrBr, signExtend12, CODE_BASE]
  rw [execute_step _ (fm_fetch _ 1 (by omega) (by simp [CODE_BASE])) rfl]
  simp [execInstrBr]
  rw [execute_step _ (fm_fetch _ 2 (by omega) (by simp [CODE_BASE]))
    (ordinaryStep_ld (by simp [signExtend12]))]
  simp [signExtend12, TAPE_BASE, getMem_initState]
  rw [execute_step _ (fm_fetch _ 3 (by omega) (by simp [CODE_BASE]))
    (ordinaryStep_ld (by simp [signExtend12]))]
  simp [signExtend12, TAPE_BASE, getMem_initState]
  rw [execute_step _ (fm_fetch _ 4 (by omega) (by simp [CODE_BASE])) rfl]
  simp [execInstrBr]
  rw [execute_step _ (fm_fetch _ 5 (by omega) (by simp [CODE_BASE])) rfl]
  simp [execInstrBr]
  rw [execute_step _ (fm_fetch _ 6 (by omega) (by simp [CODE_BASE])) rfl]
  simp [execInstrBr, signExtend12]
  simp only [List.getD_eq_getElem?_getD] at h
  generalize t[7]?.getD 0#64 = a at h ⊢
  generalize t[8]?.getD 0#64 = b at h ⊢
  have ha : (a <<< 3 + 9223372036854775808#64).toNat = 2 ^ 63 + 8 * a.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
    omega
  have h10 : ∀ s : MachineState, s.getReg .x10 = a <<< 3 + 9223372036854775808#64 →
      (s.getReg .x10).toNat % 8 = 0 := fun s hs => by rw [hs, ha]; omega
  rw [execute_halt _ (fm_fetch _ 7 (by omega) (by simp [CODE_BASE])) (by simp) (h10 _ (by simp))]
  have fin : ∀ s : MachineState, s.getReg .x10 = a <<< 3 + 9223372036854775808#64 →
      s.getReg .x11 = b → (∀ x, s.getMem x = (initState firstMsgImg t).getMem x) →
      readOut s = (List.range b.toNat).map fun j => t[a.toNat + j]?.getD 0#64 := by
    intro s hx10 hx11 hm
    rw [readOut, readWords_eq, hx10, hx11]
    refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    have hj' : (a <<< 3 + 9223372036854775808#64 + BitVec.ofNat 64 (8 * j)).toNat =
        2 ^ 63 + 8 * (a.toNat + j) := by
      rw [BitVec.toNat_add, ha, BitVec.toNat_ofNat]; omega
    rw [hm, getMem_initState, hj', ite_eq_left (by simp [TAPE_BASE])]
    simp [TAPE_BASE, List.getD_eq_getElem?_getD]
  rw [fin _ (by simp) (by simp) (by simp)]

private theorem toNat_toWord {a : ℕ} (h : a < 2 ^ 64) : (toWord a).toNat = a := Nat.mod_eq_of_lt h

/-- **The first-message image on a framed tape** outputs section 3. -/
theorem run_firstMsgImage_frame (secs : List (List Word)) (h3 : 3 < secs.length)
    (hb : frameStart secs 3 + secs[3].length < 2 ^ 60) (f : ℕ) :
    run firstMsgImg (frame secs) (f + 8) = some secs[3] := by
  have h7 := frame_getD_start secs h3
  have h8 := frame_getD_len secs h3
  simp only [show 1 + 2 * 3 = 7 from rfl, show 2 + 2 * 3 = 8 from rfl] at h7 h8
  rw [run_firstMsgImage _ _
      (by rw [h7, h8, toNat_toWord (by omega), toNat_toWord (by omega)]; omega),
    h7, h8, toNat_toWord (by omega), toNat_toWord (by omega)]
  congr 1
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  exact frame_getD_sec secs h3 h2

/-- **The first-message image on an extractor tape** outputs the first round's words. -/
theorem run_firstMsgImage_tape (j : ℕ) (s : Layout K × Stmt) (r0 : List Word)
    (R : List (List Word)) (w : List Word) (f : ℕ)
    (hb : 2 * R.length + s.1.words.length + r0.length + 46 < 2 ^ 60) :
    run firstMsgImg (extractorTape j s (r0 :: R) w) (f + 8) = some r0 := by
  refine run_firstMsgImage_frame _ (by simp) ?_ f
  simp [frameStart]
  omega

/-- **The first-message extractor**: before round `m`, it returns the first round's words,
decoded (as the witness tables if `m = 0`), when they fit. -/
theorem firstMsg_extractMid (k : ℕ) {n : ℕ} (sh : Fin n → Round) (m : Fin n)
    (s : Layout K × Stmt) (tr : Transcript sh m.succ) (w : Mid n m.succ)
    (hb : 2 * m.val + s.1.words.length + (Round.words _ (tr (0 : Fin (m.val + 1)))).length + 46 <
      2 ^ 60)
    (hc : (Round.words _ (tr (0 : Fin (m.val + 1)))).length ≤ witCap k)
    (E : ExtractorImage k n) (hE : E.img = firstMsgImg) (hf : 8 ≤ E.fuel m.castSucc) :
    (E.toExtractor sh).extractMid m s tr w =
      decMid s.1 m.castSucc (Round.words _ (tr (0 : Fin (m.val + 1)))) := by
  refine E.extractMid_eq_of_run sh (run_mono (f := 0 + 8) ?_ hf) hc
  rw [hE]
  show run _ (extractorTape _ _ (List.ofFn fun i : Fin (m.val + 1) => _) _) _ = _
  rw [List.ofFn_succ]
  exact run_firstMsgImage_tape _ _ _ _ _ 0 (by simpa using hb)

end RecursionFast
