/-
  RecursionFast.Library.WitnessSending  (UNTRUSTED, kernel-checked)

  **The witness-sending argument** (DESIGN-v3 §7.3, V3-9): the proof is the witness, the
  verifier decides the relation directly with no oracle query, and the extractor reads the
  witness off the proof. It is a complete `Certificate` (`certificate`), the positive control of
  every clause of the contract's certificate, and the argument of the baseline entry (Stage S2,
  in the submissions repository, DESIGN-v3 §7.7).

  * **Proof format.** `encode w` is the bytes of the extractor output words of `w` (`witWords`,
    `Library/Words.lean`), so a proof packs back to exactly the words that denote its witness
    (`decode_encode`).
  * **Verifier.** `check c π`: `π` decodes to a leaf witness of at most `chainCap` steps
    (checked first) whose chain ends at the statement's chain end, or to a node witness whose
    statement is `nodeStmt c₁ c₂` and whose children are accepted by the instantiated verifier,
    recursively (each child at most `proofCap` bytes). A node proof must be the canonical
    encoding, so its children are shorter and the recursion terminates. `V c π := ret (check c π)`:
    no query, `qV = 0`.
  * **Prover.** `P c w := ret (encode w)`. Every witness of the relation fits the format
    (`fits_of_rel`: a leaf's length is at most `chainCap`, a node's children within `proofCap`),
    so completeness needs no normalisation and no unbounded encoding (V3-S1-A20).
  * **Extractor.** `E c π L := decode π`, and the image `img` (`tests/asm/proofwords.S`, 8
    instructions) outputs the proof's packed words in place (`run_img`), so it computes `E` in 8
    steps on every input (`computes`).
  * **Security.** `KS` with the potential `μ := 0`, `ε = 0`, `qV = 0` (`ks`, `KState.zero`): an
    accepted proof decodes to a witness of the relation, by the definition of `check`
    (`check_sound`), on every log.
-/
import RecursionFast.Contract.Certificate
import RecursionFast.Library.Words
import RecursionFast.Library.Machine
import RecursionFast.Library.Security

open scoped NNReal

namespace RecursionFast.WitnessSending
open RiscvZkvm.Rv64 (MachineState Instr Reg execInstrBr signExtend12)

/-! ## Proof format -/

/-- The proof that sends the witness `w`: the bytes of its output words. -/
def encode (w : Wit) : Proof := ⟨(wordsBytes (witWords w)).toArray⟩

/-- The witness a proof sends: its packed words, read as an extractor output. -/
def decode (π : Proof) : Option Wit := decodeWit (packBytes π.data.toList)

theorem encode_data (w : Wit) : (encode w).data.toList = wordsBytes (witWords w) := rfl

theorem decode_encode (w : Wit) (h : w.Fits) : decode (encode w) = some w := by
  rw [decode, encode_data, packBytes_wordsBytes, decodeWit_witWords w h]

theorem size_encode (w : Wit) : (encode w).size = 8 * (witWords w).length := by
  rw [← wordsBytes_length, ← encode_data, Array.length_toList]; rfl

theorem size_eq_length (π : Proof) : π.size = π.data.toList.length := Array.length_toList.symm

theorem size_encode_leaf (s : Digest) (n : ℕ) : (encode (.leaf s n)).size = 48 := by
  rw [size_encode]; simp [witWords, packBytes_digest_length]

/-! ## The argument -/

/-- **The witness-sending decision**: `π` decodes to a leaf witness of `c` (its length within
`chainCap`, checked before any hash), or is the canonical encoding of a node witness of `c` whose
two children (each at most `proofCap` bytes) are accepted, recursively. -/
def check (c : Digest) (π : Proof) : Bool :=
  match decode π with
  | some (.leaf s n) => decide (n ≤ chainCap) && decide (c = leafStmt (chainEnd s n) n)
  | some (.node c₁ c₂ π₁ π₂) =>
    if _h : encode (.node c₁ c₂ π₁ π₂) = π then
      decide (c = nodeStmt c₁ c₂) && (decide (π₁.size ≤ proofCap) && check c₁ π₁) &&
        (decide (π₂.size ≤ proofCap) && check c₂ π₂)
    else false
  | none => false
termination_by π.size
decreasing_by
  all_goals
    rw [← _h, size_encode]
    simp only [witWords, bytesWords, List.length_cons, List.length_append, packBytes_length,
      ← size_eq_length]
    omega

/-- The verifier: `check`, with no oracle query. -/
def V (c : Digest) (π : Proof) : OProg Bool := .ret (check c π)

/-- The honest prover: send the witness. -/
def P (_ : Digest) (w : Wit) : OProg Proof := .ret (encode w)

/-- The extractor's specification: the witness the proof sends. -/
def E (_ : Digest) (π : Proof) (_ : Log) : Option Wit := decode π

/-- The extractor image (`tests/asm/proofwords.S`): `t1 := 2^63; a1 := tape[4] (|π|);
a1 := (a1 + 7) >> 3; a0 := t1 + 40 (tape word 5); HALT`, i.e. output the proof's packed words in
place. -/
def img : Image :=
  ⟨[0x00100313, 0x03f31313, 0x02033583, 0x00758593, 0x0035d593, 0x02830513, 0x00000293,
    0x00000073], []⟩

/-- The extractor's fuel: 8 steps on every input. -/
def fuel (_ : ℕ) : ℕ := 8

/-- **The witness-sending submission**: error `0`, no verifier query, fuel 8. -/
def submission : Submission where
  V := V
  P := P
  E := E
  img := img
  ε := 0
  qV := 0
  fuel := fuel

/-! ## The instantiated verifier and the relation -/

theorem Vb_eq (c : Digest) (π : Proof) :
    submission.Vb c π = (decide (π.size ≤ proofCap) && check c π) := by
  simp [Submission.Vb, submission, V, OProg.run]

theorem size_le_of_Vb {c : Digest} {π : Proof} (h : submission.Vb c π = true) :
    π.size ≤ proofCap := by
  rw [Vb_eq, Bool.and_eq_true] at h; exact of_decide_eq_true h.1

/-- On a leaf proof, `check` decides the leaf clause. -/
theorem check_leaf (c s : Digest) {n : ℕ} (hn : n < 2 ^ 64) :
    check c (encode (.leaf s n)) =
      (decide (n ≤ chainCap) && decide (c = leafStmt (chainEnd s n) n)) := by
  unfold check; rw [decode_encode (.leaf s n) hn]

/-- **An accepted proof decodes to a witness of the relation.** -/
theorem check_sound {c : Digest} {π : Proof} (h : check c π = true) :
    ∃ w, decode π = some w ∧ Rel submission.Vb c w := by
  unfold check at h
  split at h
  next s n hd =>
    rw [Bool.and_eq_true] at h
    exact ⟨.leaf s n, hd, of_decide_eq_true h.1, of_decide_eq_true h.2⟩
  next c₁ c₂ π₁ π₂ hd =>
    split at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      refine ⟨.node c₁ c₂ π₁ π₂, hd, h.1.1, ?_, ?_⟩ <;> rw [Vb_eq] <;> simp [h]
    · cases h
  · cases h

/-- Every witness of the relation fits the output format. -/
theorem fits_of_rel {c : Digest} {w : Wit} (h : Rel submission.Vb c w) : w.Fits := by
  cases w with
  | leaf s n => exact h.1.trans_lt (by decide)
  | node c₁ c₂ π₁ π₂ => exact ⟨size_le_of_Vb h.2.1, size_le_of_Vb h.2.2⟩

/-- **The honest proof of a witness is accepted.** -/
theorem check_encode {c : Digest} {w : Wit} (hR : Rel submission.Vb c w) (hf : w.Fits) :
    check c (encode w) = true := by
  unfold check
  rw [decode_encode w hf]
  cases w with
  | leaf s n => simp [hR.1, hR.2]
  | node c₁ c₂ π₁ π₂ =>
    obtain ⟨hc, h₁, h₂⟩ := hR
    rw [Vb_eq] at h₁ h₂
    simp_all

/-! ## The certificate -/

/-- The knowledge state: the potential `0` (every accepted proof decodes to a witness). -/
def kstate : KState (Rel submission.Vb) V E 0 :=
  KState.zero 0 fun _ _ _ h => check_sound (Option.some.inj h)

/-- **Knowledge soundness** at error `0` with no verifier query. -/
theorem ks : KS (Rel submission.Vb) submission.V submission.E submission.ε submission.qV :=
  ⟨⟨kstate⟩, fun _ _ _ => le_rfl⟩

/-- **Perfect completeness**, for every oracle function. -/
theorem complete : Complete (Rel submission.Vb) submission.P submission.V :=
  fun _ _ _ hR => check_encode hR (fits_of_rel hR)

/-- The decoded program of `img`. -/
private def prog : List Instruction :=
  [.base (.ADDI .x6 .x0 1), .base (.SLLI .x6 .x6 63), .base (.LD .x11 .x6 32),
   .base (.ADDI .x11 .x11 7), .base (.SRLI .x11 .x11 3), .base (.ADDI .x10 .x6 40),
   .base (.ADDI .x5 .x0 0), .base .ECALL]

private theorem img_fetch (s : MachineState) (idx : ℕ) (hidx : idx < 8)
    (hpc : s.pc = BitVec.ofNat 64 (CODE_BASE + 4 * idx)) : fetch img s = prog[idx]? := by
  rw [fetch_eq idx (by simp [CODE_BASE]; omega) hpc]
  interval_cases idx <;> rfl

/-- **The image on any tape** whose word 4 is at most `2^20`: it outputs the `⌈tape[4] / 8⌉`
words from tape word 5 on, in 8 steps. -/
theorem run_img (t : List Word) (f : ℕ) (h : (t.getD 4 0).toNat ≤ 2 ^ 20) :
    run img t (f + 8) =
      some ((List.range (((t.getD 4 0).toNat + 7) / 8)).map fun j => t.getD (5 + j) 0) := by
  unfold run
  rw [execute_step _ (img_fetch _ 0 (by omega) rfl) rfl]
  simp [execInstrBr, signExtend12, CODE_BASE]
  rw [execute_step _ (img_fetch _ 1 (by omega) (by simp [CODE_BASE])) rfl]
  simp [execInstrBr]
  rw [execute_step _ (img_fetch _ 2 (by omega) (by simp [CODE_BASE]))
    (ordinaryStep_ld (by simp [signExtend12]))]
  simp [signExtend12, TAPE_BASE, getMem_initState]
  rw [execute_step _ (img_fetch _ 3 (by omega) (by simp [CODE_BASE])) rfl]
  simp [execInstrBr, signExtend12]
  rw [execute_step _ (img_fetch _ 4 (by omega) (by simp [CODE_BASE])) rfl]
  simp [execInstrBr]
  rw [execute_step _ (img_fetch _ 5 (by omega) (by simp [CODE_BASE])) rfl]
  simp [execInstrBr, signExtend12]
  rw [execute_step _ (img_fetch _ 6 (by omega) (by simp [CODE_BASE])) rfl]
  simp [execInstrBr, signExtend12]
  rw [execute_halt _ (img_fetch _ 7 (by omega) (by simp [CODE_BASE])) (by simp) (by simp)]
  simp only [List.getD_eq_getElem?_getD] at h
  generalize t[4]?.getD 0#64 = a at h ⊢
  have hn : ((a + 7#64) >>> 3).toNat = (a.toNat + 7) / 8 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    congr 1
    omega
  have fin : ∀ s : MachineState, s.getReg .x10 = 9223372036854775848#64 →
      s.getReg .x11 = (a + 7#64) >>> 3 → (∀ x, s.getMem x = (initState img t).getMem x) →
      readOut s = (List.range ((a.toNat + 7) / 8)).map fun j => t[5 + j]?.getD 0#64 := by
    intro s hx10 hx11 hm
    rw [readOut, readWords_eq, hx10, hx11, hn]
    refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    have hj' : (9223372036854775848#64 + BitVec.ofNat 64 (8 * j)).toNat =
        2 ^ 63 + 8 * (5 + j) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    rw [hm, getMem_initState, hj', ite_eq_left (by simp [TAPE_BASE])]
    simp [TAPE_BASE, List.getD_eq_getElem?_getD]
  rw [fin _ (by simp) (by simp) (by simp)]

theorem extractorInput_eq (c : Digest) (π : Proof) (L : Log) :
    extractorInput c π L = (packBytes c.toList ++ [toWord π.size]) ++ packBytes π.data.toList ++
      (toWord L.length ::
        L.flatMap fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList) := by
  unfold extractorInput bytesWords
  rw [size_eq_length]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- **The image computes the extractor** in 8 steps on every input. -/
theorem computes : ImageComputes submission.img submission.E submission.fuel := by
  intro c π L hπ _
  have h4 := packBytes_digest_length c
  have h5 : (packBytes c.toList ++ [toWord π.size]).length = 5 := by simp [h4]
  have hm : (packBytes π.data.toList).length = (π.size + 7) / 8 := by simp [packBytes_length]
  have g4 : ((extractorInput c π L).getD 4 0).toNat = π.size := by
    rw [extractorInput_eq, List.append_assoc, List.append_assoc, List.singleton_append,
      show 4 = (packBytes c.toList).length from h4.symm, getD_append_length,
      toNat_toWord (lt_of_le_of_lt hπ (by decide))]
  refine ⟨packBytes π.data.toList, ?_, ?_, rfl⟩
  · show run img _ (0 + 8) = _
    rw [run_img _ 0 (by rw [g4]; exact hπ), g4]
    congr 1
    refine List.ext_getElem (by simp [hm]) fun j _ h2 => ?_
    rw [List.getElem_map, List.getElem_range, extractorInput_eq, show 5 + j =
      (packBytes c.toList ++ [toWord π.size]).length + j by rw [h5], getD_append_mid _ _ _ h2]
  · unfold outCap proofCap at *
    omega

/-- **The witness-sending submission is certified.** -/
theorem certificate : Certificate submission where
  secure := ks
  complete := complete
  computes := computes
  cap := ⟨zero_le, Nat.zero_le _, fun _ => Nat.le_add_right_of_le (by decide : 8 ≤ 2 ^ 40),
    by decide⟩

end RecursionFast.WitnessSending
