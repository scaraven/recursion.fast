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
  * **Verifier (strict, #10, V3-S2R-A5).** `check c π`: `π` is the canonical encoding of a leaf
    witness of at most `chainCap` steps (checked before the hash) whose chain ends at the
    statement's chain end, or of a node witness whose statement is `nodeStmt c₁ c₂` and whose
    children are accepted by the instantiated verifier, recursively (each child at most `proofCap`
    bytes). Requiring the canonical encoding for leaves as well as nodes is what makes it reject the
    benchmark's appended-byte and truncated canaries (`check_canonical`; the S1 form accepted
    malleated leaves). It decodes with the linear-time twins `decodeF`, `encodeF` (`decodeF_eq`,
    `encodeF_eq`; `check_eq` states it with the specification functions). `V c π := ret
    (check c π)`: no query, `qV = 0`.
  * **Prover.** `P c w := ret (encode w)`. Every witness of the relation fits the format
    (`fits_of_rel`), so perfect completeness needs no normalisation (`complete_perfect`); the
    certificate's completeness is at `δ = 0` through `complete_withError_zero`.
  * **Extractor.** `E c π L := decode π`, and the program `ext` (5 memory words, 21 statements)
    copies the proof's packed words from the input tape to the output, one loop iteration of 8
    steps per word (`ext_exec`), so it computes `E` within `fuel t = 8 · t` steps (`computes`).
  * **Security.** `KS` with the potential `μ := 0`, `ε = 0`, `qV = 0` (`ks`, `KState.zero`): an
    accepted proof decodes to a witness of the relation, by the definition of `check`
    (`check_sound`), on every log.
-/
import RecursionFast.Contract.Certificate
import RecursionFast.Library.Words
import RecursionFast.Library.Machine
import RecursionFast.Library.Security
import RecursionFast.Library.Completeness

open scoped NNReal

namespace RecursionFast.WitnessSending
open RecursionFast XStmt

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

/-- `decode` in linear time (`decodeF_eq`). -/
def decodeF (π : Proof) : Option Wit := decodeWitF (packFast π.data.toList)

theorem decodeF_eq (π : Proof) : decodeF π = decode π := by
  rw [decodeF, decodeWitF_eq, packFast_eq]; rfl

/-- `encode` in linear time (`encodeF_eq`). -/
def encodeF (w : Wit) : Proof := ⟨(wordsBytes (witWordsF w)).toArray⟩

theorem encodeF_eq (w : Wit) : encodeF w = encode w := by
  rw [encodeF, witWordsF_eq]; rfl

/-! ## The argument -/

/-- **The strict witness-sending decision**: `π` is the canonical encoding of a leaf witness of
`c` (its length within `chainCap`, checked before any hash), or of a node witness of `c` whose two
children (each at most `proofCap` bytes) are accepted, recursively. -/
def check (c : Digest) (π : Proof) : Bool :=
  match decodeF π with
  | some (.leaf s n) =>
    decide (encodeF (.leaf s n) = π) && decide (n ≤ chainCap) &&
      decide (c = leafStmt (chainEnd s n) n)
  | some (.node c₁ c₂ π₁ π₂) =>
    if _h : encodeF (.node c₁ c₂ π₁ π₂) = π then
      decide (c = nodeStmt c₁ c₂) && (decide (π₁.size ≤ proofCap) && check c₁ π₁) &&
        (decide (π₂.size ≤ proofCap) && check c₂ π₂)
    else false
  | none => false
termination_by π.size
decreasing_by
  all_goals
    rw [← _h, encodeF_eq, size_encode]
    simp only [witWords, bytesWords, List.length_cons, List.length_append, packBytes_length,
      ← size_eq_length]
    omega

/-- The verifier: `check`, with no oracle query. -/
def V (c : Digest) (π : Proof) : OProg Bool := .ret (check c π)

/-- The honest prover: send the witness. -/
def P (_ : Digest) (w : Wit) : OProg Proof := .ret (encode w)

/-- The extractor's specification: the witness the proof sends. -/
def E (_ : Digest) (π : Proof) (_ : Log) : Option Wit := decode π

/-- One loop iteration: read tape word `M[0]` into `M[3]`, output it, `M[0] += 1`,
`M[2] := M[0] < M[1]`. -/
def step : XStmt := .seq (.input 3 0) (.seq (.out 3) (.seq (.op .add 0 0 4) (.op .ltu 2 0 1)))

/-- Set up the loop: `M[1] := ⌈tape[4] / 8⌉ + 5` (the end of the proof's words), `M[0] := 5`,
`M[4] := 1`, `M[2] := M[0] < M[1]`. -/
def pre : XStmt := seqs (.const 0 4) [.input 1 0, .const 3 7, .op .add 1 1 3, .const 3 3,
  .op .shr 1 1 3, .const 0 5, .op .add 1 1 0, .const 4 1, .op .ltu 2 0 1]

/-- **The extractor program**: output the proof's packed words (tape words `5 … 4 + ⌈|π|/8⌉`). -/
def ext : XProg := ⟨5, .seq pre (.loop 2 step)⟩

/-- The extractor's fuel: 8 steps per tape word. -/
def fuel (t : ℕ) : ℕ := 8 * t

/-- **The witness-sending submission**: errors `0`, no verifier query, fuel `8 · t`. -/
def submission : Submission where
  V := V
  P := P
  E := E
  ext := ext
  ε := 0
  δ := 0
  qV := 0
  fuel := fuel

/-! ## The instantiated verifier and the relation -/

theorem Vb_eq (c : Digest) (π : Proof) :
    submission.Vb c π = (decide (π.size ≤ proofCap) && check c π) := by
  simp [Submission.Vb, submission, V, OProg.run]

theorem size_le_of_Vb {c : Digest} {π : Proof} (h : submission.Vb c π = true) :
    π.size ≤ proofCap := by
  rw [Vb_eq, Bool.and_eq_true] at h; exact of_decide_eq_true h.1

/-- `check`, with the specification functions `decode` and `encode`. -/
theorem check_eq (c : Digest) (π : Proof) : check c π =
    match decode π with
    | some (.leaf s n) =>
      decide (encode (.leaf s n) = π) && decide (n ≤ chainCap) &&
        decide (c = leafStmt (chainEnd s n) n)
    | some (.node c₁ c₂ π₁ π₂) =>
      if encode (.node c₁ c₂ π₁ π₂) = π then
        decide (c = nodeStmt c₁ c₂) && (decide (π₁.size ≤ proofCap) && check c₁ π₁) &&
          (decide (π₂.size ≤ proofCap) && check c₂ π₂)
      else false
    | none => false := by
  rw [check, decodeF_eq]
  simp only [encodeF_eq, dite_eq_ite]

/-- On a leaf proof, `check` decides the leaf clause. -/
theorem check_leaf (c s : Digest) {n : ℕ} (hn : n < 2 ^ 64) :
    check c (encode (.leaf s n)) =
      (decide (n ≤ chainCap) && decide (c = leafStmt (chainEnd s n) n)) := by
  rw [check_eq, decode_encode (.leaf s n) hn]; simp

/-- **Strictness**: an accepted proof is the canonical encoding of the witness it decodes to. -/
theorem check_canonical {c : Digest} {π : Proof} (h : check c π = true) :
    ∃ w, decode π = some w ∧ encode w = π := by
  rw [check_eq] at h
  split at h
  next s n hd =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨_, hd, h.1.1⟩
  next c₁ c₂ π₁ π₂ hd =>
    split at h
    · exact ⟨_, hd, ‹_›⟩
    · cases h
  · cases h

/-- **An accepted proof decodes to a witness of the relation.** -/
theorem check_sound {c : Digest} {π : Proof} (h : check c π = true) :
    ∃ w, decode π = some w ∧ Rel submission.Vb c w := by
  rw [check_eq] at h
  split at h
  next s n hd =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨.leaf s n, hd, h.1.2, h.2⟩
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

/-- **The honest proof of a witness of the relation is accepted.** -/
theorem check_encode {c : Digest} {w : Wit} (hR : Rel submission.Vb c w) :
    check c (encode w) = true := by
  rw [check_eq, decode_encode w (fits_of_rel hR)]
  cases w with
  | leaf s n => simp [hR.1, hR.2]
  | node c₁ c₂ π₁ π₂ =>
    obtain ⟨hc, h₁, h₂⟩ := hR
    rw [Vb_eq] at h₁ h₂
    simp_all

/-- **What the verifier decides**: a proof is accepted exactly when it is within `proofCap` and is
the canonical encoding of a witness of the relation. -/
theorem Vb_iff (c : Digest) (π : Proof) : submission.Vb c π = true ↔
    π.size ≤ proofCap ∧ ∃ w, decode π = some w ∧ encode w = π ∧ Rel submission.Vb c w := by
  rw [Vb_eq, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨fun ⟨hs, h⟩ => ⟨hs, ?_⟩, fun ⟨hs, w, _, he, hR⟩ => ⟨hs, he ▸ check_encode hR⟩⟩
  obtain ⟨w, hd, he⟩ := check_canonical h
  obtain ⟨w', hd', hR⟩ := check_sound h
  rw [hd] at hd'; cases hd'
  exact ⟨w, hd, he, hR⟩

/-! ## Knowledge soundness and completeness -/

/-- The knowledge state: the potential `0` (every accepted proof decodes to a witness). -/
def kstate : KState (Rel submission.Vb) V E 0 :=
  KState.zero 0 fun _ _ _ h => check_sound (Option.some.inj h)

/-- **Knowledge soundness** at error `0` with no verifier query. -/
theorem ks : KS (Rel submission.Vb) submission.V submission.E submission.ε submission.qV :=
  ⟨⟨kstate⟩, fun _ _ _ => le_rfl⟩

/-- **Perfect completeness**, for every oracle function. -/
theorem complete_perfect : Complete (Rel submission.Vb) submission.P submission.V :=
  fun _ _ _ hR => check_encode hR

/-- **Completeness at error `0`.** -/
theorem complete :
    CompleteWithError (Rel submission.Vb) submission.P submission.V submission.δ :=
  complete_withError_zero complete_perfect

/-! ## The extractor program -/

/-- The loop's memory after `i` of `m` words: the next tape index, the end index, the loop
condition, the last word read and the constant `1`. -/
def st (m i : ℕ) (y : Word) : Array Word :=
  #[toWord (i + 5), toWord (m + 5), if i < m then 1 else 0, y, 1]

/-- The set-up block, from the zero memory, in 19 steps. -/
theorem pre_exec (I : Array Word) (n : ℕ) (o : Array Word) (ks : List XStmt) :
    exec I (n + 19) (Array.replicate 5 0) o (pre :: ks) =
      exec I n #[5, (I.getD 4 0 + 7) >>> 3 + 5,
        if (5 : Word) < (I.getD 4 0 + 7) >>> 3 + 5 then 1 else 0, 3, 1] o ks := by
  rw [show Array.replicate 5 (0 : Word) = #[0, 0, 0, 0, 0] from rfl]
  simp [pre, seqs, exec, XOp.eval]

/-- **The copy loop**: from word `i` of `m`, `k = m - i` iterations of 8 steps output tape words
`i + 5, …, m + 4`. -/
theorem loop_exec (I : Array Word) {m : ℕ} (hm : m + 6 < 2 ^ 64) :
    ∀ k i y (o : Array Word) f, i + k = m →
      exec I (f + 8 * k + 1) (st m i y) o [.loop 2 step] =
        some (o.toList ++ (List.range k).map fun j => I.getD (i + j + 5) 0) := by
  intro k
  induction k with
  | zero =>
    intro i y o f hi
    subst hi
    simp [st, exec]
  | succ k ih =>
    intro i y o f hi
    have hlt : i < m := by omega
    have h1 : toWord (i + 1 + 5) < toWord (m + 5) ↔ i + 1 < m :=
      (toWord_lt_toWord (by omega) (by omega)).trans (by omega)
    have h5 : (toWord (i + 5)).toNat = i + 5 := toNat_toWord (by omega)
    have hs := runs_seq (runs_input (I := I) 3 0 (st m i y) o) (runs_seq (runs_out 3 _ _)
      (runs_seq (runs_op .add 0 0 4 _ _) (runs_op .ltu 2 0 1 _ _)))
    have h6 : toWord (i + 1 + 5) = toWord (i + 5) + 1 := by
      rw [toWord_add_one, show i + 5 + 1 = i + 1 + 5 by omega]
    have key : Runs I step (st m i y) o 7 (st m (i + 1) (I.getD (i + 5) 0))
        (o.push (I.getD (i + 5) 0)) := by
      convert hs using 2
      · rfl
      · simp only [st, Array.getD_eq_getD_getElem?, XOp.eval, h6, ← h1]
        simp [h5]
      · simp [st, h5]
    rw [show f + 8 * (k + 1) + 1 = (7 + (f + 8 * k + 1)) + 1 by ring,
      exec_loop_ne (by simp [st, hlt]), key, ih (i + 1) _ _ f (by omega)]
    simp [List.range_succ_eq_map, Nat.add_assoc, Nat.add_comm 1]

theorem extractorInput_eq (c : Digest) (π : Proof) (L : Log) :
    extractorInput c π L = (packBytes c.toList ++ [toWord π.size]) ++ packBytes π.data.toList ++
      (toWord L.length ::
        L.flatMap fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList) := by
  unfold extractorInput bytesWords
  rw [size_eq_length]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- The set-up block's result is the loop's initial memory. -/
theorem pre_mem {s : ℕ} (hs : s ≤ proofCap) :
    (#[5, (toWord s + 7) >>> 3 + 5, if (5 : Word) < (toWord s + 7) >>> 3 + 5 then 1 else 0, 3, 1] :
      Array Word) = st ((s + 7) / 8) 0 3 := by
  unfold proofCap at hs
  have he : (toWord s + 7) >>> 3 + 5 = toWord ((s + 7) / 8 + 5) := by
    apply BitVec.eq_of_toNat_eq
    have h7 : (7 : Word).toNat = 7 := rfl
    have h5 : (5 : Word).toNat = 5 := rfl
    simp only [toWord, BitVec.toNat_add, h7, h5, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    omega
  have hc : (5 : Word) < toWord ((s + 7) / 8 + 5) ↔ 0 < (s + 7) / 8 :=
    (toWord_lt_toWord (a := 0 + 5) (by omega) (by omega)).trans (by omega)
  rw [he]
  simp only [st, hc]
  rfl

/-- **The program on a proof's tape**: it outputs the proof's packed words, within `8 · t`
steps. -/
theorem ext_run (c : Digest) (π : Proof) (L : Log) (hπ : π.size ≤ proofCap) :
    ext.run (extractorInput c π L) (fuel (extractorInput c π L).length) =
      some (packBytes π.data.toList) := by
  set t := extractorInput c π L with ht
  have h4 := packBytes_digest_length c
  have h5 : (packBytes c.toList ++ [toWord π.size]).length = 5 := by simp [h4]
  have hm : (packBytes π.data.toList).length = (π.size + 7) / 8 := by simp [packBytes_length]
  have g4 : t.getD 4 0 = toWord π.size := by
    rw [ht, extractorInput_eq, List.append_assoc, List.append_assoc, List.singleton_append,
      show 4 = (packBytes c.toList).length from h4.symm, getD_append_length]
  have hlen : (π.size + 7) / 8 + 6 ≤ t.length := by
    rw [ht, extractorInput_eq]; simp only [List.length_append, List.length_cons, h5, hm]; omega
  have hI : ∀ i, t.toArray.getD i 0 = t.getD i 0 := fun i => by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  unfold XProg.run
  simp only [ext, fuel, show 5 ≤ 8 * t.length by omega, ↓reduceIte]
  set m := (π.size + 7) / 8
  rw [show 8 * t.length - 5 = ((8 * t.length - 5 - 8 * m - 21) + 8 * m + 1 + 19) + 1 by omega]
  rw [exec_seq, pre_exec, hI, g4, pre_mem hπ,
    loop_exec _ (by unfold proofCap at hπ; omega) m 0 3 #[] _ (by omega)]
  congr 1
  refine List.ext_getElem (by simp [hm, m]) fun j _ h2 => ?_
  simp only [List.nil_append, List.getElem_map, List.getElem_range]
  rw [hI, ht, extractorInput_eq,
    show 0 + j + 5 = (packBytes c.toList ++ [toWord π.size]).length + j by rw [h5]; omega,
    getD_append_mid _ _ _ h2]

/-- **The program computes the extractor** within `8 · t` steps on every input. -/
theorem computes : Computes submission.ext submission.E submission.fuel := by
  intro c π L hπ _
  refine ⟨packBytes π.data.toList, ext_run c π L hπ, ?_, rfl⟩
  rw [packBytes_length, ← size_eq_length]
  unfold outCap; unfold proofCap at hπ; omega

/-- **The witness-sending submission is certified.** -/
theorem certificate : Certificate submission where
  secure := ks
  complete := complete
  computes := computes
  cap := ⟨zero_le, zero_le, Nat.zero_le _, fun t => by
    simp only [submission, fuel, extractorBudget]; omega, by decide⟩

end RecursionFast.WitnessSending
