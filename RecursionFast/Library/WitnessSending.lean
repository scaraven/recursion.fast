/-
  RecursionFast.Library.WitnessSending  (UNTRUSTED, kernel-checked)

  **The witness-sending argument under v4** (DESIGN-v3 §7.3, V3-9; docs/v4/BRIEF.md stage A): the
  proof is the witness, the verifier decides the relation directly with no oracle query, and the
  extractor reads the witness off the proof. It is a complete `Certificate` (`certificate`, for
  every public key), the core-side positive control that the v4 certificate is satisfiable, and
  the argument of the smoke entry of stage B.

  * **Proof format.** `encode w` is the bytes of the extractor output words of `w` (`witWords`,
    `Library/Words.lean`), so a proof packs back to exactly the words that denote its witness
    (`decode_encode`). A node proof carries its two children's **signed proofs** (proof, trace,
    signature).
  * **Verifier (strict, #10, V3-S2R-A5).** `check vk c π`: `π` is the canonical encoding of a leaf
    witness of at most `chainCap` steps (checked before the hash) whose chain ends at the
    statement's chain end, or of a node witness whose statement is `nodeStmt c₁ c₂` and whose
    children `acc vk` accepts: each child's proof length within a word, its trace within `qV = 0`
    entries (RA-M2) and its queries within `queryCap`, its signature valid on its trace's digest,
    and, since this verifier asks no query, its trace **empty** (exact consumption, V4-A3) and its
    proof accepted by `check`, recursively. Canonical encodings for leaves and nodes make it
    reject appended and truncated bytes (`check_canonical`). It runs the linear-time decoder
    twins and the word-level hashes (`Library/Fast.lean`); `check_eq` states it with the
    specification functions. `V vk c π := ret (check vk c π)`: no query, `qV = 0`.
  * **Prover.** `P vk c w := ret (encode w)`. Every witness of the relation fits the format
    (`fits_of_rel`: `acc` keeps each child's proof length within a word, empties the trace, and
    `SigOk` fixes the signature's counts), so perfect completeness needs no normalisation
    (`complete_perfect`); the certificate's completeness is at `δ = 0` through
    `complete_withError_zero`, for every key. Since V4-A11 the relation's witnesses are unbounded
    below the word: a node proof is longer than its children, so the verifier accepts proofs of
    every size up to about `2^65` bytes (`Controls/Relation.lean`, `deep_accepted`), and the
    prover copies whatever it is given.
  * **Extractor.** `E c π L := decode π` (no key, V4-6), and the program `ext` (5 memory words,
    21 statements, v3's unchanged) copies the proof's packed words from the input tape to the
    output, 8 steps per word (`computes`), on the contract's domain of proofs up to `8 · outCap`
    bytes, the longest whose words fit the output cap (`Controls/Extractor.lean`,
    `ws_output_beyond_domain`).
  * **Security.** `KS` at `ε = 0`, `qV = 0` (`ks`), through the potential `μ := 0` (`kstate`,
    `KState.zero`) and the bridge `KState.ks` (`Library/PaperTheorem.lean`): an accepted proof
    decodes to a witness of the relation by the definition of `check` (`check_sound`), on every
    log and under every key.
-/
import RecursionFast.Contract.Certificate
import RecursionFast.Library.Words
import RecursionFast.Library.Machine
import RecursionFast.Library.Security
import RecursionFast.Library.Completeness
import RecursionFast.Library.PaperTheorem
import RecursionFast.Library.Fast
import RecursionFast.Library.Trace

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

theorem size_encode (w : Wit) : (encode w).size = 8 * (witWords w).length :=
  List.size_toArray.trans (wordsBytes_length _)

theorem size_eq_length (π : Proof) : π.size = π.data.toList.length := Array.length_toList.symm

theorem size_encode_leaf (s : Digest) (n : ℕ) : (encode (.leaf s n)).size = 48 := by
  simp [size_encode, witWords, packBytes_digest_length]

/-- `decode` in linear time (`decodeF_eq`). -/
def decodeF (π : Proof) : Option Wit := decodeWit (packFast π.data.toList)

theorem decodeF_eq (π : Proof) : decodeF π = decode π := congrArg decodeWit (packFast_eq _)

/-- `encode` in linear time (`encodeF_eq`). -/
def encodeF (w : Wit) : Proof := ⟨(wordsBytes (witWordsF w)).toArray⟩

theorem encodeF_eq (w : Wit) : encodeF w = encode w := by
  rw [encodeF, encode, witWordsF_eq]

/-- A child's proof is shorter than its parent's encoding. -/
theorem size_child_lt (c₁ c₂ : Digest) (p₁ p₂ : Signed) :
    p₁.π.size < (encode (.node c₁ c₂ p₁ p₂)).size ∧
      p₂.π.size < (encode (.node c₁ c₂ p₁ p₂)).size := by
  simp only [size_encode, witWords, signedWords, bytesWords, List.length_cons, List.length_append,
    packBytes_length, ← size_eq_length]
  omega

/-! ## The argument -/

/-- **The strict witness-sending decision** under the key `vk`: `π` is the canonical encoding of
a leaf witness of `c` (its length within `chainCap`, checked before any hash), or of a node
witness of `c` whose two children are accepted (`acc vk` of this verifier, unfolded: proof
length within a word, trace length (`qV = 0`) and queries capped, signature valid, trace empty,
proof accepted recursively). -/
def check (vk c : Digest) (π : Proof) : Bool :=
  match decodeF π with
  | some (.leaf s n) =>
    decide (encodeF (.leaf s n) = π) && decide (n ≤ chainCap) &&
      decide (c = leafStmtF (chainEndF s n) n)
  | some (.node c₁ c₂ p₁ p₂) =>
    if _h : encodeF (.node c₁ c₂ p₁ p₂) = π then
      decide (c = nodeStmtF c₁ c₂) &&
        (decide (p₁.π.size < 2 ^ 64) && decide (p₁.tr.length ≤ 0) &&
          decide (∀ e ∈ p₁.tr, e.1.size ≤ queryCap) &&
          SigOkF vk (traceDigestF p₁.tr) p₁.σ && (p₁.tr.isEmpty && check vk c₁ p₁.π)) &&
        (decide (p₂.π.size < 2 ^ 64) && decide (p₂.tr.length ≤ 0) &&
          decide (∀ e ∈ p₂.tr, e.1.size ≤ queryCap) &&
          SigOkF vk (traceDigestF p₂.tr) p₂.σ && (p₂.tr.isEmpty && check vk c₂ p₂.π))
    else false
  | none => false
termination_by π.size
decreasing_by
  · rw [← _h, encodeF_eq]; exact (size_child_lt c₁ c₂ p₁ p₂).1
  · rw [← _h, encodeF_eq]; exact (size_child_lt c₁ c₂ p₁ p₂).2

/-- The verifier: `check`, with no oracle query. -/
def V (vk c : Digest) (π : Proof) : OProg Bool := .ret (check vk c π)

/-- The honest prover: send the witness. -/
def P (_ _ : Digest) (w : Wit) : OProg Proof := .ret (encodeF w)

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
def ext : XProg := ⟨5, 0, .seq pre (.loop 2 step)⟩

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

/-! ## Acceptance and the relation -/

/-- `runSeq` of a program that asks nothing: the trace must be empty. -/
theorem runSeq_ret_eq (b : Bool) (tr : Trace) :
    decide ((OProg.ret b).runSeq tr = some true) = (tr.isEmpty && b) := by
  cases tr <;> cases b <;> rfl

/-- **What `acc` of this submission decides.** -/
theorem acc_eq (vk c : Digest) (p : Signed) : submission.acc vk c p =
    (decide (p.π.size < 2 ^ 64) && decide (p.tr.length ≤ 0) &&
      decide (∀ e ∈ p.tr, e.1.size ≤ queryCap) && SigOk vk (traceDigest p.tr) p.σ &&
      (p.tr.isEmpty && check vk c p.π)) :=
  congrArg (_ && ·) (runSeq_ret_eq _ _)

/-- `check`, with the specification functions. -/
theorem check_eq (vk c : Digest) (π : Proof) : check vk c π =
    match decode π with
    | some (.leaf s n) =>
      decide (encode (.leaf s n) = π) && decide (n ≤ chainCap) &&
        decide (c = leafStmt (chainEnd s n) n)
    | some (.node c₁ c₂ p₁ p₂) =>
      if encode (.node c₁ c₂ p₁ p₂) = π then
        decide (c = nodeStmt c₁ c₂) && submission.acc vk c₁ p₁ && submission.acc vk c₂ p₂
      else false
    | none => false := by
  rw [check, decodeF_eq]
  simp only [encodeF_eq, dite_eq_ite, acc_eq, leafStmtF_eq, chainEndF_eq, nodeStmtF_eq,
    SigOkF_eq, traceDigestF_eq]

/-- An accepted proof is the canonical encoding of a witness of the relation it decodes to. -/
private theorem exists_of_check {vk c : Digest} {π : Proof} (h : check vk c π = true) :
    ∃ w, decode π = some w ∧ encode w = π ∧ Rel (submission.acc vk) c w := by
  rw [check_eq] at h
  split at h
  next s n hd =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨.leaf s n, hd, h.1.1, h.1.2, h.2⟩
  next c₁ c₂ p₁ p₂ hd =>
    split at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨.node c₁ c₂ p₁ p₂, hd, ‹_›, h.1.1, h.1.2, h.2⟩
    · cases h
  · cases h

/-- **Strictness**: an accepted proof is the canonical encoding of the witness it decodes to. -/
theorem check_canonical {vk c : Digest} {π : Proof} (h : check vk c π = true) :
    ∃ w, decode π = some w ∧ encode w = π :=
  (exists_of_check h).imp fun _ h => ⟨h.1, h.2.1⟩

/-- **An accepted proof decodes to a witness of the relation.** -/
theorem check_sound {vk c : Digest} {π : Proof} (h : check vk c π = true) :
    ∃ w, decode π = some w ∧ Rel (submission.acc vk) c w :=
  (exists_of_check h).imp fun _ h => ⟨h.1, h.2.2⟩

/-- An accepted child fits the output format: `acc` keeps its proof's length within a word,
empties its trace, and `SigOk` fixes its signature's counts. -/
theorem fits_of_acc {vk c : Digest} {p : Signed} (h : submission.acc vk c p = true) :
    p.Fits := by
  simp only [acc_eq, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff, SigOk] at h
  obtain ⟨⟨⟨⟨hπ, -⟩, -⟩, ⟨⟨hi, ho⟩, hp⟩, -⟩, htr, -⟩ := h
  exact ⟨hπ, by simp [htr], by simp [htr], hi.trans (by decide), ho, hp⟩

/-- Every witness of the relation fits the output format. -/
theorem fits_of_rel {vk c : Digest} {w : Wit} (h : Rel (submission.acc vk) c w) : w.Fits := by
  cases w with
  | leaf s n => exact h.1.trans_lt (by decide)
  | node c₁ c₂ p₁ p₂ => exact ⟨fits_of_acc h.2.1, fits_of_acc h.2.2⟩

/-- **The honest proof of a witness of the relation is accepted.** -/
theorem check_encode {vk c : Digest} {w : Wit} (hR : Rel (submission.acc vk) c w) :
    check vk c (encode w) = true := by
  rw [check_eq, decode_encode w (fits_of_rel hR)]
  cases w <;> simp [hR.1, hR.2]

/-- **What the verifier decides**: a proof is accepted exactly when it is the canonical encoding
of a witness of the relation. -/
theorem check_iff (vk c : Digest) (π : Proof) : check vk c π = true ↔
    ∃ w, decode π = some w ∧ encode w = π ∧ Rel (submission.acc vk) c w :=
  ⟨exists_of_check, fun ⟨_, _, he, hR⟩ => he ▸ check_encode hR⟩

/-! ## Knowledge soundness and completeness -/

/-- The knowledge state under `vk`: the potential `0` (every accepted proof decodes to a
witness). -/
def kstate (vk : Digest) : KState (Rel (submission.acc vk)) (V vk) E 0 :=
  KState.zero 0 fun _ _ _ h => check_sound (Option.some.inj h)

/-- **Knowledge soundness** at error `0` with no verifier query, under every key. -/
theorem ks (vk : Digest) :
    KS (Rel (submission.acc vk)) (submission.V vk) submission.E submission.ε submission.qV :=
  (kstate vk).ks fun _ _ _ => le_rfl

/-- **Perfect completeness**, for every oracle function and key. -/
theorem complete_perfect (vk : Digest) :
    Complete (Rel (submission.acc vk)) (submission.P vk) (submission.V vk) := fun _ _ _ hR =>
  (congrArg (check _ _) (encodeF_eq _)).trans (check_encode hR)

/-- **Completeness at error `0`**, under every key. -/
theorem complete (vk : Digest) :
    CompleteWithError (Rel (submission.acc vk)) (submission.P vk) (submission.V vk)
      submission.δ :=
  complete_withError_zero (complete_perfect vk)

/-! ## The extractor program (v3's, unchanged) -/

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
    intro i y o f rfl
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
      logWords L := by
  simp only [extractorInput, bytesWords, size_eq_length, List.append_assoc, List.cons_append,
    List.nil_append]

/-- The set-up block's result is the loop's initial memory. -/
theorem pre_mem {s : ℕ} (hs : s < 2 ^ 60) :
    (#[5, (toWord s + 7) >>> 3 + 5, if (5 : Word) < (toWord s + 7) >>> 3 + 5 then 1 else 0, 3, 1] :
      Array Word) = st ((s + 7) / 8) 0 3 := by
  have he : (toWord s + 7) >>> 3 + 5 = toWord ((s + 7) / 8 + 5) := by
    apply BitVec.eq_of_toNat_eq
    have h7 : (7 : Word).toNat = 7 := rfl
    have h5 : (5 : Word).toNat = 5 := rfl
    simp only [toWord, BitVec.toNat_add, h7, h5, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    omega
  have hc : (5 : Word) < toWord ((s + 7) / 8 + 5) ↔ 0 < (s + 7) / 8 :=
    (toWord_lt_toWord (a := 0 + 5) (by omega) (by omega)).trans (by omega)
  simp only [he, st, hc]
  rfl

/-- **The program on a proof's tape**: it outputs the proof's packed words, within `8 · t`
steps (for every proof below `2^60` bytes, the contract's domain and beyond). -/
theorem ext_run (c : Digest) (π : Proof) (L : Log) (hπ : π.size < 2 ^ 60) :
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
    rw [ht, extractorInput_eq]
    simp only [List.length_append, logWords, List.length_cons, h5, hm]; omega
  simp only [XProg.run, ext, fuel, XProg.memFor, Nat.zero_mul, Nat.add_zero,
    show 5 ≤ 8 * t.length by omega, ↓reduceIte]
  set m := (π.size + 7) / 8
  rw [show 8 * t.length - 5 = ((8 * t.length - 5 - 8 * m - 21) + 8 * m + 1 + 19) + 1 by omega,
    exec_seq, pre_exec, getD_toArray, g4, pre_mem hπ,
    loop_exec _ (by omega) m 0 3 #[] _ (by omega)]
  congr 1
  refine List.ext_getElem (by simp [hm, m]) fun j _ h2 => ?_
  simp only [List.nil_append, List.getElem_map, List.getElem_range]
  rw [getD_toArray, ht, extractorInput_eq,
    show 0 + j + 5 = (packBytes c.toList ++ [toWord π.size]).length + j by rw [h5]; omega,
    getD_append_mid _ _ _ h2]

/-- **The program computes the extractor** within `8 · t` steps on every input. -/
theorem computes : Computes submission.ext submission.E submission.fuel := by
  intro c π L hπ _ _
  unfold outCap at hπ
  refine ⟨packBytes π.data.toList, ext_run c π L (by omega), ?_, rfl⟩
  rw [packBytes_length, ← size_eq_length]
  unfold outCap
  omega

/-- **The witness-sending submission is certified**, for every public key. -/
theorem certificate : Certificate submission where
  secure := ks
  complete := complete
  computes := computes
  cap := ⟨zero_le, zero_le, Nat.zero_le _, fun t => by
    simp only [submission, fuel, extractorBudget]; omega, by decide⟩

end RecursionFast.WitnessSending
