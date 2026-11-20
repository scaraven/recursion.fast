/-
# Controls: a certified verifier that asks the oracle and is extracted from the log

The satisfiability control for **log-based extraction**. The witness-sending submission
(`Library/WitnessSending.lean`) asks no query and its extractor reads the proof; the backdoor
(`Controls/Backdoor.lean`) reads the proof too. This submission's verifier asks the oracle, and on
one kind of proof its extractor can only find the witness in the query log, by a program of the
contract's machine. It has a full `CertificateR`: so the certificate admits a verifier whose
knowledge comes from its oracle answers, extracted straight-line from the final log within the
budget.

**Masked leaf ∨ witness-sending.** The verifier `V vk c π` asks one query, `cq c` (the statement's
32 bytes), and gets the answer `a`:
* a proof of exactly 32 bytes is a **masked block**: `x = unmask π a` (the proof's four packed words
  XORed with the answer's), and `V` accepts iff `c = leafStmt (leafItem x) 1`, the statement of the
  one-block leaf `[x]`;
* any other proof is decided as by the witness-sending verifier (`dec`): the canonical encoding of
  a leaf witness, or of a node witness whose children this submission's `acc` accepts (unfolded:
  `qV = 1`, so a child's trace is the one entry `(cq c₁, a₁)`, and the child's decision is `dec` on
  that answer, recursively).
No witness-sending proof has 32 bytes (a leaf's is `16 + 32n`, a node's more than 72), so the two
kinds do not overlap.

* **Prover.** On a one-block leaf `[x]`: ask `cq c` and send `mask x a`. Otherwise send the witness.
  Perfect completeness over every oracle function (`complete_perfect`): the verifier's one query
  is the prover's, so it reads the same answer and unmasks `x` (`unmask_mask`).
* **Extractor.** `E c π L`: on a 32-byte proof, the first log entry whose query is `cq c`,
  unmasked: the leaf `[unmask π a]` (none if the log has no such entry); otherwise the witness the
  proof sends. The answer is in the log because the verifier asked it: on the honest masked proof
  `E` returns the leaf from a log holding that answer and nothing from the empty log
  (`extractor_reads_log`).
* **Knowledge soundness** at `ε = 0`, `qV = 1` (`ks`), through the zero potential: an accepted
  proof on a log is extracted from that log (`accepted_extracted`), under every key.
* **The program** `ext` (24 memory words, 167 statements, `ext_size`): it reads `|π|`; on 32 bytes
  it scans the log by **query** (length word `32` and the statement's four words; each entry's
  query is skipped by its length word, as in `Controls/LogScan.lean`), and on the first match it
  outputs the leaf tag, one block, and the proof's words XORed with the answer's; otherwise it
  copies the proof's packed words, as the witness-sending program does. Within `32 · t` steps on
  the contract's whole domain (`computes`).
* `certificateR`: the `CertificateR` against the claim `ε = 0`, `δ = 0`, `qV = 1`, fuel `32 · t`.

Negative:
* `not_qV_zero`: the verifier asks its query: with `qV = 0` it is not knowledge-sound (its query
  bound fails).
* `extractor_reads_log`: one proof, two logs: the leaf from the log holding the answer, nothing
  from the empty log.
-/
import RecursionFast.Controls.LogScan

open scoped NNReal

namespace RecursionFast.Controls.MaskedLeaf
open RecursionFast XStmt

/-! ## The mask -/

/-- The verifier's one query on the statement `c`: its 32 bytes. -/
def cq (c : Digest) : ByteArray := ⟨c.toArray⟩

/-- Four words, the pairwise XOR of the first four of `p` and `q`. -/
def xor4 (p q : List Word) : List Word :=
  [p.getD 0 0 ^^^ q.getD 0 0, p.getD 1 0 ^^^ q.getD 1 0, p.getD 2 0 ^^^ q.getD 2 0,
    p.getD 3 0 ^^^ q.getD 3 0]

/-- **The block a 32-byte proof hides under the answer `a`**: the proof's first four packed words
XORed with the answer's. -/
def unmask (π : Proof) (a : Digest) : Digest :=
  ⟨(wordsBytes (xor4 (packBytes π.data.toList) (packBytes a.toList))).toArray, by
    simp [wordsBytes_length, xor4]⟩

/-- The proof that hides the block `x` under the answer `a`. -/
def mask (x a : Digest) : Proof :=
  ⟨(wordsBytes (xor4 (packBytes x.toList) (packBytes a.toList))).toArray⟩

theorem packBytes_unmask (π : Proof) (a : Digest) :
    packBytes (unmask π a).toList = xor4 (packBytes π.data.toList) (packBytes a.toList) := by
  simp [unmask, packBytes_wordsBytes]

theorem packBytes_mask (x a : Digest) :
    packBytes (mask x a).data.toList = xor4 (packBytes x.toList) (packBytes a.toList) := by
  simp [mask, packBytes_wordsBytes]

theorem size_mask (x a : Digest) : (mask x a).size = 32 := by
  simp [mask, ByteArray.size, wordsBytes_length, xor4]

theorem xor4_xor4 (p q : List Word) (hp : p.length = 4) : xor4 (xor4 p q) q = p := by
  conv_rhs => rw [LogScan.four p hp]
  simp [xor4, BitVec.xor_assoc]

/-- A digest is the bytes of its packed words. -/
theorem wordsBytes_packBytes (x : Digest) : wordsBytes (packBytes x.toList) = x.toList := by
  have h := unpack_packBytes x.toList
  rwa [List.take_of_length_le (by simp [wordsBytes_length, packBytes_digest_length])] at h

/-- **Unmasking undoes masking.** -/
theorem unmask_mask (x a : Digest) : unmask (mask x a) a = x := by
  apply Vector.toList_inj.mp
  have h : (unmask (mask x a) a).toList =
      wordsBytes (xor4 (packBytes (mask x a).data.toList) (packBytes a.toList)) := by
    simp [unmask]
  rw [h, packBytes_mask, xor4_xor4 _ _ (packBytes_digest_length x), wordsBytes_packBytes]

theorem dataRoot_single (x : Digest) : dataRoot [x] = leafItem x := rfl

/-! ## The argument -/

/-- The decision on a one-entry trace: the entry is the query `cq c`, and `d` accepts its answer.
Any other trace is rejected. -/
def seqOk (c : Digest) (d : Digest → Bool) : Trace → Bool
  | [(q, a)] => decide (q = cq c) && d a
  | _ => false

/-- **The decision** under the key `vk` on the statement `c`, the proof `π` and the answer `a` to
`cq c`: a 32-byte proof is a masked block of the one-block leaf; any other proof is the canonical
encoding of a leaf witness of `c` or of a node witness of `c` whose children `acc vk` of this
submission accepts (unfolded: proof length within a word, at most `qV = 1` trace entry, queries
within `queryCap`, signature valid, and the trace the one entry `(cq c₁, a₁)` on whose answer the
child's proof is decided, recursively). -/
def dec (vk c : Digest) (π : Proof) (a : Digest) : Bool :=
  if π.size = 32 then decide (c = leafStmtF (leafItemF (unmask π a)) 1) else
  match WitnessSending.decodeF π with
  | some (.leaf xs) =>
    decide (WitnessSending.encodeF (.leaf xs) = π) && decide (xs.length ≤ leafCap) &&
      decide (c = leafStmtF (dataRootF xs) xs.length)
  | some (.node c₁ c₂ p₁ p₂) =>
    if _h : WitnessSending.encodeF (.node c₁ c₂ p₁ p₂) = π then
      decide (c = nodeStmtF c₁ c₂) &&
        (decide (p₁.π.size < 2 ^ 64) && decide (p₁.tr.length ≤ 1) &&
          decide (∀ e ∈ p₁.tr, e.1.size ≤ queryCap) &&
          SigOkF vk (traceDigestF p₁.tr) p₁.σ && seqOk c₁ (fun a₁ => dec vk c₁ p₁.π a₁) p₁.tr) &&
        (decide (p₂.π.size < 2 ^ 64) && decide (p₂.tr.length ≤ 1) &&
          decide (∀ e ∈ p₂.tr, e.1.size ≤ queryCap) &&
          SigOkF vk (traceDigestF p₂.tr) p₂.σ && seqOk c₂ (fun a₂ => dec vk c₂ p₂.π a₂) p₂.tr)
    else false
  | none => false
termination_by π.size
decreasing_by
  · rw [← _h, WitnessSending.encodeF_eq]; exact (WitnessSending.size_child_lt c₁ c₂ p₁ p₂).1
  · rw [← _h, WitnessSending.encodeF_eq]; exact (WitnessSending.size_child_lt c₁ c₂ p₁ p₂).2

/-- **The verifier**: ask `cq c`, decide on its answer. -/
def V (vk c : Digest) (π : Proof) : OProg Bool := .query (cq c) fun a => .ret (dec vk c π a)

/-- **The honest prover**: a one-block leaf is masked under the answer to `cq c`; any other
witness is sent. -/
def P (_ c : Digest) : Wit → OProg Proof
  | .leaf [x] => .query (cq c) fun a => .ret (mask x a)
  | w => .ret (WitnessSending.encodeF w)

/-- **The extractor's specification**: on a 32-byte proof, the block unmasked under the answer of
the first log entry for `cq c`; otherwise the witness the proof sends. -/
def E (c : Digest) (π : Proof) (L : Log) : Option Wit :=
  if π.size = 32 then (L.find? fun e => e.1 = cq c).map fun e => .leaf [unmask π e.2]
  else WitnessSending.decode π

/-! ## The extractor program

Memory (24 words): `0 … 3` the statement's words, `4` the tape position, `5` the entries left (the
copy's end), `6` the match flag, `7` the loop condition, `8` a scratch word, `9 … 12` the constants
`1, 7, 3, 4`, `13`, `14` scratch words, `15` stays `0`, `16 … 19` the proof's words, `20` the
constant `32`, `21` the branch flag `|π| = 32`, `22` the word `|π|`, `23` unused. -/

/-- Read `|π|`, compare it with `32`; set the constants. -/
def pre0 : XStmt := seqs (.const 4 4)
  [.input 22 4, .const 20 32, .op .eq 21 22 20, .const 9 1, .const 10 7, .const 11 3, .const 12 4]

/-- The copy's set-up: `M[5] := ⌈|π| / 8⌉ + 5` (the end of the proof's words), `M[4] := 5`. -/
def cpre : XStmt := seqs (.op .add 5 22 10)
  [.op .shr 5 5 11, .const 4 5, .op .add 5 5 4, .op .ltu 7 4 5]

/-- One copy step: output tape word `M[4]`, `M[4] += 1`. -/
def cstep : XStmt := .seq (.input 8 4) (.seq (.out 8) (.seq (.op .add 4 4 9) (.op .ltu 7 4 5)))

/-- The masked branch's set-up: read the statement and the proof's four words, the number of
entries; position at the first entry (tape word `10`). -/
def mpre : XStmt := seqs (.const 4 0)
  [.input 0 4, .const 4 1, .input 1 4, .const 4 2, .input 2 4, .const 4 3, .input 3 4,
   .const 4 5, .input 16 4, .const 4 6, .input 17 4, .const 4 7, .input 18 4, .const 4 8,
   .input 19 4, .const 4 9, .input 5 4, .const 4 10, .const 7 1]

/-- An entry: the match flag `M[6]` (the query's length word is `32` and its next four words are
the statement's), then skip the query (`⌈|q|/8⌉` without overflow, as `Controls/LogScan.lean`):
`M[4]` is the answer's position. -/
def mhead : XStmt := seqs (.input 8 4)
  [.op .eq 6 8 20, .op .add 14 4 9,
   .input 13 14, .op .eq 13 13 0, .op .and 6 6 13,
   .op .add 14 14 9, .input 13 14, .op .eq 13 13 1, .op .and 6 6 13,
   .op .add 14 14 9, .input 13 14, .op .eq 13 13 2, .op .and 6 6 13,
   .op .add 14 14 9, .input 13 14, .op .eq 13 13 3, .op .and 6 6 13,
   .op .and 13 8 10, .op .ltu 13 15 13, .op .shr 8 8 11, .op .add 8 8 13,
   .op .add 4 4 9, .op .add 4 4 8, .const 13 0]

/-- A match: output the leaf tag `0`, one block, the proof's words XORed with the answer's; stop. -/
def mfound : XStmt := seqs (.out 15)
  [.out 9, .input 14 4, .op .xor 14 16 14, .out 14, .op .add 4 4 9,
   .input 14 4, .op .xor 14 17 14, .out 14, .op .add 4 4 9,
   .input 14 4, .op .xor 14 18 14, .out 14, .op .add 4 4 9,
   .input 14 4, .op .xor 14 19 14, .out 14, .const 7 0]

/-- No match: move to the next entry. -/
def mnext : XStmt := seqs (.op .add 4 4 12) [.op .sub 5 5 9]

/-- One iteration of the scan: an entry if any is left, else stop. -/
def mbody : XStmt := .ite 5 (.seq mhead (.ite 6 mfound mnext)) (.const 7 0)

/-- **The extractor program**: the scan by query on a 32-byte proof, else the copy. -/
def ext : XProg :=
  ⟨24, 0, .seq pre0 (.ite 21 (.seq mpre (.loop 7 mbody)) (.seq cpre (.loop 7 cstep)))⟩

/-- The extractor's fuel: `32` steps per tape word. -/
def fuel (t : ℕ) : ℕ := 32 * t

/-- **The masked-leaf submission**: errors `0`, one verifier query, fuel `32 · t`. -/
def submission : Submission where
  V := V
  P := P
  E := E
  ext := ext
  ε := 0
  δ := 0
  qV := 1
  fuel := fuel

/-! ## Acceptance and the relation -/

/-- `runSeq` of the verifier: the trace must be the one entry for `cq c`. -/
theorem runSeq_V (vk c : Digest) (π : Proof) (tr : Trace) :
    decide ((V vk c π).runSeq tr = some true) = seqOk c (dec vk c π) tr := by
  match tr with
  | [] => rfl
  | [(q, a)] => by_cases h : q = cq c <;> simp [V, OProg.runSeq, seqOk, h]
  | (q, a) :: _ :: _ => by_cases h : q = cq c <;> simp [V, OProg.runSeq, seqOk, h]

/-- **What `acc` of this submission decides.** -/
theorem acc_eq (vk c : Digest) (p : Signed) : submission.acc vk c p =
    (decide (p.π.size < 2 ^ 64) && decide (p.tr.length ≤ 1) &&
      decide (∀ e ∈ p.tr, e.1.size ≤ queryCap) && SigOk vk (traceDigest p.tr) p.σ &&
      seqOk c (dec vk c p.π) p.tr) :=
  congrArg (_ && ·) (runSeq_V _ _ _ _)

/-- `dec`, with the specification functions. -/
theorem dec_eq (vk c : Digest) (π : Proof) (a : Digest) : dec vk c π a =
    if π.size = 32 then decide (c = leafStmt (leafItem (unmask π a)) 1) else
    match WitnessSending.decode π with
    | some (.leaf xs) =>
      decide (WitnessSending.encode (.leaf xs) = π) && decide (xs.length ≤ leafCap) &&
        decide (c = leafStmt (dataRoot xs) xs.length)
    | some (.node c₁ c₂ p₁ p₂) =>
      if WitnessSending.encode (.node c₁ c₂ p₁ p₂) = π then
        decide (c = nodeStmt c₁ c₂) && submission.acc vk c₁ p₁ && submission.acc vk c₂ p₂
      else false
    | none => false := by
  rw [dec, WitnessSending.decodeF_eq]
  simp only [WitnessSending.encodeF_eq, dite_eq_ite, acc_eq, leafStmtF_eq, leafItemF_eq,
    dataRootF_eq, nodeStmtF_eq, SigOkF_eq, traceDigestF_eq]

/-- An accepted proof that is not 32 bytes decodes to a witness of the relation. -/
theorem dec_sound {vk c : Digest} {π : Proof} {a : Digest} (h32 : π.size ≠ 32)
    (h : dec vk c π a = true) :
    ∃ w, WitnessSending.decode π = some w ∧ Rel (submission.acc vk) c w := by
  rw [dec_eq] at h
  simp only [h32, ↓reduceIte] at h
  split at h
  next xs hd =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨.leaf xs, hd, h.1.2, h.2⟩
  next c₁ c₂ p₁ p₂ hd =>
    split at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨.node c₁ c₂ p₁ p₂, hd, h.1.1, h.1.2, h.2⟩
    · cases h
  · cases h

/-- **An accepted proof is extracted from the log**: if the verifier accepts on the log `L`, the
extractor returns a witness of the relation from `π` and `L`. -/
theorem accepted_extracted (vk : Digest) (L : Log) (c : Digest) (π : Proof)
    (h : (V vk c π).runLog L = some true) :
    ∃ w, E c π L = some w ∧ Rel (submission.acc vk) c w := by
  simp only [V, OProg.runLog] at h
  cases hf : L.find? (fun e => decide (e.1 = cq c)) with
  | none => simp [hf] at h
  | some e =>
    simp only [hf, Option.bind_some, Option.some.injEq] at h
    by_cases h32 : π.size = 32
    · simp only [dec_eq, h32, ↓reduceIte, decide_eq_true_eq] at h
      refine ⟨.leaf [unmask π e.2], by simp [E, h32, hf], by simp [leafCap], ?_⟩
      simpa [dataRoot_single] using h
    · obtain ⟨w, hw, hR⟩ := dec_sound h32 h
      exact ⟨w, by simp [E, h32, hw], hR⟩

/-- An accepted child fits the output format. -/
theorem fits_of_acc {vk c : Digest} {p : Signed} (h : submission.acc vk c p = true) :
    p.Fits := by
  simp only [acc_eq, Bool.and_eq_true, decide_eq_true_eq, SigOk] at h
  obtain ⟨⟨⟨⟨hπ, hl⟩, hq⟩, ⟨⟨hi, ho⟩, hp⟩, -⟩, -⟩ := h
  exact ⟨hπ, by omega, fun e he => (hq e he).trans_lt (by decide), hi.trans (by decide), ho, hp⟩

/-- Every witness of the relation fits the output format. -/
theorem fits_of_rel {vk c : Digest} {w : Wit} (h : Rel (submission.acc vk) c w) : w.Fits := by
  cases w with
  | leaf xs => exact h.1.trans_lt (by decide)
  | node c₁ c₂ p₁ p₂ => exact ⟨fits_of_acc h.2.1, fits_of_acc h.2.2⟩

/-- No witness-sending proof has 32 bytes. -/
theorem size_encode_ne (w : Wit) : (WitnessSending.encode w).size ≠ 32 := by
  cases w with
  | leaf xs => rw [WitnessSending.size_encode_leaf]; omega
  | node =>
    rw [WitnessSending.size_encode]
    simp only [witWords, List.length_cons, List.length_append, packBytes_digest_length]; omega

/-- **The honest proof of a witness that is not a one-block leaf is accepted.** -/
theorem dec_encode {vk c : Digest} {w : Wit} (hR : Rel (submission.acc vk) c w) (a : Digest) :
    dec vk c (WitnessSending.encode w) a = true := by
  rw [dec_eq]
  simp only [size_encode_ne w, ↓reduceIte, WitnessSending.decode_encode w (fits_of_rel hR)]
  cases w <;> simp [hR.1, hR.2]

/-! ## Knowledge soundness and completeness -/

/-- The knowledge state under `vk`: the potential `0` (every accepted proof is extracted). -/
def kstate (vk : Digest) : KState (Rel (submission.acc vk)) (V vk) E 0 :=
  KState.zero 0 (accepted_extracted vk)

/-- The verifier asks one query. -/
theorem queries_V (vk : Digest) (H : ByteArray → Digest) (c : Digest) (π : Proof) :
    ((V vk c π).queries H).length = 1 := rfl

/-- **Knowledge soundness** at error `0` with one verifier query, under every key. -/
theorem ks (vk : Digest) :
    KS (Rel (submission.acc vk)) (submission.V vk) submission.E submission.ε submission.qV :=
  (kstate vk).ks fun H c π => (queries_V vk H c π).le

/-- **Perfect completeness**, for every oracle function and key. -/
theorem complete_perfect (vk : Digest) :
    Complete (Rel (submission.acc vk)) (submission.P vk) (submission.V vk) := by
  intro H c w hR
  show dec vk c ((P vk c w).run H) (H (cq c)) = true
  match w, hR with
  | .leaf [x], hR =>
    show dec vk c (mask x (H (cq c))) (H (cq c)) = true
    simp only [dec_eq, size_mask, ↓reduceIte, unmask_mask, decide_eq_true_eq]
    exact hR.2
  | .leaf [], hR => exact (congrArg (dec vk c · _) (WitnessSending.encodeF_eq _)).trans (dec_encode hR _)
  | .leaf (_ :: _ :: _), hR =>
    exact (congrArg (dec vk c · _) (WitnessSending.encodeF_eq _)).trans (dec_encode hR _)
  | .node .., hR =>
    exact (congrArg (dec vk c · _) (WitnessSending.encodeF_eq _)).trans (dec_encode hR _)

/-- **Completeness at error `0`**, under every key. -/
theorem complete (vk : Digest) :
    CompleteWithError (Rel (submission.acc vk)) (submission.P vk) (submission.V vk)
      submission.δ :=
  complete_withError_zero (complete_perfect vk)

/-! ## The program's runs

The set-up block and the branch (`masked_start`, `copy_start`); an iteration of the scan passes over
an entry whose query is not `cq c` in 56 steps (`miter_next`), outputs the leaf on a match in 89
steps and stops (`miter_found`), and stops at the end of the log (`miter_end`); `mloop` runs the
scan over the log by induction. The copy loop is `Library/WitnessSending.lean`'s, on this memory
(`cloop`). -/

open LogScan in
/-- The memory at the start of a scan iteration: the statement's words `cw`, the position `p`, the
entries left `n`, the proof's words `pw`, scratch words. -/
def mst (cw pw : List Word) (p n : ℕ) (x6 x8 x13 x14 : Word) : Array Word :=
  #[cw.getD 0 0, cw.getD 1 0, cw.getD 2 0, cw.getD 3 0, toWord p, toWord n, x6, 1, x8, 1, 7, 3, 4,
    x13, x14, 0, pw.getD 0 0, pw.getD 1 0, pw.getD 2 0, pw.getD 3 0, 32, 1, 32, 0]

/-- The memory at the start of a copy iteration: word `i` of `m`, the last word read `y`. -/
def cst (s m i : ℕ) (y : Word) : Array Word :=
  #[0, 0, 0, 0, toWord (i + 5), toWord (m + 5), 0, if i < m then 1 else 0, y, 1, 7, 3, 4, 0, 0, 0,
    0, 0, 0, 0, 32, 0, toWord s, 0]

theorem replicate24 : Array.replicate 24 (0 : Word) =
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl

/-- The constants' set-up, from the zero memory. -/
theorem pre0_exec (I : Array Word) {s : Word} (h4 : I.getD 4 0 = s) (f : ℕ) (o : Array Word)
    (ks : List XStmt) :
    exec I (f + 15) (Array.replicate 24 0) o (pre0 :: ks) = exec I f
      #[0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 7, 3, 4, 0, 0, 0, 0, 0, 0, 0, 32,
        if s = 32 then 1 else 0, s, 0] o ks := by
  simp only [BitVec.ofNat_eq_ofNat, Array.getD_eq_getD_getElem?] at h4
  rw [replicate24]
  simp [pre0, seqs, exec, XOp.eval, h4]

theorem mpre_exec (I : Array Word) (cw pw : List Word) {n : ℕ}
    (h0 : I.getD 0 0 = cw.getD 0 0) (h1 : I.getD 1 0 = cw.getD 1 0)
    (h2 : I.getD 2 0 = cw.getD 2 0) (h3 : I.getD 3 0 = cw.getD 3 0)
    (h5 : I.getD 5 0 = pw.getD 0 0) (h6 : I.getD 6 0 = pw.getD 1 0)
    (h7 : I.getD 7 0 = pw.getD 2 0) (h8 : I.getD 8 0 = pw.getD 3 0) (h9 : I.getD 9 0 = toWord n)
    (f : ℕ) (o : Array Word) (ks : List XStmt) :
    exec I (f + 39) #[0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 7, 3, 4, 0, 0, 0, 0, 0, 0, 0, 32, 1, 32, 0] o
      (mpre :: ks) = exec I f (mst cw pw 10 n 0 0 0 0) o ks := by
  simp only [BitVec.ofNat_eq_ofNat, Array.getD_eq_getD_getElem?] at h0 h1 h2 h3 h5 h6 h7 h8 h9
  simp [mpre, seqs, exec, h0, h1, h2, h3, h5, h6, h7, h8, h9, mst, show toWord 10 = 10#64 from rfl]

theorem cpre_exec (I : Array Word) {s : ℕ} (hs : s < 2 ^ 60) (f : ℕ) (o : Array Word)
    (ks : List XStmt) :
    exec I (f + 9) #[0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 7, 3, 4, 0, 0, 0, 0, 0, 0, 0, 32, 0, toWord s, 0]
      o (cpre :: ks) = exec I f (cst s ((s + 7) / 8) 0 0) o ks := by
  have hc := LogScan.ceil8 (s := s) (by omega)
  have he : toWord ((s + 7) / 8) + 5#64 = toWord ((s + 7) / 8 + 5) := by
    simp only [toWord, BitVec.ofNat_add]
  have hlt : (5#64 < toWord ((s + 7) / 8 + 5)) ↔ 0 < (s + 7) / 8 :=
    (toWord_lt_toWord (a := 0 + 5) (by omega) (by omega)).trans (by omega)
  simp only [BitVec.ofNat_eq_ofNat] at hc
  simp only [cpre, seqs, exec, XOp.eval]
  simp [hc, he, cst, hlt, show toWord 5 = 5#64 from rfl]

theorem masked_start (I : Array Word) (cw pw : List Word) {n : ℕ}
    (h0 : I.getD 0 0 = cw.getD 0 0) (h1 : I.getD 1 0 = cw.getD 1 0)
    (h2 : I.getD 2 0 = cw.getD 2 0) (h3 : I.getD 3 0 = cw.getD 3 0) (h4 : I.getD 4 0 = 32)
    (h5 : I.getD 5 0 = pw.getD 0 0) (h6 : I.getD 6 0 = pw.getD 1 0)
    (h7 : I.getD 7 0 = pw.getD 2 0) (h8 : I.getD 8 0 = pw.getD 3 0) (h9 : I.getD 9 0 = toWord n)
    (f : ℕ) (o : Array Word) :
    exec I (f + 57) (Array.replicate 24 0) o [ext.body] =
      exec I f (mst cw pw 10 n 0 0 0 0) o [.loop 7 mbody] := by
  rw [show f + 57 = (f + 39 + 1 + 1) + 15 + 1 by omega, ext, exec_seq, pre0_exec I h4,
    LogScan.exec_ite_ne (by decide), exec_seq]
  simp only [↓reduceIte]
  exact mpre_exec I cw pw h0 h1 h2 h3 h5 h6 h7 h8 h9 f o _

theorem copy_start (I : Array Word) {s : ℕ} (hs : s < 2 ^ 60) (h32 : s ≠ 32)
    (h4 : I.getD 4 0 = toWord s) (f : ℕ) (o : Array Word) :
    exec I (f + 27) (Array.replicate 24 0) o [ext.body] =
      exec I f (cst s ((s + 7) / 8) 0 0) o [.loop 7 cstep] := by
  have hne : ¬ toWord s = 32 := fun h => h32 (by
    have := congrArg BitVec.toNat h; rwa [toNat_toWord (by omega)] at this)
  rw [show f + 27 = (f + 9 + 1 + 1) + 15 + 1 by omega, ext, exec_seq, pre0_exec I h4,
    LogScan.exec_ite_eq (by simp only [hne, ↓reduceIte]; rfl), exec_seq]
  simp only [hne, ↓reduceIte]
  exact cpre_exec I hs f o _

/-- The five comparisons, combined. -/
theorem flag5 (a b c d e : Prop) [Decidable a] [Decidable b] [Decidable c] [Decidable d]
    [Decidable e] :
    (((((if a then 1#64 else 0#64) &&& if b then 1#64 else 0#64) &&& if c then 1#64 else 0#64) &&&
      if d then 1#64 else 0#64) &&& if e then 1#64 else 0#64) =
    if a ∧ b ∧ c ∧ d ∧ e then 1#64 else 0#64 := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases hd : d <;>
    by_cases he : e <;> simp [ha, hb, hc, hd, he]

/-- The match condition of the entry at `p` whose query has `ℓ` bytes. -/
def hit (I : Array Word) (cw : List Word) (p ℓ : ℕ) : Prop :=
  toWord ℓ = 32 ∧ I.getD (p + 1) 0 = cw.getD 0 0 ∧ I.getD (p + 2) 0 = cw.getD 1 0 ∧
    I.getD (p + 3) 0 = cw.getD 2 0 ∧ I.getD (p + 4) 0 = cw.getD 3 0

instance (I : Array Word) (cw : List Word) (p ℓ : ℕ) : Decidable (hit I cw p ℓ) := by
  unfold hit; infer_instance

theorem mhead_exec (I : Array Word) (cw pw : List Word) {p n ℓ : ℕ} (x6 x8 x13 x14 : Word)
    (hℓ : ℓ < 2 ^ 64) (hp5 : p + 5 ≤ 2 ^ 64) (hq : I.getD p 0 = toWord ℓ) (f : ℕ) (o : Array Word)
    (ks : List XStmt) :
    exec I (f + 49) (mst cw pw p n x6 x8 x13 x14) o (mhead :: ks) = exec I f
      (mst cw pw (p + 1 + (ℓ + 7) / 8) n (if hit I cw p ℓ then 1 else 0) (toWord ((ℓ + 7) / 8)) 0
        (toWord (p + 4))) o ks := by
  have t1 : toWord p + 1#64 = toWord (p + 1) := toWord_add_one p
  have t2 : toWord (p + 1) + 1#64 = toWord (p + 2) := toWord_add_one _
  have t3 : toWord (p + 2) + 1#64 = toWord (p + 3) := toWord_add_one _
  have t4 : toWord (p + 3) + 1#64 = toWord (p + 4) := toWord_add_one _
  have hP : toWord (p + 1) + toWord ((ℓ + 7) / 8) = toWord (p + 1 + (ℓ + 7) / 8) := by
    simp only [toWord, BitVec.ofNat_add]
  simp only [BitVec.ofNat_eq_ofNat, Array.getD_eq_getD_getElem?] at hq
  simp [mhead, seqs, exec, XOp.eval, mst, hq, toNat_toWord (by omega : p < 2 ^ 64),
    toNat_toWord (by omega : p + 1 < 2 ^ 64), toNat_toWord (by omega : p + 2 < 2 ^ 64),
    toNat_toWord (by omega : p + 3 < 2 ^ 64), toNat_toWord (by omega : p + 4 < 2 ^ 64),
    t1, t2, t3, t4, hP, LogScan.ceilw hℓ, flag5, hit]

theorem mst_n_ne {cw pw : List Word} {p n : ℕ} (x6 x8 x13 x14 : Word) (hn0 : n ≠ 0)
    (hn : n < 2 ^ 64) : (mst cw pw p n x6 x8 x13 x14).getD 5 0 ≠ 0 := by
  simpa [mst] using (toWord_eq_zero hn).not.mpr hn0

theorem miter_next (I : Array Word) (cw pw : List Word) {p n ℓ : ℕ} (x6 x8 x13 x14 : Word)
    (hn0 : n ≠ 0) (hn : n < 2 ^ 64) (hℓ : ℓ < 2 ^ 64) (hp5 : p + 5 ≤ 2 ^ 64)
    (hq : I.getD p 0 = toWord ℓ) (hmiss : ¬ hit I cw p ℓ) (f : ℕ) (o : Array Word) :
    exec I (f + 56) (mst cw pw p n x6 x8 x13 x14) o [.loop 7 mbody] =
      exec I f (mst cw pw (p + 1 + (ℓ + 7) / 8 + 4) (n - 1) 0 (toWord ((ℓ + 7) / 8)) 0
        (toWord (p + 4))) o [.loop 7 mbody] := by
  rw [show f + 56 = (f + 3 + 1 + 49) + 1 + 1 + 1 by omega, exec_loop_ne (by simp [mst]), mbody,
    LogScan.exec_ite_ne (mst_n_ne x6 x8 x13 x14 hn0 hn), exec_seq,
    mhead_exec I cw pw x6 x8 x13 x14 hℓ hp5 hq,
    LogScan.exec_ite_eq (by simp [mst, hmiss])]
  have e1 : toWord (p + 1 + (ℓ + 7) / 8) + 4#64 = toWord (p + 1 + (ℓ + 7) / 8 + 4) := by
    simp only [toWord, BitVec.ofNat_add]
  have e2 : toWord n - 1#64 = toWord (n - 1) := LogScan.toWord_sub_one hn0
  simp [mnext, seqs, exec, XOp.eval, mst, e1, e2, hmiss]

theorem miter_found (I : Array Word) (cw pw aw : List Word) {p n ℓ : ℕ} (x6 x8 x13 x14 : Word)
    (hn0 : n ≠ 0) (hn : n < 2 ^ 64) (hℓ : ℓ < 2 ^ 64) (hp : p + 1 + (ℓ + 7) / 8 + 4 ≤ 2 ^ 64)
    (hp5 : p + 5 ≤ 2 ^ 64) (hq : I.getD p 0 = toWord ℓ)
    (ha : ∀ j < 4, I.getD (p + 1 + (ℓ + 7) / 8 + j) 0 = aw.getD j 0) (hhit : hit I cw p ℓ)
    (f : ℕ) (o : Array Word) :
    exec I (f + 89) (mst cw pw p n x6 x8 x13 x14) o [.loop 7 mbody] =
      some (o.toList ++ 0 :: 1 :: xor4 pw aw) := by
  rw [show f + 89 = (f + 1 + 35 + 1 + 49) + 1 + 1 + 1 by omega, exec_loop_ne (by simp [mst]),
    mbody, LogScan.exec_ite_ne (mst_n_ne x6 x8 x13 x14 hn0 hn), exec_seq,
    mhead_exec I cw pw x6 x8 x13 x14 hℓ hp5 hq,
    LogScan.exec_ite_ne (by simp [mst, hhit])]
  set P := p + 1 + (ℓ + 7) / 8
  have a0 := ha 0 (by omega)
  have a1 := ha 1 (by omega)
  have a2 := ha 2 (by omega)
  have a3 := ha 3 (by omega)
  have t1 : toWord P + 1#64 = toWord (P + 1) := toWord_add_one P
  have t2 : toWord (P + 1) + 1#64 = toWord (P + 2) := toWord_add_one _
  have t3 : toWord (P + 2) + 1#64 = toWord (P + 3) := toWord_add_one _
  simp only [Nat.add_zero, BitVec.ofNat_eq_ofNat, Array.getD_eq_getD_getElem?] at a0 a1 a2 a3
  simp [mfound, seqs, exec, XOp.eval, mst, xor4, t1, t2, t3, a0, a1, a2, a3,
    toNat_toWord (by omega : P < 2 ^ 64), toNat_toWord (by omega : P + 1 < 2 ^ 64),
    toNat_toWord (by omega : P + 2 < 2 ^ 64), toNat_toWord (by omega : P + 3 < 2 ^ 64)]

theorem miter_end (I : Array Word) (cw pw : List Word) {p : ℕ} (x6 x8 x13 x14 : Word) (f : ℕ)
    (o : Array Word) : exec I (f + 4) (mst cw pw p 0 x6 x8 x13 x14) o [.loop 7 mbody] =
      some o.toList := by
  simp [mst, mbody, exec, show toWord 0 = 0#64 from rfl]

/-- **The copy loop**: from word `i` of `m`, `k = m - i` iterations of 8 steps output tape words
`i + 5, …, m + 4`. -/
theorem cloop (I : Array Word) {s m : ℕ} (hm : m + 6 < 2 ^ 64) :
    ∀ k i y (o : Array Word) f, i + k = m →
      exec I (f + 8 * k + 1) (cst s m i y) o [.loop 7 cstep] =
        some (o.toList ++ (List.range k).map fun j => I.getD (i + j + 5) 0) := by
  intro k
  induction k with
  | zero =>
    intro i y o f rfl
    simp [cst, exec]
  | succ k ih =>
    intro i y o f hi
    have hlt : i < m := by omega
    have h1 : toWord (i + 1 + 5) < toWord (m + 5) ↔ i + 1 < m :=
      (toWord_lt_toWord (by omega) (by omega)).trans (by omega)
    have h5 : (toWord (i + 5)).toNat = i + 5 := toNat_toWord (by omega)
    have hs := runs_seq (runs_input (I := I) 8 4 (cst s m i y) o) (runs_seq (runs_out 8 _ _)
      (runs_seq (runs_op .add 4 4 9 _ _) (runs_op .ltu 7 4 5 _ _)))
    have h6 : toWord (i + 1 + 5) = toWord (i + 5) + 1 := by
      rw [toWord_add_one, show i + 5 + 1 = i + 1 + 5 by omega]
    have key : Runs I cstep (cst s m i y) o 7 (cst s m (i + 1) (I.getD (i + 5) 0))
        (o.push (I.getD (i + 5) 0)) := by
      convert hs using 2
      · rfl
      · simp only [cst, Array.getD_eq_getD_getElem?, XOp.eval, h6, ← h1]
        simp [h5]
      · simp [cst, h5]
    rw [show f + 8 * (k + 1) + 1 = (7 + (f + 8 * k + 1)) + 1 by ring,
      exec_loop_ne (by simp [cst, hlt]), key, ih (i + 1) _ _ f (by omega)]
    simp [List.range_succ_eq_map, Nat.add_assoc, Nat.add_comm 1]

/-- The scan's output for the result of the search. -/
def moutW (pw : List Word) : Option (ByteArray × Digest) → List Word
  | none => []
  | some e => 0 :: 1 :: xor4 pw (packBytes e.2.toList)

theorem size_cq (c : Digest) : (cq c).size = 32 := c.size_toArray

theorem cq_data (c : Digest) : (cq c).data.toList = c.toList := rfl

/-- A 32-byte query whose packed words are the statement's is `cq c`. -/
theorem eq_cq {q : ByteArray} {c : Digest} (hq : q.size = 32)
    (h : packBytes q.data.toList = packBytes c.toList) : q = cq c := by
  have h1 := unpack_packBytes q.data.toList
  have h2 := unpack_packBytes c.toList
  have hl : q.data.toList.length = 32 := by rw [Array.length_toList]; exact hq
  rw [h, hl] at h1
  rw [Vector.length_toList] at h2
  rw [h2] at h1
  cases q with
  | mk d => exact congrArg ByteArray.mk (Array.toList_inj.mp h1.symm)

/-- A query's words on the tape. -/
theorem query_words {T A rest : List Word} {e : ByteArray × Digest}
    (hT : T = A ++ LogScan.ew e ++ rest) {j : ℕ} (hj : j < (packBytes e.1.data.toList).length) :
    T.toArray.getD (A.length + 1 + j) 0 = (packBytes e.1.data.toList)[j] := by
  rw [getD_toArray, hT, show A ++ LogScan.ew e ++ rest =
      (A ++ [toWord e.1.data.toList.length]) ++ packBytes e.1.data.toList ++
        (packBytes e.2.toList ++ rest) by simp [LogScan.ew, bytesWords],
    show A.length + 1 + j = (A ++ [toWord e.1.data.toList.length]).length + j by simp,
    getD_append_mid _ _ _ hj]

/-- **The match is the query `cq c`.** -/
theorem hit_iff {T A rest : List Word} {e : ByteArray × Digest} (c : Digest)
    (hT : T = A ++ LogScan.ew e ++ rest) (hℓ : e.1.size < 2 ^ 64) :
    hit T.toArray (packBytes c.toList) A.length e.1.size ↔ e.1 = cq c := by
  have hw : ∀ j < 4, e.1.size = 32 →
      T.toArray.getD (A.length + 1 + j) 0 = (packBytes e.1.data.toList).getD j 0 := by
    intro j hj h32
    have hl : (packBytes e.1.data.toList).length = 4 := by
      rw [packBytes_length, Array.length_toList, ByteArray.size_data, h32]
    rw [query_words hT (by omega), List.getD_eq_getElem _ _ (by omega)]
  constructor
  · rintro ⟨h32, h0, h1, h2, h3⟩
    have hs : e.1.size = 32 := by
      have := congrArg BitVec.toNat h32; rwa [toNat_toWord hℓ] at this
    refine eq_cq hs ?_
    have hl : (packBytes e.1.data.toList).length = 4 := by
      rw [packBytes_length, Array.length_toList, ByteArray.size_data, hs]
    rw [LogScan.four _ hl, LogScan.four (packBytes c.toList) (packBytes_digest_length c),
      ← hw 0 (by omega) hs, ← hw 1 (by omega) hs, ← hw 2 (by omega) hs, ← hw 3 (by omega) hs]
    simp only [Nat.add_zero, Nat.add_assoc] at h0 h1 h2 h3 ⊢
    rw [h0, h1, h2, h3]
  · intro he
    have hs : e.1.size = 32 := by rw [he, size_cq]
    refine ⟨by rw [hs]; rfl, ?_, ?_, ?_, ?_⟩ <;>
      [have := hw 0 (by omega) hs; have := hw 1 (by omega) hs; have := hw 2 (by omega) hs;
        have := hw 3 (by omega) hs] <;>
      simpa [he, cq_data, Nat.add_assoc] using this

theorem mloop (c : Digest) (pw : List Word) (T : List Word) (hT : T.length ≤ 2 ^ 64) :
    ∀ (L : Log) (A : List Word) (x6 x8 x13 x14 : Word) (o : Array Word) (f : ℕ),
      T = A ++ L.flatMap LogScan.ew → (∀ e ∈ L, e.1.size < 2 ^ 64) → L.length < 2 ^ 64 →
      exec T.toArray (f + 56 * L.length + 89)
        (mst (packBytes c.toList) pw A.length L.length x6 x8 x13 x14) o [.loop 7 mbody] =
        some (o.toList ++ moutW pw (L.find? fun e => e.1 = cq c)) := by
  intro L
  induction L with
  | nil =>
    intro A x6 x8 x13 x14 o f _ _ _
    simpa [moutW] using miter_end T.toArray (packBytes c.toList) pw x6 x8 x13 x14 (f + 85) o
  | cons e L ih =>
    intro A x6 x8 x13 x14 o f hA hq hi
    have hlen := congrArg List.length hA
    simp only [List.flatMap_cons, List.length_append, LogScan.ew_length] at hlen
    have hA' : T = (A ++ LogScan.ew e) ++ L.flatMap LogScan.ew := by
      rw [hA, List.flatMap_cons, List.append_assoc]
    have hq0 : T.toArray.getD A.length 0 = toWord e.1.size := by
      rw [getD_toArray, hA, List.flatMap_cons]
      simp only [LogScan.ew, bytesWords, List.cons_append, List.append_assoc]
      rw [getD_append_length, Array.length_toList, ByteArray.size_data]
    have ha : ∀ j < 4, T.toArray.getD (A.length + 1 + (e.1.size + 7) / 8 + j) 0 =
        (packBytes e.2.toList).getD j 0 := fun j hj => by
      rw [getD_toArray, hA, List.flatMap_cons, LogScan.ew]
      have : A.length + 1 + (e.1.size + 7) / 8 =
          (A ++ bytesWords e.1.data.toList).length := by
        simp only [bytesWords, List.length_append, List.length_cons, packBytes_length,
          Array.length_toList, ByteArray.size_data]
        omega
      rw [this, ← List.append_assoc, ← List.append_assoc,
        getD_append_mid _ _ _ (by rw [packBytes_digest_length]; exact hj),
        List.getD_eq_getElem _ _ (by rw [packBytes_digest_length]; exact hj)]
    have hℓ := hq e (by simp)
    have hp : A.length + 1 + (e.1.size + 7) / 8 + 4 ≤ 2 ^ 64 := by omega
    have hlA : (A ++ LogScan.ew e).length = A.length + 1 + (e.1.size + 7) / 8 + 4 := by
      rw [List.length_append, LogScan.ew_length]; omega
    have hiff := hit_iff (T := T) (A := A) c hA' hℓ
    rw [List.length_cons]
    by_cases hc : e.1 = cq c
    · rw [List.find?_cons_of_pos (by simpa using hc),
        show f + 56 * (L.length + 1) + 89 = (f + 56 * L.length + 56) + 89 by ring,
        miter_found T.toArray _ pw _ x6 x8 x13 x14 (by simp) (by simp at hi; omega) hℓ hp
          (by omega) hq0 ha (hiff.mpr hc)]
      rfl
    · rw [List.find?_cons_of_neg (by simpa using hc),
        show f + 56 * (L.length + 1) + 89 = (f + 56 * L.length + 89) + 56 by ring,
        miter_next T.toArray _ pw x6 x8 x13 x14 (by simp) (by simp at hi; omega) hℓ (by omega)
          hq0 (mt hiff.mp hc), Nat.add_sub_cancel, ← hlA,
        ih (A ++ LogScan.ew e) _ _ _ _ o f hA' (fun e' he' => hq e' (by simp [he']))
          (by simp at hi; omega)]

/-! ## The program computes the extractor -/

theorem decode_moutW (π : Proof) (e : ByteArray × Digest) :
    decodeWit (moutW (packBytes π.data.toList) (some e)) = some (.leaf [unmask π e.2]) := by
  have := decodeWit_witWords (.leaf [unmask π e.2]) (show [_].length < 2 ^ 64 by simp)
  simp only [witWords, List.length_cons, List.length_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, packBytes_unmask] at this
  simpa [moutW, show toWord 0 = 0 from rfl, show toWord 1 = 1 from rfl] using this

/-- **The program computes the extractor** within `32 · t` steps, on the contract's whole domain. -/
theorem computes : Computes submission.ext submission.E submission.fuel := by
  intro c π L hπ hq ht
  show ∃ o, ext.run _ (32 * _) = some o ∧ o.length ≤ outCap ∧ decodeWit o = E c π L
  set T := extractorInput c π L with hT
  set m := (π.size + 7) / 8
  have hA : T = ((packBytes c.toList ++ [toWord π.size]) ++ packBytes π.data.toList ++
      [toWord L.length]) ++ L.flatMap LogScan.ew := by
    rw [hT, WitnessSending.extractorInput_eq]; simp; rfl
  have h4 := packBytes_digest_length c
  have hm : (packBytes π.data.toList).length = m := by
    simp [packBytes_length, m, Array.length_toList]
  have hAl : ((packBytes c.toList ++ [toWord π.size]) ++ packBytes π.data.toList ++
      [toWord L.length]).length = m + 6 := by simp [h4, hm]; omega
  have hlen := congrArg List.length hA
  rw [List.length_append, hAl] at hlen
  have h5L := LogScan.flatMap_length L
  have hc : ∀ j < 4, T.toArray.getD j 0 = (packBytes c.toList).getD j 0 := fun j hj => by
    rw [getD_toArray, hA]
    simp only [List.append_assoc]
    rw [List.getD_append _ _ _ _ (by rw [h4]; exact hj)]
  have hs : T.toArray.getD 4 0 = toWord π.size := by
    rw [getD_toArray, hA]
    simp only [List.append_assoc, List.cons_append]
    rw [show 4 = (packBytes c.toList).length from h4.symm, getD_append_length]
  have hpw : ∀ j < m, T.toArray.getD (5 + j) 0 = (packBytes π.data.toList).getD j 0 :=
    fun j hj => by
      rw [getD_toArray, hA, List.append_assoc, List.append_assoc,
        show 5 + j = (packBytes c.toList ++ [toWord π.size]).length + j by simp [h4],
        ← List.append_assoc, getD_append_mid _ _ _ (by rw [hm]; exact hj),
        List.getD_eq_getElem _ _ (by rw [hm]; exact hj)]
  have hn : T.toArray.getD (m + 5) 0 = toWord L.length := by
    rw [getD_toArray, hA, show packBytes c.toList ++ [toWord π.size] ++ packBytes π.data.toList ++
        [toWord L.length] ++ L.flatMap LogScan.ew = (packBytes c.toList ++ [toWord π.size] ++
        packBytes π.data.toList) ++ toWord L.length :: L.flatMap LogScan.ew by simp,
      show m + 5 = (packBytes c.toList ++ [toWord π.size] ++ packBytes π.data.toList).length by
        simp [h4, hm]; omega, getD_append_length]
  have hπc : π.size < 2 ^ 60 := by unfold outCap at hπ; omega
  have hmem : ext.memFor T.length = 24 := by simp [ext, XProg.memFor]
  rw [XProg.run_eq (by omega), hmem]
  by_cases h32 : π.size = 32
  · have hm4 : m = 4 := by simp [m, h32]
    simp only [hm4] at hpw hn hlen
    rw [show 32 * T.length - 24 = (32 * T.length - 24 - 57 - 56 * L.length - 89) +
        56 * L.length + 89 + 57 by omega,
      masked_start T.toArray (packBytes c.toList) (packBytes π.data.toList)
        (hc 0 (by omega)) (hc 1 (by omega)) (hc 2 (by omega)) (hc 3 (by omega))
        (by rw [hs, h32]; rfl) (hpw 0 (by omega)) (hpw 1 (by omega)) (hpw 2 (by omega))
        (hpw 3 (by omega)) hn,
      show (10 : ℕ) = ((packBytes c.toList ++ [toWord π.size]) ++ packBytes π.data.toList ++
        [toWord L.length]).length by rw [hAl, hm4],
      mloop c _ T ht L _ 0 0 0 0 #[] _ hA hq (by omega)]
    refine ⟨_, rfl, ?_, ?_⟩
    · cases L.find? (fun e => e.1 = cq c) <;> simp [moutW, xor4, outCap]
    · simp only [E, h32, ↓reduceIte, List.nil_append]
      cases h : L.find? (fun e => e.1 = cq c) with
      | none => rfl
      | some e => exact decode_moutW π e
  · rw [show 32 * T.length - 24 = ((32 * T.length - 24 - 8 * m - 1 - 27) + 8 * m + 1) + 27 by
        omega, copy_start T.toArray hπc h32 hs,
      cloop T.toArray (by omega) m 0 0 #[] _ (by omega)]
    refine ⟨_, rfl, ?_, ?_⟩
    · simp [m, outCap] at hπ ⊢; omega
    · simp only [E, h32, ↓reduceIte, WitnessSending.decode, List.nil_append]
      congr 1
      refine List.ext_getElem (by simp [hm]) fun j _ h2 => ?_
      simp only [List.getElem_map, List.getElem_range, Nat.zero_add]
      rw [show j + 5 = 5 + j by omega, hpw j (by rw [hm] at h2; exact h2),
        List.getD_eq_getElem _ _ h2]

/-- The program has 167 statements. -/
theorem ext_size : ext.body.size = 167 := rfl

/-! ## The certificate -/

/-- **The masked-leaf submission is certified**, for every public key. -/
theorem certificate : Certificate submission where
  secure := ks
  complete := complete
  computes := computes
  cap := ⟨zero_le, zero_le, by decide, fun t => by
    simp only [submission, fuel, extractorBudget]; omega, by
    show ext.body.size ≤ progCap; rw [ext_size]; decide⟩

/-- The claim of the masked-leaf submission, as a challenge renders it. -/
def declared : Declared where
  ε := 0
  δ := 0
  qV := 1
  fuel := fuel

/-- **The certificate against the rendered claim.** -/
theorem certificateR : CertificateR declared submission :=
  ⟨certificate, le_rfl, le_rfl, le_rfl, fun t => ⟨le_rfl, certificate.cap.2.2.2.1 t⟩⟩

/-! ## Negatives -/

/-- **The verifier asks its query**: with the bound `qV = 0` it is not knowledge-sound, for any
extractor and error. -/
theorem not_qV_zero (vk : Digest) (E' : Digest → Proof → Log → Option Wit) (ε : ℝ≥0) :
    ¬ KS (Rel (submission.acc vk)) (V vk) E' ε 0 := fun h =>
  absurd (h.1 (fun _ => Vector.replicate 32 0) (Vector.replicate 32 0) .empty)
    (by rw [queries_V]; decide)

/-- **The extractor reads the log**: on the honest masked proof it returns the leaf from a log
holding the answer to `cq c`, and nothing from the empty log. -/
theorem extractor_reads_log (c x a : Digest) :
    E c (mask x a) [(cq c, a)] = some (.leaf [x]) ∧ E c (mask x a) [] = none := by
  simp [E, size_mask, unmask_mask]

end RecursionFast.Controls.MaskedLeaf
