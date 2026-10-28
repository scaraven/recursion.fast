/-
# Controls: a program that reads the log (`Contract/Extractor.lean`; V3-S2R review M2)

The handoff's log-indexing control (§2.5): a program of the contract's machine that finds a log
entry **by its answer**, as an extractor finds a preimage, and computes that specification within
`16 · t` steps, well inside the budget's linear term `2^16 · t`. It reads every part of the tape
that a log-reading extractor needs: the statement, the proof's length word (to skip the proof),
the number of entries, and for each entry the query's length word, from which it computes
`⌈|q|/8⌉` without overflow to skip the query, and the 4-word answer, which it compares with the
statement. The proof uses the domain's bound on query lengths (`Computes`, V3-S2R-A9): a length
word is a number's low 64 bits, so without it no program could tell where an entry ends.

* `findE c π L`: the leaf witness `(c, j)` for the first entry `j` whose answer is `c`, or none.
* `scan`: 16 memory words (`memPerWord = 0`: one pass needs no memory proportional to the tape),
  106 statements (`XStmt.size`). Set-up 42 steps, then 50 steps per entry passed over, 59 on the
  matching entry and 4 at the end of the log; an entry has at least 5 words, so `16 · t` covers it.

Positive:
* `scan_computes`: **`Computes scan findE (16 · t)`**, on the contract's whole domain, and
  `scan_fuel_le`: `16 · t ≤ B t`.
* `scan_kat`: on a two-entry log whose second answer is the statement, the output is the leaf
  `(c, 1)` (the kernel runs the program).

Negative:
* `scan_fuel_short`: not within `10 · t` steps: on the 6-word tape of the empty log the program
  needs 62.
* `scan_not_none`: it does not compute the extractor that returns nothing: on the log of
  `scan_kat` it outputs a witness, so it reads the log.
-/
import RecursionFast.Library.WitnessSending

namespace RecursionFast.Controls.LogScan
open RecursionFast XStmt

/-- **The specification**: the leaf witness `(c, j)` for the first log entry `j` whose answer is
the statement `c`, or none. -/
def findE (c : Digest) (_ : Proof) (L : Log) : Option Wit :=
  (L.findIdx? fun e => e.2 = c).map (.leaf c)

/-! ## The program

Memory: cells `0 … 3` the statement's words, `4` the tape position `p`, `5` the entries left `n`,
`6` the entry index `i`, `7` the loop condition, `8` a scratch word, `9 … 12` the constants
`1, 7, 3, 4`, `13` the match flag, `14` a scratch word, `15` stays `0`. -/

/-- Read the statement, skip the proof, read the number of entries; position at the first entry. -/
def pre : XStmt := seqs (.const 4 0)
  [.input 0 4, .const 4 1, .input 1 4, .const 4 2, .input 2 4, .const 4 3, .input 3 4,
   .const 9 1, .const 10 7, .const 11 3, .const 12 4,
   .const 4 4, .input 8 4, .op .add 8 8 10, .op .shr 8 8 11,
   .op .add 4 4 9, .op .add 4 4 8, .input 5 4, .op .add 4 4 9, .const 7 1]

/-- Skip the entry's query (`⌈|q|/8⌉` as `(|q| >>> 3) + (|q| % 8 ≠ 0)`, without overflow) and
compare its answer with the statement. -/
def head : XStmt := seqs (.input 8 4)
  [.op .and 13 8 10, .op .ltu 13 15 13, .op .shr 8 8 11, .op .add 8 8 13,
   .op .add 4 4 9, .op .add 4 4 8,
   .input 14 4, .op .eq 13 14 0,
   .op .add 8 4 9, .input 14 8, .op .eq 14 14 1, .op .and 13 13 14,
   .op .add 8 8 9, .input 14 8, .op .eq 14 14 2, .op .and 13 13 14,
   .op .add 8 8 9, .input 14 8, .op .eq 14 14 3, .op .and 13 13 14]

/-- A match: output the leaf `(c, i)` and stop. -/
def found : XStmt := seqs (.out 15) [.out 0, .out 1, .out 2, .out 3, .out 6, .const 7 0]

/-- No match: move to the next entry. -/
def next : XStmt := seqs (.op .add 4 4 12) [.op .add 6 6 9, .op .sub 5 5 9]

/-- One iteration: an entry if any is left, else stop. -/
def body : XStmt := .ite 5 (.seq head (.ite 13 found next)) (.const 7 0)

/-- **The log scan.** -/
def scan : XProg := ⟨16, 0, .seq pre (.loop 7 body)⟩

/-! ## Correctness

`st` is the memory at the start of an iteration. The set-up block reaches it (`pre_exec`); an
iteration passes over an entry whose answer is not the statement in 50 steps (`iter_next`), outputs
the leaf on a match in 58 steps and stops (`iter_found`), and stops at the end of the log
(`iter_end`). `scan_loop` runs the loop over the log by induction, within `50` steps per entry
and `9` more. -/

/-- The memory at the start of an iteration. -/
def st (cw : List Word) (p n i : ℕ) (x acc y : Word) : Array Word :=
  #[cw.getD 0 0, cw.getD 1 0, cw.getD 2 0, cw.getD 3 0, toWord p, toWord n, toWord i, 1, x, 1, 7, 3,
    4, acc, y, 0]

/-- `(s + 7) >>> 3` on a small proof length. -/
theorem ceil8 {s : ℕ} (hs : s + 7 < 2 ^ 64) : (toWord s + 7) >>> 3 = toWord ((s + 7) / 8) := by
  apply BitVec.eq_of_toNat_eq
  have h7 : (7 : Word).toNat = 7 := rfl
  simp only [toWord, BitVec.toNat_add, h7, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  omega

theorem pre_exec (I : Array Word) (cw : List Word) {s n : ℕ} (hs : s + 13 < 2 ^ 64)
    (h0 : I.getD 0 0 = cw.getD 0 0) (h1 : I.getD 1 0 = cw.getD 1 0)
    (h2 : I.getD 2 0 = cw.getD 2 0) (h3 : I.getD 3 0 = cw.getD 3 0)
    (h4 : I.getD 4 0 = toWord s) (h5 : I.getD ((s + 7) / 8 + 5) 0 = toWord n)
    (f : ℕ) (o : Array Word) (ks : List XStmt) :
    exec I (f + 41) (Array.replicate 16 0) o (pre :: ks) =
      exec I f (st cw ((s + 7) / 8 + 6) n 0 (toWord ((s + 7) / 8)) 0 0) o ks := by
  rw [show Array.replicate 16 (0 : Word) = #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] from
    rfl]
  have hc := ceil8 (s := s) (by omega)
  simp only [BitVec.ofNat_eq_ofNat, Array.getD_eq_getD_getElem?] at h0 h1 h2 h3 h4 h5 hc
  have hm : (toWord ((s + 7) / 8)).toNat = (s + 7) / 8 := toNat_toWord (by omega)
  have hi : (5 + (s + 7) / 8) % 18446744073709551616 = (s + 7) / 8 + 5 := by omega
  have hp : 5#64 + toWord ((s + 7) / 8) + 1#64 = toWord ((s + 7) / 8 + 6) := by
    apply BitVec.eq_of_toNat_eq; simp only [toWord, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp [pre, seqs, exec, XOp.eval, h0, h1, h2, h3, h4, hc, hm, hi, h5, hp, st,
    show toWord 0 = 0#64 from rfl]

/-- `⌈ℓ/8⌉` without overflow, for every `ℓ < 2^64`. -/
theorem ceilw {ℓ : ℕ} (hℓ : ℓ < 2 ^ 64) :
    (toWord ℓ >>> 3 + if 0#64 < toWord ℓ &&& 7#64 then 1#64 else 0#64) = toWord ((ℓ + 7) / 8) := by
  apply BitVec.eq_of_toNat_eq
  have h7 : (toWord ℓ &&& 7#64).toNat = ℓ % 8 := by
    simp only [BitVec.toNat_and, toNat_toWord hℓ]
    exact Nat.and_two_pow_sub_one_eq_mod ℓ 3
  have hlt : (0#64 < toWord ℓ &&& 7#64) ↔ 0 < ℓ % 8 := by
    rw [BitVec.lt_def, h7]; simp
  split_ifs with h <;> rw [hlt] at h <;>
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, toWord, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] <;> omega

/-- The four comparisons, combined. -/
theorem flag (a0 a1 a2 a3 c0 c1 c2 c3 : Word) :
    ((((if a0 = c0 then 1#64 else 0#64) &&& if a1 = c1 then 1#64 else 0#64) &&&
      if a2 = c2 then 1#64 else 0#64) &&& if a3 = c3 then 1#64 else 0#64) =
    if a0 = c0 ∧ a1 = c1 ∧ a2 = c2 ∧ a3 = c3 then 1#64 else 0#64 := by
  by_cases h0 : a0 = c0 <;> by_cases h1 : a1 = c1 <;> by_cases h2 : a2 = c2 <;>
    by_cases h3 : a3 = c3 <;> simp [h0, h1, h2, h3]

theorem head_exec (I : Array Word) (cw aw : List Word) {p n i ℓ : ℕ} (x acc y : Word)
    (hℓ : ℓ < 2 ^ 64) (hp : p + 1 + (ℓ + 7) / 8 + 4 ≤ 2 ^ 64)
    (hq : I.getD p 0 = toWord ℓ) (ha : ∀ j < 4, I.getD (p + 1 + (ℓ + 7) / 8 + j) 0 = aw.getD j 0)
    (f : ℕ) (o : Array Word) (ks : List XStmt) :
    exec I (f + 41) (st cw p n i x acc y) o (head :: ks) = exec I f
      #[cw.getD 0 0, cw.getD 1 0, cw.getD 2 0, cw.getD 3 0, toWord (p + 1 + (ℓ + 7) / 8), toWord n,
        toWord i, 1, toWord (p + 1 + (ℓ + 7) / 8 + 3), 1, 7, 3, 4,
        if aw.getD 0 0 = cw.getD 0 0 ∧ aw.getD 1 0 = cw.getD 1 0 ∧ aw.getD 2 0 = cw.getD 2 0 ∧
          aw.getD 3 0 = cw.getD 3 0 then 1 else 0,
        if aw.getD 3 0 = cw.getD 3 0 then 1 else 0, 0] o ks := by
  set P := p + 1 + (ℓ + 7) / 8 with hP
  have hP' : toWord p + 1#64 + toWord ((ℓ + 7) / 8) = toWord P := by
    simp only [hP, toWord, BitVec.ofNat_add]
  have a0 := ha 0 (by omega)
  have a1 := ha 1 (by omega)
  have a2 := ha 2 (by omega)
  have a3 := ha 3 (by omega)
  have t1 : toWord P + 1#64 = toWord (P + 1) := toWord_add_one P
  have t2 : toWord (P + 1) + 1#64 = toWord (P + 2) := toWord_add_one _
  have t3 : toWord (P + 2) + 1#64 = toWord (P + 3) := toWord_add_one _
  simp only [Nat.add_zero, BitVec.ofNat_eq_ofNat, Array.getD_eq_getD_getElem?] at hq a0 a1 a2 a3
  simp [head, seqs, exec, XOp.eval, st, hq, toNat_toWord (by omega : p < 2 ^ 64), ceilw hℓ, hP', t1,
    t2, t3, toNat_toWord (by omega : P < 2 ^ 64), toNat_toWord (by omega : P + 1 < 2 ^ 64),
    toNat_toWord (by omega : P + 2 < 2 ^ 64), toNat_toWord (by omega : P + 3 < 2 ^ 64), a0, a1, a2,
    a3, flag]

theorem exec_ite_eq {I : Array Word} {c : ℕ} {p q : XStmt} {M o : Array Word} {n : ℕ}
    {ks : List XStmt} (h : M.getD c 0 = 0) :
    exec I (n + 1) M o (.ite c p q :: ks) = exec I n M o (q :: ks) := by
  simp only [exec, h, ↓reduceIte]

theorem exec_ite_ne {I : Array Word} {c : ℕ} {p q : XStmt} {M o : Array Word} {n : ℕ}
    {ks : List XStmt} (h : M.getD c 0 ≠ 0) :
    exec I (n + 1) M o (.ite c p q :: ks) = exec I n M o (p :: ks) := by
  simp only [exec, h, ↓reduceIte]

theorem toWord_sub_one {n : ℕ} (h : n ≠ 0) : toWord n - 1 = toWord (n - 1) := by
  conv_lhs => rw [show n = n - 1 + 1 by omega, ← toWord_add_one]
  simp [BitVec.add_sub_cancel]

theorem st_n_ne {cw : List Word} {p n i : ℕ} (x acc y : Word) (hn0 : n ≠ 0) (hn : n < 2 ^ 64) :
    (st cw p n i x acc y).getD 5 0 ≠ 0 := by
  simpa [st] using (toWord_eq_zero hn).not.mpr hn0

theorem iter_next (I : Array Word) (cw aw : List Word) {p n i ℓ : ℕ} (x acc y : Word)
    (hn0 : n ≠ 0) (hn : n < 2 ^ 64) (hℓ : ℓ < 2 ^ 64) (hp : p + 1 + (ℓ + 7) / 8 + 4 ≤ 2 ^ 64)
    (hq : I.getD p 0 = toWord ℓ) (ha : ∀ j < 4, I.getD (p + 1 + (ℓ + 7) / 8 + j) 0 = aw.getD j 0)
    (hmiss : ¬ (aw.getD 0 0 = cw.getD 0 0 ∧ aw.getD 1 0 = cw.getD 1 0 ∧
      aw.getD 2 0 = cw.getD 2 0 ∧ aw.getD 3 0 = cw.getD 3 0))
    (f : ℕ) (o : Array Word) :
    exec I (f + 50) (st cw p n i x acc y) o [.loop 7 body] =
      exec I f (st cw (p + 1 + (ℓ + 7) / 8 + 4) (n - 1) (i + 1) (toWord (p + 1 + (ℓ + 7) / 8 + 3))
        0 (if aw.getD 3 0 = cw.getD 3 0 then 1 else 0)) o [.loop 7 body] := by
  rw [show f + 50 = (f + 5 + 1 + 41 + 1) + 1 + 1 by omega, exec_loop_ne (by simp [st]), body,
    exec_ite_ne (st_n_ne x acc y hn0 hn), exec_seq, head_exec I cw aw x acc y hℓ hp hq ha,
    exec_ite_eq (by show (if _ then (1 : Word) else 0) = 0; simp only [hmiss, ↓reduceIte])]
  rw [show f + 5 = f + 1 + 1 + 1 + 1 + 1 by omega]
  simp only [next, seqs, exec]
  refine congrArg (fun M => exec I f M o _) ?_
  have e1 : toWord (p + 1 + (ℓ + 7) / 8) + 4#64 = toWord (p + 1 + (ℓ + 7) / 8 + 4) := by
    simp only [toWord, BitVec.ofNat_add]
  have e2 : toWord n - 1#64 = toWord (n - 1) := toWord_sub_one hn0
  have e3 : toWord i + 1#64 = toWord (i + 1) := toWord_add_one i
  simp [st, XOp.eval, e1, e2, e3]
  simpa using hmiss

theorem iter_found (I : Array Word) (cw aw : List Word) {p n i ℓ : ℕ} (x acc y : Word)
    (hn0 : n ≠ 0) (hn : n < 2 ^ 64) (hℓ : ℓ < 2 ^ 64) (hp : p + 1 + (ℓ + 7) / 8 + 4 ≤ 2 ^ 64)
    (hq : I.getD p 0 = toWord ℓ) (ha : ∀ j < 4, I.getD (p + 1 + (ℓ + 7) / 8 + j) 0 = aw.getD j 0)
    (hhit : aw.getD 0 0 = cw.getD 0 0 ∧ aw.getD 1 0 = cw.getD 1 0 ∧
      aw.getD 2 0 = cw.getD 2 0 ∧ aw.getD 3 0 = cw.getD 3 0)
    (f : ℕ) (o : Array Word) :
    exec I (f + 59) (st cw p n i x acc y) o [.loop 7 body] =
      some (o.toList ++ [0, cw.getD 0 0, cw.getD 1 0, cw.getD 2 0, cw.getD 3 0, toWord i]) := by
  rw [show f + 59 = (f + 1 + 13 + 1 + 41 + 1) + 1 + 1 by omega, exec_loop_ne (by simp [st]), body,
    exec_ite_ne (st_n_ne x acc y hn0 hn), exec_seq, head_exec I cw aw x acc y hℓ hp hq ha,
    exec_ite_ne (by
      show (if _ then (1 : Word) else 0) ≠ 0; simp only [hhit, and_self, ↓reduceIte]; decide)]
  simp [found, seqs, exec]

theorem iter_end (I : Array Word) (cw : List Word) {p i : ℕ} (x acc y : Word) (f : ℕ)
    (o : Array Word) : exec I (f + 4) (st cw p 0 i x acc y) o [.loop 7 body] = some o.toList := by
  simp [st, body, exec, show toWord 0 = 0#64 from rfl]

/-- An entry's words on the tape: the query, length-prefixed, then the answer. -/
def ew (e : ByteArray × Digest) : List Word := bytesWords e.1.data.toList ++ packBytes e.2.toList

/-- The output of the scan from index `i` on, for the result `r` of the search. -/
def outW (cw : List Word) (i : ℕ) : Option ℕ → List Word
  | none => []
  | some j => 0 :: cw ++ [toWord (i + j)]

theorem ew_length (e : ByteArray × Digest) :
    (ew e).length = 1 + (e.1.size + 7) / 8 + 4 := by
  simp only [ew, bytesWords, List.length_append, List.length_cons, packBytes_digest_length]
  simp only [packBytes_length, Array.length_toList, ByteArray.size_data]
  omega

theorem flatMap_length (L : Log) : 5 * L.length ≤ (L.flatMap ew).length := by
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [List.flatMap_cons, List.length_append, ew_length, List.length_cons]; omega

theorem four (l : List Word) (h : l.length = 4) :
    l = [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0] := by
  match l, h with
  | [_, _, _, _], _ => rfl

theorem words_eq_iff (a c : Digest) :
    ((packBytes a.toList).getD 0 0 = (packBytes c.toList).getD 0 0 ∧
      (packBytes a.toList).getD 1 0 = (packBytes c.toList).getD 1 0 ∧
      (packBytes a.toList).getD 2 0 = (packBytes c.toList).getD 2 0 ∧
      (packBytes a.toList).getD 3 0 = (packBytes c.toList).getD 3 0) ↔ a = c := by
  refine ⟨fun ⟨h0, h1, h2, h3⟩ => ?_, fun h => h ▸ ⟨rfl, rfl, rfl, rfl⟩⟩
  have he : packBytes a.toList = packBytes c.toList := by
    rw [four _ (packBytes_digest_length a), four (packBytes c.toList) (packBytes_digest_length c),
      h0, h1, h2, h3]
  refine Vector.toList_inj.mp ?_
  rw [← unpack_packBytes a.toList, ← unpack_packBytes c.toList, he, a.length_toList,
    c.length_toList]

theorem scan_loop (c : Digest) (T : List Word) (hT : T.length ≤ 2 ^ 64) :
    ∀ (L : Log) (A : List Word) (i : ℕ) (x acc y : Word) (o : Array Word) (f : ℕ),
      T = A ++ L.flatMap ew → (∀ e ∈ L, e.1.size < 2 ^ 64) → i + L.length < 2 ^ 64 →
      exec T.toArray (f + 50 * L.length + 9) (st (packBytes c.toList) A.length L.length i x acc y)
        o [.loop 7 body] =
        some (o.toList ++ outW (packBytes c.toList) i (L.findIdx? fun e => e.2 = c)) := by
  intro L
  induction L with
  | nil =>
    intro A i x acc y o f _ _ _
    simpa [outW] using iter_end T.toArray (packBytes c.toList) x acc y (f + 5) o
  | cons e L ih =>
    intro A i x acc y o f hA hq hi
    have hlen := congrArg List.length hA
    simp only [List.flatMap_cons, List.length_append, ew_length] at hlen
    have hq0 : T.toArray.getD A.length 0 = toWord e.1.size := by
      rw [getD_toArray, hA, List.flatMap_cons]
      simp only [ew, bytesWords, List.cons_append, List.append_assoc]
      rw [getD_append_length, Array.length_toList, ByteArray.size_data]
    have ha : ∀ j < 4, T.toArray.getD (A.length + 1 + (e.1.size + 7) / 8 + j) 0 =
        (packBytes e.2.toList).getD j 0 := fun j hj => by
      rw [getD_toArray, hA, List.flatMap_cons, ew]
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
    have hA' : T = (A ++ ew e) ++ L.flatMap ew := by rw [hA, List.flatMap_cons, List.append_assoc]
    have hlA : (A ++ ew e).length = A.length + 1 + (e.1.size + 7) / 8 + 4 := by
      rw [List.length_append, ew_length]; omega
    rw [List.findIdx?_cons, List.length_cons]
    by_cases hc : e.2 = c
    · rw [show f + 50 * (L.length + 1) + 9 = (f + 50 * L.length) + 59 by ring,
        iter_found T.toArray _ _ x acc y (by simp) (by simp at hi; omega) hℓ hp hq0 ha
          ((words_eq_iff _ _).mpr hc)]
      simp only [hc, decide_true, ↓reduceIte, outW, Nat.add_zero]
      conv_rhs => rw [four _ (packBytes_digest_length c)]
      rfl
    · rw [show f + 50 * (L.length + 1) + 9 = (f + 50 * L.length + 9) + 50 by ring,
        iter_next T.toArray _ _ x acc y (by simp) (by simp at hi; omega) hℓ hp hq0 ha
          (mt (words_eq_iff _ _).mp hc), Nat.add_sub_cancel, ← hlA,
        ih (A ++ ew e) (i + 1) _ _ _ o f hA' (fun e' he' => hq e' (by simp [he']))
          (by simp at hi; omega)]
      cases h : L.findIdx? (fun e => e.2 = c) <;> simp [hc, outW, Nat.add_right_comm, Nat.add_assoc]

theorem decode_outW (c : Digest) {i j : ℕ} (hj : i + j < 2 ^ 64) :
    decodeWit (outW (packBytes c.toList) i (some j)) = some (.leaf c (i + j)) :=
  decodeWit_witWords (.leaf c (i + j)) hj

/-- **The log scan computes `findE` within `16 · t` steps**, on every input of the domain. -/
theorem scan_computes : Computes scan findE fun t => 16 * t := by
  intro c π L hπ hq ht
  set T := extractorInput c π L with hT
  set m := (π.size + 7) / 8
  have hA : T = ((packBytes c.toList ++ [toWord π.size]) ++ packBytes π.data.toList ++
      [toWord L.length]) ++ L.flatMap ew := by
    rw [hT, WitnessSending.extractorInput_eq]; simp; rfl
  have h4 := packBytes_digest_length c
  have hm : (packBytes π.data.toList).length = m := by
    simp [packBytes_length, m, Array.length_toList]
  have hAl : ((packBytes c.toList ++ [toWord π.size]) ++ packBytes π.data.toList ++
      [toWord L.length]).length = m + 6 := by simp [h4, hm]; omega
  have hlen := congrArg List.length hA
  rw [List.length_append, hAl] at hlen
  have h5L := flatMap_length L
  have hc : ∀ j < 4, T.toArray.getD j 0 = (packBytes c.toList).getD j 0 := fun j hj => by
    rw [getD_toArray, hA]
    simp only [List.append_assoc]
    rw [List.getD_append _ _ _ _ (by rw [h4]; exact hj)]
  have hs : T.toArray.getD 4 0 = toWord π.size := by
    rw [getD_toArray, hA]
    simp only [List.append_assoc, List.cons_append]
    rw [show 4 = (packBytes c.toList).length from h4.symm, getD_append_length]
  have hn : T.toArray.getD (m + 5) 0 = toWord L.length := by
    rw [getD_toArray, hA, show packBytes c.toList ++ [toWord π.size] ++ packBytes π.data.toList ++
        [toWord L.length] ++ L.flatMap ew = (packBytes c.toList ++ [toWord π.size] ++
        packBytes π.data.toList) ++ toWord L.length :: L.flatMap ew by simp,
      show m + 5 = (packBytes c.toList ++ [toWord π.size] ++ packBytes π.data.toList).length by
        simp [h4, hm]; omega, getD_append_length]
  have hπc : π.size + 13 < 2 ^ 64 := by unfold outCap at hπ; omega
  have hrun := scan_loop c T ht L _ 0 (toWord m) 0 0 #[]
    (16 * T.length - 16 - 42 - 50 * L.length - 9) hA hq (by omega)
  rw [hAl] at hrun
  rw [XProg.run_eq (by simp [scan, XProg.memFor]; omega)]
  simp only [scan, XProg.memFor, Nat.zero_mul, Nat.add_zero]
  rw [show 16 * T.length - 16 = ((16 * T.length - 16 - 42 - 50 * L.length - 9) + 50 * L.length + 9
      + 41) + 1 by omega, exec_seq,
    pre_exec T.toArray _ hπc (hc 0 (by omega)) (hc 1 (by omega)) (hc 2 (by omega)) (hc 3 (by omega))
      hs hn, hrun]
  refine ⟨_, rfl, ?_, ?_⟩
  · cases L.findIdx? (fun e => e.2 = c) <;> simp [outW, h4, outCap]
  · unfold findE
    cases h : L.findIdx? (fun e => e.2 = c) with
    | none => rfl
    | some j =>
      have hj := (List.findIdx?_eq_some_iff_findIdx_eq.mp h).1
      simpa using decode_outW c (i := 0) (j := j) (by omega)
/-! ## Known answers and negatives -/

/-- The statement `01…01`, the proof `aa bb cc`, a log of a 9-byte query answered `02…02` and an
empty query answered `01…01`. -/
def katLog : Log :=
  [(⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩, Vector.replicate 32 2), (⟨#[]⟩, Vector.replicate 32 1)]

/-- The tape of the known answer. -/
def katTape : List Word := extractorInput (Vector.replicate 32 1) ⟨#[0xaa, 0xbb, 0xcc]⟩ katLog

/-- The leaf `(01…01, 1)`: the second entry's answer is the statement. -/
theorem scan_kat : scan.run katTape (16 * katTape.length) =
    some [0, 0x0101010101010101, 0x0101010101010101, 0x0101010101010101, 0x0101010101010101,
      1] := by
  decide +kernel

/-- The fuel is within the budget's linear term. -/
theorem scan_fuel_le (t : ℕ) : 16 * t ≤ extractorBudget t := by unfold extractorBudget; omega

/-- The tape of the zero statement, the empty proof and the empty log (6 words). -/
def tape0 : List Word := extractorInput (Vector.replicate 32 0) ByteArray.empty []

theorem scan_run_short : scan.run tape0 60 = none := by decide +kernel

/-- **Not within `10 · t` steps**: on the empty log's 6-word tape the program needs 62. -/
theorem scan_fuel_short : ¬ Computes scan findE fun t => 10 * t := by
  intro h
  obtain ⟨o, ho, -⟩ := h (Vector.replicate 32 0) .empty [] (by decide) (by simp) (by decide)
  exact nomatch scan_run_short.symm.trans ho

/-- **It reads the log**: it does not compute the extractor that returns nothing, since on the
known answer's log it outputs a witness. -/
theorem scan_not_none : ¬ Computes scan (fun _ _ _ => none) fun t => 16 * t := by
  intro h
  obtain ⟨o, ho, -, hd⟩ := h (Vector.replicate 32 1) ⟨#[0xaa, 0xbb, 0xcc]⟩ katLog (by decide)
    (by decide) (by decide)
  rw [show extractorInput _ _ katLog = katTape from rfl, scan_kat] at ho
  cases ho
  exact nomatch hd

end RecursionFast.Controls.LogScan
