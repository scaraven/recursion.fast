/-
  RecursionFast.Library.Words  (UNTRUSTED, kernel-checked)

  Facts about the extractor's tape and output formats (`Contract/Extractor.lean`).

  * **Packed bytes.** `wordByte_packBytes`: byte `i` of `packBytes b` is `b`'s byte `i` (`0` past
    its end). `wordsBytes` unpacks words to bytes and `packBytes_wordsBytes` undoes it, so a byte
    string that is the bytes of some words packs back to exactly those words; `unpack_packBytes`:
    unpacking `packBytes b` and keeping `|b|` bytes gives `b`.
  * `ofLE_enc64`, `enc64_inj`: `enc64` is the 8-byte little-endian encoding, injective below
    `2^64`.
  * **The output format.** `witWords` writes a witness in the format `decodeWit` reads
    (`sigWords`, `signedWords` for its parts), and `decodeWit_witWords` reads it back when every
    number fits in a word and the signatures have their fixed counts (`Wit.Fits`), with the words
    after it ignored (`readWit_witWords`). The readers are proved one by one (`readNat_toWord`,
    `readBytes_packBytes`, `readString_bytesWords`, `readDigest_packBytes`, `readList_flatMap`,
    `readTrace_logWords`, `readSig_sigWords`, `readSigned_signedWords`). `witWords` is the encoder
    an extractor program implements; the contract needs only the decoder.
  * **Linear-time twins** (#10, from v3). The compiled code of the contract's `packBytes` is
    quadratic in the length (a list re-read from its start for every word). `packFast` and
    `witWordsF` compute the same functions in linear time (`packFast_eq`, `witWordsF_eq`); a
    verifier runs them, and its proofs rewrite them back. The v4 decoder `decodeWit` is linear by
    itself (strict reading with `take`, `drop`, `flatMap`).
-/
import RecursionFast.Contract.Extractor
import Mathlib.Data.List.GetD
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

namespace RecursionFast

/-! ## Little-endian numbers -/

theorem ofLE_cons (d : UInt8) (ds : List UInt8) : ofLE (d :: ds) = d.toNat + 256 * ofLE ds := rfl

theorem ofLE_lt (ds : List UInt8) : ofLE ds < 256 ^ ds.length := by
  induction ds with
  | nil => simp [ofLE]
  | cons d ds ih =>
    rw [ofLE_cons, List.length_cons, Nat.pow_succ]
    have := d.toNat_lt
    omega

/-- Digit `i` of a little-endian number is byte `i` (`0` past the end). -/
theorem ofLE_div_mod (ds : List UInt8) (i : ℕ) : ofLE ds / 256 ^ i % 256 = (ds.getD i 0).toNat := by
  induction ds generalizing i with
  | nil => simp [ofLE]
  | cons d ds ih =>
    have hd := d.toNat_lt
    cases i with
    | zero => simp [ofLE_cons]
    | succ i =>
      rw [List.getD_cons_succ, ← ih i, Nat.pow_succ', ← Nat.div_div_eq_div_mul, ofLE_cons]
      congr 2
      omega

theorem toUInt8_mod (x : ℕ) : (x % 256).toUInt8 = x.toUInt8 :=
  UInt8.toNat_inj.mp (by simp [Nat.toUInt8])

theorem ofLE_ofFn (x k : ℕ) :
    ofLE (List.ofFn fun i : Fin k => (x / 256 ^ i.val).toUInt8) = x % 256 ^ k := by
  induction k generalizing x with
  | zero => simp [ofLE, Nat.mod_one]
  | succ k ih =>
    simp [List.ofFn_succ, ofLE_cons, pow_succ', ← Nat.div_div_eq_div_mul, ih, Nat.mod_mul,
      Nat.toUInt8]

/-- `enc64 n` is the little-endian encoding of `n mod 2^64`. -/
theorem ofLE_enc64 (n : ℕ) : ofLE (enc64 n) = n % 2 ^ 64 := by
  rw [enc64, ofLE_ofFn]; norm_num

theorem enc64_length (n : ℕ) : (enc64 n).length = 8 := by simp [enc64]

/-- **`enc64` is injective below `2^64`.** -/
theorem enc64_inj {m n : ℕ} (hm : m < 2 ^ 64) (hn : n < 2 ^ 64) (h : enc64 m = enc64 n) :
    m = n := by
  have := congrArg ofLE h
  rwa [ofLE_enc64, ofLE_enc64, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn] at this

/-! ## Packed bytes -/

theorem packBytes_length (b : List UInt8) : (packBytes b).length = (b.length + 7) / 8 := by
  simp [packBytes]

theorem toNat_toWord {a : ℕ} (h : a < 2 ^ 64) : (toWord a).toNat = a := Nat.mod_eq_of_lt h

theorem toWord_add_one (a : ℕ) : toWord a + 1 = toWord (a + 1) := by
  simp [toWord, BitVec.ofNat_add]

theorem toWord_lt_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    toWord a < toWord b ↔ a < b := by
  rw [BitVec.lt_def, toNat_toWord ha, toNat_toWord hb]

theorem toWord_eq_zero {a : ℕ} (ha : a < 2 ^ 64) : toWord a = 0 ↔ a = 0 := by
  rw [← BitVec.toNat_inj, toNat_toWord ha]; rfl

/-- Byte `i` of words read as packed bytes; `0` beyond their end. -/
def wordByte (ws : List Word) (i : ℕ) : UInt8 :=
  ((ws.getD (i / 8) 0).toNat / 256 ^ (i % 8)).toUInt8

/-- Byte `i` of `packBytes b` is byte `i` of `b`, and `0` past its end. -/
theorem wordByte_packBytes (b : List UInt8) (i : ℕ) : wordByte (packBytes b) i = b.getD i 0 := by
  unfold wordByte
  by_cases hi : i / 8 < (packBytes b).length
  · rw [List.getD_eq_getElem _ _ hi]
    simp only [packBytes, List.getElem_map, List.getElem_range]
    have h64 : ofLE ((b.drop (8 * (i / 8))).take 8) < 2 ^ 64 :=
      (ofLE_lt _).trans_le (Nat.pow_le_pow_right (by norm_num) (by simp) : _ ≤ 256 ^ 8)
    rw [toNat_toWord h64, ← toUInt8_mod, ofLE_div_mod, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      show 8 * (i / 8) + i % 8 = i by omega]
    cases b[i]? <;> simp
  · rw [packBytes_length] at hi
    rw [List.getD_eq_default _ _ (by rw [packBytes_length]; omega),
      List.getD_eq_default _ _ (by omega)]
    simp

/-- Words unpacked to bytes, eight little-endian bytes per word (`packBytes` undone). -/
def wordsBytes (ws : List Word) : List UInt8 := ws.flatMap wordBytes

theorem ofLE_wordBytes (w : Word) : ofLE (wordBytes w) = w.toNat := by
  rw [wordBytes, ofLE_ofFn, Nat.mod_eq_of_lt (by simpa using w.isLt)]

theorem wordBytes_length (w : Word) : (wordBytes w).length = 8 := by simp [wordBytes]

theorem wordsBytes_length (ws : List Word) : (wordsBytes ws).length = 8 * ws.length := by
  simp [wordsBytes, wordBytes, List.length_flatMap, mul_comm]

theorem packBytes_append8 {pre : List UInt8} (rest : List UInt8) (h : pre.length = 8) :
    packBytes (pre ++ rest) = toWord (ofLE pre) :: packBytes rest := by
  have hl : (pre ++ rest).length + 7 = 8 * 1 + (rest.length + 7) := by simp [h]; omega
  rw [packBytes, hl, Nat.mul_add_div (by norm_num), Nat.add_comm, List.range_succ_eq_map]
  simp [packBytes, h, Nat.mul_succ, Nat.add_comm (8 * _) 8, ← List.drop_drop, List.drop_left' h]

/-- Packing the bytes of words gives the words back. -/
theorem packBytes_wordsBytes (ws : List Word) : packBytes (wordsBytes ws) = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [show wordsBytes (w :: ws) = wordBytes w ++ wordsBytes ws from rfl,
      packBytes_append8 _ (by simp [wordBytes]), ih, ofLE_wordBytes]
    simp [toWord]

theorem wordByte_eq_getD (ws : List Word) (i : ℕ) :
    wordByte ws i = (wordsBytes ws).getD i 0 := by
  rw [← wordByte_packBytes, packBytes_wordsBytes]

/-- **Unpacking `packBytes b` and keeping `|b|` bytes gives `b`.** -/
theorem unpack_packBytes (b : List UInt8) : (wordsBytes (packBytes b)).take b.length = b := by
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · rw [List.length_take, wordsBytes_length, packBytes_length]; omega
  · rw [List.getElem_take]
    have hi : i < (wordsBytes (packBytes b)).length := by
      rw [wordsBytes_length, packBytes_length]; omega
    have := wordByte_eq_getD (packBytes b) i
    rw [wordByte_packBytes, List.getD_eq_getElem _ _ h2, List.getD_eq_getElem _ _ hi] at this
    exact this.symm

/-! ## The output format -/

/-- A signature's output words: its index, then its chain values and path digests, packed. -/
def sigWords (σ : Sig) : List Word :=
  toWord σ.idx :: (σ.ots.flatMap fun d => packBytes d.toList) ++
    σ.path.flatMap fun d => packBytes d.toList

/-- A signed proof's output words: the proof (length-prefixed), the trace, the signature. -/
def signedWords (p : Signed) : List Word :=
  bytesWords p.π.data.toList ++ logWords p.tr ++ sigWords p.σ

/-- The output words of a witness, in the format `decodeWit` reads. -/
def witWords : Wit → List Word
  | .leaf s n => toWord 0 :: packBytes s.toList ++ [toWord n]
  | .node c₁ c₂ p₁ p₂ => toWord 1 :: packBytes c₁.toList ++ packBytes c₂.toList ++
      signedWords p₁ ++ signedWords p₂

/-- A signed proof fits the output format: every number in a word, the signature's counts
fixed. -/
def Signed.Fits (p : Signed) : Prop :=
  p.π.size < 2 ^ 64 ∧ p.tr.length < 2 ^ 64 ∧ (∀ e ∈ p.tr, e.1.size < 2 ^ 64) ∧
    p.σ.idx < 2 ^ 64 ∧ p.σ.ots.length = wotsLen ∧ p.σ.path.length = sigHeight

/-- A witness fits the output format: a leaf's length below `2^64`, a node's children fit. -/
def Wit.Fits : Wit → Prop
  | .leaf _ n => n < 2 ^ 64
  | .node _ _ p₁ p₂ => p₁.Fits ∧ p₂.Fits

theorem packBytes_digest_length (d : Digest) : (packBytes d.toList).length = 4 := by
  simp [packBytes_length]

theorem getD_append_length (pre rest : List Word) (x : Word) :
    (pre ++ x :: rest).getD pre.length 0 = x := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_append_mid (pre mid rest : List Word) {j : ℕ} (h : j < mid.length) :
    (pre ++ mid ++ rest).getD (pre.length + j) 0 = mid[j] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, List.getElem?_append_left h,
    List.getElem?_eq_getElem h]

/-! ### The readers, one by one -/

theorem readNat_toWord {n : ℕ} (h : n < 2 ^ 64) (o : List Word) :
    readNat.run (toWord n :: o) = some (n, o) := by
  simp [readNat, StateT.run, toNat_toWord h]

theorem readBytes_packBytes (b : List UInt8) (o : List Word) :
    (readBytes b.length).run (packBytes b ++ o) = some (b, o) := by
  have hl := packBytes_length b
  simp only [readBytes, StateT.run, ← hl, List.take_left', List.drop_left', ite_true]
  rw [show List.flatMap wordBytes (packBytes b) = wordsBytes (packBytes b) from rfl,
    unpack_packBytes]

theorem readString_bytesWords (b : ByteArray) (h : b.size < 2 ^ 64) (o : List Word) :
    readString.run (bytesWords b.data.toList ++ o) = some (b, o) := by
  have hs : b.data.toList.length < 2 ^ 64 := by simpa using h
  simp only [readString, bytesWords, List.cons_append, StateT.run_bind, readNat_toWord hs,
    Option.bind_eq_bind, Option.bind_some, readBytes_packBytes, StateT.run_pure]
  simp

theorem readDigest_packBytes (d : Digest) (o : List Word) :
    readDigest.run (packBytes d.toList ++ o) = some (d, o) := by
  have := readBytes_packBytes d.toList o
  simp only [Vector.length_toList] at this
  simp only [readDigest, StateT.run_bind, this, Option.bind_eq_bind, Option.bind_some,
    StateT.run_pure]
  exact congrArg (fun x => some (x, o)) (Vector.ext fun i hi => by simp)

theorem readList_flatMap {α : Type} (r : Reader α) (enc : α → List Word) (P : α → Prop)
    (hr : ∀ x, P x → ∀ o, r.run (enc x ++ o) = some (x, o)) :
    ∀ (xs : List α), (∀ x ∈ xs, P x) → ∀ o : List Word,
      (readList r xs.length).run (xs.flatMap enc ++ o) = some (xs, o)
  | [], _, o => by simp [readList]
  | x :: xs, hP, o => by
    simp only [List.length_cons, readList, List.flatMap_cons, List.append_assoc, StateT.run_bind,
      hr x (hP x (List.mem_cons_self ..)), Option.bind_eq_bind, Option.bind_some,
      readList_flatMap r enc P hr xs (fun y hy => hP y (List.mem_cons_of_mem _ hy)) o,
      StateT.run_pure]
    rfl

theorem readEntry_run (e : ByteArray × Digest) (h : e.1.size < 2 ^ 64) (o : List Word) :
    readEntry.run (bytesWords e.1.data.toList ++ packBytes e.2.toList ++ o) = some (e, o) := by
  simp only [readEntry, List.append_assoc, StateT.run_bind, readString_bytesWords _ h,
    Option.bind_eq_bind, Option.bind_some, readDigest_packBytes, StateT.run_pure]
  rfl

theorem readTrace_logWords (tr : Trace) (hl : tr.length < 2 ^ 64)
    (hq : ∀ e ∈ tr, e.1.size < 2 ^ 64) (o : List Word) :
    readTrace.run (logWords tr ++ o) = some (tr, o) := by
  simp only [readTrace, logWords, List.cons_append, StateT.run_bind, readNat_toWord hl,
    Option.bind_eq_bind, Option.bind_some]
  exact readList_flatMap readEntry _ (fun e => e.1.size < 2 ^ 64)
    (fun e he o => by simpa using readEntry_run e he o) tr hq o

theorem readSig_sigWords (σ : Sig) (hi : σ.idx < 2 ^ 64) (ho : σ.ots.length = wotsLen)
    (hp : σ.path.length = sigHeight) (o : List Word) :
    readSig.run (sigWords σ ++ o) = some (σ, o) := by
  have hd := readList_flatMap readDigest (fun d => packBytes d.toList) (fun _ => True)
    (fun d _ o => readDigest_packBytes d o)
  simp only [readSig, sigWords, List.cons_append, List.append_assoc, StateT.run_bind,
    readNat_toWord hi, Option.bind_eq_bind, Option.bind_some, ← ho, ← hp,
    hd σ.ots (fun _ _ => trivial), hd σ.path (fun _ _ => trivial), StateT.run_pure]
  rfl

theorem readSigned_signedWords (p : Signed) (h : p.Fits) (o : List Word) :
    readSigned.run (signedWords p ++ o) = some (p, o) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [readSigned, signedWords, List.append_assoc, StateT.run_bind,
    readString_bytesWords _ h1, Option.bind_eq_bind, Option.bind_some, readTrace_logWords _ h2 h3,
    readSig_sigWords _ h4 h5 h6, StateT.run_pure]
  rfl

/-- **The decoder reads `witWords` back**, with any words after it. -/
theorem readWit_witWords (w : Wit) (h : w.Fits) (o : List Word) :
    readWit.run (witWords w ++ o) = some (w, o) := by
  cases w with
  | leaf s n =>
    simp only [witWords, List.cons_append, List.append_assoc, readWit,
      StateT.run_bind, readNat_toWord (show 0 < 2 ^ 64 by norm_num), Option.bind_eq_bind,
      Option.bind_some, readDigest_packBytes, readNat_toWord (show n < 2 ^ 64 from h),
      StateT.run_pure]
    rfl
  | node c₁ c₂ p₁ p₂ =>
    simp only [witWords, List.cons_append, List.append_assoc, readWit, StateT.run_bind,
      readNat_toWord (show 1 < 2 ^ 64 by norm_num), Option.bind_eq_bind, Option.bind_some,
      readDigest_packBytes, readSigned_signedWords _ h.1, readSigned_signedWords _ h.2,
      StateT.run_pure]
    rfl

/-- **The decoder reads `witWords` back** when the witness fits the format. -/
theorem decodeWit_witWords (w : Wit) (h : w.Fits) : decodeWit (witWords w) = some w := by
  have := readWit_witWords w h []
  rw [List.append_nil] at this
  simp only [decodeWit, StateT.run', StateT.run] at this ⊢
  rw [this]; rfl

/-! ## Linear-time twins -/

/-- `packBytes`, eight bytes at a time. -/
def packFast : List UInt8 → List Word
  | [] => []
  | b@(_ :: _) => toWord (ofLE (b.take 8)) :: packFast (b.drop 8)
termination_by b => b.length

theorem packFast_eq (b : List UInt8) : packFast b = packBytes b := by
  fun_induction packFast b with
  | case1 => rfl
  | case2 x xs ih =>
    rw [ih, packBytes, packBytes, List.length_drop, List.length_cons,
      show (xs.length + 1 + 7) / 8 = (xs.length + 1 - 8 + 7) / 8 + 1 by omega,
      List.range_succ_eq_map]
    simp [Nat.mul_succ, Nat.add_comm (8 * _) 8, ← List.drop_drop]

/-- `bytesWords` with `packFast`. -/
def bytesWordsF (b : List UInt8) : List Word := toWord b.length :: packFast b

/-- `logWords` with `packFast`. -/
def logWordsF (L : Log) : List Word :=
  toWord L.length :: L.flatMap fun e => bytesWordsF e.1.data.toList ++ packFast e.2.toList

/-- `sigWords` with `packFast`. -/
def sigWordsF (σ : Sig) : List Word :=
  toWord σ.idx :: (σ.ots.flatMap fun d => packFast d.toList) ++
    σ.path.flatMap fun d => packFast d.toList

/-- `signedWords` with `packFast`. -/
def signedWordsF (p : Signed) : List Word :=
  bytesWordsF p.π.data.toList ++ logWordsF p.tr ++ sigWordsF p.σ

/-- `witWords` with `packFast`. -/
def witWordsF : Wit → List Word
  | .leaf s n => toWord 0 :: packFast s.toList ++ [toWord n]
  | .node c₁ c₂ p₁ p₂ => toWord 1 :: packFast c₁.toList ++ packFast c₂.toList ++
      signedWordsF p₁ ++ signedWordsF p₂

theorem bytesWordsF_eq (b : List UInt8) : bytesWordsF b = bytesWords b := by
  rw [bytesWordsF, bytesWords, packFast_eq]

theorem logWordsF_eq (L : Log) : logWordsF L = logWords L := by
  simp only [logWordsF, logWords, bytesWordsF_eq, packFast_eq]

theorem signedWordsF_eq (p : Signed) : signedWordsF p = signedWords p := by
  simp only [signedWordsF, signedWords, sigWordsF, sigWords, bytesWordsF_eq, logWordsF_eq,
    packFast_eq]

theorem witWordsF_eq (w : Wit) : witWordsF w = witWords w := by
  cases w <;> simp only [witWordsF, witWords, signedWordsF_eq, packFast_eq]

end RecursionFast
