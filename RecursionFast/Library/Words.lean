/-
  RecursionFast.Library.Words  (UNTRUSTED, kernel-checked)

  Facts about the extractor's tape and output formats (`Contract/Extractor.lean`).

  * **Packed bytes.** `wordByte_packBytes`: byte `i` of `packBytes b` is `b`'s byte `i` (`0` past
    its end). `wordsBytes` unpacks words to bytes and `packBytes_wordsBytes` undoes it, so a byte
    string that is the bytes of some words packs back to exactly those words.
  * **The output format.** `witWords` writes a witness in the format `decodeWit` reads, and
    `decodeWit_witWords` reads it back when the leaf length fits in a word and the two proofs in
    `proofCap` (`Wit.Fits`). `witWords` is the encoder an extractor program implements; the
    contract itself needs only the decoder.
  * **Linear-time twins** (#10, from the S2a entry's `BaselineV3.lean`). The compiled code of the
    contract's `packBytes` and `bytesAt` is quadratic in the length (a list re-read from its start
    for every word or byte; 563 s to reject a random 1 MiB proof). `packFast`, `bytesAtF`,
    `decodeWitF` and `witWordsF` compute the same functions in linear time (`packFast_eq`,
    `bytesAtF_eq`, `decodeWitF_eq`, `witWordsF_eq`); a verifier runs them, and its proofs rewrite
    them back.
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

theorem wordByte_append_left {ws rest : List Word} {i : ℕ} (h : i / 8 < ws.length) :
    wordByte (ws ++ rest) i = wordByte ws i := by
  simp [wordByte, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-- The 8 little-endian bytes of a word. -/
def wordBytes (w : Word) : List UInt8 := List.ofFn fun i : Fin 8 => (w.toNat / 256 ^ i.val).toUInt8

/-- Words unpacked to bytes, eight little-endian bytes per word (`packBytes` undone). -/
def wordsBytes (ws : List Word) : List UInt8 := ws.flatMap wordBytes

theorem ofLE_ofFn (x k : ℕ) :
    ofLE (List.ofFn fun i : Fin k => (x / 256 ^ i.val).toUInt8) = x % 256 ^ k := by
  induction k generalizing x with
  | zero => simp [ofLE, Nat.mod_one]
  | succ k ih =>
    simp [List.ofFn_succ, ofLE_cons, pow_succ', ← Nat.div_div_eq_div_mul, ih, Nat.mod_mul,
      Nat.toUInt8]

theorem ofLE_wordBytes (w : Word) : ofLE (wordBytes w) = w.toNat := by
  rw [wordBytes, ofLE_ofFn, Nat.mod_eq_of_lt (by simpa using w.isLt)]

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

/-! ## The output format -/

/-- The output words of a witness, in the format `decodeWit` reads. -/
def witWords : Wit → List Word
  | .leaf s n => toWord 0 :: packBytes s.toList ++ [toWord n]
  | .node c₁ c₂ π₁ π₂ => toWord 1 :: packBytes c₁.toList ++ packBytes c₂.toList ++
      bytesWords π₁.data.toList ++ bytesWords π₂.data.toList

/-- The witness fits the output format: a leaf's length is below `2^64`, a node's two proofs
have at most `proofCap` bytes. -/
def Wit.Fits : Wit → Prop
  | .leaf _ n => n < 2 ^ 64
  | .node _ _ π₁ π₂ => π₁.size ≤ proofCap ∧ π₂.size ≤ proofCap

theorem packBytes_digest_length (d : Digest) : (packBytes d.toList).length = 4 := by
  simp [packBytes_length]

theorem digestAt_packBytes (pre rest : List Word) (d : Digest) :
    digestAt (pre ++ packBytes d.toList ++ rest) pre.length = d := by
  ext i hi
  simp only [digestAt, Vector.getElem_ofFn, List.append_assoc, List.drop_left]
  rw [wordByte_append_left (by rw [packBytes_digest_length]; omega), wordByte_packBytes,
    List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem bytesAt_packBytes (pre rest : List Word) (π : Proof) :
    bytesAt (pre ++ packBytes π.data.toList ++ rest) pre.length π.size = π := by
  simp only [bytesAt, List.append_assoc, List.drop_left]
  refine ByteArray.ext (Array.ext' (List.ext_getElem (by simp) fun i _ h => ?_))
  rw [List.getElem_map, List.getElem_range,
    wordByte_append_left (by rw [packBytes_length]; omega), wordByte_packBytes,
    List.getD_eq_getElem _ _ h]

theorem getD_append_length (pre rest : List Word) (x : Word) :
    (pre ++ x :: rest).getD pre.length 0 = x := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_append_mid (pre mid rest : List Word) {j : ℕ} (h : j < mid.length) :
    (pre ++ mid ++ rest).getD (pre.length + j) 0 = mid[j] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, List.getElem?_append_left h,
    List.getElem?_eq_getElem h]

/-- `decodeWit` on a non-empty output, unfolded. -/
theorem decodeWit_cons (t : Word) (r : List Word) : decodeWit (t :: r) =
    if t = 0 then some (.leaf (digestAt (t :: r) 1) ((t :: r).getD 5 0).toNat)
    else if t = 1 ∧ ((t :: r).getD 9 0).toNat ≤ proofCap ∧
        ((t :: r).getD (10 + (((t :: r).getD 9 0).toNat + 7) / 8) 0).toNat ≤ proofCap then
      some (.node (digestAt (t :: r) 1) (digestAt (t :: r) 5)
        (bytesAt (t :: r) 10 ((t :: r).getD 9 0).toNat)
        (bytesAt (t :: r) (11 + (((t :: r).getD 9 0).toNat + 7) / 8)
          ((t :: r).getD (10 + (((t :: r).getD 9 0).toNat + 7) / 8) 0).toNat))
    else none := rfl

/-! Reading at an offset: drop a word or a segment from the front, then read a packed field. -/

private theorem digestAt_cons {a : Word} {l : List Word} {k : ℕ} (h : 0 < k) :
    digestAt (a :: l) k = digestAt l (k - 1) := by
  cases k <;> simp_all [digestAt]

private theorem digestAt_append {X l : List Word} {k : ℕ} (h : X.length ≤ k) :
    digestAt (X ++ l) k = digestAt l (k - X.length) := by
  simp [digestAt, List.drop_append, List.drop_eq_nil_of_le h]

private theorem bytesAt_cons {a : Word} {l : List Word} {k n : ℕ} (h : 0 < k) :
    bytesAt (a :: l) k n = bytesAt l (k - 1) n := by
  cases k <;> simp_all [bytesAt]

private theorem bytesAt_append {X l : List Word} {k n : ℕ} (h : X.length ≤ k) :
    bytesAt (X ++ l) k n = bytesAt l (k - X.length) n := by
  simp [bytesAt, List.drop_append, List.drop_eq_nil_of_le h]

private theorem digestAt_zero (d : Digest) (l : List Word) :
    digestAt (packBytes d.toList ++ l) 0 = d := digestAt_packBytes [] l d

private theorem bytesAt_zero (π : Proof) (l : List Word) :
    bytesAt (packBytes π.data.toList ++ l) 0 π.size = π := bytesAt_packBytes [] l π

private theorem bytesAt_nil (π : Proof) : bytesAt (packBytes π.data.toList) 0 π.size = π := by
  simpa using bytesAt_packBytes [] [] π

/-- **The decoder reads `witWords` back** when the witness fits the format. -/
theorem decodeWit_witWords (w : Wit) (h : w.Fits) : decodeWit (witWords w) = some w := by
  cases w with
  | leaf s n =>
    have := packBytes_digest_length s
    replace h : n < 2 ^ 64 := h
    simp (disch := omega) [witWords, decodeWit_cons, toWord, digestAt_cons, digestAt_zero,
      List.getElem?_append_right, List.getElem?_cons, Nat.mod_eq_of_lt]
  | node c₁ c₂ π₁ π₂ =>
    obtain ⟨h₁, h₂⟩ := h
    have h₁' : π₁.size < 2 ^ 64 := by unfold proofCap at h₁; omega
    have h₂' : π₂.size < 2 ^ 64 := by unfold proofCap at h₂; omega
    have := packBytes_digest_length c₁
    have := packBytes_digest_length c₂
    have : (packBytes π₁.data.toList).length = (π₁.size + 7) / 8 := by simp [packBytes_length]
    simp (disch := omega) [witWords, bytesWords, decodeWit_cons, toWord, digestAt_cons,
      digestAt_append, digestAt_zero, bytesAt_cons, bytesAt_append, bytesAt_zero, bytesAt_nil,
      List.getElem?_append_right, List.getElem?_cons, ite_eq_right, Nat.mod_eq_of_lt,
      packBytes_digest_length, h₁, h₂]

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

/-- `bytesAt`, through an array of the unpacked bytes. -/
def bytesAtF (o : List Word) (k n : ℕ) : Proof :=
  let a := (wordsBytes (o.drop k)).toArray
  ⟨((List.range n).map fun i => a.getD i 0).toArray⟩

theorem wordByte_eq_getD (ws : List Word) (i : ℕ) :
    wordByte ws i = (wordsBytes ws).getD i 0 := by
  rw [← wordByte_packBytes, packBytes_wordsBytes]

theorem bytesAtF_eq (o : List Word) (k n : ℕ) : bytesAtF o k n = bytesAt o k n := by
  simp [bytesAtF, bytesAt, wordByte_eq_getD, List.getD_eq_getElem?_getD]

/-- `decodeWit` with `bytesAtF` for `bytesAt`. -/
def decodeWitF : List Word → Option Wit
  | [] => none
  | o@(t :: _) =>
    let w (k : ℕ) := (o.getD k 0).toNat
    let m := (w 9 + 7) / 8
    if t = 0 then some (.leaf (digestAt o 1) (w 5))
    else if t = 1 ∧ w 9 ≤ proofCap ∧ w (10 + m) ≤ proofCap then
      some (.node (digestAt o 1) (digestAt o 5) (bytesAtF o 10 (w 9))
        (bytesAtF o (11 + m) (w (10 + m))))
    else none

theorem decodeWitF_eq (o : List Word) : decodeWitF o = decodeWit o := by
  cases o with
  | nil => rfl
  | cons t r => simp only [decodeWitF, decodeWit, bytesAtF_eq]

/-- `witWords` with `packFast` for `packBytes`. -/
def witWordsF : Wit → List Word
  | .leaf s n => toWord 0 :: packFast s.toList ++ [toWord n]
  | .node c₁ c₂ π₁ π₂ => toWord 1 :: packFast c₁.toList ++ packFast c₂.toList ++
      (toWord π₁.data.toList.length :: packFast π₁.data.toList) ++
      (toWord π₂.data.toList.length :: packFast π₂.data.toList)

theorem witWordsF_eq (w : Wit) : witWordsF w = witWords w := by
  cases w <;> simp only [witWordsF, witWords, bytesWords, packFast_eq]

end RecursionFast
