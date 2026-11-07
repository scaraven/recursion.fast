/-
  RecursionFast.Library.KeccakFast  (UNTRUSTED, kernel-checked)

  **A word-level Keccak-256 proved equal to the contract's**, for the compiled badge path. The
  contract's `keccakF` (`Contract/Hash/Keccak.lean`) keeps the
  state in a `Vector` and builds a new one per step, and its sponge works on lists; it is the
  readable reference. The twins here keep the 25 lanes in the fields of a structure and write
  every step out:

  * `thetaF`, `rhoF`, `piF`, `chiF` (printed by `scripts/speed/gen_keccak_twin.py`), `iotaF`,
    `roundF`, `keccakFF`, with **`keccakF_toVec : keccakF s.toVec = (keccakFF s).toVec`**. The proof
    is symbolic: each step is the contract's on a vector of 25 free words (`theta_toVec`, …,
    `chi_toVec`, by `simp` on the lane indices), a round is their composition (`round_toVec`), and
    the 24 rounds follow by induction on the list of round constants (`foldl_round`). No
    permutation is evaluated.
  * The sponge over a `ByteArray`: `padB` (`padB_data`), `laneAt` and `xorBlock` (the block's
    lanes, `xorBlock_toVec`), `loopB` (the absorbing loop, `loopB_toVec` against `absorb`),
    `outBytes` (`outBytes_eq`), and **`digestB_eq : digestB b = keccakDigest b.data.toList`**;
    `digestL` for lists, and `keccak256_eq_digestL`.
  The kernel evaluates `keccakFF` about thirty times faster than the contract's `keccakF`, so the
  known-answer controls (`Controls/Keccak.lean`) go through `digestB_eq`.
-/
import RecursionFast.Contract.Relation
import Mathlib.Tactic.IntervalCases

namespace RecursionFast.Keccak

/-- The 25 lanes of a state as separate words, field `aᵢ` the lane `i = x + 5y`. -/
structure S25 where
  (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 :
    UInt64)

/-- The words as the contract's state. -/
def S25.toVec (s : S25) : State :=
  #v[s.a0, s.a1, s.a2, s.a3, s.a4, s.a5, s.a6, s.a7, s.a8, s.a9, s.a10, s.a11, s.a12, s.a13,
    s.a14, s.a15, s.a16, s.a17, s.a18, s.a19, s.a20, s.a21, s.a22, s.a23, s.a24]

/-- A state as separate words. -/
def S25.ofVec (a : State) : S25 :=
  ⟨a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8],
   a[9], a[10], a[11], a[12], a[13], a[14], a[15], a[16], a[17],
   a[18], a[19], a[20], a[21], a[22], a[23], a[24]⟩

theorem S25.toVec_ofVec (a : State) : (S25.ofVec a).toVec = a := by
  obtain ⟨⟨l⟩, hl⟩ := a
  match l, hl with
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _ => rfl

/-! ## The permutation on separate words -/

/-- `rotl` with the offset a machine word, inlined, so that a compiled rotation by a constant is
two shifts (`rotl_1`; the offsets of ρ by `rfl` in `rho_toVec`). -/
@[inline] def rotK (w n : UInt64) : UInt64 := w <<< n ||| w >>> (64 - n)

theorem rotl_1 (w : UInt64) : rotl w 1 = rotK w 1 := rfl

/-- θ on separate words (`theta_toVec`). -/
@[inline] def thetaF (s : S25) : S25 :=
  let c0 := s.a0 ^^^ s.a5 ^^^ s.a10 ^^^ s.a15 ^^^ s.a20
  let c1 := s.a1 ^^^ s.a6 ^^^ s.a11 ^^^ s.a16 ^^^ s.a21
  let c2 := s.a2 ^^^ s.a7 ^^^ s.a12 ^^^ s.a17 ^^^ s.a22
  let c3 := s.a3 ^^^ s.a8 ^^^ s.a13 ^^^ s.a18 ^^^ s.a23
  let c4 := s.a4 ^^^ s.a9 ^^^ s.a14 ^^^ s.a19 ^^^ s.a24
  let d0 := c4 ^^^ rotK c1 1
  let d1 := c0 ^^^ rotK c2 1
  let d2 := c1 ^^^ rotK c3 1
  let d3 := c2 ^^^ rotK c4 1
  let d4 := c3 ^^^ rotK c0 1
  ⟨s.a0 ^^^ d0, s.a1 ^^^ d1, s.a2 ^^^ d2, s.a3 ^^^ d3, s.a4 ^^^ d4,
   s.a5 ^^^ d0, s.a6 ^^^ d1, s.a7 ^^^ d2, s.a8 ^^^ d3, s.a9 ^^^ d4,
   s.a10 ^^^ d0, s.a11 ^^^ d1, s.a12 ^^^ d2, s.a13 ^^^ d3, s.a14 ^^^ d4,
   s.a15 ^^^ d0, s.a16 ^^^ d1, s.a17 ^^^ d2, s.a18 ^^^ d3, s.a19 ^^^ d4,
   s.a20 ^^^ d0, s.a21 ^^^ d1, s.a22 ^^^ d2, s.a23 ^^^ d3, s.a24 ^^^ d4⟩

/-- ρ on separate words, the offsets written out (`rho_toVec`). -/
@[inline] def rhoF (s : S25) : S25 :=
  ⟨rotK s.a0 0, rotK s.a1 1, rotK s.a2 62, rotK s.a3 28, rotK s.a4 27,
   rotK s.a5 36, rotK s.a6 44, rotK s.a7 6, rotK s.a8 55, rotK s.a9 20,
   rotK s.a10 3, rotK s.a11 10, rotK s.a12 43, rotK s.a13 25, rotK s.a14 39,
   rotK s.a15 41, rotK s.a16 45, rotK s.a17 15, rotK s.a18 21, rotK s.a19 8,
   rotK s.a20 18, rotK s.a21 2, rotK s.a22 61, rotK s.a23 56, rotK s.a24 14⟩

/-- π on separate words: field `x + 5y` is field `(x + 3y) % 5 + 5x` (`pi_toVec`). -/
@[inline] def piF (s : S25) : S25 :=
  ⟨s.a0, s.a6, s.a12, s.a18, s.a24, s.a3, s.a9, s.a10, s.a16,
   s.a22, s.a1, s.a7, s.a13, s.a19, s.a20, s.a4, s.a5, s.a11,
   s.a17, s.a23, s.a2, s.a8, s.a14, s.a15, s.a21⟩

/-- χ on separate words (`chi_toVec`). -/
@[inline] def chiF (s : S25) : S25 :=
  ⟨s.a0 ^^^ (~~~s.a1 &&& s.a2), s.a1 ^^^ (~~~s.a2 &&& s.a3),
   s.a2 ^^^ (~~~s.a3 &&& s.a4), s.a3 ^^^ (~~~s.a4 &&& s.a0),
   s.a4 ^^^ (~~~s.a0 &&& s.a1), s.a5 ^^^ (~~~s.a6 &&& s.a7),
   s.a6 ^^^ (~~~s.a7 &&& s.a8), s.a7 ^^^ (~~~s.a8 &&& s.a9),
   s.a8 ^^^ (~~~s.a9 &&& s.a5), s.a9 ^^^ (~~~s.a5 &&& s.a6),
   s.a10 ^^^ (~~~s.a11 &&& s.a12), s.a11 ^^^ (~~~s.a12 &&& s.a13),
   s.a12 ^^^ (~~~s.a13 &&& s.a14), s.a13 ^^^ (~~~s.a14 &&& s.a10),
   s.a14 ^^^ (~~~s.a10 &&& s.a11), s.a15 ^^^ (~~~s.a16 &&& s.a17),
   s.a16 ^^^ (~~~s.a17 &&& s.a18), s.a17 ^^^ (~~~s.a18 &&& s.a19),
   s.a18 ^^^ (~~~s.a19 &&& s.a15), s.a19 ^^^ (~~~s.a15 &&& s.a16),
   s.a20 ^^^ (~~~s.a21 &&& s.a22), s.a21 ^^^ (~~~s.a22 &&& s.a23),
   s.a22 ^^^ (~~~s.a23 &&& s.a24), s.a23 ^^^ (~~~s.a24 &&& s.a20),
   s.a24 ^^^ (~~~s.a20 &&& s.a21)⟩

/-- ι on separate words: the round constant `c` XORed into lane `A[0, 0]`. -/
@[inline] def iotaF (s : S25) (c : UInt64) : S25 := { s with a0 := s.a0 ^^^ c }

/-- One round on separate words. -/
@[inline] def roundF (s : S25) (c : UInt64) : S25 := iotaF (chiF (piF (rhoF (thetaF s)))) c

/-- **`Keccak-f[1600]` on separate words.** -/
def keccakFF (s : S25) : S25 := rc.foldl roundF s

/-! ### `keccakFF` is `keccakF` -/

theorem theta_toVec (s : S25) : theta s.toVec = (thetaF s).toVec := by
  simp only [theta, ofLanes, lane, S25.toVec, thetaF, rotl_1,
    Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.zero_mod,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]

theorem rho_toVec (s : S25) : rho s.toVec = (rhoF s).toVec := by
  ext i hi
  simp only [rho, Vector.getElem_ofFn]
  interval_cases i <;> rfl

theorem pi_toVec (s : S25) : pi s.toVec = (piF s).toVec := by
  simp only [pi, ofLanes, lane, S25.toVec, piF,
    Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.zero_mod,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]

theorem chi_toVec (s : S25) : chi s.toVec = (chiF s).toVec := by
  simp only [chi, ofLanes, lane, S25.toVec, chiF,
    Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.zero_mod,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]

/-- A round on separate words is the contract's round. -/
theorem round_toVec (s : S25) (c : UInt64) : round s.toVec c = (roundF s c).toVec := by
  simp only [round, theta_toVec, rho_toVec, pi_toVec, chi_toVec]
  rfl

theorem foldl_round (l : List UInt64) (s : S25) :
    l.foldl round s.toVec = (l.foldl roundF s).toVec := by
  induction l generalizing s with
  | nil => rfl
  | cons c l ih => simp only [List.foldl_cons, round_toVec, ih]

/-- **The word-level permutation is the contract's.** -/
theorem keccakF_toVec (s : S25) : keccakF s.toVec = (keccakFF s).toVec := by
  simp only [keccakF, keccakFF, ← Vector.foldl_toList, foldl_round]

/-! ## The sponge over a byte array -/

/-- Byte `i` of `b` as a word, `0` past its end. -/
@[inline] def byteAt (b : ByteArray) (i : Nat) : UInt64 :=
  if h : i < b.size then b[i].toUInt64 else 0

/-- The little-endian word of the bytes `o … o + 7` of `b` (`0` past its end). -/
@[inline] def laneAt (b : ByteArray) (o : Nat) : UInt64 :=
  byteAt b o ||| byteAt b (o + 1) <<< 8 ||| byteAt b (o + 2) <<< 16 ||| byteAt b (o + 3) <<< 24 |||
    byteAt b (o + 4) <<< 32 ||| byteAt b (o + 5) <<< 40 ||| byteAt b (o + 6) <<< 48 |||
    byteAt b (o + 7) <<< 56

/-- The block at byte `o` of `b` XORed into the 17 rate lanes. -/
@[inline] def xorBlock (s : S25) (b : ByteArray) (o : Nat) : S25 :=
  ⟨s.a0 ^^^ laneAt b (o + 8 * 0), s.a1 ^^^ laneAt b (o + 8 * 1), s.a2 ^^^ laneAt b (o + 8 * 2),
   s.a3 ^^^ laneAt b (o + 8 * 3), s.a4 ^^^ laneAt b (o + 8 * 4), s.a5 ^^^ laneAt b (o + 8 * 5),
   s.a6 ^^^ laneAt b (o + 8 * 6), s.a7 ^^^ laneAt b (o + 8 * 7), s.a8 ^^^ laneAt b (o + 8 * 8),
   s.a9 ^^^ laneAt b (o + 8 * 9), s.a10 ^^^ laneAt b (o + 8 * 10), s.a11 ^^^ laneAt b (o + 8 * 11),
   s.a12 ^^^ laneAt b (o + 8 * 12), s.a13 ^^^ laneAt b (o + 8 * 13),
   s.a14 ^^^ laneAt b (o + 8 * 14),
   s.a15 ^^^ laneAt b (o + 8 * 15), s.a16 ^^^ laneAt b (o + 8 * 16), s.a17,
   s.a18, s.a19, s.a20,
   s.a21, s.a22, s.a23,
   s.a24⟩

/-- The absorbing loop over `n` blocks of `b` from byte `o`. -/
def loopB (b : ByteArray) (s : S25) (o : Nat) : Nat → S25
  | 0 => s
  | n + 1 => loopB b (keccakFF (xorBlock s b o)) (o + rate) n

/-- `b` padded (the contract's `pad`) in a byte array. -/
def padB (b : ByteArray) : ByteArray :=
  let p := rate - b.size % rate
  if p = 1 then b.push 0x81 else (b.push 0x01 ++ ⟨Array.replicate (p - 2) 0⟩).push 0x80

/-- The 32 output bytes: lanes `0 … 3`, each little-endian. -/
def outBytes (s : S25) : Digest :=
  #v[(s.a0 >>> 0).toUInt8, (s.a0 >>> 8).toUInt8, (s.a0 >>> 16).toUInt8, (s.a0 >>> 24).toUInt8,
    (s.a0 >>> 32).toUInt8, (s.a0 >>> 40).toUInt8, (s.a0 >>> 48).toUInt8, (s.a0 >>> 56).toUInt8,
    (s.a1 >>> 0).toUInt8, (s.a1 >>> 8).toUInt8, (s.a1 >>> 16).toUInt8, (s.a1 >>> 24).toUInt8,
    (s.a1 >>> 32).toUInt8, (s.a1 >>> 40).toUInt8, (s.a1 >>> 48).toUInt8, (s.a1 >>> 56).toUInt8,
    (s.a2 >>> 0).toUInt8, (s.a2 >>> 8).toUInt8, (s.a2 >>> 16).toUInt8, (s.a2 >>> 24).toUInt8,
    (s.a2 >>> 32).toUInt8, (s.a2 >>> 40).toUInt8, (s.a2 >>> 48).toUInt8, (s.a2 >>> 56).toUInt8,
    (s.a3 >>> 0).toUInt8, (s.a3 >>> 8).toUInt8, (s.a3 >>> 16).toUInt8, (s.a3 >>> 24).toUInt8,
    (s.a3 >>> 32).toUInt8, (s.a3 >>> 40).toUInt8, (s.a3 >>> 48).toUInt8, (s.a3 >>> 56).toUInt8]

/-- The all-zero state. -/
def zeroS : S25 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- **Keccak-256 of a byte array**, as a digest (`digestB_eq`). -/
def digestB (b : ByteArray) : Digest :=
  let p := padB b
  outBytes (loopB p zeroS 0 (p.size / rate))

/-! ### `digestB` is `keccakDigest` -/

theorem byteAt_eq (b : ByteArray) (o k : ℕ) (hk : k < rate) :
    (((b.data.toList.drop o).take rate).toArray.getD k 0).toUInt64 = byteAt b (o + k) := by
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_take,
    List.getElem?_drop, hk, ite_true, byteAt]
  split
  · rename_i h
    rw [List.getElem?_eq_getElem (by simpa using h), Option.getD_some]; rfl
  · rename_i h
    rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem blockLane_unfold (a : Array UInt8) (i : ℕ) : blockLane a i =
    (0 : UInt64) ||| (a.getD (8 * i) 0).toUInt64 <<< 0 ||| (a.getD (8 * i + 1) 0).toUInt64 <<< 8 |||
      (a.getD (8 * i + 2) 0).toUInt64 <<< 16 ||| (a.getD (8 * i + 3) 0).toUInt64 <<< 24 |||
      (a.getD (8 * i + 4) 0).toUInt64 <<< 32 ||| (a.getD (8 * i + 5) 0).toUInt64 <<< 40 |||
      (a.getD (8 * i + 6) 0).toUInt64 <<< 48 ||| (a.getD (8 * i + 7) 0).toUInt64 <<< 56 := rfl

theorem blockLane_eq (b : ByteArray) (o i : ℕ) (hi : i < 17) :
    blockLane ((b.data.toList.drop o).take rate).toArray i = laneAt b (o + 8 * i) := by
  have r : rate = 136 := rfl
  rw [blockLane_unfold, byteAt_eq b o (8 * i) (by omega), byteAt_eq b o (8 * i + 1) (by omega),
    byteAt_eq b o (8 * i + 2) (by omega), byteAt_eq b o (8 * i + 3) (by omega),
    byteAt_eq b o (8 * i + 4) (by omega), byteAt_eq b o (8 * i + 5) (by omega),
    byteAt_eq b o (8 * i + 6) (by omega), byteAt_eq b o (8 * i + 7) (by omega)]
  simp only [laneAt, Nat.add_assoc, UInt64.shiftLeft_zero, UInt64.zero_or]

theorem blockLane_zero (b : ByteArray) (o i : ℕ) (hi : 17 ≤ i) :
    blockLane ((b.data.toList.drop o).take rate).toArray i = 0 := by
  have h : ∀ k, ((b.data.toList.drop o).take rate).toArray.getD (8 * i + k) 0 = 0 := by
    intro k
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_take]
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by simp only [rate]; omega))]; rfl
  have h0 := h 0
  rw [Nat.add_zero] at h0
  rw [blockLane_unfold, h0, h 1, h 2, h 3, h 4, h 5, h 6, h 7]
  decide

theorem xorBlock_toVec (s : S25) (b : ByteArray) (o : ℕ) :
    (xorBlock s b o).toVec =
      Vector.ofFn fun i =>
        s.toVec[i] ^^^ blockLane ((b.data.toList.drop o).take rate).toArray i := by
  ext i hi
  simp only [Vector.getElem_ofFn]
  interval_cases i <;>
    first
    | (rw [blockLane_eq _ _ _ (by decide)]; rfl)
    | (rw [blockLane_zero _ _ _ (by decide), UInt64.xor_zero]; rfl)

theorem loopB_toVec (b : ByteArray) : ∀ (n : ℕ) (s : S25) (o : ℕ),
    (loopB b s o n).toVec = absorb s.toVec (b.data.toList.drop o) n
  | 0, s, o => rfl
  | n + 1, s, o => by
    rw [loopB, absorb, ← xorBlock_toVec, keccakF_toVec, loopB_toVec b n, List.drop_drop]

theorem padB_data (b : ByteArray) : (padB b).data.toList = pad b.data.toList := by
  have hl : b.data.toList.length = b.size := by simp
  simp only [padB, pad, hl]
  split
  · rw [ByteArray.data_push, Array.toList_push]
  · rw [ByteArray.data_push, Array.toList_push, ByteArray.data_append, Array.toList_append,
      ByteArray.data_push, Array.toList_push, Array.toList_replicate]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem outBytes_eq (s : S25) : outBytes s = ⟨((s.toVec.toList.flatMap fun w =>
    (List.range 8).map fun k => (w >>> (8 * k).toUInt64).toUInt8).take 32).toArray,
      by simp [List.map_const']⟩ := rfl

/-- **The byte-array hash is the contract's.** -/
theorem digestB_eq (b : ByteArray) : digestB b = keccakDigest b.data.toList := by
  have h := loopB_toVec (padB b) ((padB b).size / rate) zeroS 0
  have hs : (padB b).size = (pad b.data.toList).length := by
    rw [← padB_data]; simp
  rw [List.drop_zero, padB_data, hs] at h
  simp only [digestB, keccakDigest, keccak256, outBytes_eq, h, hs]
  rfl

/-- Keccak-256 of a list of bytes, through the byte-array path. -/
def digestL (l : List UInt8) : Digest := digestB ⟨l.toArray⟩

theorem digestL_eq (l : List UInt8) : digestL l = keccakDigest l := by
  rw [digestL, digestB_eq]

/-- The contract's `keccak256` through the byte-array path (how the known answers are checked). -/
theorem keccak256_eq_digestL (l : List UInt8) : keccak256 l = (digestL l).toList := by
  rw [digestL_eq]; simp [keccakDigest]

end RecursionFast.Keccak
