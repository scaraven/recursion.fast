/-
  RecursionFast.Library.Blake2sFast  (UNTRUSTED, kernel-checked)

  **A word-level BLAKE2s-256 proved equal to the contract's** (C9, C10, C-m3, V4-A7 (d)). The
  contract's `compress` keeps the working vector in a `Vector` and reads the schedule `sigma` at
  run time, and its message path builds lists; compiled, it costs about 1 µs per compression and
  about 5 µs per hashed block (`logs/A-speed-final.log`). The twins here keep the sixteen words in
  registers and write the schedule out:

  * `compressF` (`W16` fields, `G` with constant rotations, `mix0 … mix7`, `roundF`) and
    **`compressF_eq : compressF h m t f0 f1 = compress h m t f0 f1`** for all inputs. The proof is
    symbolic: each `mixᵢ` is `mix` at its four positions by `rfl` (`mix_0 … mix_7`), a round is
    eight of them (`round_toVec`), `sigma.foldl` unrolls by `rfl` (`foldl_sigma`), and the initial
    state is a literal once `h` is split into its eight words (`initialState_eq`). No hash is
    evaluated.
  * The message path over a `ByteArray`: `blockAt` (the block at a byte offset, `blockAt_eq`),
    `loopB` (the block loop, `loopB_eq` against `compressInput`), `outBytes` (`outBytes_eq`), and
    **`digestB_eq : digestB b = blake2sDigest b.data.toList`**; `digestL` for lists.
  Measured: about 0.25 µs per compression and 0.4 µs per block of a long message, against 1 µs and
  5.5 µs for the reference (`docs/v4/stages/A-contract-RESULT.md`).
-/
import RecursionFast.Contract.Relation
import Mathlib.Tactic.IntervalCases

namespace RecursionFast.Blake2s

/-- The sixteen words of `F`'s working vector, as separate fields. -/
structure W16 where
  (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt32)

/-- The working vector as the contract's vector. -/
def W16.toVec (w : W16) : Vector UInt32 16 :=
  #v[w.v0, w.v1, w.v2, w.v3, w.v4, w.v5, w.v6, w.v7, w.v8, w.v9, w.v10, w.v11, w.v12, w.v13,
    w.v14, w.v15]

/-- The mixing function `G` on four words, rotations by constants. -/
@[inline] def G (a b c d x y : UInt32) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let va := a + b + x
  let t := d ^^^ va
  let vd := t >>> 16 ||| t <<< 16
  let vc := c + vd
  let t := b ^^^ vc
  let vb := t >>> 12 ||| t <<< 20
  let va := va + vb + y
  let t := vd ^^^ va
  let vd := t >>> 8 ||| t <<< 24
  let vc := vc + vd
  let t := vb ^^^ vc
  let vb := t >>> 7 ||| t <<< 25
  (va, vb, vc, vd)

/-- `mix` at positions `0 4 8 12` (a column), on separate words. -/
@[inline] def mix0 (w : W16) (x y : UInt32) : W16 :=
  let (a, b, c, d) := G w.v0 w.v4 w.v8 w.v12 x y; { w with v0 := a, v4 := b, v8 := c, v12 := d }
/-- `mix` at positions `1 5 9 13` (a column), on separate words. -/
@[inline] def mix1 (w : W16) (x y : UInt32) : W16 :=
  let (a, b, c, d) := G w.v1 w.v5 w.v9 w.v13 x y; { w with v1 := a, v5 := b, v9 := c, v13 := d }
/-- `mix` at positions `2 6 10 14` (a column), on separate words. -/
@[inline] def mix2 (w : W16) (x y : UInt32) : W16 :=
  let (a, b, c, d) := G w.v2 w.v6 w.v10 w.v14 x y; { w with v2 := a, v6 := b, v10 := c, v14 := d }
/-- `mix` at positions `3 7 11 15` (a column), on separate words. -/
@[inline] def mix3 (w : W16) (x y : UInt32) : W16 :=
  let (a, b, c, d) := G w.v3 w.v7 w.v11 w.v15 x y; { w with v3 := a, v7 := b, v11 := c, v15 := d }
/-- `mix` at positions `0 5 10 15` (a diagonal), on separate words. -/
@[inline] def mix4 (w : W16) (x y : UInt32) : W16 :=
  let (a, b, c, d) := G w.v0 w.v5 w.v10 w.v15 x y; { w with v0 := a, v5 := b, v10 := c, v15 := d }
/-- `mix` at positions `1 6 11 12` (a diagonal), on separate words. -/
@[inline] def mix5 (w : W16) (x y : UInt32) : W16 :=
  let (a, b, c, d) := G w.v1 w.v6 w.v11 w.v12 x y; { w with v1 := a, v6 := b, v11 := c, v12 := d }
/-- `mix` at positions `2 7 8 13` (a diagonal), on separate words. -/
@[inline] def mix6 (w : W16) (x y : UInt32) : W16 :=
  let (a, b, c, d) := G w.v2 w.v7 w.v8 w.v13 x y; { w with v2 := a, v7 := b, v8 := c, v13 := d }
/-- `mix` at positions `3 4 9 14` (a diagonal), on separate words. -/
@[inline] def mix7 (w : W16) (x y : UInt32) : W16 :=
  let (a, b, c, d) := G w.v3 w.v4 w.v9 w.v14 x y; { w with v3 := a, v4 := b, v9 := c, v14 := d }

/-- One round on separate words, the message words given in the round's order. -/
@[inline] def roundF (w : W16) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt32) :
    W16 :=
  mix7 (mix6 (mix5 (mix4 (mix3 (mix2 (mix1 (mix0 w x0 x1) x2 x3) x4 x5) x6 x7) x8 x9) x10 x11)
    x12 x13) x14 x15

/-- `compress` on separate words, the schedule `sigma` written out. -/
def compressF (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64) (f0 f1 : UInt32) :
    Vector UInt32 8 :=
  let m0 := m[0]; let m1 := m[1]; let m2 := m[2]; let m3 := m[3]; let m4 := m[4]
  let m5 := m[5]; let m6 := m[6]; let m7 := m[7]; let m8 := m[8]; let m9 := m[9]
  let m10 := m[10]; let m11 := m[11]; let m12 := m[12]; let m13 := m[13]; let m14 := m[14]
  let m15 := m[15]
  let v : W16 := ⟨h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], iv[0], iv[1], iv[2], iv[3],
    iv[4] ^^^ t.toUInt32, iv[5] ^^^ (t >>> 32).toUInt32, iv[6] ^^^ f0, iv[7] ^^^ f1⟩
  let v := roundF v m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15
  let v := roundF v m14 m10 m4 m8 m9 m15 m13 m6 m1 m12 m0 m2 m11 m7 m5 m3
  let v := roundF v m11 m8 m12 m0 m5 m2 m15 m13 m10 m14 m3 m6 m7 m1 m9 m4
  let v := roundF v m7 m9 m3 m1 m13 m12 m11 m14 m2 m6 m5 m10 m4 m0 m15 m8
  let v := roundF v m9 m0 m5 m7 m2 m4 m10 m15 m14 m1 m11 m12 m6 m8 m3 m13
  let v := roundF v m2 m12 m6 m10 m0 m11 m8 m3 m4 m13 m7 m5 m15 m14 m1 m9
  let v := roundF v m12 m5 m1 m15 m14 m13 m4 m10 m0 m7 m6 m3 m9 m2 m8 m11
  let v := roundF v m13 m11 m7 m14 m12 m1 m3 m9 m5 m0 m15 m4 m8 m6 m2 m10
  let v := roundF v m6 m15 m14 m9 m11 m3 m0 m8 m12 m2 m13 m7 m1 m4 m10 m5
  let v := roundF v m10 m2 m8 m4 m7 m6 m1 m5 m15 m11 m9 m14 m3 m12 m13 m0
  #v[h[0] ^^^ v.v0 ^^^ v.v8, h[1] ^^^ v.v1 ^^^ v.v9, h[2] ^^^ v.v2 ^^^ v.v10,
     h[3] ^^^ v.v3 ^^^ v.v11, h[4] ^^^ v.v4 ^^^ v.v12, h[5] ^^^ v.v5 ^^^ v.v13,
     h[6] ^^^ v.v6 ^^^ v.v14, h[7] ^^^ v.v7 ^^^ v.v15]

/-! ### `compressF` is `compress` -/

/-- `mix{k}` is `mix` at its positions. -/
theorem mix_0 (w : W16) (x y : UInt32) : mix w.toVec 0 4 8 12 x y = (mix0 w x y).toVec := rfl
/-- `mix{k}` is `mix` at its positions. -/
theorem mix_1 (w : W16) (x y : UInt32) : mix w.toVec 1 5 9 13 x y = (mix1 w x y).toVec := rfl
/-- `mix{k}` is `mix` at its positions. -/
theorem mix_2 (w : W16) (x y : UInt32) : mix w.toVec 2 6 10 14 x y = (mix2 w x y).toVec := rfl
/-- `mix{k}` is `mix` at its positions. -/
theorem mix_3 (w : W16) (x y : UInt32) : mix w.toVec 3 7 11 15 x y = (mix3 w x y).toVec := rfl
/-- `mix{k}` is `mix` at its positions. -/
theorem mix_4 (w : W16) (x y : UInt32) : mix w.toVec 0 5 10 15 x y = (mix4 w x y).toVec := rfl
/-- `mix{k}` is `mix` at its positions. -/
theorem mix_5 (w : W16) (x y : UInt32) : mix w.toVec 1 6 11 12 x y = (mix5 w x y).toVec := rfl
/-- `mix{k}` is `mix` at its positions. -/
theorem mix_6 (w : W16) (x y : UInt32) : mix w.toVec 2 7 8 13 x y = (mix6 w x y).toVec := rfl
/-- `mix{k}` is `mix` at its positions. -/
theorem mix_7 (w : W16) (x y : UInt32) : mix w.toVec 3 4 9 14 x y = (mix7 w x y).toVec := rfl

/-- A round on separate words is the contract's round. -/
theorem round_toVec (w : W16) (m : Vector UInt32 16) (s : Vector (Fin 16) 16) :
    round w.toVec m s = (roundF w m[s[0]] m[s[1]] m[s[2]] m[s[3]] m[s[4]] m[s[5]] m[s[6]] m[s[7]]
      m[s[8]] m[s[9]] m[s[10]] m[s[11]] m[s[12]] m[s[13]] m[s[14]] m[s[15]]).toVec := by
  simp only [round, mix_0, mix_1, mix_2, mix_3, mix_4, mix_5, mix_6, mix_7, roundF]

/-- The ten rounds, unrolled. -/
theorem foldl_sigma (f : Vector UInt32 16 → Vector (Fin 16) 16 → Vector UInt32 16) (x) :
    sigma.foldl f x = f (f (f (f (f (f (f (f (f (f x sigma[0]) sigma[1]) sigma[2]) sigma[3])
      sigma[4]) sigma[5]) sigma[6]) sigma[7]) sigma[8]) sigma[9] := rfl


/-- The initial working vector, word by word. -/
theorem initialState_eq (h : Vector UInt32 8) (t : UInt64) (f0 f1 : UInt32) :
    initialState h t f0 f1 = (⟨h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], iv[0], iv[1],
      iv[2], iv[3], iv[4] ^^^ t.toUInt32, iv[5] ^^^ (t >>> 32).toUInt32, iv[6] ^^^ f0,
      iv[7] ^^^ f1⟩ : W16).toVec := by
  obtain ⟨⟨l⟩, hl⟩ := h
  match l, hl with
  | [_, _, _, _, _, _, _, _], _ => rfl

/-- **The word-level compression is the contract's.** -/
theorem compressF_eq (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64) (f0 f1 : UInt32) :
    compressF h m t f0 f1 = compress h m t f0 f1 := by
  simp only [compress, foldl_sigma, initialState_eq, round_toVec]
  rfl

/-! ## The message path over a byte array -/

/-- Byte `i` of `b`, `0` past its end. -/
@[inline] def byteAt (b : ByteArray) (i : Nat) : UInt32 :=
  if h : i < b.size then b[i].toUInt32 else 0

/-- The little-endian word at byte `i` of `b`. -/
@[inline] def wordAt (b : ByteArray) (i : Nat) : UInt32 :=
  byteAt b i ||| byteAt b (i + 1) <<< 8 ||| byteAt b (i + 2) <<< 16 ||| byteAt b (i + 3) <<< 24

/-- The message block at byte `o` of `b`. -/
def blockAt (b : ByteArray) (o : Nat) : Vector UInt32 16 :=
  #v[wordAt b o, wordAt b (o + 4), wordAt b (o + 8), wordAt b (o + 12), wordAt b (o + 16),
    wordAt b (o + 20), wordAt b (o + 24), wordAt b (o + 28), wordAt b (o + 32), wordAt b (o + 36),
    wordAt b (o + 40), wordAt b (o + 44), wordAt b (o + 48), wordAt b (o + 52), wordAt b (o + 56),
    wordAt b (o + 60)]

/-- The block loop over a byte array, from byte `o`. -/
def loopB (b : ByteArray) (h : Vector UInt32 8) (o : Nat) : Nat → Vector UInt32 8
  | 0 => compressF h (blockAt b o) b.size.toUInt64 0xFFFFFFFF 0
  | n + 1 => loopB b (compressF h (blockAt b o) (o + 64).toUInt64 0 0) (o + 64) n

/-- The 32 output bytes of a chaining value, each word little-endian. -/
def outBytes (h : Vector UInt32 8) : Digest :=
  #v[h[0].toUInt8, (h[0] >>> 8).toUInt8, (h[0] >>> 16).toUInt8, (h[0] >>> 24).toUInt8,
    h[1].toUInt8, (h[1] >>> 8).toUInt8, (h[1] >>> 16).toUInt8, (h[1] >>> 24).toUInt8,
    h[2].toUInt8, (h[2] >>> 8).toUInt8, (h[2] >>> 16).toUInt8, (h[2] >>> 24).toUInt8,
    h[3].toUInt8, (h[3] >>> 8).toUInt8, (h[3] >>> 16).toUInt8, (h[3] >>> 24).toUInt8,
    h[4].toUInt8, (h[4] >>> 8).toUInt8, (h[4] >>> 16).toUInt8, (h[4] >>> 24).toUInt8,
    h[5].toUInt8, (h[5] >>> 8).toUInt8, (h[5] >>> 16).toUInt8, (h[5] >>> 24).toUInt8,
    h[6].toUInt8, (h[6] >>> 8).toUInt8, (h[6] >>> 16).toUInt8, (h[6] >>> 24).toUInt8,
    h[7].toUInt8, (h[7] >>> 8).toUInt8, (h[7] >>> 16).toUInt8, (h[7] >>> 24).toUInt8]

/-- The unkeyed BLAKE2s-256 initial chaining value: `iv` with the parameter block `0x01010020`. -/
def h0 : Vector UInt32 8 := iv.set 0 (iv[0] ^^^ 0x01010020)

/-- **BLAKE2s-256 of a byte array**, as a digest (`digestB_eq`). -/
def digestB (b : ByteArray) : Digest := outBytes (loopB b h0 0 ((b.size - 1) / 64))

/-! ### `digestB` is `blake2sDigest` -/

theorem byteAt_eq (b : ByteArray) (o k : ℕ) (hk : k < 64) :
    (((b.data.toList.drop o).take 64).toArray.getD k 0).toUInt32 = byteAt b (o + k) := by
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_take,
    List.getElem?_drop, hk, ite_true, byteAt]
  split
  · rename_i h
    rw [List.getElem?_eq_getElem (by simpa using h), Option.getD_some]; rfl
  · rename_i h
    rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem blockAt_eq (b : ByteArray) (o : ℕ) : blockAt b o = block (b.data.toList.drop o) := by
  ext i hi
  simp only [block, Vector.getElem_ofFn, byteAt_eq b o _ (by omega : 4 * i < 64),
    byteAt_eq b o _ (by omega : 4 * i + 1 < 64), byteAt_eq b o _ (by omega : 4 * i + 2 < 64),
    byteAt_eq b o _ (by omega : 4 * i + 3 < 64)]
  interval_cases i <;> rfl

theorem loopB_eq (b : ByteArray) : ∀ (n : ℕ) (h : Vector UInt32 8) (o : ℕ), o + 64 * n ≤ b.size →
    loopB b h o n = compressInput h o (b.data.toList.drop o) n
  | 0, h, o, ho => by
    simp only [loopB, compressInput, compressF_eq, blockAt_eq, List.length_drop,
      Array.length_toList, ByteArray.size_data]
    rw [show o + (b.size - o) = b.size by omega]
  | n + 1, h, o, ho => by
    rw [loopB, compressInput, compressF_eq, blockAt_eq, loopB_eq b n _ (o + 64) (by omega),
      List.drop_drop]

theorem outBytes_eq (h : Vector UInt32 8) :
    outBytes h = ⟨(((h.toList.flatMap fun w : UInt32 => [w.toUInt8, (w >>> 8).toUInt8,
      (w >>> 16).toUInt8, (w >>> 24).toUInt8]).take 32).toArray), by simp [List.map_const']⟩ := by
  obtain ⟨⟨l⟩, hl⟩ := h
  match l, hl with
  | [_, _, _, _, _, _, _, _], _ => rfl

/-- **The byte-array hash is the contract's.** -/
theorem digestB_eq (b : ByteArray) : digestB b = blake2sDigest b.data.toList := by
  have hsz : b.data.toList.length = b.size := by simp
  simp only [digestB, blake2sDigest, blake2s256, blake2s, List.length_nil, ↓reduceIte,
    List.nil_append, outBytes_eq, hsz]
  rw [loopB_eq b _ _ 0 (by omega), List.drop_zero]
  rfl

/-- BLAKE2s-256 of a list of bytes, through the byte-array path. -/
def digestL (l : List UInt8) : Digest := digestB ⟨l.toArray⟩

theorem digestL_eq (l : List UInt8) : digestL l = blake2sDigest l := by
  rw [digestL, digestB_eq]

end RecursionFast.Blake2s
