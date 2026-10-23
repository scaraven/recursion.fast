/-
  RecursionFast.Library.Signer  (UNTRUSTED, kernel-checked)

  **The Lean reference signer** of the contract's signature (`Contract/Signature.lean`, V4-3,
  V4-A4), and the theorem that its signatures pass `SigOk` (`sigOk_sign`). It is the
  specification the service is tested against, derivation included (V4-A4).

  * **Secret chain starts.** `sign`, `pk` and `authPath` take any function `sk : ℕ → ℕ → Digest`
    (key index, chain index) of secret chain starts, and the theorem holds for every one. The
    reference derivation (V4-A4) is `chainStart seed j i = BLAKE2s-256 keyed by seed of
    (0x53 ‖ enc64 j ‖ byte i)` (tag `S`, `tagSecret`), with a 32-byte signing seed drawn
    independently of the oracle's key. That independence, not the tag, separates the chain
    starts from the oracle's answers: oracle queries are untagged, so `0x53 ‖ …` is itself a
    legal query, answered under the other key (V4-A4 as corrected by stage D).
  * **One-time key `j`.** Chain `i` runs from `sk j i` (position 0) to its end at position 3
    (`pubEnds`); the key's leaf hashes the 133 ends (`wotsLeaf`).
  * **The key tree** (`node t k`, level `t`, index `k`; level 0 the leaves) has height 16; the
    public key is its root (`pk`). The authentication path of key `j` lists, from the leaves up,
    the sibling of the node on `j`'s path (`authPath`).
  * **A signature** of the 32-byte message `m` with key `j`: chain `i` advanced to position
    `dᵢ`, the `i`-th WOTS digit of `m` (`sign`).
  * `sigOk_sign`: for every `sk`, `j < 2^16` and `m`, `SigOk (pk sk) m (sign sk j m) = true`.
    Proved symbolically from the chain's additivity (`wotsChain_add`), the digits being at most 3
    (`wotsDigits_le`, `wotsDigits_length`) and the path's climb (`sigRoot_authPath`); no hash is
    evaluated (kernel BLAKE2s costs about 2.4 s per compression; one check is about 300).
  * **The checksum's domination** (`wotsDigits_dominates`, RA-m1): for two different messages,
    some WOTS digit of the second is below the first's (from `msgDigits_inj` and the checksum
    falling when message digits rise), so a signature cannot be walked forward along its chains
    into a signature of another message. Kernel-checked, no hash.
  * `pk` and `sign` are computable; `Library/SignerFast.lean` has their fast twins and how to run
    them.
-/
import RecursionFast.Library.Trace

namespace RecursionFast.Signer
open RecursionFast

/-- Domain tag of a secret chain start's derivation input (`S`, V4-A4). -/
def tagSecret : UInt8 := 0x53

/-- **The reference secret chain start** of chain `i` of one-time key `j`: BLAKE2s-256 keyed by
the signing seed (32 bytes) of `tagSecret ‖ enc64 j ‖ i`. -/
def chainStart (seed : List UInt8) (j i : ℕ) : Digest :=
  ⟨(blake2s seed 32 (tagSecret :: enc64 j ++ [i.toUInt8])).toArray, by
    simp [blake2s, List.map_const']⟩

variable (sk : ℕ → ℕ → Digest)

/-- The 133 chain ends of one-time key `j`: chain `i` from `sk j i` walked to position 3. -/
def pubEnds (j : ℕ) : List Digest := (List.range wotsLen).map fun i => wotsChain j i 0 3 (sk j i)

/-- Node `k` of level `t` of the key tree: the leaf of key `k` at level 0, the hash of its two
children above. -/
def node : ℕ → ℕ → Digest
  | 0, k => wotsLeaf k (pubEnds sk k)
  | t + 1, k => sigNode (node t (2 * k)) (node t (2 * k + 1))

/-- **The public key**: the root of the key tree. -/
def pk : Digest := node sk sigHeight 0

/-- The index of the sibling of node `k` of a level. -/
def sib (k : ℕ) : ℕ := if k % 2 = 0 then k + 1 else k - 1

/-- The `n` siblings on the path from node `k` of level `t` upwards. -/
def sibs : ℕ → ℕ → ℕ → List Digest
  | _, _, 0 => []
  | t, k, n + 1 => node sk t (sib k) :: sibs (t + 1) (k / 2) n

/-- **The authentication path of key `j`**: its 16 siblings, leaf level first. -/
def authPath (j : ℕ) : List Digest := sibs sk 0 j sigHeight

/-- **The signature of the message `m` with key `j`**: chain `i` advanced to the `i`-th digit
of `m`, and the authentication path. -/
def sign (j : ℕ) (m : Digest) : Sig :=
  ⟨j, (wotsDigits m).mapIdx fun i d => wotsChain j i 0 d (sk j i), authPath sk j⟩

/-! ## The chain -/

/-- Walking `a + b` steps is walking `a`, then `b`. -/
theorem wotsChain_add (j i : ℕ) : ∀ (s a b : ℕ) (x : Digest),
    wotsChain j i s (a + b) x = wotsChain j i (s + a) b (wotsChain j i s a x)
  | s, 0, b, x => by simp [wotsChain]
  | s, a + 1, b, x => by
    rw [show a + 1 + b = (a + b) + 1 by omega, wotsChain, wotsChain, wotsChain_add j i (s + 1) a b,
      show s + 1 + a = s + (a + 1) by omega]

theorem msgDigits_length (m : Digest) : (msgDigits m).length = 128 := by
  simp [msgDigits, List.length_flatMap]

theorem wotsDigits_length (m : Digest) : (wotsDigits m).length = wotsLen := by
  simp [wotsDigits, msgDigits_length, wotsLen]

/-- Every WOTS digit is at most 3. -/
theorem wotsDigits_le (m : Digest) : ∀ d ∈ wotsDigits m, d ≤ 3 := by
  intro d hd
  simp only [wotsDigits, msgDigits, List.mem_append, List.mem_flatMap, List.mem_map] at hd
  rcases hd with ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> omega

/-! ## The checksum (RA-m1) -/

/-- Four base-4 digits, low first, as a byte. -/
private def ofDigits4 : List ℕ → List UInt8
  | a :: b :: c :: d :: r => (a + 4 * b + 16 * c + 64 * d).toUInt8 :: ofDigits4 r
  | _ => []

private theorem byte_of_digits (b : UInt8) :
    (b.toNat / 4 ^ 0 % 4 + 4 * (b.toNat / 4 ^ 1 % 4) + 16 * (b.toNat / 4 ^ 2 % 4) +
      64 * (b.toNat / 4 ^ 3 % 4)).toUInt8 = b := by
  have h := b.toNat_lt
  have : b.toNat / 4 ^ 0 % 4 + 4 * (b.toNat / 4 ^ 1 % 4) + 16 * (b.toNat / 4 ^ 2 % 4) +
      64 * (b.toNat / 4 ^ 3 % 4) = b.toNat := by norm_num; omega
  rw [this]; exact UInt8.ofNat_toNat

private theorem ofDigits4_msgDigits (m : Digest) : ofDigits4 (msgDigits m) = m.toList := by
  have h : ∀ l : List UInt8, ofDigits4 (l.flatMap fun b => [b.toNat / 4 ^ 0 % 4,
      b.toNat / 4 ^ 1 % 4, b.toNat / 4 ^ 2 % 4, b.toNat / 4 ^ 3 % 4]) = l := by
    intro l
    induction l with
    | nil => rfl
    | cons b l ih =>
      rw [List.flatMap_cons, List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.nil_append, ofDigits4, ih, byte_of_digits]
  have e : msgDigits m = m.toList.flatMap fun b => [b.toNat / 4 ^ 0 % 4,
      b.toNat / 4 ^ 1 % 4, b.toNat / 4 ^ 2 % 4, b.toNat / 4 ^ 3 % 4] := by
    simp only [msgDigits, List.range_succ, List.range_zero, List.map_nil,
      List.map_cons, List.nil_append, List.cons_append]
  rw [e, h]

/-- **The message digits determine the message.** -/
theorem msgDigits_inj {m m' : Digest} (h : msgDigits m = msgDigits m') : m = m' := by
  have := congrArg ofDigits4 h
  rw [ofDigits4_msgDigits, ofDigits4_msgDigits] at this
  exact Vector.toList_inj.mp this

/-- Raising digits lowers the complement sum, weakly. -/
private theorem sum_sub_le : ∀ (d d' : List ℕ), d.length = d'.length →
    (∀ i, d.getD i 0 ≤ d'.getD i 0) → (d'.map (3 - ·)).sum ≤ (d.map (3 - ·)).sum
  | [], [], _, _ => le_rfl
  | a :: d, a' :: d', hl, h => by
    have h0 := h 0
    have ih := sum_sub_le d d' (by simpa using hl) fun i => h (i + 1)
    simp only [List.getD_cons_zero] at h0
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Raising some digit (all at most 3) lowers the complement sum strictly. -/
private theorem sum_sub_lt : ∀ (d d' : List ℕ), d.length = d'.length →
    (∀ i, d.getD i 0 ≤ d'.getD i 0) → (∀ x ∈ d', x ≤ 3) → d ≠ d' →
      (d'.map (3 - ·)).sum < (d.map (3 - ·)).sum
  | [], [], _, _, _, hne => absurd rfl hne
  | a :: d, a' :: d', hl, h, h3, hne => by
    have h0 := h 0
    have ha' := h3 a' (List.mem_cons_self ..)
    simp only [List.getD_cons_zero] at h0
    have hle := sum_sub_le d d' (by simpa using hl) fun i => h (i + 1)
    simp only [List.map_cons, List.sum_cons]
    by_cases hab : a = a'
    · subst hab
      have := sum_sub_lt d d' (by simpa using hl) (fun i => h (i + 1))
        (fun x hx => h3 x (List.mem_cons_of_mem _ hx)) (fun he => hne (he ▸ rfl))
      omega
    · omega

/-- The complement sum of `n` digits is at most `3n`. -/
private theorem checksum_le : ∀ d : List ℕ, (d.map (3 - ·)).sum ≤ 3 * d.length
  | [] => le_rfl
  | a :: d => by
    have := checksum_le d
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- If no base-4 digit of `y` is below `x`'s (both below `4^k`), then `x ≤ y`. -/
private theorem le_of_digits : ∀ (k x y : ℕ), x < 4 ^ k → y < 4 ^ k →
    (∀ t < k, x / 4 ^ t % 4 ≤ y / 4 ^ t % 4) → x ≤ y
  | 0, x, y, hx, _, _ => by simp at hx; omega
  | k + 1, x, y, hx, hy, h => by
    have h0 := h 0 (by omega)
    rw [pow_succ] at hx hy
    have ih := le_of_digits k (x / 4) (y / 4) (by omega) (by omega) fun t ht => by
      have := h (t + 1) (by omega)
      rwa [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at this
    simp only [pow_zero, Nat.div_one] at h0
    omega

private theorem wotsDigits_getD_msg (m : Digest) {i : ℕ} (hi : i < 128) :
    (wotsDigits m).getD i 0 = (msgDigits m).getD i 0 := by
  simp only [wotsDigits, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by rw [msgDigits_length]; exact hi)]

private theorem wotsDigits_getD_check (m : Digest) {t : ℕ} (ht : t < 5) :
    (wotsDigits m).getD (128 + t) 0 = ((msgDigits m).map (3 - ·)).sum / 4 ^ t % 4 := by
  simp only [wotsDigits, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by rw [msgDigits_length]; omega), msgDigits_length]
  simp [ht]

/-- **The checksum's domination property**: for two different messages, some WOTS digit of the
second is below the first's, so a signature of the first cannot be walked forward along its
chains into a signature of the second. -/
theorem wotsDigits_dominates {m m' : Digest} (h : m ≠ m') :
    ∃ i < wotsLen, (wotsDigits m').getD i 0 < (wotsDigits m).getD i 0 := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have hd : ∀ i, (msgDigits m).getD i 0 ≤ (msgDigits m').getD i 0 := by
    intro i
    by_cases hi : i < 128
    · rw [← wotsDigits_getD_msg m hi, ← wotsDigits_getD_msg m' hi]
      exact hcon i (by unfold wotsLen; omega)
    · rw [List.getD_eq_default _ _ (by rw [msgDigits_length]; omega),
        List.getD_eq_default _ _ (by rw [msgDigits_length]; omega)]
  have h3 : ∀ x ∈ msgDigits m', x ≤ 3 := fun x hx =>
    wotsDigits_le m' x (List.mem_append_left _ hx)
  have hlt := sum_sub_lt _ _ (by rw [msgDigits_length, msgDigits_length]) hd h3
    fun he => h (msgDigits_inj he)
  have hC := checksum_le (msgDigits m)
  have hC' := checksum_le (msgDigits m')
  rw [msgDigits_length] at hC hC'
  have hle := le_of_digits 5 ((msgDigits m).map (3 - ·)).sum ((msgDigits m').map (3 - ·)).sum
    (by norm_num; omega) (by norm_num; omega) fun t ht => by
    rw [← wotsDigits_getD_check m ht, ← wotsDigits_getD_check m' ht]
    exact hcon _ (by unfold wotsLen; omega)
  omega

/-- **The signature's chain ends are the key's.** -/
theorem wotsEnds_sign (j : ℕ) (m : Digest) :
    wotsEnds j m (sign sk j m).ots = pubEnds sk j := by
  simp only [wotsEnds, sign, pubEnds]
  refine List.ext_getElem (by simp [wotsDigits_length]) fun i h1 h2 => ?_
  have hi : i < (wotsDigits m).length := by simpa [wotsDigits_length] using h2
  have hd : (wotsDigits m)[i] ≤ 3 := wotsDigits_le m _ (List.getElem_mem _)
  simp only [List.getElem_mapIdx, List.getElem_zip, List.getElem_map, List.getElem_range]
  conv_rhs => rw [← Nat.add_sub_cancel' hd, wotsChain_add, Nat.zero_add]

/-! ## The path -/

theorem sibs_length : ∀ t k n, (sibs sk t k n).length = n
  | _, _, 0 => rfl
  | t, k, n + 1 => by simp [sibs, sibs_length (t + 1) (k / 2) n]

/-- **The climb**: from node `k` of level `t` along its `n` siblings, the root reached is node
`k / 2^n` of level `t + n`. -/
theorem sigRoot_sibs :
    ∀ n t k, sigRoot k (node sk t k) (sibs sk t k n) = node sk (t + n) (k / 2 ^ n)
  | 0, t, k => by simp [sibs, sigRoot]
  | n + 1, t, k => by
    rw [sibs, sigRoot, show t + (n + 1) = t + 1 + n by omega, pow_succ', ← Nat.div_div_eq_div_mul,
      ← sigRoot_sibs n (t + 1) (k / 2)]
    congr 1
    simp only [node, sib]
    split_ifs with h
    · rw [show 2 * (k / 2) = k by omega]
    · rw [show 2 * (k / 2) = k - 1 by omega, Nat.sub_add_cancel (by omega : 1 ≤ k)]

theorem sigRoot_authPath (j : ℕ) (hj : j < 2 ^ sigHeight) :
    sigRoot j (node sk 0 j) (authPath sk j) = pk sk := by
  rw [authPath, sigRoot_sibs, Nat.zero_add, Nat.div_eq_of_lt hj, pk]

/-! ## The theorem -/

/-- **An honest signature verifies**: for every secret function, key index below `2^16` and
message, the signature passes `SigOk` under the public key. -/
theorem sigOk_sign (j : ℕ) (hj : j < 2 ^ sigHeight) (m : Digest) :
    SigOk (pk sk) m (sign sk j m) = true := by
  simp only [SigOk, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hj, by simp [sign, wotsDigits_length]⟩, sibs_length _ _ _ _⟩,
    wotsEnds_sign sk j m ▸ sigRoot_authPath sk j hj⟩

end RecursionFast.Signer
