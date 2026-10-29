/-
  RecursionFast.Library.SignerFast  (UNTRUSTED, kernel-checked)

  **The executable reference signer** (V4-A4: the service is tested against the Lean signer,
  derivation included). `Library/Signer.lean` defines the signer for proofs; computing its public
  key with the contract's reference BLAKE2s (about 31 million compressions for `2^16` keys) takes
  minutes, and `authPath` recomputes subtrees. This file computes the same values fast, each
  proved equal to the reference:

  * `chainStartF seed j i` (the keyed BLAKE2s derivation through the word-level path,
    `blake2sKeyedB`) `= Signer.chainStart seed j i` (`chainStartF_eq`);
  * `Tree`, the key tree's levels as arrays, computed once (`buildTree`, `2^17 − 1` nodes), with
    `buildTree_get`: entry `k` of level `t` is `Signer.node sk t k`;
  * `Tree.pk` `= Signer.pk sk` and `Tree.sign` `= Signer.sign sk j m` (`Tree.pk_eq`,
    `Tree.sign_eq`): a signature costs one WOTS pass (about 200 chain steps) and array lookups.

  **How to run it.** `scripts/speed/Signer.lean` is a command-line front end (see its header):
  `lake -f scripts/speed/lakefile.toml build signer`, then
  `.lake/build/bin/signer <seed-hex> <j> <message-hex>` prints `vk`, then the signature as
  `idx`, the 133 chain values and the 16 path digests, one hex digest per line.
-/
import RecursionFast.Library.Signer
import RecursionFast.Library.Fast

namespace RecursionFast.Signer
open RecursionFast Blake2s

/-! ## Keyed BLAKE2s through the byte-array path -/

/-- BLAKE2s-256 keyed by `key` (`1 ≤ |key| ≤ 32`) of `msg`, through the byte-array path: the key
block, zero-padded to 64 bytes, then the message. -/
def blake2sKeyedB (key : List UInt8) (msg : List UInt8) : Digest :=
  let b : ByteArray := ⟨(key ++ List.replicate (64 - key.length) 0 ++ msg).toArray⟩
  outBytes (loopB b (iv.set 0 (iv[0] ^^^ (0x01010000 : UInt32) ^^^ key.length.toUInt32 <<< 8 ^^^
    (32 : Nat).toUInt32)) 0 ((b.size - 1) / 64))

theorem blake2sKeyedB_eq (key msg : List UInt8) (hk : key ≠ []) :
    blake2sKeyedB key msg = ⟨(blake2s key 32 msg).toArray, by simp [blake2s, List.map_const']⟩ := by
  have hkk : key.length ≠ 0 := by simpa using hk
  simp only [blake2sKeyedB, blake2s, hkk, ↓reduceIte, outBytes_eq]
  rw [loopB_eq _ _ _ 0 (by simp; omega), List.drop_zero]
  simp [ByteArray.size]

/-- The reference chain start (`Signer.chainStart`) through the byte-array path. -/
def chainStartF (seed : List UInt8) (j i : ℕ) : Digest :=
  blake2sKeyedB seed (tagSecret :: enc64 j ++ [i.toUInt8])

theorem chainStartF_eq (seed : List UInt8) (hs : seed ≠ []) :
    chainStartF seed = chainStart seed := by
  funext j i
  rw [chainStartF, blake2sKeyedB_eq _ _ hs, chainStart]

/-! ## The key tree, computed once -/

variable (sk : ℕ → ℕ → Digest)

/-- The chain ends of key `j`, with the fast hashes. -/
def pubEndsF (j : ℕ) : List Digest :=
  (List.range wotsLen).map fun i => wotsChainF j i 0 3 (sk j i)

/-- The leaf of key `k`, with the fast hashes. -/
def leafF (k : ℕ) : Digest := wotsLeafF k (pubEndsF sk k)

theorem leafF_eq (k : ℕ) : leafF sk k = node sk 0 k := by
  simp only [leafF, pubEndsF, node, pubEnds, wotsChainF_eq, wotsLeafF_eq]

/-- The level above: adjacent nodes hashed in pairs. -/
def levelUp (l : Array Digest) : Array Digest :=
  Array.ofFn fun k : Fin (l.size / 2) => sigNodeF (l.getD (2 * k) 0) (l.getD (2 * k + 1) 0)

/-- Levels `t … t + n` of the key tree from level `t` (`2^(16 - t)` nodes). -/
def levelsFrom : ℕ → Array Digest → List (Array Digest)
  | 0, l => [l]
  | n + 1, l => l :: levelsFrom n (levelUp l)

/-- **The key tree's 17 levels**, leaves first, from the secret function `sk`. -/
def buildTree : List (Array Digest) :=
  levelsFrom sigHeight (Array.ofFn fun k : Fin (2 ^ sigHeight) => leafF sk k)

theorem levelUp_size (l : Array Digest) : (levelUp l).size = l.size / 2 := by simp [levelUp]

/-- If level `t` is exact (`2^(n+1)` entries, entry `k` is `node sk t k`), so is level
`t + 1`. -/
theorem levelUp_get {t n : ℕ} {l : Array Digest} (hs : l.size = 2 ^ (n + 1))
    (hl : ∀ k < l.size, l.getD k 0 = node sk t k) :
    (levelUp l).size = 2 ^ n ∧
      ∀ k < (levelUp l).size, (levelUp l).getD k 0 = node sk (t + 1) k := by
  have hsz : (levelUp l).size = 2 ^ n := by
    rw [levelUp_size, hs, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  refine ⟨hsz, fun k hk => ?_⟩
  rw [hsz] at hk
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some]
  simp only [levelUp, Array.getElem_ofFn]
  rw [hl _ (by rw [hs, pow_succ]; omega), hl _ (by rw [hs, pow_succ]; omega), sigNodeF_eq, node]

theorem levelsFrom_get : ∀ (n t : ℕ) (l : Array Digest), l.size = 2 ^ n →
    (∀ k < l.size, l.getD k 0 = node sk t k) →
      ∀ u ≤ n, ∀ k < 2 ^ (n - u), ((levelsFrom n l).getD u #[]).getD k 0 = node sk (t + u) k
  | 0, t, l, hs, hl, u, hu, k, hk => by
    obtain rfl : u = 0 := by omega
    simp only [levelsFrom, List.getD_cons_zero, Nat.add_zero]
    exact hl k (by rw [hs]; simpa using hk)
  | n + 1, t, l, hs, hl, u, hu, k, hk => by
    cases u with
    | zero =>
      simp only [levelsFrom, List.getD_cons_zero, Nat.add_zero]
      exact hl k (by rw [hs]; simpa using hk)
    | succ u =>
      rw [show n + 1 - (u + 1) = n - u by omega] at hk
      obtain ⟨hs', hl'⟩ := levelUp_get sk hs hl
      simp only [levelsFrom, List.getD_cons_succ]
      rw [levelsFrom_get n (t + 1) (levelUp l) hs' hl' u (by omega) k (by omega),
        Nat.add_assoc, Nat.add_comm 1 u]

/-- **Entry `k` of level `t` of the computed tree is `Signer.node sk t k`.** -/
theorem buildTree_get {t k : ℕ} (ht : t ≤ sigHeight) (hk : k < 2 ^ (sigHeight - t)) :
    ((buildTree sk).getD t #[]).getD k 0 = node sk t k := by
  have := levelsFrom_get sk sigHeight 0 (Array.ofFn fun k : Fin (2 ^ sigHeight) => leafF sk k)
    (by simp) (fun k hk => by
      simp only [Array.size_ofFn] at hk
      simp [Array.getD_eq_getD_getElem?, hk, leafF_eq]) t ht k hk
  rwa [Nat.zero_add] at this

/-! ## Public key and signatures from the computed tree -/

/-- The public key: the root of the computed tree. -/
def Tree.pk (T : List (Array Digest)) : Digest := (T.getD sigHeight #[]).getD 0 0

/-- The `n` siblings on the path from node `k` of level `t`, read from the computed tree. -/
def Tree.sibs (T : List (Array Digest)) : ℕ → ℕ → ℕ → List Digest
  | _, _, 0 => []
  | t, k, n + 1 => (T.getD t #[]).getD (sib k) 0 :: Tree.sibs T (t + 1) (k / 2) n

/-- **A signature from the computed tree**: the WOTS values with the fast hashes and the path
read from the tree. -/
def Tree.sign (T : List (Array Digest)) (j : ℕ) (m : Digest) : Sig :=
  ⟨j, (wotsDigits m).mapIdx fun i d => wotsChainF j i 0 d (sk j i), Tree.sibs T 0 j sigHeight⟩

theorem Tree.pk_eq : Tree.pk (buildTree sk) = Signer.pk sk := by
  rw [Tree.pk, buildTree_get sk le_rfl (by simp), Signer.pk]

theorem sib_lt {k m : ℕ} (hk : k < 2 * m) : sib k < 2 * m := by
  unfold sib; split_ifs <;> omega

theorem Tree.sibs_eq : ∀ (n t k : ℕ), t + n ≤ sigHeight → k < 2 ^ (sigHeight - t) →
    Tree.sibs (buildTree sk) t k n = Signer.sibs sk t k n
  | 0, _, _, _, _ => rfl
  | n + 1, t, k, htn, hk => by
    have hpow : 2 ^ (sigHeight - t) = 2 * 2 ^ (sigHeight - (t + 1)) := by
      rw [← pow_succ']; congr 1; omega
    rw [Tree.sibs, Signer.sibs, buildTree_get sk (by omega) (by rw [hpow] at hk ⊢; exact sib_lt hk),
      Tree.sibs_eq n (t + 1) (k / 2) (by omega) (by rw [hpow] at hk; omega)]

theorem Tree.sign_eq (j : ℕ) (hj : j < 2 ^ sigHeight) (m : Digest) :
    Tree.sign sk (buildTree sk) j m = Signer.sign sk j m := by
  simp only [Tree.sign, Signer.sign, wotsChainF_eq, Signer.authPath]
  rw [Tree.sibs_eq sk sigHeight 0 j (by omega) (by simpa using hj)]

/-- **The fast signer's signatures verify** under the fast signer's key. -/
theorem Tree.sigOk_sign (j : ℕ) (hj : j < 2 ^ sigHeight) (m : Digest) :
    SigOk (Tree.pk (buildTree sk)) m (Tree.sign sk (buildTree sk) j m) = true :=
  Tree.pk_eq sk ▸ Tree.sign_eq sk j hj m ▸ Signer.sigOk_sign sk j hj m

end RecursionFast.Signer
