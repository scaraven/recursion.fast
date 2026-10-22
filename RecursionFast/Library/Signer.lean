/-
  RecursionFast.Library.Signer  (UNTRUSTED, kernel-checked)

  **The Lean reference signer** of the contract's signature (`Contract/Signature.lean`, V4-3,
  V4-A4), and the theorem that its signatures pass `SigOk` (`sigOk_sign`). It is the
  specification the service is tested against, derivation included (V4-A4).

  * **Secret chain starts.** `sign`, `pk` and `authPath` take any function `sk : ℕ → ℕ → Digest`
    (key index, chain index) of secret chain starts, and the theorem holds for every one. The
    reference derivation (V4-A4) is `chainStart seed j i = BLAKE2s-256 keyed by seed of
    (0x53 ‖ enc64 j ‖ byte i)` (tag `S`, `tagSecret`), with a 32-byte signing seed drawn
    independently of the oracle's key, so that no oracle query can equal a derivation input.
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

/-- **The signature's chain ends are the key's.** -/
theorem wotsEnds_sign (j : ℕ) (m : Digest) :
    wotsEnds j m (sign sk j m).ots = pubEnds sk j := by
  simp only [wotsEnds, sign, pubEnds]
  refine List.ext_getElem (by simp [wotsDigits_length]) fun i h1 h2 => ?_
  have hi : i < (wotsDigits m).length := by simpa [wotsDigits_length] using h2
  have hd : (wotsDigits m)[i] ≤ 3 := wotsDigits_le m _ (List.getElem_mem _)
  simp only [List.getElem_mapIdx, List.getElem_zip, List.getElem_map, List.getElem_range]
  have := wotsChain_add j i 0 (wotsDigits m)[i] (3 - (wotsDigits m)[i]) (sk j i)
  rw [Nat.zero_add, Nat.add_sub_cancel' hd] at this
  exact this.symm

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
    have hup : (if k % 2 = 0 then sigNode (node sk t k) (node sk t (sib k))
        else sigNode (node sk t (sib k)) (node sk t k)) = node sk (t + 1) (k / 2) := by
      simp only [node, sib]
      split_ifs with h
      · rw [show 2 * (k / 2) = k by omega]
      · rw [show 2 * (k / 2) = k - 1 by omega, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    rw [sibs, sigRoot, hup, sigRoot_sibs n (t + 1) (k / 2), Nat.div_div_eq_div_mul, ← pow_succ',
      show t + 1 + n = t + (n + 1) by omega]

theorem sigRoot_authPath (j : ℕ) (hj : j < 2 ^ sigHeight) :
    sigRoot j (node sk 0 j) (authPath sk j) = pk sk := by
  rw [authPath, sigRoot_sibs, Nat.zero_add, Nat.div_eq_of_lt hj, pk]

/-! ## The theorem -/

/-- **An honest signature verifies**: for every secret function, key index below `2^16` and
message, the signature passes `SigOk` under the public key. -/
theorem sigOk_sign (j : ℕ) (hj : j < 2 ^ sigHeight) (m : Digest) :
    SigOk (pk sk) m (sign sk j m) = true := by
  have hl : (sign sk j m).ots.length = wotsLen := by simp [sign, wotsDigits_length]
  have hp : (sign sk j m).path.length = sigHeight := sibs_length _ _ _ _
  simp only [SigOk, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hj, hl⟩, hp⟩, ?_⟩
  have h := wotsEnds_sign sk j m
  simp only [sign] at h ⊢
  rw [h]
  exact sigRoot_authPath sk j hj

end RecursionFast.Signer
