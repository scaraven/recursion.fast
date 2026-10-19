/-
# Controls: the relation (`Contract/Relation.lean`), positive and negative        (DESIGN-v3 §2.3)

Known answers are decided by the kernel (`decide +kernel`, about 2.5 s per BLAKE2s compression);
each expected digest is the output of the `python3 -I` command in its docstring (`hashlib`,
CPython 3, `blake2s`, `digest_size=32`). The start of every chain is `s0 = 00 01 … 1f`.

Positive:
* `chain1_kat`, `chain2_kat`, `chain16_kat`: `chainEnd s0 n` for `n = 1, 2, 16`: each step hashes
  `tagChain ‖ d` (33 bytes).
* `leafStmt_kat`, `nodeStmt_kat`: the byte layouts `tagLeaf ‖ h ‖ enc64 n` and
  `tagNode ‖ c₁ ‖ c₂` (the runner hashes the same bytes).
* `node_of_two_leaves`: under the witness-sending verifier, which recomputes chains
  (`Library/WitnessSending.lean`), a node digest of two leaf digests is in the relation with the
  two leaf proofs as its witness, for every two starts and lengths up to `chainCap`.
* `leaf_at_chainCap`: a chain of exactly `chainCap` steps is in the relation (the bound is `≤`).
* `tags_separate`: the four tags are distinct bytes, the chain, leaf and node preimages and the
  oracle's inputs start with their own tag, so no oracle input is a chain, leaf or node preimage.

Negative (concrete instances at `s0`, `n = 1`, except where every argument is quantified):
* `wrong_end`: the leaf statement of the chain's start, not its end, is not witnessed by the start.
* `leaf_over_chainCap`: a chain of `chainCap + 1` steps is not in the relation, for every start
  and verifier (the bound is checked before the hash).
* `node_statement_mismatch`: two accepted children under a statement that is not their `nodeStmt`
  (a leaf statement); `node_needs_statement`: the same for every statement and children.
* `first_child_rejected`, `second_child_rejected`: one child is a correct leaf proof, the other a
  well-formed leaf proof for the statement of the chain's start.
* `Vb_over_cap`: every submission's instantiated verifier rejects every proof above `proofCap`;
  `deep_accepted_but_capped`: the witness-sending verifier accepts a 13-level proof of
  1,114,024 bytes that the cap then rejects (so the cap is what rejects it).
-/
import RecursionFast.Library.WitnessSending
import RecursionFast.Controls.Blake2s

namespace RecursionFast.Controls.Relation
open RecursionFast RecursionFast.WitnessSending
open RecursionFast.Controls.Blake2s (hex)

/-- The digest written by a hex string. -/
def ofHex (s : String) : Digest := Vector.ofFn fun i => (hex s).getD i 0

/-- The chain start `00 01 … 1f`. -/
def s0 : Digest := Vector.ofFn fun i => i.val.toUInt8

/-! ## Known answers -/

/-- `python3 -I -c "import hashlib; print(hashlib.blake2s(b'C'+bytes(range(32))).hexdigest())"` -/
theorem chain1_kat : (chainEnd s0 1).toList =
    hex "7b3746567b4e4fabc189813de4005675433183b47660560825d4741774350544" := by decide +kernel

/-- `python3 -I -c "import hashlib; H=lambda b: hashlib.blake2s(b'C'+b).digest();
print(H(H(bytes(range(32)))).hex())"` -/
theorem chain2_kat : (chainEnd s0 2).toList =
    hex "84de040b23986f9880cc37aec1852359e17c164ac488dc81edf784cee0ae1945" := by decide +kernel

/-- `python3 -I -c "import hashlib; d=bytes(range(32))
for _ in range(16): d=hashlib.blake2s(b'C'+d).digest()
print(d.hex())"` -/
theorem chain16_kat : (chainEnd s0 16).toList =
    hex "a71f6bd7ac08ab5936654a7904bd8feb7636e1f0eb556ae2619ba7c1be41e58d" := by decide +kernel

/-- `python3 -I -c "import hashlib;
h=bytes.fromhex('a71f6bd7ac08ab5936654a7904bd8feb7636e1f0eb556ae2619ba7c1be41e58d');
print(hashlib.blake2s(b'L'+h+(16).to_bytes(8,'little')).hexdigest())"` -/
theorem leafStmt_kat :
    (leafStmt (ofHex "a71f6bd7ac08ab5936654a7904bd8feb7636e1f0eb556ae2619ba7c1be41e58d")
      16).toList =
      hex "c81156bc71500494780f6635d8533cb9e7b738f5c408ebadb58ceef477cd2b4b" := by decide +kernel

/-- `python3 -I -c "import hashlib;
a=bytes.fromhex('7b3746567b4e4fabc189813de4005675433183b47660560825d4741774350544');
b=bytes.fromhex('84de040b23986f9880cc37aec1852359e17c164ac488dc81edf784cee0ae1945');
print(hashlib.blake2s(b'N'+a+b).hexdigest())"` (the digests of `chain1_kat`, `chain2_kat`) -/
theorem nodeStmt_kat :
    (nodeStmt (ofHex "7b3746567b4e4fabc189813de4005675433183b47660560825d4741774350544")
      (ofHex "84de040b23986f9880cc37aec1852359e17c164ac488dc81edf784cee0ae1945")).toList =
      hex "23b28cbc4bf7d65abbf43ff39084438ba0fb080bdef09b9e4830b10deada1bab" := by decide +kernel

/-! ## Tags -/

/-- **Tags separate**: the four tags are distinct bytes; the chain, leaf and node preimages start
with `tagChain`, `tagLeaf`, `tagNode` and every oracle input with `tagRO`, so no oracle input is
one of those preimages, whatever the lengths. -/
theorem tags_separate (q : ByteArray) (d h c₁ c₂ : Digest) (n : ℕ) :
    [tagChain, tagLeaf, tagNode, tagRO].Nodup ∧
    chainStep d = blake2sDigest (tagChain :: d.toList) ∧
    leafStmt h n = blake2sDigest (tagLeaf :: (h.toList ++ enc64 n)) ∧
    nodeStmt c₁ c₂ = blake2sDigest (tagNode :: (c₁.toList ++ c₂.toList)) ∧
    blake2sOracle q = blake2sDigest (tagRO :: q.data.toList) ∧
    ∀ x y : List UInt8,
      tagRO :: x ≠ tagChain :: y ∧ tagRO :: x ≠ tagLeaf :: y ∧ tagRO :: x ≠ tagNode :: y :=
  ⟨by decide, rfl, rfl, rfl, rfl, fun _ _ => ⟨by simp [tagRO, tagChain], by simp [tagRO, tagLeaf],
    by simp [tagRO, tagNode]⟩⟩

/-! ## Leaves -/

/-- A chain of exactly `chainCap` steps is in the relation (no chain is hashed: the statement is
the leaf statement of its own end). -/
theorem leaf_at_chainCap (Vb : Digest → Proof → Bool) (s : Digest) :
    Rel Vb (leafStmt (chainEnd s chainCap) chainCap) (.leaf s chainCap) := ⟨le_rfl, rfl⟩

/-- **Over the chain bound**: a chain of `chainCap + 1` steps is not in the relation. -/
theorem leaf_over_chainCap (Vb : Digest → Proof → Bool) (s : Digest) :
    ¬ Rel Vb (leafStmt (chainEnd s (chainCap + 1)) (chainCap + 1)) (.leaf s (chainCap + 1)) :=
  fun h => absurd h.1 (by omega)

/-- The statement of the chain's start is not the statement of its end (`s0`, `n = 1`). -/
theorem start_ne_end : leafStmt s0 1 ≠ leafStmt (chainEnd s0 1) 1 := by decide +kernel

/-- **Wrong chain end** (an instance: `s0`, `n = 1`): the leaf statement committing to the start,
not the end, is not witnessed by the start, under every verifier. -/
theorem wrong_end (Vb : Digest → Proof → Bool) : ¬ Rel Vb (leafStmt s0 1) (.leaf s0 1) :=
  fun h => start_ne_end h.2

/-! ## Nodes -/

/-- The correct leaf digest of the chain of one step from `s0`, and the wrong one (the start's). -/
abbrev cOk : Digest := leafStmt (chainEnd s0 1) 1
abbrev cBad : Digest := leafStmt s0 1

/-- The witness-sending proof of the leaf `(s0, 1)`. -/
abbrev π₁ : Proof := encode (.leaf s0 1)

theorem Vb_ok : submission.Vb cOk π₁ = true := by
  rw [Vb_eq, check_leaf _ _ (by decide), size_encode_leaf]; simp [proofCap, chainCap]

theorem Vb_bad : submission.Vb cBad π₁ = false := by
  rw [Vb_eq, check_leaf _ _ (by decide)]
  simp [show cBad ≠ leafStmt (chainEnd s0 1) 1 from start_ne_end]

/-- **A node with two leaf children** is in the relation of the witness-sending verifier, which
recomputes both chains. -/
theorem node_of_two_leaves (s₁ s₂ : Digest) {n₁ n₂ : ℕ} (h₁ : n₁ ≤ chainCap)
    (h₂ : n₂ ≤ chainCap) :
    Rel submission.Vb (nodeStmt (leafStmt (chainEnd s₁ n₁) n₁) (leafStmt (chainEnd s₂ n₂) n₂))
      (.node (leafStmt (chainEnd s₁ n₁) n₁) (leafStmt (chainEnd s₂ n₂) n₂)
        (encode (.leaf s₁ n₁)) (encode (.leaf s₂ n₂))) := by
  have h₁' : n₁ < 2 ^ 64 := h₁.trans_lt (by decide)
  have h₂' : n₂ < 2 ^ 64 := h₂.trans_lt (by decide)
  refine ⟨rfl, ?_, ?_⟩ <;> rw [Vb_eq, check_leaf _ _ ‹_›, size_encode_leaf] <;>
    simp [proofCap, h₁, h₂]

/-- **The node clause needs its statement**: whatever the children, a statement other than their
`nodeStmt` is not in the relation. -/
theorem node_needs_statement (Vb : Digest → Proof → Bool) {c c₁ c₂ : Digest} (π₁ π₂ : Proof)
    (h : c ≠ nodeStmt c₁ c₂) : ¬ Rel Vb c (.node c₁ c₂ π₁ π₂) := fun hR => h hR.1

/-- **Statement mismatch** (an instance): two accepted children under their own leaf statement,
which is not their `nodeStmt`. -/
theorem node_statement_mismatch : ¬ Rel submission.Vb cOk (.node cOk cOk π₁ π₁) :=
  node_needs_statement _ _ _ (by decide +kernel)

/-- **A node whose first child is rejected** (an instance): the second child is correct. -/
theorem first_child_rejected :
    ¬ Rel submission.Vb (nodeStmt cBad cOk) (.node cBad cOk π₁ π₁) := fun h =>
  absurd h.2.1 (by rw [Vb_bad]; decide)

/-- **A node whose second child is rejected** (an instance): the first child is correct. -/
theorem second_child_rejected :
    ¬ Rel submission.Vb (nodeStmt cOk cBad) (.node cOk cBad π₁ π₁) := fun h =>
  absurd h.2.2 (by rw [Vb_bad]; decide)

/-- **Over the cap**: every submission's instantiated verifier rejects a proof longer than
`proofCap`. -/
theorem Vb_over_cap (S : Submission) (c : Digest) {π : Proof} (h : proofCap < π.size) :
    S.Vb c π = false := ite_eq_right (by omega)

/-- A tree of `k` levels over one leaf: the digest. -/
def deepStmt : ℕ → Digest
  | 0 => leafStmt (chainEnd s0 0) 0
  | k + 1 => nodeStmt (deepStmt k) (deepStmt k)

/-- A tree of `k` levels over one leaf: the witness-sending proof. -/
def deepProof : ℕ → Proof
  | 0 => encode (.leaf s0 0)
  | k + 1 => encode (.node (deepStmt k) (deepStmt k) (deepProof k) (deepProof k))

theorem deepProof_size (k : ℕ) : (deepProof k).size + 88 = 136 * 2 ^ k := by
  induction k with
  | zero => rw [deepProof, size_encode_leaf]; rfl
  | succ k ih =>
    obtain ⟨m, hm⟩ : 8 ∣ (deepProof k).size := by
      cases k <;> simp only [deepProof, size_encode] <;> exact Dvd.intro _ rfl
    rw [deepProof, size_encode]
    simp only [witWords, bytesWords, List.length_cons, List.length_append, packBytes_length,
      Vector.length_toList, ← size_eq_length, pow_succ]
    omega

/-- One more level: a node over two copies of an accepted proof within the cap is accepted. -/
private theorem deepProof_check_succ {k : ℕ} (h : check (deepStmt k) (deepProof k) = true)
    (hcap : (deepProof k).size ≤ proofCap) :
    check (deepStmt (k + 1)) (deepProof (k + 1)) = true := by
  have hV : submission.Vb (deepStmt k) (deepProof k) = true := by rw [Vb_eq, h]; simpa using hcap
  rw [deepProof, deepStmt]
  exact check_encode ⟨rfl, hV, hV⟩ ⟨hcap, hcap⟩

theorem deepProof_check (k : ℕ) (hk : k ≤ 12) : check (deepStmt k) (deepProof k) = true := by
  induction k with
  | zero => rw [deepProof, deepStmt, check_leaf _ _ (by decide)]; simp [chainCap]
  | succ k ih =>
    have hs := deepProof_size k
    have : 2 ^ k ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact deepProof_check_succ (ih (by omega)) (by unfold proofCap; omega)

/-- **The cap is what rejects**: the witness-sending verifier accepts the 13-level proof (its
children, 556,968 bytes each, are within the cap), which has 1,114,024 bytes, and the
instantiated verifier rejects it. -/
theorem deep_accepted_but_capped :
    check (deepStmt 13) (deepProof 13) = true ∧ (deepProof 13).size = 1114024 ∧
      submission.Vb (deepStmt 13) (deepProof 13) = false := by
  have hs := deepProof_size 13
  have hs12 := deepProof_size 12
  exact ⟨deepProof_check_succ (deepProof_check 12 le_rfl) (by unfold proofCap; omega), by omega,
    Vb_over_cap _ _ (by unfold proofCap; omega)⟩

end RecursionFast.Controls.Relation
