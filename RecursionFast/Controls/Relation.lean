/-
# Controls: the relation (`Contract/Relation.lean`) and acceptance (`Submission.acc`)    (V4)

Known answers are decided by the kernel (`decide +kernel`, about 2.5 s per BLAKE2s compression);
each expected digest is the output of the `python3 -I` command in its docstring (`hashlib`,
CPython 3, `blake2s`, `digest_size=32`). The start of every chain is `s0 = 00 01 … 1f`. Signed
children are built with the Lean reference signer (`Library/Signer.lean`) for **every** secret
function `sk`, and their signatures are proved valid symbolically (`sigOk_sign`, no hash
evaluated; V4-A7 (b), C-m12).

Positive:
* `chain1_kat`, `chain2_kat`, `chain16_kat`, `leafStmt_kat`, `nodeStmt_kat`: v3's byte layouts.
* `acc_leafSigned`: the witness-sending signed proof of a leaf (empty trace, a reference
  signature of its digest) is accepted under the signer's key.
* **`node_of_two_leaves`** (the node clause): under the witness-sending `acc` and the key
  `pk sk`, a node digest of two leaf digests is in the relation with the two signed leaf proofs
  as its witness, for every secret function, two starts and lengths up to `chainCap`;
  `node_of_two_leaves_ref` with the reference derivation of V4-A4.
* `leaf_at_chainCap`: a chain of exactly `chainCap` steps is in the relation.
* `tags_separate`: the seven tags are distinct bytes, and each hash input of the contract starts
  with its own tag.

Negative:
* `wrong_end`, `leaf_over_chainCap` (every `acc`), as in v3.
* `node_needs_statement` (every `acc`), `node_statement_mismatch` (an instance).
* `first_child_rejected`, `second_child_rejected`: a validly signed child whose proof is for the
  wrong statement.
* **`child_other_key`**: a child signed under `pk sk` is rejected under every other key.
* **`child_trace_nonempty`**: a witness-sending child carrying a trace, even a validly signed
  one, is rejected (exact consumption, V4-A3).
* **`acc_changed_answer`**: if `acc` accepts one proof on two different traces with one
  signature, the signature verifies on two different digests, or the two traces' encodings
  collide: a changed answer is never free.
* `acc_query_at_cap` (positive): a signed one-entry trace whose query has exactly `queryCap`
  bytes is accepted under a verifier that asks it (exact consumption, cap, signature).
* `acc_over_cap`, `acc_query_over_cap`: every submission's `acc` rejects a proof above
  `proofCap` and a trace with a query above `queryCap`; `deep_accepted_but_capped`: the
  witness-sending verifier accepts a 7-level proof of 1,232,456 bytes (its children, 611,400
  bytes each, within the cap) that `acc` then rejects, so the cap is what rejects it.
-/
import RecursionFast.Library.WitnessSending
import RecursionFast.Library.Signer
import RecursionFast.Controls.Hex
import RecursionFast.Controls.Signature

namespace RecursionFast.Controls.Relation
open RecursionFast RecursionFast.WitnessSending
open RecursionFast.Controls.Blake2s (hex)

/-- The digest written by a hex string. -/
def ofHex (s : String) : Digest := Vector.ofFn fun i => (hex s).getD i 0

/-- The chain start `00 01 … 1f`. -/
def s0 : Digest := Vector.ofFn fun i => i.val.toUInt8

/-! ## Known answers (v3) -/

/-- `python3 -I -c "import hashlib; print(hashlib.blake2s(b'C'+bytes(range(32))).hexdigest())"` -/
theorem chain1_kat : (chainEnd s0 1).toList =
    hex "7b3746567b4e4fabc189813de4005675433183b47660560825d4741774350544" := by
  rw [← chainEndF_eq]
  decide +kernel

/-- `python3 -I -c "import hashlib; H=lambda b: hashlib.blake2s(b'C'+b).digest();
print(H(H(bytes(range(32)))).hex())"` -/
theorem chain2_kat : (chainEnd s0 2).toList =
    hex "84de040b23986f9880cc37aec1852359e17c164ac488dc81edf784cee0ae1945" := by
  rw [← chainEndF_eq]
  decide +kernel

/-- `python3 -I -c "import hashlib; d=bytes(range(32))
for _ in range(16): d=hashlib.blake2s(b'C'+d).digest()
print(d.hex())"` -/
theorem chain16_kat : (chainEnd s0 16).toList =
    hex "a71f6bd7ac08ab5936654a7904bd8feb7636e1f0eb556ae2619ba7c1be41e58d" := by
  rw [← chainEndF_eq]
  decide +kernel

/-- `python3 -I -c "import hashlib;
h=bytes.fromhex('a71f6bd7ac08ab5936654a7904bd8feb7636e1f0eb556ae2619ba7c1be41e58d');
print(hashlib.blake2s(b'L'+h+(16).to_bytes(8,'little')).hexdigest())"` -/
theorem leafStmt_kat :
    (leafStmt (ofHex "a71f6bd7ac08ab5936654a7904bd8feb7636e1f0eb556ae2619ba7c1be41e58d")
      16).toList =
      hex "c81156bc71500494780f6635d8533cb9e7b738f5c408ebadb58ceef477cd2b4b" := by
  rw [← leafStmtF_eq]
  decide +kernel

/-- `python3 -I -c "import hashlib;
a=bytes.fromhex('7b3746567b4e4fabc189813de4005675433183b47660560825d4741774350544');
b=bytes.fromhex('84de040b23986f9880cc37aec1852359e17c164ac488dc81edf784cee0ae1945');
print(hashlib.blake2s(b'N'+a+b).hexdigest())"` (the digests of `chain1_kat`, `chain2_kat`) -/
theorem nodeStmt_kat :
    (nodeStmt (ofHex "7b3746567b4e4fabc189813de4005675433183b47660560825d4741774350544")
      (ofHex "84de040b23986f9880cc37aec1852359e17c164ac488dc81edf784cee0ae1945")).toList =
      hex "23b28cbc4bf7d65abbf43ff39084438ba0fb080bdef09b9e4830b10deada1bab" := by
  rw [← nodeStmtF_eq]
  decide +kernel

/-! ## Tags -/

/-- **Tags separate**: the seven tags are distinct bytes, and each hash input of the contract
starts with its own tag (the chain step, the leaf and node statements, the trace digest, the
WOTS chain step and leaf, the signature's Merkle node). -/
theorem tags_separate (d h c₁ c₂ x : Digest) (n j i s : ℕ) (tr : Trace) (ends : List Digest) :
    [tagChain, tagLeaf, tagNode, tagTrace, tagWots, tagWotsLeaf, tagSigNode].Nodup ∧
    chainStep d = blake2sDigest (tagChain :: d.toList) ∧
    leafStmt h n = blake2sDigest (tagLeaf :: (h.toList ++ enc64 n)) ∧
    nodeStmt c₁ c₂ = blake2sDigest (tagNode :: (c₁.toList ++ c₂.toList)) ∧
    traceDigest tr = blake2sDigest (tagTrace :: traceBytes tr) ∧
    wotsStep j i s x = blake2sDigest (tagWots :: (enc64 j ++ [i.toUInt8, s.toUInt8] ++ x.toList)) ∧
    wotsLeaf j ends = blake2sDigest (tagWotsLeaf :: (enc64 j ++ ends.flatMap Vector.toList)) ∧
    sigNode c₁ c₂ = blake2sDigest (tagSigNode :: (c₁.toList ++ c₂.toList)) :=
  ⟨by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Leaves -/

/-- A chain of exactly `chainCap` steps is in the relation. -/
theorem leaf_at_chainCap (acc : Digest → Signed → Bool) (s : Digest) :
    Rel acc (leafStmt (chainEnd s chainCap) chainCap) (.leaf s chainCap) := ⟨le_rfl, rfl⟩

/-- **Over the chain bound**: a chain of `chainCap + 1` steps is not in the relation. -/
theorem leaf_over_chainCap (acc : Digest → Signed → Bool) (s : Digest) :
    ¬ Rel acc (leafStmt (chainEnd s (chainCap + 1)) (chainCap + 1)) (.leaf s (chainCap + 1)) :=
  fun h => absurd h.1 (by omega)

/-- The statement of the chain's start is not the statement of its end (`s0`, `n = 1`). -/
theorem start_ne_end : leafStmt s0 1 ≠ leafStmt (chainEnd s0 1) 1 := by
  rw [← leafStmtF_eq, ← chainEndF_eq]
  decide +kernel

/-- **Wrong chain end**: the leaf statement committing to the start is not witnessed by the
start, under every `acc`. -/
theorem wrong_end (acc : Digest → Signed → Bool) : ¬ Rel acc (leafStmt s0 1) (.leaf s0 1) :=
  fun h => start_ne_end h.2

/-! ## Signed leaf proofs -/

/-- The witness-sending signed proof of the leaf `(s, n)`: the proof, the empty trace, and the
reference signature with key `j` of the empty trace's digest. -/
def leafSigned (sk : ℕ → ℕ → Digest) (j : ℕ) (s : Digest) (n : ℕ) : Signed :=
  ⟨encode (.leaf s n), [], Signer.sign sk j (traceDigest [])⟩

theorem leafSigned_sig (sk : ℕ → ℕ → Digest) {j : ℕ} (hj : j < 2 ^ sigHeight) (s : Digest)
    (n : ℕ) : SigOk (Signer.pk sk) (traceDigest (leafSigned sk j s n).tr)
      (leafSigned sk j s n).σ = true := Signer.sigOk_sign sk j hj _

/-- `acc` of a signed leaf proof: the leaf proof is accepted for the statement. -/
theorem acc_leafSigned_iff (sk : ℕ → ℕ → Digest) {j : ℕ} (hj : j < 2 ^ sigHeight) (c s : Digest)
    {n : ℕ} (hn : n < 2 ^ 64) :
    submission.acc (Signer.pk sk) c (leafSigned sk j s n) =
      (decide (n ≤ chainCap) && decide (c = leafStmt (chainEnd s n) n)) := by
  rw [acc_eq, leafSigned_sig sk hj, ← check_leaf' c s hn]
  simp [leafSigned, size_encode_leaf, proofCap]
where
  check_leaf' (c s : Digest) {n : ℕ} (hn : n < 2 ^ 64) :
      check (Signer.pk sk) c (encode (.leaf s n)) =
        (decide (n ≤ chainCap) && decide (c = leafStmt (chainEnd s n) n)) := by
    rw [check_eq, decode_encode (.leaf s n) hn]; simp

/-- **A signed leaf proof is accepted** under the signer's key. -/
theorem acc_leafSigned (sk : ℕ → ℕ → Digest) {j : ℕ} (hj : j < 2 ^ sigHeight) (s : Digest)
    {n : ℕ} (hn : n ≤ chainCap) :
    submission.acc (Signer.pk sk) (leafStmt (chainEnd s n) n) (leafSigned sk j s n) = true := by
  rw [acc_leafSigned_iff sk hj _ s (hn.trans_lt (by decide))]; simp [hn]

/-! ## Nodes -/

/-- **A node with two signed leaf children** is in the relation under the signer's key, for
every secret function, starts and lengths up to `chainCap` (V4-A7 (b)). -/
theorem node_of_two_leaves (sk : ℕ → ℕ → Digest) (s₁ s₂ : Digest) {n₁ n₂ : ℕ}
    (h₁ : n₁ ≤ chainCap) (h₂ : n₂ ≤ chainCap) :
    Rel (submission.acc (Signer.pk sk))
      (nodeStmt (leafStmt (chainEnd s₁ n₁) n₁) (leafStmt (chainEnd s₂ n₂) n₂))
      (.node (leafStmt (chainEnd s₁ n₁) n₁) (leafStmt (chainEnd s₂ n₂) n₂)
        (leafSigned sk 0 s₁ n₁) (leafSigned sk 1 s₂ n₂)) :=
  ⟨rfl, acc_leafSigned sk (by decide) s₁ h₁, acc_leafSigned sk (by decide) s₂ h₂⟩

/-- The node control with the reference derivation of V4-A4, for every seed. -/
theorem node_of_two_leaves_ref (seed : List UInt8) (s₁ s₂ : Digest) {n₁ n₂ : ℕ}
    (h₁ : n₁ ≤ chainCap) (h₂ : n₂ ≤ chainCap) :
    Rel (submission.acc (Signer.pk (Signer.chainStart seed)))
      (nodeStmt (leafStmt (chainEnd s₁ n₁) n₁) (leafStmt (chainEnd s₂ n₂) n₂))
      (.node (leafStmt (chainEnd s₁ n₁) n₁) (leafStmt (chainEnd s₂ n₂) n₂)
        (leafSigned (Signer.chainStart seed) 0 s₁ n₁)
        (leafSigned (Signer.chainStart seed) 1 s₂ n₂)) :=
  node_of_two_leaves _ s₁ s₂ h₁ h₂

/-- **The node clause needs its statement**: whatever the children, a statement other than their
`nodeStmt` is not in the relation. -/
theorem node_needs_statement (acc : Digest → Signed → Bool) {c c₁ c₂ : Digest} (p₁ p₂ : Signed)
    (h : c ≠ nodeStmt c₁ c₂) : ¬ Rel acc c (.node c₁ c₂ p₁ p₂) := fun hR => h hR.1

/-- The correct leaf digest of the chain of one step from `s0`, and the wrong one. -/
abbrev cOk : Digest := leafStmt (chainEnd s0 1) 1
abbrev cBad : Digest := leafStmt s0 1

/-- **Statement mismatch** (an instance): two accepted children under their own leaf statement,
which is not their `nodeStmt`, under every `acc`. -/
theorem node_statement_mismatch (acc : Digest → Signed → Bool) (p₁ p₂ : Signed) :
    ¬ Rel acc cOk (.node cOk cOk p₁ p₂) := by
  refine node_needs_statement _ _ _ ?_
  rw [cOk, ← leafStmtF_eq, ← chainEndF_eq, ← nodeStmtF_eq]
  decide +kernel

theorem acc_bad (sk : ℕ → ℕ → Digest) {j : ℕ} (hj : j < 2 ^ sigHeight) :
    submission.acc (Signer.pk sk) cBad (leafSigned sk j s0 1) = false := by
  rw [acc_leafSigned_iff sk hj _ s0 (by decide)]
  simp [show cBad ≠ leafStmt (chainEnd s0 1) 1 from start_ne_end]

/-- **A node whose first child is rejected**: validly signed, but its proof is for another
statement. -/
theorem first_child_rejected (sk : ℕ → ℕ → Digest) :
    ¬ Rel (submission.acc (Signer.pk sk)) (nodeStmt cBad cOk)
      (.node cBad cOk (leafSigned sk 0 s0 1) (leafSigned sk 1 s0 1)) := fun h =>
  absurd h.2.1 (by rw [acc_bad sk (by decide)]; decide)

/-- **A node whose second child is rejected.** -/
theorem second_child_rejected (sk : ℕ → ℕ → Digest) :
    ¬ Rel (submission.acc (Signer.pk sk)) (nodeStmt cOk cBad)
      (.node cOk cBad (leafSigned sk 0 s0 1) (leafSigned sk 1 s0 1)) := fun h =>
  absurd h.2.2 (by rw [acc_bad sk (by decide)]; decide)

/-- **A child signed under another key is rejected**, under every key other than the signer's. -/
theorem child_other_key (sk : ℕ → ℕ → Digest) {vk : Digest} (hvk : vk ≠ Signer.pk sk)
    (c₁ c₂ s : Digest) (n : ℕ) (p₂ : Signed) :
    ¬ Rel (submission.acc vk) (nodeStmt c₁ c₂) (.node c₁ c₂ (leafSigned sk 0 s n) p₂) := fun h => by
  have hs := Controls.Signature.sigOk_other_key (leafSigned_sig sk (j := 0) (by decide) s n) hvk
  simpa [acc_eq, hs] using h.2.1

/-- **A child carrying a trace is rejected** by the witness-sending `acc` (it asks no query, and
the trace must be used up exactly, V4-A3), even with a valid signature on that trace. -/
theorem child_trace_nonempty (vk c₁ c₂ : Digest) (π : Proof) (e : ByteArray × Digest)
    (tr : Trace) (σ : Sig) (p₂ : Signed) :
    ¬ Rel (submission.acc vk) (nodeStmt c₁ c₂) (.node c₁ c₂ ⟨π, e :: tr, σ⟩ p₂) := fun h => by
  simpa [acc_eq] using h.2.1

/-- **A changed answer is never free**: if `acc` accepts one proof with one signature on two
different traces, the signature verifies on both digests, and they differ unless the traces'
encodings collide. -/
theorem acc_changed_answer (S : Submission) (vk c : Digest) (π : Proof) (σ : Sig)
    {tr tr' : Trace} (h : S.acc vk c ⟨π, tr, σ⟩ = true) (h' : S.acc vk c ⟨π, tr', σ⟩ = true)
    (hne : tr ≠ tr') : SigOk vk (traceDigest tr) σ = true ∧ SigOk vk (traceDigest tr') σ = true ∧
      (traceDigest tr ≠ traceDigest tr' ∨ Nonempty Collision) := by
  simp only [Submission.acc, Bool.and_eq_true, decide_eq_true_eq] at h h'
  refine ⟨h.1.2, h'.1.2, ?_⟩
  by_cases hd : traceDigest tr = traceDigest tr'
  · rcases traceDigest_eq (fun e he => (h.1.1.2 e he).trans_lt (by decide))
      (fun e he => (h'.1.1.2 e he).trans_lt (by decide)) hd with ht | ⟨c, -⟩
    · exact absurd ht hne
    · exact Or.inr ⟨c⟩
  · exact Or.inl hd

/-! ## The caps -/

/-- **Over the proof cap**: every submission's `acc` rejects a proof longer than `proofCap`. -/
theorem acc_over_cap (S : Submission) (vk c : Digest) (p : Signed) (h : proofCap < p.π.size) :
    S.acc vk c p = false := by
  simp [Submission.acc, show ¬ p.π.size ≤ proofCap by omega]

/-- **Over the query cap**: every submission's `acc` rejects a trace with a query longer than
`queryCap`. -/
theorem acc_query_over_cap (S : Submission) (vk c : Digest) (p : Signed) {e : ByteArray × Digest}
    (he : e ∈ p.tr) (h : queryCap < e.1.size) : S.acc vk c p = false := by
  have : ¬ ∀ e ∈ p.tr, e.1.size ≤ queryCap := fun hall => absurd (hall e he) (by omega)
  unfold Submission.acc
  rw [decide_eq_false this]
  simp

/-- The verifier that asks the one query `q` and accepts (the witness-sending submission
otherwise). -/
def oneQuery (q : ByteArray) : Submission :=
  { submission with V := fun _ _ _ => .query q fun _ => .ret true }

/-- The longest query `acc` admits: `queryCap` zero bytes. -/
def qMax : ByteArray := ⟨Array.replicate queryCap 0⟩

/-- **A signed trace with a query of exactly `queryCap` bytes is accepted** (the cap is `≤`)
under a verifier that asks that query: exact consumption, the query cap and the reference
signature on the trace's digest all pass, for every secret function, answer and proof within
`proofCap`. -/
theorem acc_query_at_cap (sk : ℕ → ℕ → Digest) (a c : Digest) {π : Proof}
    (hπ : π.size ≤ proofCap) :
    (oneQuery qMax).acc (Signer.pk sk) c
      ⟨π, [(qMax, a)], Signer.sign sk 0 (traceDigest [(qMax, a)])⟩ = true := by
  have hq : qMax.size = queryCap := by simp [qMax, ByteArray.size]
  simp [Submission.acc, oneQuery, hπ, hq, Signer.sigOk_sign sk 0 (by decide), OProg.runSeq]

/-- A tree of `k` levels over one leaf: the digest. -/
def deepStmt : ℕ → Digest
  | 0 => leafStmt (chainEnd s0 0) 0
  | k + 1 => nodeStmt (deepStmt k) (deepStmt k)

/-- A tree of `k` levels over one leaf: the witness-sending proof, children signed with key `0`
of `sk`. -/
def deepProof (sk : ℕ → ℕ → Digest) : ℕ → Proof
  | 0 => encode (.leaf s0 0)
  | k + 1 => encode (.node (deepStmt k) (deepStmt k)
      ⟨deepProof sk k, [], Signer.sign sk 0 (traceDigest [])⟩
      ⟨deepProof sk k, [], Signer.sign sk 0 (traceDigest [])⟩)

theorem sigWords_sign_length (sk : ℕ → ℕ → Digest) (m : Digest) :
    (sigWords (Signer.sign sk 0 m)).length = 597 := by
  simp [sigWords, Signer.sign, List.length_flatMap, packBytes_digest_length,
    Signer.wotsDigits_length, Signer.authPath, Signer.sibs_length, wotsLen, sigHeight]

theorem deepProof_size (sk : ℕ → ℕ → Digest) (k : ℕ) :
    (deepProof sk k).size + 9656 = 9704 * 2 ^ k := by
  induction k with
  | zero => rw [deepProof, size_encode_leaf]; rfl
  | succ k ih =>
    obtain ⟨m, hm⟩ : 8 ∣ (deepProof sk k).size := by
      cases k <;> simp only [deepProof, size_encode] <;> exact Dvd.intro _ rfl
    rw [deepProof, size_encode]
    simp only [witWords, signedWords, bytesWords, logWords, List.length_cons, List.length_append,
      packBytes_length, Vector.length_toList, List.length_nil, List.flatMap_nil,
      sigWords_sign_length, ← size_eq_length, pow_succ]
    omega

/-- One more level: a node over two signed copies of an accepted proof within the cap is
accepted. -/
private theorem deepProof_check_succ (sk : ℕ → ℕ → Digest) {k : ℕ}
    (h : check (Signer.pk sk) (deepStmt k) (deepProof sk k) = true)
    (hcap : (deepProof sk k).size ≤ proofCap) :
    check (Signer.pk sk) (deepStmt (k + 1)) (deepProof sk (k + 1)) = true := by
  have hacc : submission.acc (Signer.pk sk) (deepStmt k)
      ⟨deepProof sk k, [], Signer.sign sk 0 (traceDigest [])⟩ = true := by
    rw [acc_eq, Signer.sigOk_sign sk 0 (by decide)]; simp [h, hcap]
  rw [deepProof, deepStmt]
  exact check_encode ⟨rfl, hacc, hacc⟩

theorem deepProof_check (sk : ℕ → ℕ → Digest) (k : ℕ) (hk : k ≤ 6) :
    check (Signer.pk sk) (deepStmt k) (deepProof sk k) = true := by
  induction k with
  | zero =>
    rw [deepProof, deepStmt]
    exact check_encode (show Rel _ _ (.leaf s0 0) from ⟨Nat.zero_le _, rfl⟩)
  | succ k ih =>
    have hs := deepProof_size sk k
    have : 2 ^ k ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact deepProof_check_succ sk (ih (by omega)) (by unfold proofCap; omega)

/-- **The cap is what rejects**: the witness-sending verifier accepts the 7-level proof (its
children, 611,400 bytes each, are within the cap), which has 1,232,456 bytes, and `acc` rejects
it, signature and all. -/
theorem deep_accepted_but_capped (sk : ℕ → ℕ → Digest) :
    check (Signer.pk sk) (deepStmt 7) (deepProof sk 7) = true ∧
      (deepProof sk 7).size = 1232456 ∧
      submission.acc (Signer.pk sk) (deepStmt 7)
        ⟨deepProof sk 7, [], Signer.sign sk 0 (traceDigest [])⟩ = false := by
  have hs := deepProof_size sk 7
  have hs6 := deepProof_size sk 6
  exact ⟨deepProof_check_succ sk (deepProof_check sk 6 le_rfl) (by unfold proofCap; omega),
    by omega, acc_over_cap _ _ _ _ (by unfold proofCap; simp only; omega)⟩

end RecursionFast.Controls.Relation
