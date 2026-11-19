/-
# Controls: the relation (`Contract/Relation.lean`) and acceptance (`Submission.acc`)

Known answers are decided by the kernel (`decide +kernel` on the word-level twins of
`Library/Fast.lean`, proved equal to the contract's hashes); each expected digest is the output of
the `python3 -I` command in its docstring, run from the repository root (`harness/rfh/keccak.py`,
the runner's Keccak-256, itself checked against OpenSSL's `keccak-256`). The seed of every leaf
is `s0 = 00 01 … 1f`. Signed children are built with the Lean reference signer
(`Library/Signer.lean`) for **every** secret function `sk`, and their signatures are proved valid
symbolically (`sigOk_sign`, no hash evaluated).

Positive:
* `item0_kat`, `item1_kat`, `value2_kat` (the XOR of the first two), `value16_kat`, `leafStmt_kat`,
  `nodeStmt_kat`: the byte layouts.
* `acc_leafSigned`: the witness-sending signed proof of a leaf (empty trace, a reference
  signature of its digest) is accepted under the signer's key.
* **`node_of_two_leaves`** (the node clause): under the witness-sending `acc` and the key
  `pk sk`, a node digest of two leaf digests is in the relation with the two signed leaf proofs
  as its witness, for every secret function, two seeds and sizes up to `leafCap`;
  `node_of_two_leaves_ref` with the reference derivation of the WOTS chain starts.
* `leaf_at_leafCap`: a leaf of exactly `leafCap` hashes is in the relation.
* `tags_separate`: the seven tags are distinct bytes, and each hash input of the contract starts
  with its own tag.

Negative:
* `wrong_value` (the seed in place of the value), `wrong_seed` (another seed),
  `wrong_count` (one hash dropped), `extra_item` (one hash added), `leaf_over_leafCap` (every
  `acc`).
* `node_needs_statement` (every `acc`), `node_statement_mismatch` (an instance).
* `first_child_rejected`, `second_child_rejected`: a validly signed child whose proof is for the
  wrong statement.
* **`child_other_key`**: a child signed under `pk sk` is rejected under every other key.
* **`child_trace_nonempty`**: a witness-sending child carrying a trace, even a validly signed
  one, is rejected (exact consumption).
* **`acc_changed_answer`**: if `acc` accepts one proof on two different traces with one
  signature, the signature verifies on two different digests, or the two traces' tagged
  encodings are an explicit collision: a changed answer is never free.
* `acc_query_at_cap` (positive): a signed one-entry trace whose query has exactly `queryCap`
  bytes is accepted under a verifier that asks it and declares `qV = 1` (exact consumption,
  trace length at `qV`, query cap, signature).
* `acc_trace_over_qV`, `acc_two_entries_rejected`: every submission's `acc` rejects a
  trace longer than its `qV`; the instance at `qV + 1 = 2` entries.
* `acc_over_word`, `acc_query_over_cap`: every submission's `acc` rejects a proof of `2^64`
  bytes or more (its length does not fit a word) and a trace with a query above
  `queryCap`; `deep_accepted_but_unwritable`: the witness-sending verifier accepts a 51-level
  proof of `9704 · 2^51 − 9656` bytes (its children within the word) that `acc` then rejects, so
  the word bound is what rejects it.

What bounds a proof (positive):
* `deep_accepted`: no cap below the word: `acc` accepts the witness-sending proof of a tree of
  `k` levels, `9704 · 2^k − 9656` bytes, for every `k ≤ 50`; `deep7_over_old_cap`: the 7-level
  one, 1,232,456 bytes, above `2^20` bytes. What bounds a recursive entry's proofs
  is its own verifier; what bounds a deployed file is the runner's 64 MiB cap
  (`harness/season.toml`).
-/
import RecursionFast.Library.WitnessSending
import RecursionFast.Library.Signer
import RecursionFast.Controls.Hex
import RecursionFast.Controls.Signature

namespace RecursionFast.Controls.Relation
open RecursionFast RecursionFast.WitnessSending
open RecursionFast.Controls.Keccak (hex)

/-- The digest written by a hex string. -/
def ofHex (s : String) : Digest := Vector.ofFn fun i => (hex s).getD i 0

/-- The seed `00 01 … 1f`. -/
def s0 : Digest := Vector.ofFn fun i => i.val.toUInt8

/-- Another seed, `01 02 … 20`. -/
def s1 : Digest := Vector.ofFn fun i => (i.val + 1).toUInt8

/-! ## Known answers -/

/-- `python3 -I -c "import sys; sys.path.insert(0, 'harness'); from rfh.keccak import keccak256 as K;
print(K(b'H'+bytes(range(32))+(0).to_bytes(8,'little')).hex())"` -/
theorem item0_kat : (leafItem s0 0).toList =
    hex "da513675c495534390e0dfb57a4b2d94b8ec604af01e1cacb5bfa117e4178b11" := by
  rw [← leafItemF_eq]
  decide +kernel

/-- `python3 -I -c "import sys; sys.path.insert(0, 'harness'); from rfh.keccak import keccak256 as K;
print(K(b'H'+bytes(range(32))+(1).to_bytes(8,'little')).hex())"` -/
theorem item1_kat : (leafItem s0 1).toList =
    hex "422927c492ce04e6a6ee85dac40f023ffabf0384da8d3a63e491fbf923fc2b9f" := by
  rw [← leafItemF_eq]
  decide +kernel

/-- The XOR of `item0_kat` and `item1_kat`: `python3 -I -c "import sys; sys.path.insert(0,
'harness'); from rfh.keccak import keccak256 as K; I=lambda j: K(b'H'+bytes(range(32))+j.to_bytes(8,
'little')); print(bytes(a^b for a,b in zip(I(0),I(1))).hex())"` -/
theorem value2_kat : (leafValue s0 2).toList =
    hex "987811b1565b57a5360e5a6fbe442fab425363ce2a9326cf512e5aeec7eba08e" := by
  rw [← leafValueF_eq]
  decide +kernel

/-- `python3 -I -c "import sys; sys.path.insert(0, 'harness'); from rfh.keccak import keccak256 as K; v=bytes(32)
for j in range(16): v=bytes(a^b for a,b in zip(v,K(b'H'+bytes(range(32))+j.to_bytes(8,'little'))))
print(v.hex())"` -/
theorem value16_kat : (leafValue s0 16).toList =
    hex "d6d13655281cf163636b2dd8aa4a0666566ddc04bf3b515c0462e54c98860458" := by
  rw [← leafValueF_eq]
  decide +kernel

/-- `python3 -I -c "import sys; sys.path.insert(0, 'harness'); from rfh.keccak import keccak256 as K;
h=bytes.fromhex('d6d13655281cf163636b2dd8aa4a0666566ddc04bf3b515c0462e54c98860458');
print(K(b'L'+h+(16).to_bytes(8,'little')).hex())"` (the value of `value16_kat`) -/
theorem leafStmt_kat :
    (leafStmt (ofHex "d6d13655281cf163636b2dd8aa4a0666566ddc04bf3b515c0462e54c98860458")
      16).toList =
      hex "73e4f8a699e3bde6cc6bfecd0fc2370a0e0503bd29f06554ad8a32d81caeb2f9" := by
  rw [← leafStmtF_eq]
  decide +kernel

/-- `python3 -I -c "import sys; sys.path.insert(0, 'harness'); from rfh.keccak import keccak256 as K;
a=bytes.fromhex('da513675c495534390e0dfb57a4b2d94b8ec604af01e1cacb5bfa117e4178b11');
b=bytes.fromhex('422927c492ce04e6a6ee85dac40f023ffabf0384da8d3a63e491fbf923fc2b9f');
print(K(b'N'+a+b).hex())"` (the digests of `item0_kat`, `item1_kat`) -/
theorem nodeStmt_kat :
    (nodeStmt (ofHex "da513675c495534390e0dfb57a4b2d94b8ec604af01e1cacb5bfa117e4178b11")
      (ofHex "422927c492ce04e6a6ee85dac40f023ffabf0384da8d3a63e491fbf923fc2b9f")).toList =
      hex "955f38142d22184c40620a09850718e312df8622264ea4c6c7dc4983e8f5df9b" := by
  rw [← nodeStmtF_eq]
  decide +kernel

/-! ## Tags -/

/-- **Tags separate**: the seven tags are distinct bytes, and each hash input of the contract
starts with its own tag (the leaf item, the leaf and node statements, the trace digest, the
WOTS chain step and leaf, the signature's Merkle node). -/
theorem tags_separate (d h c₁ c₂ x : Digest) (n j i s : ℕ) (tr : Trace) (ends : List Digest) :
    [tagItem, tagLeaf, tagNode, tagTrace, tagWots, tagWotsLeaf, tagSigNode].Nodup ∧
    leafItem d n = keccakDigest (tagItem :: (d.toList ++ enc64 n)) ∧
    leafStmt h n = keccakDigest (tagLeaf :: (h.toList ++ enc64 n)) ∧
    nodeStmt c₁ c₂ = keccakDigest (tagNode :: (c₁.toList ++ c₂.toList)) ∧
    traceDigest tr = keccakDigest (tagTrace :: traceBytes tr) ∧
    wotsStep j i s x = keccakDigest (tagWots :: (enc64 j ++ [i.toUInt8, s.toUInt8] ++ x.toList)) ∧
    wotsLeaf j ends = keccakDigest (tagWotsLeaf :: (enc64 j ++ ends.flatMap Vector.toList)) ∧
    sigNode c₁ c₂ = keccakDigest (tagSigNode :: (c₁.toList ++ c₂.toList)) :=
  ⟨by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Leaves -/

/-- A leaf of exactly `leafCap` hashes is in the relation. -/
theorem leaf_at_leafCap (acc : Digest → Signed → Bool) (s : Digest) :
    Rel acc (leafStmt (leafValue s leafCap) leafCap) (.leaf s leafCap) := ⟨le_rfl, rfl⟩

/-- **Over the leaf bound**: a leaf of `leafCap + 1` hashes is not in the relation. -/
theorem leaf_over_leafCap (acc : Digest → Signed → Bool) (s : Digest) :
    ¬ Rel acc (leafStmt (leafValue s (leafCap + 1)) (leafCap + 1)) (.leaf s (leafCap + 1)) :=
  fun h => absurd h.1 (by omega)

/-- The statement of the seed is not the statement of its leaf's value (`s0`, `n = 1`). -/
theorem seed_ne_value : leafStmt s0 1 ≠ leafStmt (leafValue s0 1) 1 := by
  rw [← leafStmtF_eq, ← leafValueF_eq]
  decide +kernel

/-- **Wrong value**: the leaf statement committing to the seed itself is not witnessed by the
seed, under every `acc`. -/
theorem wrong_value (acc : Digest → Signed → Bool) : ¬ Rel acc (leafStmt s0 1) (.leaf s0 1) :=
  fun h => seed_ne_value h.2

/-- **Wrong seed**: the statement of the leaf of `s0` with one hash is not witnessed by another
seed `s1` with one hash, under every `acc`. -/
theorem wrong_seed (acc : Digest → Signed → Bool) :
    ¬ Rel acc (leafStmt (leafValue s0 1) 1) (.leaf s1 1) := fun h => by
  revert h; rw [Rel, ← leafStmtF_eq, ← leafValueF_eq]
  decide +kernel

/-- **One hash dropped**: the statement of the leaf of `s0` with two hashes is not witnessed by
`s0` with one hash, under every `acc`. -/
theorem wrong_count (acc : Digest → Signed → Bool) :
    ¬ Rel acc (leafStmt (leafValue s0 2) 2) (.leaf s0 1) := fun h => by
  revert h; rw [Rel, ← leafStmtF_eq, ← leafValueF_eq]
  decide +kernel

/-- **One hash added**: the statement of the leaf of `s0` with one hash, and the value of one
hash committed with the count `2`, are not witnessed by `s0` with two hashes, under every
`acc`. -/
theorem extra_item (acc : Digest → Signed → Bool) :
    ¬ Rel acc (leafStmt (leafValue s0 1) 1) (.leaf s0 2) ∧
      ¬ Rel acc (leafStmt (leafValue s0 1) 2) (.leaf s0 2) := by
  constructor <;> rw [Rel, ← leafStmtF_eq, ← leafValueF_eq] <;> decide +kernel

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
      (decide (n ≤ leafCap) && decide (c = leafStmt (leafValue s n) n)) := by
  rw [acc_eq, leafSigned_sig sk hj, ← check_leaf' c s hn]
  simp [leafSigned, size_encode_leaf]
where
  check_leaf' (c s : Digest) {n : ℕ} (hn : n < 2 ^ 64) :
      check (Signer.pk sk) c (encode (.leaf s n)) =
        (decide (n ≤ leafCap) && decide (c = leafStmt (leafValue s n) n)) := by
    rw [check_eq, decode_encode (.leaf s n) hn]; simp

/-- **A signed leaf proof is accepted** under the signer's key. -/
theorem acc_leafSigned (sk : ℕ → ℕ → Digest) {j : ℕ} (hj : j < 2 ^ sigHeight) (s : Digest)
    {n : ℕ} (hn : n ≤ leafCap) :
    submission.acc (Signer.pk sk) (leafStmt (leafValue s n) n) (leafSigned sk j s n) = true := by
  rw [acc_leafSigned_iff sk hj _ s (hn.trans_lt (by decide))]; simp [hn]

/-! ## Nodes -/

/-- **A node with two signed leaf children** is in the relation under the signer's key, for
every secret function, seeds and sizes up to `leafCap`. -/
theorem node_of_two_leaves (sk : ℕ → ℕ → Digest) (s₁ s₂ : Digest) {n₁ n₂ : ℕ}
    (h₁ : n₁ ≤ leafCap) (h₂ : n₂ ≤ leafCap) :
    Rel (submission.acc (Signer.pk sk))
      (nodeStmt (leafStmt (leafValue s₁ n₁) n₁) (leafStmt (leafValue s₂ n₂) n₂))
      (.node (leafStmt (leafValue s₁ n₁) n₁) (leafStmt (leafValue s₂ n₂) n₂)
        (leafSigned sk 0 s₁ n₁) (leafSigned sk 1 s₂ n₂)) :=
  ⟨rfl, acc_leafSigned sk (by decide) s₁ h₁, acc_leafSigned sk (by decide) s₂ h₂⟩

/-- The node control with the reference derivation of the WOTS chain starts, for every signer
seed. -/
theorem node_of_two_leaves_ref (seed : List UInt8) (s₁ s₂ : Digest) {n₁ n₂ : ℕ}
    (h₁ : n₁ ≤ leafCap) (h₂ : n₂ ≤ leafCap) :
    Rel (submission.acc (Signer.pk (Signer.chainStart seed)))
      (nodeStmt (leafStmt (leafValue s₁ n₁) n₁) (leafStmt (leafValue s₂ n₂) n₂))
      (.node (leafStmt (leafValue s₁ n₁) n₁) (leafStmt (leafValue s₂ n₂) n₂)
        (leafSigned (Signer.chainStart seed) 0 s₁ n₁)
        (leafSigned (Signer.chainStart seed) 1 s₂ n₂)) :=
  node_of_two_leaves _ s₁ s₂ h₁ h₂

/-- **The node clause needs its statement**: whatever the children, a statement other than their
`nodeStmt` is not in the relation. -/
theorem node_needs_statement (acc : Digest → Signed → Bool) {c c₁ c₂ : Digest} (p₁ p₂ : Signed)
    (h : c ≠ nodeStmt c₁ c₂) : ¬ Rel acc c (.node c₁ c₂ p₁ p₂) := fun hR => h hR.1

/-- The correct leaf digest of one hash of `s0`, and the wrong one (committing to `s0`). -/
abbrev cOk : Digest := leafStmt (leafValue s0 1) 1
abbrev cBad : Digest := leafStmt s0 1

/-- **Statement mismatch** (an instance): two accepted children under their own leaf statement,
which is not their `nodeStmt`, under every `acc`. -/
theorem node_statement_mismatch (acc : Digest → Signed → Bool) (p₁ p₂ : Signed) :
    ¬ Rel acc cOk (.node cOk cOk p₁ p₂) := by
  refine node_needs_statement _ _ _ ?_
  rw [cOk, ← leafStmtF_eq, ← leafValueF_eq, ← nodeStmtF_eq]
  decide +kernel

theorem acc_bad (sk : ℕ → ℕ → Digest) {j : ℕ} (hj : j < 2 ^ sigHeight) :
    submission.acc (Signer.pk sk) cBad (leafSigned sk j s0 1) = false := by
  rw [acc_leafSigned_iff sk hj _ s0 (by decide)]
  simp [show cBad ≠ leafStmt (leafValue s0 1) 1 from seed_ne_value]

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
the trace must be used up exactly), even with a valid signature on that trace. -/
theorem child_trace_nonempty (vk c₁ c₂ : Digest) (π : Proof) (e : ByteArray × Digest)
    (tr : Trace) (σ : Sig) (p₂ : Signed) :
    ¬ Rel (submission.acc vk) (nodeStmt c₁ c₂) (.node c₁ c₂ ⟨π, e :: tr, σ⟩ p₂) := fun h => by
  simpa [acc_eq] using h.2.1

/-- **A changed answer is never free**: if `acc` accepts one proof with one signature on two
different traces, the signature verifies on both digests, and they differ unless the two traces'
tagged encodings are an explicit collision. -/
theorem acc_changed_answer (S : Submission) (vk c : Digest) (π : Proof) (σ : Sig)
    {tr tr' : Trace} (h : S.acc vk c ⟨π, tr, σ⟩ = true) (h' : S.acc vk c ⟨π, tr', σ⟩ = true)
    (hne : tr ≠ tr') : SigOk vk (traceDigest tr) σ = true ∧ SigOk vk (traceDigest tr') σ = true ∧
      (traceDigest tr ≠ traceDigest tr' ∨ ∃ col : Collision,
        col.x = tagTrace :: traceBytes tr ∧ col.y = tagTrace :: traceBytes tr') := by
  simp only [Submission.acc, Bool.and_eq_true, decide_eq_true_eq] at h h'
  refine ⟨h.1.2, h'.1.2, ?_⟩
  by_cases hd : traceDigest tr = traceDigest tr'
  · rcases traceDigest_eq (fun e he => (h.1.1.2 e he).trans_lt (by decide))
      (fun e he => (h'.1.1.2 e he).trans_lt (by decide)) hd with ht | hc
    · exact absurd ht hne
    · exact Or.inr hc
  · exact Or.inl hd

/-! ## The caps -/

/-- **Over the word**: every submission's `acc` rejects a proof of `2^64` bytes or more. -/
theorem acc_over_word (S : Submission) (vk c : Digest) (p : Signed) (h : 2 ^ 64 ≤ p.π.size) :
    S.acc vk c p = false := by
  simp only [Submission.acc, decide_eq_false h.not_gt, Bool.false_and]

/-- **Over the query cap**: every submission's `acc` rejects a trace with a query longer than
`queryCap`. -/
theorem acc_query_over_cap (S : Submission) (vk c : Digest) (p : Signed) {e : ByteArray × Digest}
    (he : e ∈ p.tr) (h : queryCap < e.1.size) : S.acc vk c p = false := by
  have : ¬ ∀ e ∈ p.tr, e.1.size ≤ queryCap := fun hall => absurd (hall e he) (by omega)
  unfold Submission.acc
  rw [decide_eq_false this]
  simp

/-- The verifier that asks the one query `q` and accepts, declaring `qV = 1` (the
witness-sending submission otherwise). -/
def oneQuery (q : ByteArray) : Submission :=
  { submission with V := fun _ _ _ => .query q fun _ => .ret true, qV := 1 }

/-- The longest query `acc` admits: `queryCap` zero bytes. -/
def qMax : ByteArray := ⟨Array.replicate queryCap 0⟩

/-- **A signed trace with a query of exactly `queryCap` bytes, and exactly `qV = 1` entries, is
accepted** (both caps are `≤`) under a verifier that asks that query: exact consumption, the
trace-length and query caps and the reference signature on the trace's digest all pass, for
every secret function, answer and proof whose length fits a word. -/
theorem acc_query_at_cap (sk : ℕ → ℕ → Digest) (a c : Digest) {π : Proof}
    (hπ : π.size < 2 ^ 64) :
    (oneQuery qMax).acc (Signer.pk sk) c
      ⟨π, [(qMax, a)], Signer.sign sk 0 (traceDigest [(qMax, a)])⟩ = true := by
  have hq : qMax.size = queryCap := by simp [qMax, ByteArray.size]
  rw [Submission.acc, decide_eq_true hπ]
  simp [oneQuery, hq, Signer.sigOk_sign sk 0 (by decide), OProg.runSeq]

/-- **Over the trace-length cap**: every submission's `acc` rejects a trace with more
than `qV` entries, whatever its signature. -/
theorem acc_trace_over_qV (S : Submission) (vk c : Digest) (p : Signed) (h : S.qV < p.tr.length) :
    S.acc vk c p = false := by
  simp [Submission.acc, show ¬ p.tr.length ≤ S.qV by omega]

/-- An instance at `qV + 1 = 2` entries: the trace of `acc_query_at_cap` with its entry
repeated is rejected under a verifier declaring `qV = 1`, signature and all. -/
theorem acc_two_entries_rejected (sk : ℕ → ℕ → Digest) (a c : Digest) (π : Proof) :
    (oneQuery qMax).acc (Signer.pk sk) c ⟨π, [(qMax, a), (qMax, a)],
      Signer.sign sk 0 (traceDigest [(qMax, a), (qMax, a)])⟩ = false :=
  acc_trace_over_qV _ _ _ _ (by simp [oneQuery])

/-- A tree of `k` levels over one leaf: the digest. -/
def deepStmt : ℕ → Digest
  | 0 => leafStmt (leafValue s0 0) 0
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

/-- The signed proof of a tree of `k` levels: the proof, the empty trace, key `0`'s signature. -/
def deepSigned (sk : ℕ → ℕ → Digest) (k : ℕ) : Signed :=
  ⟨deepProof sk k, [], Signer.sign sk 0 (traceDigest [])⟩

/-- `acc` of a tree's signed proof is `check` of its proof, once its length fits a word. -/
private theorem acc_deepSigned (sk : ℕ → ℕ → Digest) {k : ℕ}
    (hw : (deepProof sk k).size < 2 ^ 64) :
    submission.acc (Signer.pk sk) (deepStmt k) (deepSigned sk k) =
      check (Signer.pk sk) (deepStmt k) (deepProof sk k) := by
  simp only [deepSigned]; rw [acc_eq, Signer.sigOk_sign sk 0 (by decide), decide_eq_true hw]; simp

/-- One more level: a node over two signed copies of an accepted proof whose length fits a word
is accepted. -/
private theorem deepProof_check_succ (sk : ℕ → ℕ → Digest) {k : ℕ}
    (h : check (Signer.pk sk) (deepStmt k) (deepProof sk k) = true)
    (hw : (deepProof sk k).size < 2 ^ 64) :
    check (Signer.pk sk) (deepStmt (k + 1)) (deepProof sk (k + 1)) = true := by
  have hacc := (acc_deepSigned sk hw).trans h
  rw [deepProof, deepStmt]
  exact check_encode ⟨rfl, hacc, hacc⟩

/-- The tree's proof of `k ≤ 50` levels has a length that fits a word. -/
private theorem deepProof_word (sk : ℕ → ℕ → Digest) {k : ℕ} (hk : k ≤ 50) :
    (deepProof sk k).size < 2 ^ 64 := by
  have hs := deepProof_size sk k
  have : 2 ^ k ≤ 2 ^ 50 := Nat.pow_le_pow_right (by norm_num) hk
  omega

theorem deepProof_check (sk : ℕ → ℕ → Digest) (k : ℕ) (hk : k ≤ 51) :
    check (Signer.pk sk) (deepStmt k) (deepProof sk k) = true := by
  induction k with
  | zero =>
    rw [deepProof, deepStmt]
    exact check_encode (show Rel _ _ (.leaf s0 0) from ⟨Nat.zero_le _, rfl⟩)
  | succ k ih => exact deepProof_check_succ sk (ih (by omega)) (deepProof_word sk (by omega))

/-- **No cap below the word**: `acc` accepts the signed witness-sending proof of a tree
of `k` levels, `9704 · 2^k − 9656` bytes, for every `k ≤ 50`. -/
theorem deep_accepted (sk : ℕ → ℕ → Digest) {k : ℕ} (hk : k ≤ 50) :
    submission.acc (Signer.pk sk) (deepStmt k) (deepSigned sk k) = true ∧
      (deepProof sk k).size + 9656 = 9704 * 2 ^ k :=
  ⟨(acc_deepSigned sk (deepProof_word sk hk)).trans (deepProof_check sk k (by omega)),
    deepProof_size sk k⟩

/-- **Above `2^20` bytes**: the 7-level proof has 1,232,456 bytes, more than `2^20`, and `acc`
accepts it. -/
theorem deep7_over_old_cap (sk : ℕ → ℕ → Digest) :
    submission.acc (Signer.pk sk) (deepStmt 7) (deepSigned sk 7) = true ∧
      (deepProof sk 7).size = 1232456 ∧ 2 ^ 20 < (deepProof sk 7).size := by
  have hs := deepProof_size sk 7
  exact ⟨(deep_accepted sk (by norm_num)).1, by omega, by omega⟩

/-- **The word is what rejects**: the witness-sending verifier accepts the 51-level proof (its
children's lengths fit a word), which has `2^64` bytes or more, and `acc` rejects it, signature
and all. -/
theorem deep_accepted_but_unwritable (sk : ℕ → ℕ → Digest) :
    check (Signer.pk sk) (deepStmt 51) (deepProof sk 51) = true ∧
      2 ^ 64 ≤ (deepProof sk 51).size ∧
      submission.acc (Signer.pk sk) (deepStmt 51) (deepSigned sk 51) = false := by
  have hs := deepProof_size sk 51
  have hw : 2 ^ 64 ≤ (deepProof sk 51).size := by omega
  exact ⟨deepProof_check sk 51 le_rfl, hw, acc_over_word _ _ _ _ hw⟩

end RecursionFast.Controls.Relation
