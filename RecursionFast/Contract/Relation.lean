/-
# Contract: the relation over digests                                             (TRUSTED)

v4 (docs/v4/BRIEF.md §2, §4.1; V4-3, V4-16), from DESIGN-v3 §2.1 (V3-7). One relation over
32-byte statement digests, parameterised by an acceptance predicate `acc` on **signed proofs**
(`Certificate.lean` plugs in `Submission.acc` under a public key). A **leaf** digest commits to
the end of a BLAKE2s chain of at most `chainCap` steps and its length; its witness is the chain's
start (unchanged from v3). A **node** digest commits to two child digests; its witness is two
signed proofs that `acc` accepts.

**Why signed proofs (V4-3, BRIEF P2).** Under the signed random oracle the oracle is a keyed
BLAKE2s held by a service that also signs the answers a proof used. A signed proof `(π, tr, σ)`
is a proof, the trace of oracle answers it was verified against (queries in the order asked), and
the service's signature on the trace's digest. A child is accepted relative to its signed trace,
never by evaluating the oracle, so the relation is an ordinary relation once the public key is
fixed, and every hash it evaluates is public BLAKE2s (v3's `Vb`, which instantiated the oracle
inside the relation, is gone with O-25).

**Byte layouts (normative; the runner and the service hash the same bytes).**
* `chainStep d = BLAKE2s-256(tagChain ‖ d)`: 33 bytes, one compression (V3-S1-A19);
  `chainEnd s n` applies it `n` times.
* `leafStmt h n = BLAKE2s-256(tagLeaf ‖ h ‖ enc64 n)`: 41 bytes.
* `nodeStmt c₁ c₂ = BLAKE2s-256(tagNode ‖ c₁ ‖ c₂)`: 65 bytes.
* `enc64 n`: the 8 little-endian bytes of `n mod 2^64` (Rust `u64::to_le_bytes`); injective below
  `2^64`, which covers every chain length, accepted query length (`queryCap`) and key index the
  contract hashes.
* The trace digest and the signature's hashes are in `Signature.lean`.
* Tags (V3-S1-A5, A19; V4-16): `C` chain, `L` leaf, `N` node, `T` trace, `W` WOTS chain step,
  `K` WOTS leaf, `M` signature Merkle node: seven distinct first bytes, one per hash input of the
  contract (`Controls/Relation.lean`, `tags_separate`). v3's `R` (the oracle's prefix) is gone: the
  deployed oracle is keyed (V4-2), and keyed BLAKE2s differs from the unkeyed hash on every input
  (its first block is the key).

**Chain bound (V3-S1-A20).** A leaf witness has at most `chainCap = 2^20` steps, checked before
the hash: completeness does not ask for proofs of chains no prover handles, and a verifier that
recomputes chains is not driven past its time cap by a proof declaring a huge length.

`Digest` is a 32-byte vector (V3-S1-A4: a closure would be re-evaluated on every byte read).
-/
import RecursionFast.Contract.Hash.Blake2s
import Mathlib.Logic.Function.Iterate

namespace RecursionFast

/-- A 32-byte digest: a BLAKE2s-256 output, and the statement of the relation. -/
abbrev Digest := Vector UInt8 32

/-- A proof: any byte string (`acc` rejects one whose length does not fit a 64-bit word). -/
abbrev Proof := ByteArray

/-- The longest oracle query a signed trace may hold: `2^20` bytes (the service's own cap). -/
def queryCap : ℕ := 2 ^ 20

/-- The longest chain a leaf statement may commit to: `2^20` steps. -/
def chainCap : ℕ := 2 ^ 20

/-- BLAKE2s-256 of a byte string, as a digest. -/
def blake2sDigest (m : List UInt8) : Digest :=
  ⟨(blake2s256 m).toArray, by simp [blake2s256, blake2s, List.map_const']⟩

/-- Domain tag of a chain step's preimage (`C`). -/
def tagChain : UInt8 := 0x43

/-- Domain tag of a leaf statement's preimage (`L`). -/
def tagLeaf : UInt8 := 0x4C

/-- Domain tag of a node statement's preimage (`N`). -/
def tagNode : UInt8 := 0x4E

/-- Domain tag of a trace digest's preimage (`T`). -/
def tagTrace : UInt8 := 0x54

/-- Domain tag of a WOTS chain step's preimage (`W`). -/
def tagWots : UInt8 := 0x57

/-- Domain tag of a WOTS leaf's preimage (`K`). -/
def tagWotsLeaf : UInt8 := 0x4B

/-- Domain tag of a signature Merkle node's preimage (`M`). -/
def tagSigNode : UInt8 := 0x4D

/-- The 8 little-endian bytes of `n mod 2^64`. -/
def enc64 (n : ℕ) : List UInt8 := List.ofFn fun i : Fin 8 => (n / 256 ^ i.val).toUInt8

/-- One step of a hash chain: the digest hashed under `tagChain`. -/
def chainStep (d : Digest) : Digest := blake2sDigest (tagChain :: d.toList)

/-- The end of the hash chain of length `n` from the start `s`. -/
def chainEnd (s : Digest) (n : ℕ) : Digest := chainStep^[n] s

/-- The statement of a leaf: the chain end `h` and the chain length `n`, hashed under `tagLeaf`. -/
def leafStmt (h : Digest) (n : ℕ) : Digest := blake2sDigest (tagLeaf :: h.toList ++ enc64 n)

/-- The statement of a node: its two children's digests, hashed under `tagNode`. -/
def nodeStmt (c₁ c₂ : Digest) : Digest := blake2sDigest (tagNode :: c₁.toList ++ c₂.toList)

/-- A trace: oracle queries with their answers, in the order a program asked them. -/
abbrev Trace := List (ByteArray × Digest)

/-- A signature (checked by `SigOk`, `Signature.lean`): the index of the one-time key used, the
WOTS chain values, and the Merkle authentication path of that key, leaf level first. -/
structure Sig where
  /-- The one-time key's index (below `2^16` for a valid signature). -/
  idx : ℕ
  /-- The WOTS chain values, one per digit (133 for a valid signature). -/
  ots : List Digest
  /-- The siblings on the path from the key's leaf to the root (16 for a valid signature). -/
  path : List Digest

/-- A signed proof: a proof, the trace of oracle answers it is verified against, and a signature
on the trace's digest. -/
structure Signed where
  /-- The proof. -/
  π : Proof
  /-- The oracle answers the verifier reads, in the order it asks. -/
  tr : Trace
  /-- The service's signature on the digest of `tr`. -/
  σ : Sig

/-- A witness: a chain start and length (leaf), or two child digests and their signed proofs
(node). -/
inductive Wit where
  /-- A leaf witness: the chain start `s` and the chain length `n`. -/
  | leaf (s : Digest) (n : ℕ)
  /-- A node witness: the child digests `c₁`, `c₂` and their signed proofs `p₁`, `p₂`. -/
  | node (c₁ c₂ : Digest) (p₁ p₂ : Signed)

/-- **The relation** for the acceptance predicate `acc`: a leaf digest is the statement of a
chain of at most `chainCap` steps from the witness's start; a node digest is the statement of two
children whose signed proofs `acc` accepts. -/
def Rel (acc : Digest → Signed → Bool) : Digest → Wit → Prop
  | c, .leaf s n => n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n
  | c, .node c₁ c₂ p₁ p₂ => c = nodeStmt c₁ c₂ ∧ acc c₁ p₁ = true ∧ acc c₂ p₂ = true

end RecursionFast
