/-
# Contract: the relation over digests                                             (TRUSTED)

One relation over
32-byte statement digests, parameterised by an acceptance predicate `acc` on **signed proofs**
(`Certificate.lean` plugs in `Submission.acc` under a public key). A **leaf** digest commits to
the XOR of `n ≤ leafCap` independent Keccak-256 hashes of a seed (one per index `j < n`) and to
`n`; its witness is the seed and `n`. A **node** digest commits to two child digests; its witness
is two signed proofs that `acc` accepts.

**Why signed proofs.** Under the signed random oracle the oracle is a keyed
Keccak-256 held by a service that also signs the answers a proof used. A signed proof `(π, tr, σ)`
is a proof, the trace of oracle answers it was verified against (queries in the order asked), and
the service's signature on the trace's digest. A child is accepted relative to its signed trace,
never by evaluating the oracle, so the relation is an ordinary relation once the public key is
fixed, and every hash it evaluates is public Keccak-256: no public hash instantiates the oracle
inside the relation.

**Byte layouts (normative; the runner and the service hash the same bytes).**
* `leafItem s j = Keccak-256(tagItem ‖ s ‖ enc64 j)`: 41 bytes, one permutation; the `j`-th
  hash of the leaf with seed `s`.
* `leafValue s n = leafItem s 0 ⊕ … ⊕ leafItem s (n − 1)`, the bytewise XOR (`digestXor`) of the
  leaf's `n` hashes; the zero digest for `n = 0`. The hashes are independent of each other, so a
  prover computes them in parallel.
* `leafStmt h n = Keccak-256(tagLeaf ‖ h ‖ enc64 n)`: 41 bytes, with `h = leafValue s n`.
* `nodeStmt c₁ c₂ = Keccak-256(tagNode ‖ c₁ ‖ c₂)`: 65 bytes.
* `enc64 n`: the 8 little-endian bytes of `n mod 2^64` (Rust `u64::to_le_bytes`); injective below
  `2^64`, which covers every leaf size and hash index, accepted query length (`queryCap`) and
  key index the contract hashes.
* The trace digest and the signature's hashes are in `Signature.lean`.
* Tags: `H` leaf item, `L` leaf, `N` node, `T` trace, `W` WOTS chain step,
  `K` WOTS leaf, `M` signature Merkle node: seven distinct first bytes, one per hash input of the
  contract (`Controls/Relation.lean`, `tags_separate`). The oracle has no tag: the
  deployed oracle is keyed: its input starts with the secret 32-byte key, so computing an
  answer without the key, or a public tagged hash that equals one, is the PRF assumption.

**Leaf bound.** A leaf witness covers at most `leafCap = 2^22` hashes, checked before
any hash: completeness and knowledge soundness are asked only for leaves up to the season's
size, `2^22`, about one Ethereum slot's Keccak work in leanVM's deployment model (22,400
signatures × about 187 permutations). It bounds what checking a leaf witness costs, whatever
size a proof declares: the composition walk's leaf checks (`Library/Compose.lean`), and any
decoder or extractor that checks a leaf, hash at most `2^22` items per leaf.

`Digest` is a 32-byte vector (a closure would be re-evaluated on every byte read).
-/
import RecursionFast.Contract.Hash.Keccak
import Mathlib.Data.Nat.Notation

namespace RecursionFast

/-- A 32-byte digest: a Keccak-256 output, and the statement of the relation. -/
abbrev Digest := Vector UInt8 32

/-- A proof: any byte string (`acc` rejects one whose length does not fit a 64-bit word). -/
abbrev Proof := ByteArray

/-- The longest oracle query a signed trace may hold: `2^20` bytes (the service's own cap). -/
def queryCap : ℕ := 2 ^ 20

/-- The most hashes a leaf statement may cover: `2^22`. -/
def leafCap : ℕ := 2 ^ 22

/-- Keccak-256 of a byte string, as a digest. -/
def keccakDigest (m : List UInt8) : Digest :=
  ⟨(keccak256 m).toArray, by simp [keccak256, List.map_const']⟩

/-- Domain tag of a leaf item's preimage (`H`). -/
def tagItem : UInt8 := 0x48

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

/-- The `j`-th hash of the leaf with seed `s`: the seed and `j`, hashed under `tagItem`. -/
def leafItem (s : Digest) (j : ℕ) : Digest := keccakDigest (tagItem :: s.toList ++ enc64 j)

/-- The bytewise XOR of two digests. -/
def digestXor (a b : Digest) : Digest := Vector.zipWith (· ^^^ ·) a b

/-- The value of the leaf with seed `s` and `n` hashes: the XOR of `leafItem s j` over `j < n`,
by recursion on `n` (the zero digest for `n = 0`). -/
def leafValue (s : Digest) : ℕ → Digest
  | 0 => Vector.replicate 32 0
  | n + 1 => digestXor (leafValue s n) (leafItem s n)

/-- The statement of a leaf: its value `h` and its number of hashes `n`, hashed under
`tagLeaf`. -/
def leafStmt (h : Digest) (n : ℕ) : Digest := keccakDigest (tagLeaf :: h.toList ++ enc64 n)

/-- The statement of a node: its two children's digests, hashed under `tagNode`. -/
def nodeStmt (c₁ c₂ : Digest) : Digest := keccakDigest (tagNode :: c₁.toList ++ c₂.toList)

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

/-- A witness: a seed and a number of hashes (leaf), or two child digests and their signed
proofs (node). -/
inductive Wit where
  /-- A leaf witness: the seed `s` and the number of hashes `n`. -/
  | leaf (s : Digest) (n : ℕ)
  /-- A node witness: the child digests `c₁`, `c₂` and their signed proofs `p₁`, `p₂`. -/
  | node (c₁ c₂ : Digest) (p₁ p₂ : Signed)

/-- **The relation** for the acceptance predicate `acc`: a leaf digest is the statement of the
value of at most `leafCap` hashes of the witness's seed; a node digest is the statement of two
children whose signed proofs `acc` accepts. -/
def Rel (acc : Digest → Signed → Bool) : Digest → Wit → Prop
  | c, .leaf s n => n ≤ leafCap ∧ c = leafStmt (leafValue s n) n
  | c, .node c₁ c₂ p₁ p₂ => c = nodeStmt c₁ c₂ ∧ acc c₁ p₁ = true ∧ acc c₂ p₂ = true

end RecursionFast
