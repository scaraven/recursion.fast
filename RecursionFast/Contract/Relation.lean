/-
# Contract: the relation over digests                                             (TRUSTED)

One relation over 32-byte statement digests, parameterised by an acceptance predicate `acc` on **signed proofs**
(`Certificate.lean` plugs in `Submission.acc` under a public key). A **leaf** digest commits to
the Merkle root (`dataRoot`) of `n ≤ leafCap` 32-byte blocks, the leaf's data, and to `n`; its
witness is the data, the blocks in order. The runner supplies the data and computes the
statement from it; a prover is given the blocks (at `n = 0` the statement `leafStmt zero 0` is
public, with the one witness `[]`; the runner's statements have `1 ≤ n`, its shape check). A
**node** digest commits to two child digests; its witness is two signed proofs that `acc`
accepts.

**Why signed proofs.** Under the signed random oracle the oracle is a keyed
Keccak-256 held by a service that also signs the answers a proof used. A signed proof `(π, tr, σ)`
is a proof, the trace of oracle answers it was verified against (queries in the order asked), and
the service's signature on the trace's digest. A child is accepted relative to its signed trace,
never by evaluating the oracle, so the relation is an ordinary relation once the public key is
fixed, and every hash it evaluates is public Keccak-256: no public hash instantiates the oracle
inside the relation.

**Byte layouts (normative; the runner and the service hash the same bytes).**
* `leafItem x = Keccak-256(tagItem ‖ x)`: 33 bytes, one permutation; the hash of the block `x`.
* `dataNode l r = Keccak-256(tagData ‖ l ‖ r)`: 65 bytes, one permutation; a node of the data tree.
* `dataLevel`: adjacent digests paired by `dataNode`, an odd last digest carried up unhashed;
  `dataRoot xs`: `dataLevel` applied `|xs|` times to the block hashes, then the first digest (the
  zero digest for no block, `leafItem x` for one block). The statement binds `n`, so the tree's
  shape is fixed; the carry-up matters only at sizes that are not powers of two.
* `leafStmt h n = Keccak-256(tagLeaf ‖ h ‖ enc64 n)`: 41 bytes, with `h = dataRoot xs`, `n = |xs|`.
* `nodeStmt c₁ c₂ = Keccak-256(tagNode ‖ c₁ ‖ c₂)`: 65 bytes.
* `enc64 n`: the 8 little-endian bytes of `n mod 2^64` (Rust `u64::to_le_bytes`); injective below
  `2^64`, which covers every leaf size, accepted query length (`queryCap`) and key index the
  contract hashes.
* The trace digest and the signature's hashes are in `Signature.lean`.
* Tags: `H` leaf item, `D` data node, `L` leaf, `N` node, `T` trace, `W` WOTS chain step,
  `K` WOTS leaf, `M` signature Merkle node: eight distinct first bytes, one per hash input of the
  contract (`Controls/Relation.lean`, `tags_separate`). The oracle has no tag. The deployed
  oracle is keyed (its input starts with the secret 32-byte key), so computing an answer without
  the key, or a public tagged hash that equals one, is the PRF assumption.

**Leaf bound.** A leaf witness covers at most `leafCap = 2^20` blocks, checked before any hash.
Completeness and knowledge soundness are asked for every leaf up to it, odd sizes included, though
the season uses one `n` (`harness/season.toml`). The cap is set by the extractor's output cap
(`Extractor.lean`): a leaf witness of `n` blocks takes `2 + 4n` output words, and the certificate
asks for both completeness at every leaf up to `leafCap` and extraction within `outCap = 2^24`
words. At `2^22` a leaf at the cap would take `2^24 + 2` words, which no extractor could output
while `V` must accept it; at `2^20` it takes at most `2^22 + 2`, and a node whose leaf child is
sent whole and whose first child is at the 64 MiB file cap stays below `2^23 + 2^22 + 2^17 <
2^24` words. It also bounds what checking a leaf witness costs, whatever size a proof declares:
the composition walk's leaf checks (`Library/Compose.lean`), and any check through `Rel` (whose
first conjunct is `|xs| ≤ leafCap`), hash at most `2^21` times per leaf.

`Digest` is a 32-byte vector (a closure would be re-evaluated on every byte read).
-/
import RecursionFast.Contract.Hash.Keccak
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Function.Iterate

namespace RecursionFast

/-- A 32-byte digest: a Keccak-256 output, and the statement of the relation. -/
abbrev Digest := Vector UInt8 32

/-- A proof: any byte string (`acc` rejects one whose length does not fit a 64-bit word). -/
abbrev Proof := ByteArray

/-- The longest oracle query a signed trace may hold: `2^20` bytes (the service's own cap). -/
def queryCap : ℕ := 2 ^ 20

/-- The most blocks a leaf statement may cover: `2^20` (the module header says why). -/
def leafCap : ℕ := 2 ^ 20

/-- Keccak-256 of a byte string, as a digest. -/
def keccakDigest (m : List UInt8) : Digest :=
  ⟨(keccak256 m).toArray, by simp [keccak256, List.map_const']⟩

/-- Domain tag of a leaf item's preimage (`H`). -/
def tagItem : UInt8 := 0x48

/-- Domain tag of a data-tree node's preimage (`D`). -/
def tagData : UInt8 := 0x44

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

/-- The hash of one 32-byte block of a leaf's data, under `tagItem`. -/
def leafItem (x : Digest) : Digest := keccakDigest (tagItem :: x.toList)

/-- A node of a leaf's data tree: its two children's digests, hashed under `tagData`. -/
def dataNode (l r : Digest) : Digest := keccakDigest (tagData :: l.toList ++ r.toList)

/-- One level up the data tree: adjacent digests paired by `dataNode`; an odd last one carried
up. -/
def dataLevel : List Digest → List Digest
  | a :: b :: t => dataNode a b :: dataLevel t
  | t => t

/-- **The root** of a leaf's data `xs`: `dataLevel` from the block hashes, `|xs|` times (enough;
one digest is a fixed point), then the first digest; the zero digest for no block. -/
def dataRoot (xs : List Digest) : Digest :=
  (dataLevel^[xs.length] (xs.map leafItem)).headD (Vector.replicate 32 0)

/-- The statement of a leaf: its data's root `h` and its number of blocks `n`, hashed under
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

/-- A witness: a leaf's data (leaf), or two child digests and their signed proofs (node). -/
inductive Wit where
  /-- A leaf witness: the leaf's data, its blocks in order. -/
  | leaf (xs : List Digest)
  /-- A node witness: the child digests `c₁`, `c₂` and their signed proofs `p₁`, `p₂`. -/
  | node (c₁ c₂ : Digest) (p₁ p₂ : Signed)

/-- **The relation** for the acceptance predicate `acc`: a leaf digest is the statement of the
root and the size of the witness's data, at most `leafCap` blocks; a node digest is the statement
of two children whose signed proofs `acc` accepts. -/
def Rel (acc : Digest → Signed → Bool) : Digest → Wit → Prop
  | c, .leaf xs => xs.length ≤ leafCap ∧ c = leafStmt (dataRoot xs) xs.length
  | c, .node c₁ c₂ p₁ p₂ => c = nodeStmt c₁ c₂ ∧ acc c₁ p₁ = true ∧ acc c₂ p₂ = true

end RecursionFast
