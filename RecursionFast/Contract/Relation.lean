/-
# Contract: the relation over digests                                             (TRUSTED)

DESIGN-v3 §2.1, V3-7. One relation over 32-byte statement digests, parameterised by an
instantiated verifier `Vb` (a total function on bytes; `Certificate.lean` plugs in the
submission's own). A **leaf** digest commits to the end of a BLAKE2s chain of at most `chainCap`
steps and its length; its witness is the chain's start. A **node** digest commits to two child
digests; its witness is two proofs `Vb` accepts. No field, no size class, no index.

**Byte layouts (normative; the runner hashes the same bytes).**
* `chainStep d = BLAKE2s-256(tagChain ‖ d)`: 1 + 32 = 33 bytes, one compression (V3-S1-A19);
  `chainEnd s n` applies it `n` times.
* `leafStmt h n = BLAKE2s-256(tagLeaf ‖ h ‖ enc64 n)`: 1 + 32 + 8 = 41 bytes.
* `nodeStmt c₁ c₂ = BLAKE2s-256(tagNode ‖ c₁ ‖ c₂)`: 1 + 32 + 32 = 65 bytes.
* `enc64 n`: the 8 little-endian bytes of `n mod 2^64` (Rust `u64::to_le_bytes`); injective on
  the chain lengths the relation admits (`n ≤ chainCap`).
* Tags (V3-S1-A5, A19): `tagChain = 0x43` ('C'), `tagLeaf = 0x4C` ('L'), `tagNode = 0x4E` ('N'),
  `tagRO = 0x52` ('R', the prefix of every oracle input, `Certificate.lean`). Four distinct first
  bytes, so no chain, leaf or node preimage is an oracle input; the relation hashes oracle inputs
  only inside `Vb` in the node clause, which is the recursion itself.

**Chain bound (V3-S1-A20).** A leaf witness has at most `chainCap = 2^20` steps, checked before
the hash: completeness does not ask for proofs of chains no prover handles, and a verifier that
recomputes chains is not driven past its time cap by a proof declaring a huge length.

`Digest` is a 32-byte vector (V3-S1-A4: the design's `Fin 32 → UInt8` is a closure, which
compiled code re-evaluates on every byte read, so a chain of `n` steps costs `32^n` hashes).
-/
import RecursionFast.Contract.Hash.Blake2s
import Mathlib.Logic.Function.Iterate

namespace RecursionFast

/-- A 32-byte digest: a BLAKE2s-256 output, and the statement of the relation. -/
abbrev Digest := Vector UInt8 32

/-- A proof: any byte string (a verifier's wrapper rejects one longer than `proofCap`). -/
abbrev Proof := ByteArray

/-- The longest proof the instantiated verifier accepts: `2^20` bytes (1 MiB). -/
def proofCap : ℕ := 2 ^ 20

/-- The longest chain a leaf statement may commit to: `2^20` steps. -/
def chainCap : ℕ := 2 ^ 20

/-- BLAKE2s-256 of a byte string, as a digest. -/
def blake2sDigest (m : List UInt8) : Digest :=
  ⟨(blake2s256 m).toArray, by simp [blake2s256, blake2s, List.map_const']⟩

/-- Domain tag of a chain step's preimage. -/
def tagChain : UInt8 := 0x43

/-- Domain tag of a leaf statement's preimage. -/
def tagLeaf : UInt8 := 0x4C

/-- Domain tag of a node statement's preimage. -/
def tagNode : UInt8 := 0x4E

/-- Domain tag of every oracle query when the oracle is instantiated with BLAKE2s. -/
def tagRO : UInt8 := 0x52

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

/-- A witness: a chain start and length (leaf), or two child digests and their proofs (node). -/
inductive Wit where
  /-- A leaf witness: the chain start `s` and the chain length `n`. -/
  | leaf (s : Digest) (n : ℕ)
  /-- A node witness: the child digests `c₁`, `c₂` and their proofs `π₁`, `π₂`. -/
  | node (c₁ c₂ : Digest) (π₁ π₂ : Proof)

/-- **The relation** for the instantiated verifier `Vb`: a leaf digest is the statement of a
chain of at most `chainCap` steps from the witness's start; a node digest is the statement of two
children whose proofs `Vb` accepts. -/
def Rel (Vb : Digest → Proof → Bool) : Digest → Wit → Prop
  | c, .leaf s n => n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n
  | c, .node c₁ c₂ π₁ π₂ => c = nodeStmt c₁ c₂ ∧ Vb c₁ π₁ = true ∧ Vb c₂ π₂ = true

end RecursionFast
