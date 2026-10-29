/-
# Contract: the trace digest and the signature check                             (TRUSTED)

v4, V4-3 and the byte layouts of docs/v4/BRIEF.md §4.2 (normative: the service, this file and the
runner agree byte for byte). The service signs, per `sign` request, the digest of the whole trace
it answered (hash-then-sign), with a **stateful hash-based signature**: Winternitz one-time
signatures (WOTS) with base-4 digits (`w = 4`, chains of 3 steps), 133 chains per key, under a
Merkle tree of `2^16` one-time keys whose root is the public key `vk`. Every hash below is public
BLAKE2s-256 under its own tag (`Relation.lean`, V4-16).

**Why this scheme (V4-3).** Hash-based, so the contract has no group and no field (V3-1, V3-5);
BLAKE2s, so a node circuit needs one hash gadget for chains, statements, traces and signatures;
`w = 4`, which minimises the in-circuit cost of one check (about 200 chain steps on average, 67
compressions for the leaf, 32 for the path). Stateful: the service uses each index once and
refuses after `2^16` signatures (BRIEF §4.3).

**Layouts.**
* `traceDigest tr = BLAKE2s-256(tagTrace ‖ item₀ ‖ item₁ ‖ …)`, `itemᵢ = enc64 |qᵢ| ‖ qᵢ ‖ aᵢ`.
  The encoding is injective on traces whose queries are shorter than `2^64` bytes, so on every
  trace `acc` accepts (at most `queryCap` bytes per query, V4-A3, which withdrew V4-5);
  `Library/Trace.lean`, `traceBytes_inj`.
* Digits of a 32-byte message `m`: byte `i` gives the digits `4i + t = (m[i] >> 2t) & 3`,
  `t = 0 … 3` (128 digits); the checksum `C = Σ (3 − dᵢ)` over them (at most 384) gives the
  digits `128 + t = (C >> 2t) & 3`, `t = 0 … 4`. Raising a message digit lowers a checksum digit,
  so no signature can be advanced along its chains to sign another message
  (`Library/Signer.lean`, `wotsDigits_dominates`).
* Chain step `F(j, i, s, x) = BLAKE2s-256(tagWots ‖ enc64 j ‖ i ‖ s ‖ x)` (43 bytes): chain `i` of
  one-time key `j`, from position `s` to `s + 1`. A signature's value for chain `i` is the chain at
  position `dᵢ`; the verifier walks it to position 3.
* Leaf `= BLAKE2s-256(tagWotsLeaf ‖ enc64 j ‖ end₀ ‖ … ‖ end₁₃₂)` (4,265 bytes).
* Merkle node `= BLAKE2s-256(tagSigNode ‖ left ‖ right)`; at level `t = 0 … 15` the current value
  is the left child iff bit `t` of `j` is `0`, with `path[t]` the sibling.

**What is not here.** Key generation, the secret chain starts and signing are the service's (a
Lean reference signer and the theorem that its signatures pass `SigOk` are in
`Library/Signer.lean`). Unforgeability (EUF-CMA of this scheme with each index used once) is an
assumption of the design argued on paper, not a theorem of the contract; the composition theorem
(`Library/Compose.lean`, V4-8) returns an explicit forgery when it is what fails.
-/
import RecursionFast.Contract.Relation

namespace RecursionFast

/-- The bytes a trace digest hashes: each entry as `enc64 |q| ‖ q ‖ a`, in order. -/
def traceBytes (tr : Trace) : List UInt8 :=
  tr.flatMap fun e => enc64 e.1.size ++ e.1.data.toList ++ e.2.toList

/-- **The digest of a trace**, the message the service signs: its bytes hashed under
`tagTrace`. -/
def traceDigest (tr : Trace) : Digest := blake2sDigest (tagTrace :: traceBytes tr)

/-- The number of WOTS chains of a one-time key: 128 message digits and 5 checksum digits. -/
def wotsLen : ℕ := 133

/-- The height of the key tree: `2^16` one-time keys. -/
def sigHeight : ℕ := 16

/-- The 128 base-4 digits of a message: byte `i` gives digits `4i … 4i + 3`, low bits first. -/
def msgDigits (m : Digest) : List ℕ :=
  m.toList.flatMap fun b => (List.range 4).map fun t => b.toNat / 4 ^ t % 4

/-- **The WOTS digits signed for a message**: its 128 digits, then the 5 base-4 digits (low
first) of their checksum `Σ (3 − dᵢ)`. -/
def wotsDigits (m : Digest) : List ℕ :=
  let d := msgDigits m
  let C := (d.map (3 - ·)).sum
  d ++ (List.range 5).map fun t => C / 4 ^ t % 4

/-- **The chain step** `F(j, i, s, x)`: the value of chain `i` of one-time key `j` at position
`s + 1`, from its value `x` at position `s` (43 bytes hashed under `tagWots`). -/
def wotsStep (j i s : ℕ) (x : Digest) : Digest :=
  blake2sDigest (tagWots :: enc64 j ++ [i.toUInt8, s.toUInt8] ++ x.toList)

/-- The value of chain `i` of key `j` at position `s + n`, from its value `x` at position `s`. -/
def wotsChain (j i s : ℕ) : ℕ → Digest → Digest
  | 0, x => x
  | n + 1, x => wotsChain j i (s + 1) n (wotsStep j i s x)

/-- The chain ends a signature determines: chain `i` walked from its signed value at position
`dᵢ` (the `i`-th digit of `m`) to position 3. -/
def wotsEnds (j : ℕ) (m : Digest) (ots : List Digest) : List Digest :=
  ((wotsDigits m).zip ots).mapIdx fun i e => wotsChain j i e.1 (3 - e.1) e.2

/-- **The leaf of one-time key `j`**: its chain ends hashed under `tagWotsLeaf` with `j`. -/
def wotsLeaf (j : ℕ) (ends : List Digest) : Digest :=
  blake2sDigest (tagWotsLeaf :: enc64 j ++ ends.flatMap Vector.toList)

/-- A node of the key tree: its two children hashed under `tagSigNode`. -/
def sigNode (l r : Digest) : Digest := blake2sDigest (tagSigNode :: l.toList ++ r.toList)

/-- The root reached from the value `x` of node `j` of its level along the siblings `path`
(lowest level first): `x` is the left child iff `j` is even. -/
def sigRoot : ℕ → Digest → List Digest → Digest
  | _, x, [] => x
  | j, x, s :: p => sigRoot (j / 2) (if j % 2 = 0 then sigNode x s else sigNode s x) p

/-- **The signature check**: `σ` signs the message `m` under the public key `vk`: its index is
below `2^16`, it has 133 chain values and 16 siblings, and the root they determine is `vk`. -/
def SigOk (vk m : Digest) (σ : Sig) : Bool :=
  decide (σ.idx < 2 ^ sigHeight) && decide (σ.ots.length = wotsLen) &&
    decide (σ.path.length = sigHeight) &&
    decide (sigRoot σ.idx (wotsLeaf σ.idx (wotsEnds σ.idx m σ.ots)) σ.path = vk)

end RecursionFast
