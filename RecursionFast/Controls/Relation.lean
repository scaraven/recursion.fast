/-
# Controls: the relation (`Contract/Relation.lean`) and acceptance (`Submission.acc`)

Known answers are decided by the kernel (`decide +kernel` on the word-level twins of
`Library/Fast.lean`, proved equal to the contract's hashes); each expected digest is the output of
the `python3 -I` command in its docstring, run from the repository root (`harness/rfh/keccak.py`,
the runner's Keccak-256, itself checked against OpenSSL's `keccak-256`), following the byte layouts
of `Contract/Relation.lean`: `B(j)` is the block `blk j` (bytes `32j, …, 32j + 31` mod 256),
`L` one level of the data tree (pairs under `D`, an odd last digest carried up) and `R(n)` the root
of the blocks `blk 0, …, blk (n − 1)`: the data pattern and the vectors the runner's Python
reference, the service (Rust) and the toy prover (C) are checked against (`b_i = i mod 256`
over the `32n` bytes). Signed children are built with the Lean reference signer
(`Library/Signer.lean`) for **every** secret function `sk`, and their signatures are proved valid
symbolically (`sigOk_sign`, no hash evaluated).

Positive:
* `item_kat`, `item1_kat` (`leafItem` of the first two blocks), `root1_kat` (one block: its
  hash), `root2_kat`, `root3_kat` (an odd level: the third hash is carried up), `root4_kat` (two
  full levels), `root5_kat`, `root6_kat`, `root7_kat` (carry-ups above the first level: the fifth
  hash carried two levels, the last node carried at the second level, the seventh hash carried
  once then paired), `stmt9_kat` (the statement of nine blocks, the ninth hash carried three
  levels), `leafStmt_kat` (the statement of `root4_kat`'s root, `n = 4`), `rel_root4` (that
  statement is in the relation with the four blocks as its witness), `nodeStmt_kat`: the byte
  layouts;
  `leafStmt_season_kat` (the count `2^18`, the season's `n`) with `enc64` beyond its first byte
  (`enc64_season`, `enc64_kat`: 8 bytes, little-endian).
* `leafStmt_empty_kat`, `leaf_empty`, `leaf_empty_unique`: at `n = 0` the statement
  `leafStmt zero 0` is public: `[]` witnesses it and only it, so modulo a Keccak-256 collision
  its one witness is `[]` (the runner enforces `1 ≤ n`).
* `acc_leafSigned`: the witness-sending signed proof of a leaf (empty trace, a reference
  signature of its digest) is accepted under the signer's key.
* **`node_of_two_leaves`** (the node clause): under the witness-sending `acc` and the key
  `pk sk`, a node digest of two leaf digests is in the relation with the two signed leaf proofs
  as its witness, for every secret function and two leaves' data of up to `leafCap` blocks;
  `node_of_two_leaves_ref` with the reference derivation of the WOTS chain starts.
* `leaf_at_leafCap`, `leaf_at_2pow20`: a leaf of exactly `leafCap = 2^20` blocks is in the
  relation (symbolic: no hash is evaluated).
* `tags_separate`: the eight tags are distinct bytes, and each hash input of the contract starts
  with its own tag.

Negative:
* `wrong_root` (the block in place of its hash), `wrong_block` (another block), `wrong_count`
  (the right root, the wrong count), `dropped_block` (one block dropped), `extra_block` (one block
  added), `swapped_blocks` (two blocks swapped: the tree is ordered), `carry_not_duplicated` (an
  odd last digest is carried up, not paired with itself), `root_not_xor` and `xor_rejected` (the
  root is not the XOR of the block hashes, the earlier seed leaf's combination),
  `leaf_over_leafCap` (every `acc`); `leaf_over_2pow20`: the bound is `2^20` (a leaf of
  `2^20 + 1` blocks is rejected under every `acc`; `tests/mutation`'s `rel-leafcap-2^21`).
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
  `queryCap`; `acc_query_over_2pow20`: the cap is the service's `2^20` bytes (a query of
  `2^20 + 1` bytes is rejected; `tests/mutation`'s `rel-querycap-2^21`);
  `deep_accepted_but_unwritable`: the witness-sending verifier accepts a 51-level
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

/-- The block `j`: the bytes `32j, 32j + 1, …, 32j + 31` (mod 256). -/
def blk (j : ℕ) : Digest := Vector.ofFn fun i => (32 * j + i.val).toUInt8

/-- The first block, `00 01 … 1f`. -/
abbrev s0 : Digest := blk 0

/-- The second block, `20 21 … 3f`. -/
abbrev s1 : Digest := blk 1

/-- The first `n` blocks. -/
def blks (n : ℕ) : List Digest := (List.range n).map blk

/-! ## Known answers -/

/-- `python3 -I -c "import sys; sys.path.insert(0, 'harness')
from rfh.keccak import keccak256 as K
print(K(b'H'+bytes(range(32))).hex())"` -/
theorem item_kat : (leafItem s0).toList =
    hex "09910f8c671ec97437b818fd5a1cb7f10ce4be81bf37778b0605b381eaabbe69" := by
  rw [← leafItemF_eq]
  decide +kernel

/-- `python3 -I -c "import sys; sys.path.insert(0, 'harness')
from rfh.keccak import keccak256 as K
print(K(b'H'+bytes(range(32, 64))).hex())"` (the second block) -/
theorem item1_kat : (leafItem s1).toList =
    hex "bea32b562ceff4efb8e461d8068bc952e8a11b759db5b51b9fc9a335e311edee" := by
  rw [← leafItemF_eq]
  decide +kernel

/-- One block: the root is its hash (`item_kat`).
`python3 -I -c "import sys, functools as F; sys.path.insert(0, 'harness')
from rfh.keccak import keccak256 as K; B=lambda j: bytes((32*j+i)%256 for i in range(32))
L=lambda d: [K(b'D'+d[i]+d[i+1]) for i in range(0,len(d)-1,2)]+d[len(d)//2*2:]
R=lambda n: F.reduce(lambda d,_: L(d), range(n), [K(b'H'+B(j)) for j in range(n)])[0]
print(R(1).hex())"` -/
theorem root1_kat : (dataRoot (blks 1)).toList =
    hex "09910f8c671ec97437b818fd5a1cb7f10ce4be81bf37778b0605b381eaabbe69" := by
  rw [← dataRootF_eq]
  decide +kernel

/-- Two blocks: one data node over their hashes.
`python3 -I -c "import sys, functools as F; sys.path.insert(0, 'harness')
from rfh.keccak import keccak256 as K; B=lambda j: bytes((32*j+i)%256 for i in range(32))
L=lambda d: [K(b'D'+d[i]+d[i+1]) for i in range(0,len(d)-1,2)]+d[len(d)//2*2:]
R=lambda n: F.reduce(lambda d,_: L(d), range(n), [K(b'H'+B(j)) for j in range(n)])[0]
print(R(2).hex())"` -/
theorem root2_kat : (dataRoot (blks 2)).toList =
    hex "a8886ea246bda7de84ecc698aa1cc03cf96654a74818887a43b3d042e5935020" := by
  rw [← dataRootF_eq]
  decide +kernel

/-- Three blocks, an odd level: the third hash is carried up, then paired with the first node.
`python3 -I -c "import sys, functools as F; sys.path.insert(0, 'harness')
from rfh.keccak import keccak256 as K; B=lambda j: bytes((32*j+i)%256 for i in range(32))
L=lambda d: [K(b'D'+d[i]+d[i+1]) for i in range(0,len(d)-1,2)]+d[len(d)//2*2:]
R=lambda n: F.reduce(lambda d,_: L(d), range(n), [K(b'H'+B(j)) for j in range(n)])[0]
print(R(3).hex())"` -/
theorem root3_kat : (dataRoot (blks 3)).toList =
    hex "e05b7300eecd28cd7e31a9d377deea6030b49cf9bfd08b0b47c132230812615b" := by
  rw [← dataRootF_eq]
  decide +kernel

/-- Four blocks, two full levels.
`python3 -I -c "import sys, functools as F; sys.path.insert(0, 'harness')
from rfh.keccak import keccak256 as K; B=lambda j: bytes((32*j+i)%256 for i in range(32))
L=lambda d: [K(b'D'+d[i]+d[i+1]) for i in range(0,len(d)-1,2)]+d[len(d)//2*2:]
R=lambda n: F.reduce(lambda d,_: L(d), range(n), [K(b'H'+B(j)) for j in range(n)])[0]
print(R(4).hex())"` -/
theorem root4_kat : (dataRoot (blks 4)).toList =
    hex "55c3ed43367f2313bd98059444f498d7ad3efb1aa34846e9543dde3a414085b1" := by
  rw [← dataRootF_eq]
  decide +kernel

/-- Five blocks: the fifth hash is carried up two levels, then paired with the four blocks' root.
`python3 -I -c "import sys, functools as F; sys.path.insert(0, 'harness')
from rfh.keccak import keccak256 as K; B=lambda j: bytes((32*j+i)%256 for i in range(32))
L=lambda d: [K(b'D'+d[i]+d[i+1]) for i in range(0,len(d)-1,2)]+d[len(d)//2*2:]
R=lambda n: F.reduce(lambda d,_: L(d), range(n), [K(b'H'+B(j)) for j in range(n)])[0]
print(R(5).hex())"` -/
theorem root5_kat : (dataRoot (blks 5)).toList =
    hex "b2271079ecba02c30b299a5659f8b64cad48f697d2c565a754cfede0427a9420" := by
  rw [← dataRootF_eq]
  decide +kernel

/-- Six blocks: an even first level, then an odd one: the node of the last two blocks is carried up.
`python3 -I -c "import sys, functools as F; sys.path.insert(0, 'harness')
from rfh.keccak import keccak256 as K; B=lambda j: bytes((32*j+i)%256 for i in range(32))
L=lambda d: [K(b'D'+d[i]+d[i+1]) for i in range(0,len(d)-1,2)]+d[len(d)//2*2:]
R=lambda n: F.reduce(lambda d,_: L(d), range(n), [K(b'H'+B(j)) for j in range(n)])[0]
print(R(6).hex())"` -/
theorem root6_kat : (dataRoot (blks 6)).toList =
    hex "259aa413be633639776254e69323bc335fc8647907e6b499ddbff7b98d92d460" := by
  rw [← dataRootF_eq]
  decide +kernel

/-- Seven blocks: the seventh hash is carried up one level, then paired with the node of the fifth
and sixth.
`python3 -I -c "import sys, functools as F; sys.path.insert(0, 'harness')
from rfh.keccak import keccak256 as K; B=lambda j: bytes((32*j+i)%256 for i in range(32))
L=lambda d: [K(b'D'+d[i]+d[i+1]) for i in range(0,len(d)-1,2)]+d[len(d)//2*2:]
R=lambda n: F.reduce(lambda d,_: L(d), range(n), [K(b'H'+B(j)) for j in range(n)])[0]
print(R(7).hex())"` -/
theorem root7_kat : (dataRoot (blks 7)).toList =
    hex "5387590c6b14b2b1cea975eeb354600cb4154a9c45a4ff17da5137526afc592b" := by
  rw [← dataRootF_eq]
  decide +kernel

/-- The statement of nine blocks (`n = 9`: the ninth hash is carried up three levels).
`python3 -I -c "import sys, functools as F; sys.path.insert(0, 'harness')
from rfh.keccak import keccak256 as K; B=lambda j: bytes((32*j+i)%256 for i in range(32))
L=lambda d: [K(b'D'+d[i]+d[i+1]) for i in range(0,len(d)-1,2)]+d[len(d)//2*2:]
R=lambda n: F.reduce(lambda d,_: L(d), range(n), [K(b'H'+B(j)) for j in range(n)])[0]
print(K(b'L'+R(9)+(9).to_bytes(8,'little')).hex())"` -/
theorem stmt9_kat : (leafStmt (dataRoot (blks 9)) 9).toList =
    hex "f6d213f1b8205192e8445bbbf22686a6d6ed97d214530d290572be8f6f9d400a" := by
  rw [← leafStmtF_eq, ← dataRootF_eq]
  decide +kernel

/-- `python3 -I -c "import sys; sys.path.insert(0, 'harness')
from rfh.keccak import keccak256 as K
h=bytes.fromhex('55c3ed43367f2313bd98059444f498d7ad3efb1aa34846e9543dde3a414085b1');
print(K(b'L'+h+(4).to_bytes(8,'little')).hex())"` (the root of `root4_kat`) -/
theorem leafStmt_kat :
    (leafStmt (ofHex "55c3ed43367f2313bd98059444f498d7ad3efb1aa34846e9543dde3a414085b1")
      4).toList =
      hex "954cd3e680062826d0744b03ef59dbf53a9e7d55d694c46a5627e45d67a6e45f" := by
  rw [← leafStmtF_eq]
  decide +kernel

/-- **A leaf statement and its witness**: the statement of `leafStmt_kat` is in the relation with
the four blocks of `root4_kat` as its witness, under every `acc` (the root and the count are the
ones the statement commits to). -/
theorem rel_root4 (acc : Digest → Signed → Bool) :
    Rel acc (ofHex "954cd3e680062826d0744b03ef59dbf53a9e7d55d694c46a5627e45d67a6e45f")
      (.leaf (blks 4)) := by
  rw [Rel, ← leafStmtF_eq, ← dataRootF_eq]
  decide +kernel

/-- `python3 -I -c "import sys; sys.path.insert(0, 'harness')
from rfh.keccak import keccak256 as K
a=bytes.fromhex('da513675c495534390e0dfb57a4b2d94b8ec604af01e1cacb5bfa117e4178b11');
b=bytes.fromhex('422927c492ce04e6a6ee85dac40f023ffabf0384da8d3a63e491fbf923fc2b9f');
print(K(b'N'+a+b).hex())"` (two digests: the items of the earlier seed leaf) -/
theorem nodeStmt_kat :
    (nodeStmt (ofHex "da513675c495534390e0dfb57a4b2d94b8ec604af01e1cacb5bfa117e4178b11")
      (ofHex "422927c492ce04e6a6ee85dac40f023ffabf0384da8d3a63e491fbf923fc2b9f")).toList =
      hex "955f38142d22184c40620a09850718e312df8622264ea4c6c7dc4983e8f5df9b" := by
  rw [← nodeStmtF_eq]
  decide +kernel

/-- `python3 -I -c "import sys; sys.path.insert(0, 'harness')
from rfh.keccak import keccak256 as K
h=bytes.fromhex('55c3ed43367f2313bd98059444f498d7ad3efb1aa34846e9543dde3a414085b1');
print(K(b'L'+h+(2**18).to_bytes(8,'little')).hex())"` (the root of `root4_kat` with the season's
count `n = 2^18`) -/
theorem leafStmt_season_kat :
    (leafStmt (ofHex "55c3ed43367f2313bd98059444f498d7ad3efb1aa34846e9543dde3a414085b1")
      (2 ^ 18)).toList =
      hex "7fff63bbbaa1db5254cd9f32f6d51d8c5c574eee5dd95abe753128700ea48e94" := by
  rw [← leafStmtF_eq]
  decide +kernel

/-- The season's `n = 2^18` in 8 little-endian bytes: its one set bit is in the third byte. -/
theorem enc64_season : enc64 (2 ^ 18) = [0, 0, 0x04, 0, 0, 0, 0, 0] := by decide

/-- `enc64` writes 8 bytes, low byte first. -/
theorem enc64_kat : enc64 0x0807060504030201 = [1, 2, 3, 4, 5, 6, 7, 8] := by decide

/-- `python3 -I -c "import sys; sys.path.insert(0, 'harness')
from rfh.keccak import keccak256 as K
print(K(b'L'+bytes(32)+(0).to_bytes(8,'little')).hex())"`: the statement of no block, the zero
root and the count `0` (`dataRoot []` is the zero digest). -/
theorem leafStmt_empty_kat : (leafStmt (dataRoot []) 0).toList =
    hex "e5cccee57d4d4929ba748848efc9a66adafaade38cc37f8942d5bd5222a53b41" := by
  rw [← leafStmtF_eq, ← dataRootF_eq]
  decide +kernel

/-- **At `n = 0` the statement is public**: `leafStmt zero 0` is in the relation with `[]`, under
every `acc`. Harmless because the runner draws `n` with `1 ≤ n`. -/
theorem leaf_empty (acc : Digest → Signed → Bool) :
    Rel acc (leafStmt (Vector.replicate 32 0) 0) (.leaf []) := ⟨Nat.zero_le _, rfl⟩

/-- **The empty statement's one witness**: a leaf witness of no block witnesses only
`leafStmt zero 0`. -/
theorem leaf_empty_unique (acc : Digest → Signed → Bool) {c : Digest}
    (h : Rel acc c (.leaf [])) : c = leafStmt (Vector.replicate 32 0) 0 := h.2

/-! ## Tags -/

/-- **Tags separate**: the eight tags are distinct bytes, and each hash input of the contract
starts with its own tag (the leaf item, the data node, the leaf and node statements, the trace
digest, the WOTS chain step and leaf, the signature's Merkle node). -/
theorem tags_separate (d h c₁ c₂ x : Digest) (n j i s : ℕ) (tr : Trace) (ends : List Digest) :
    [tagItem, tagData, tagLeaf, tagNode, tagTrace, tagWots, tagWotsLeaf, tagSigNode].Nodup ∧
    leafItem d = keccakDigest (tagItem :: d.toList) ∧
    dataNode c₁ c₂ = keccakDigest (tagData :: (c₁.toList ++ c₂.toList)) ∧
    leafStmt h n = keccakDigest (tagLeaf :: (h.toList ++ enc64 n)) ∧
    nodeStmt c₁ c₂ = keccakDigest (tagNode :: (c₁.toList ++ c₂.toList)) ∧
    traceDigest tr = keccakDigest (tagTrace :: traceBytes tr) ∧
    wotsStep j i s x = keccakDigest (tagWots :: (enc64 j ++ [i.toUInt8, s.toUInt8] ++ x.toList)) ∧
    wotsLeaf j ends = keccakDigest (tagWotsLeaf :: (enc64 j ++ ends.flatMap Vector.toList)) ∧
    sigNode c₁ c₂ = keccakDigest (tagSigNode :: (c₁.toList ++ c₂.toList)) :=
  ⟨by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Leaves -/

/-- A leaf of exactly `leafCap` blocks is in the relation. -/
theorem leaf_at_leafCap (acc : Digest → Signed → Bool) {xs : List Digest}
    (h : xs.length = leafCap) : Rel acc (leafStmt (dataRoot xs) xs.length) (.leaf xs) :=
  ⟨h.le, rfl⟩

/-- **The leaf bound is `2^20`**: a leaf of exactly `2^20` blocks is in the relation, under every
`acc` (symbolic). -/
theorem leaf_at_2pow20 (acc : Digest → Signed → Bool) {xs : List Digest}
    (h : xs.length = 2 ^ 20) : Rel acc (leafStmt (dataRoot xs) xs.length) (.leaf xs) :=
  ⟨h.trans_le (by decide), rfl⟩

/-- **Over the leaf bound**: a leaf of `leafCap + 1` blocks is not in the relation. -/
theorem leaf_over_leafCap (acc : Digest → Signed → Bool) {xs : List Digest} (c : Digest)
    (h : xs.length = leafCap + 1) : ¬ Rel acc c (.leaf xs) :=
  fun hR => absurd hR.1 (by omega)

/-- **The leaf bound is `2^20`, not more**: a leaf of `2^20 + 1` blocks is not in the relation,
under every `acc` (`tests/mutation`'s `rel-leafcap-2^21`). -/
theorem leaf_over_2pow20 (acc : Digest → Signed → Bool) {xs : List Digest} (c : Digest)
    (h : xs.length = 2 ^ 20 + 1) : ¬ Rel acc c (.leaf xs) :=
  fun hR => absurd (h ▸ hR.1) (by decide)

/-- The statement committing to the block itself is not the statement of its leaf (`s0`, one
block): the root is the block's hash. -/
theorem block_ne_root : leafStmt s0 1 ≠ leafStmt (dataRoot [s0]) 1 := by
  rw [← leafStmtF_eq, ← dataRootF_eq]
  decide +kernel

/-- **Wrong root**: the leaf statement committing to the block itself is not witnessed by the
block, under every `acc`. -/
theorem wrong_root (acc : Digest → Signed → Bool) : ¬ Rel acc (leafStmt s0 1) (.leaf [s0]) :=
  fun h => block_ne_root h.2

/-- **Wrong block**: the statement of the leaf `[s0]` is not witnessed by `[s1]`, under every
`acc`. -/
theorem wrong_block (acc : Digest → Signed → Bool) :
    ¬ Rel acc (leafStmt (dataRoot [s0]) 1) (.leaf [s1]) := fun h => by
  revert h; rw [Rel, ← leafStmtF_eq, ← dataRootF_eq]
  decide +kernel

/-- **Wrong count**: the root of `[s0, s1]` committed with the count `1` is not witnessed by
`[s0, s1]`, under every `acc` (the statement binds the number of blocks). -/
theorem wrong_count (acc : Digest → Signed → Bool) :
    ¬ Rel acc (leafStmt (dataRoot [s0, s1]) 1) (.leaf [s0, s1]) := fun h => by
  revert h; rw [Rel, ← leafStmtF_eq, ← dataRootF_eq]
  decide +kernel

/-- **One block dropped**: the statement of `[s0, s1]` is not witnessed by `[s0]`, under every
`acc`. -/
theorem dropped_block (acc : Digest → Signed → Bool) :
    ¬ Rel acc (leafStmt (dataRoot [s0, s1]) 2) (.leaf [s0]) := fun h => by
  revert h; rw [Rel, ← leafStmtF_eq, ← dataRootF_eq]
  decide +kernel

/-- **One block added**: the statement of `[s0]`, and its root committed with the count `2`, are
not witnessed by `[s0, s1]`, under every `acc`. -/
theorem extra_block (acc : Digest → Signed → Bool) :
    ¬ Rel acc (leafStmt (dataRoot [s0]) 1) (.leaf [s0, s1]) ∧
      ¬ Rel acc (leafStmt (dataRoot [s0]) 2) (.leaf [s0, s1]) := by
  constructor <;> rw [Rel, ← leafStmtF_eq, ← dataRootF_eq] <;> decide +kernel

/-- **Two blocks swapped**: the statement of `[s0, s1]` is not witnessed by `[s1, s0]`, under
every `acc` (the data tree is ordered). -/
theorem swapped_blocks (acc : Digest → Signed → Bool) :
    ¬ Rel acc (leafStmt (dataRoot [s0, s1]) 2) (.leaf [s1, s0]) := fun h => by
  revert h; rw [Rel, ← leafStmtF_eq, ← dataRootF_eq]
  decide +kernel

/-- **The carry-up is not a duplication**: the root of three blocks is not the root of the four
blocks with the last one repeated (an odd last digest is carried up unhashed, not paired with
itself). -/
theorem carry_not_duplicated : dataRoot (blks 3) ≠ dataRoot (blks 3 ++ [blk 2]) := by
  rw [← dataRootF_eq]
  decide +kernel

/-- The bytewise XOR of two digests (the earlier seed leaf's combination of its hashes). -/
def xor2 (a b : Digest) : Digest := Vector.zipWith (· ^^^ ·) a b

/-- **The root is not the XOR of the block hashes** (`[s0, s1]`). -/
theorem root_not_xor : dataRoot [s0, s1] ≠ xor2 (leafItem s0) (leafItem s1) := by
  rw [← dataRootF_eq, ← leafItemF_eq]
  decide +kernel

/-- **The XOR's statement is rejected**: the statement committing to the XOR of the two block
hashes is not witnessed by the two blocks, under every `acc`. -/
theorem xor_rejected (acc : Digest → Signed → Bool) :
    ¬ Rel acc (leafStmt (xor2 (leafItem s0) (leafItem s1)) 2) (.leaf [s0, s1]) := fun h => by
  revert h; rw [Rel, ← leafStmtF_eq, ← dataRootF_eq, ← leafItemF_eq]
  decide +kernel

/-! ## Signed leaf proofs -/

/-- The witness-sending signed proof of the leaf `xs`: the proof, the empty trace, and the
reference signature with key `j` of the empty trace's digest. -/
def leafSigned (sk : ℕ → ℕ → Digest) (j : ℕ) (xs : List Digest) : Signed :=
  ⟨encode (.leaf xs), [], Signer.sign sk j (traceDigest [])⟩

theorem leafSigned_sig (sk : ℕ → ℕ → Digest) {j : ℕ} (hj : j < 2 ^ sigHeight) (xs : List Digest) :
    SigOk (Signer.pk sk) (traceDigest (leafSigned sk j xs).tr) (leafSigned sk j xs).σ = true :=
  Signer.sigOk_sign sk j hj _

/-- `acc` of a signed leaf proof: the leaf proof is accepted for the statement. -/
theorem acc_leafSigned_iff (sk : ℕ → ℕ → Digest) {j : ℕ} (hj : j < 2 ^ sigHeight) (c : Digest)
    {xs : List Digest} (hn : xs.length < 2 ^ 59) :
    submission.acc (Signer.pk sk) c (leafSigned sk j xs) =
      (decide (xs.length ≤ leafCap) && decide (c = leafStmt (dataRoot xs) xs.length)) := by
  rw [acc_eq, leafSigned_sig sk hj, ← check_leaf' c (hn.trans (by decide))]
  simp [leafSigned, size_encode_leaf]
  omega
where
  check_leaf' (c : Digest) {xs : List Digest} (hn : xs.length < 2 ^ 64) :
      check (Signer.pk sk) c (encode (.leaf xs)) =
        (decide (xs.length ≤ leafCap) && decide (c = leafStmt (dataRoot xs) xs.length)) := by
    rw [check_eq, decode_encode (.leaf xs) hn]; simp

/-- **A signed leaf proof is accepted** under the signer's key. -/
theorem acc_leafSigned (sk : ℕ → ℕ → Digest) {j : ℕ} (hj : j < 2 ^ sigHeight) (xs : List Digest)
    (hn : xs.length ≤ leafCap) :
    submission.acc (Signer.pk sk) (leafStmt (dataRoot xs) xs.length) (leafSigned sk j xs) =
      true := by
  rw [acc_leafSigned_iff sk hj _ (hn.trans_lt (by decide))]; simp [hn]

/-! ## Nodes -/

/-- **A node with two signed leaf children** is in the relation under the signer's key, for
every secret function and two leaves' data of up to `leafCap` blocks. -/
theorem node_of_two_leaves (sk : ℕ → ℕ → Digest) (xs₁ xs₂ : List Digest)
    (h₁ : xs₁.length ≤ leafCap) (h₂ : xs₂.length ≤ leafCap) :
    Rel (submission.acc (Signer.pk sk))
      (nodeStmt (leafStmt (dataRoot xs₁) xs₁.length) (leafStmt (dataRoot xs₂) xs₂.length))
      (.node (leafStmt (dataRoot xs₁) xs₁.length) (leafStmt (dataRoot xs₂) xs₂.length)
        (leafSigned sk 0 xs₁) (leafSigned sk 1 xs₂)) :=
  ⟨rfl, acc_leafSigned sk (by decide) xs₁ h₁, acc_leafSigned sk (by decide) xs₂ h₂⟩

/-- The node control with the reference derivation of the WOTS chain starts, for every signer
seed. -/
theorem node_of_two_leaves_ref (seed : List UInt8) (xs₁ xs₂ : List Digest)
    (h₁ : xs₁.length ≤ leafCap) (h₂ : xs₂.length ≤ leafCap) :
    Rel (submission.acc (Signer.pk (Signer.chainStart seed)))
      (nodeStmt (leafStmt (dataRoot xs₁) xs₁.length) (leafStmt (dataRoot xs₂) xs₂.length))
      (.node (leafStmt (dataRoot xs₁) xs₁.length) (leafStmt (dataRoot xs₂) xs₂.length)
        (leafSigned (Signer.chainStart seed) 0 xs₁)
        (leafSigned (Signer.chainStart seed) 1 xs₂)) :=
  node_of_two_leaves _ xs₁ xs₂ h₁ h₂

/-- **The node clause needs its statement**: whatever the children, a statement other than their
`nodeStmt` is not in the relation. -/
theorem node_needs_statement (acc : Digest → Signed → Bool) {c c₁ c₂ : Digest} (p₁ p₂ : Signed)
    (h : c ≠ nodeStmt c₁ c₂) : ¬ Rel acc c (.node c₁ c₂ p₁ p₂) := fun hR => h hR.1

/-- The correct leaf digest of the one block `s0`, and the wrong one (committing to `s0`). -/
abbrev cOk : Digest := leafStmt (dataRoot [s0]) 1
abbrev cBad : Digest := leafStmt s0 1

/-- **Statement mismatch** (an instance): two accepted children under their own leaf statement,
which is not their `nodeStmt`, under every `acc`. -/
theorem node_statement_mismatch (acc : Digest → Signed → Bool) (p₁ p₂ : Signed) :
    ¬ Rel acc cOk (.node cOk cOk p₁ p₂) := by
  refine node_needs_statement _ _ _ ?_
  rw [cOk, ← leafStmtF_eq, ← dataRootF_eq, ← nodeStmtF_eq]
  decide +kernel

theorem acc_bad (sk : ℕ → ℕ → Digest) {j : ℕ} (hj : j < 2 ^ sigHeight) :
    submission.acc (Signer.pk sk) cBad (leafSigned sk j [s0]) = false := by
  rw [acc_leafSigned_iff sk hj _ (by decide)]
  simp [show cBad ≠ leafStmt (dataRoot [s0]) 1 from block_ne_root]

/-- **A node whose first child is rejected**: validly signed, but its proof is for another
statement. -/
theorem first_child_rejected (sk : ℕ → ℕ → Digest) :
    ¬ Rel (submission.acc (Signer.pk sk)) (nodeStmt cBad cOk)
      (.node cBad cOk (leafSigned sk 0 [s0]) (leafSigned sk 1 [s0])) := fun h =>
  absurd h.2.1 (by rw [acc_bad sk (by decide)]; decide)

/-- **A node whose second child is rejected.** -/
theorem second_child_rejected (sk : ℕ → ℕ → Digest) :
    ¬ Rel (submission.acc (Signer.pk sk)) (nodeStmt cOk cBad)
      (.node cOk cBad (leafSigned sk 0 [s0]) (leafSigned sk 1 [s0])) := fun h =>
  absurd h.2.2 (by rw [acc_bad sk (by decide)]; decide)

/-- **A child signed under another key is rejected**, under every key other than the signer's. -/
theorem child_other_key (sk : ℕ → ℕ → Digest) {vk : Digest} (hvk : vk ≠ Signer.pk sk)
    (c₁ c₂ : Digest) (xs : List Digest) (p₂ : Signed) :
    ¬ Rel (submission.acc vk) (nodeStmt c₁ c₂) (.node c₁ c₂ (leafSigned sk 0 xs) p₂) := fun h => by
  have hs := Controls.Signature.sigOk_other_key (leafSigned_sig sk (j := 0) (by decide) xs) hvk
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

/-- **The query cap is the service's `2^20` bytes**: every submission's `acc` rejects a trace whose
query has `2^20 + 1` bytes, whatever its answer, proof and signature. -/
theorem acc_query_over_2pow20 (S : Submission) (vk c a : Digest) (π : Proof) (σ : Sig) :
    S.acc vk c ⟨π, [(⟨Array.replicate (2 ^ 20 + 1) 0⟩, a)], σ⟩ = false :=
  acc_query_over_cap S vk c _ (List.mem_singleton_self _)
    (show queryCap < (Array.replicate _ _).size by rw [Array.size_replicate]; decide)

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

/-- A tree of `k` levels over one leaf (the one block `s0`, a 48-byte proof): the digest. -/
def deepStmt : ℕ → Digest
  | 0 => leafStmt (dataRoot [s0]) 1
  | k + 1 => nodeStmt (deepStmt k) (deepStmt k)

/-- A tree of `k` levels over one leaf: the witness-sending proof, children signed with key `0`
of `sk`. -/
def deepProof (sk : ℕ → ℕ → Digest) : ℕ → Proof
  | 0 => encode (.leaf [s0])
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
    exact check_encode (show Rel _ _ (.leaf [s0]) from ⟨by decide, rfl⟩)
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
