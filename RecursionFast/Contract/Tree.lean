/-
# Contract: the stream's statement (the runner's) and the tree's root (the library's) (TRUSTED)

**The stream's statement (the benchmark).** The benchmark is one stream of `M` steps (plain IVC)
over the leaf values `h_1 … h_M` of size `n`, oldest first (`h_i = dataRoot xs_i`, the root of
step `i`'s data, `Relation.lean`): `c_1 = L_1`, `c_i = nodeStmt c_(i-1) L_i` with
`L_i = leafStmt h_i n` (`streamStmt`, the digest of the last step; each `c_i` is `streamStmt` of
the first `i` leaves). The runner computes these digests from its own data
(`harness/rfh/digest.py`, `stream_statements`), never from a digest a prover supplies; a
known-answer control pins the two together (`Controls/Tree.lean`, `streamStmt_kat`). The library's
stream walk is stated over it (`Library/Compose.lean`, `walkStream`, `compose_prob_stream`).

**The tree's root.** The root digest of `2^r` leaves, computed from the leaf digests by hashing
up (`nodeStmt`, adjacent pairs, level by level). No prover is benchmarked on a tree, and the
runner computes no tree root. The tree is the setting of the library's tree composition theorem
(`walk`, `compose_prob`) and of its known-answer control (`Controls/Tree.lean`, `treeRoot_kat`,
against a value computed with the harness's Python Keccak-256 reference).

**Convention.** The tree composition theorem has a power of two of leaves. `treeRoot` is total:
on an odd level the last digest is carried up unhashed, a single digest is its own root, and the
empty list has the zero digest. The theorem uses none of these cases but the single digest. So
the root does not commit to the number of leaves (`treeRoot [a, b] = treeRoot [nodeStmt a b]`,
`treeRoot [a, b, c] = treeRoot [nodeStmt a b, c]`), which is harmless where it is used: the tree
composition fixes `2^r` leaves, and nothing in `Certificate.lean` or `Security.lean` uses
`treeRoot`.
`streamStmt` does commit to its length and to `n` (for `n < 2^64`: `enc64` keeps the low 64 bits,
so `n` and `n + 2^64` give one statement): two different streams with one statement give a Keccak
collision (unwinding ends at a leaf's statement against a node's). `streamStmt` of no
leaf is the zero digest; the benchmark's streams have `M` leaves, `M` of `harness/season.toml`.
-/
import RecursionFast.Contract.Relation
import Mathlib.Logic.Function.Iterate

namespace RecursionFast

/-- **The stream's statement** over the leaf values `hs` of size `n`, oldest first, as the runner
computes it: `c_1 = leafStmt h_1 n`, `c_i = nodeStmt c_(i-1) (leafStmt h_i n)`; the zero digest
for no leaf. -/
def streamStmt (n : ℕ) : List Digest → Digest
  | [] => Vector.replicate 32 0
  | h :: hs => hs.foldl (fun c h => nodeStmt c (leafStmt h n)) (leafStmt h n)

/-- One level up: adjacent digests paired by `nodeStmt`; an odd last digest is carried up. -/
def treeLevel : List Digest → List Digest
  | c₁ :: c₂ :: cs => nodeStmt c₁ c₂ :: treeLevel cs
  | cs => cs

/-- **The root** of the tree over the leaf digests `cs`: `treeLevel` until one digest remains
(`|cs|` levels always suffice and one digest is a fixed point, `Library/Tree.lean`); the zero
digest if `cs = []`. -/
def treeRoot (cs : List Digest) : Digest :=
  (treeLevel^[cs.length] cs).headD (Vector.replicate 32 0)

end RecursionFast
