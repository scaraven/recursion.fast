/-
# Contract: the recursion tree's root (a specification of the runner)                (TRUSTED)

The root digest of `2^r` leaves, computed from the
leaf digests by hashing up (`nodeStmt`, adjacent pairs, level by level), never from a digest a
prover supplies. No prover is benchmarked on a tree, and the runner computes no tree root: the
benchmark is one stream of `nodeStmt` steps (`c_1 = L_1`, `c_i = nodeStmt c_(i-1) L_i`), which
the library's stream walk covers (`Library/Compose.lean`, `walkStream`, `compose_prob_stream`).
The tree is the setting of the library's tree composition theorem (`walk`, `compose_prob`) and
of its known-answer control (`Controls/Tree.lean`, `treeRoot_kat`, against a value computed with
the harness's Python Keccak-256 reference).

**Convention.** The tree composition theorem has a power of two of leaves. `treeRoot` is total:
on an odd level the last digest is carried up unhashed, a single digest is its own root, and the
empty list has the zero digest. The theorem uses none of these cases but the single digest.
-/
import RecursionFast.Contract.Relation
import Mathlib.Logic.Function.Iterate

namespace RecursionFast

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
