/-
# Contract: the recursion tree's root (a specification of the runner)                (TRUSTED)

DESIGN-v3 §5.1. The benchmark proves `2^r` leaves; the runner computes the root digest from the
leaf digests by hashing up (`nodeStmt`, adjacent pairs, level by level), never from a digest the
prover supplies, and checks the root proof against it. The runner's Python `treeRoot` is tested
against this definition by a known-answer control (`Controls/Tree.lean`).

**Convention (V3-S1-A8).** The runner always has a power of two of leaves. `treeRoot` is total:
on an odd level the last digest is carried up unhashed, a single digest is its own root, and the
empty list has the zero digest. None of these cases occurs in a benchmark run.
-/
import RecursionFast.Contract.Relation

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
