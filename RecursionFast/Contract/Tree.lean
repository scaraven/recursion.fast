/-
# Contract: the recursion tree's root (a specification of the runner)                (TRUSTED)

DESIGN-v3 §5.1, **unchanged in v4** (V4-16). The root digest of `2^r` leaves, computed from the
leaf digests by hashing up (`nodeStmt`, adjacent pairs, level by level), never from a digest a
prover supplies. Since V4-A11 no prover is benchmarked on a tree (the benchmark is one stream of
`nodeStmt` steps); the runner still computes this root for the instance of the chain checker
that measures `T_triv,best`, and the library's composition theorem (`Library/Compose.lean`) is
stated over it. The runner's Python `treeRoot` is tested against this definition by a
known-answer control (`Controls/Tree.lean`).

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
