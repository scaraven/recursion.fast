/-
# Controls: the tree root (`Contract/Tree.lean`), positive and negative           (DESIGN-v3 §5.1)

Positive, for every digests (by `rfl`, no hash is evaluated):
* `treeRoot_one`, `treeRoot_two`, `treeRoot_four`: one digest is its own root; two and four
  digests hash up pairwise, left to right, level by level (`nodeStmt`).
* `treeRoot_eight`: three levels.
* `treeRoot_three`, `treeRoot_nil`: the conventions for an odd level (the last digest is carried
  up) and the empty list (the zero digest), which no benchmark run uses.
* `treeRoot_recursive`: for every list, the root of two or more digests is the root of the level
  above (`Library/Tree.lean`, which also proves that `|cs|` levels suffice).
Known answer (`decide +kernel`, 6 compressions): `treeRoot_kat`, the root of the four digests
`00…00`, `01…01`, `02…02`, `03…03`, against `hashlib`: the runner's Python `treeRoot` is tested
against this value (Stage S3).

Negative: `treeRoot_order`: the order of the leaves matters (`[d₀, d₁]` and `[d₁, d₀]`).
-/
import RecursionFast.Library.Tree
import RecursionFast.Controls.Blake2s

namespace RecursionFast.Controls.Tree
open RecursionFast
open RecursionFast.Controls.Blake2s (hex)

theorem treeRoot_nil : treeRoot [] = Vector.replicate 32 0 := rfl

theorem treeRoot_one (a : Digest) : treeRoot [a] = a := rfl

theorem treeRoot_two (a b : Digest) : treeRoot [a, b] = nodeStmt a b := rfl

theorem treeRoot_three (a b c : Digest) : treeRoot [a, b, c] = nodeStmt (nodeStmt a b) c := rfl

theorem treeRoot_four (a b c d : Digest) :
    treeRoot [a, b, c, d] = nodeStmt (nodeStmt a b) (nodeStmt c d) := rfl

theorem treeRoot_eight (a b c d e f g h : Digest) :
    treeRoot [a, b, c, d, e, f, g, h] =
      nodeStmt (nodeStmt (nodeStmt a b) (nodeStmt c d)) (nodeStmt (nodeStmt e f) (nodeStmt g h)) :=
  rfl

theorem treeRoot_recursive (a b : Digest) (cs : List Digest) :
    treeRoot (a :: b :: cs) = treeRoot (treeLevel (a :: b :: cs)) := treeRoot_cons_cons a b cs

/-- The digest `i i … i`. -/
def dd (i : UInt8) : Digest := Vector.replicate 32 i

/-- `python3 -c "import hashlib; H=lambda b: hashlib.blake2s(b).digest(); d=[bytes([i])*32 for i
in range(4)]; N=lambda a,b: H(b'N'+a+b); print(N(N(d[0],d[1]),N(d[2],d[3])).hex())"` -/
theorem treeRoot_kat : (treeRoot [dd 0, dd 1, dd 2, dd 3]).toList =
    hex "818de83143463644aad53721a9656a63e41fc22c09ce5c2569bef5b0239010c4" := by decide +kernel

/-- **The order of the leaves matters.** -/
theorem treeRoot_order : treeRoot [dd 0, dd 1] ≠ treeRoot [dd 1, dd 0] := by decide +kernel

end RecursionFast.Controls.Tree
