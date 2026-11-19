/-
# Controls: the stream's statement and the tree root (`Contract/Tree.lean`), positive and negative

Positive, for every digests (by `rfl`, no hash is evaluated):
* `treeRoot_one`, `treeRoot_two`, `treeRoot_four`: one digest is its own root; two and four
  digests hash up pairwise, left to right, level by level (`nodeStmt`).
* `treeRoot_eight`: three levels.
* `treeRoot_three`, `treeRoot_nil`: the conventions for an odd level (the last digest is carried
  up) and the empty list (the zero digest), which the tree composition theorem does not use.
* `treeRoot_recursive`: for every list, the root of two or more digests is the root of the level
  above (`Library/Tree.lean`, which also proves that `|cs|` levels suffice).
Known answer (`decide +kernel`, three permutations): `treeRoot_kat`, the root of the four digests
`00…00`, `01…01`, `02…02`, `03…03`, against the harness's Python Keccak-256 reference
(`harness/rfh/keccak.py`).

The stream's statement (`Contract/Tree.lean`, `streamStmt`): `streamStmt_three` (by `rfl`) is
the runner's loop `c_1 = L_1`, `c_i = nodeStmt c_(i-1) L_i` on three leaves; known answer
(`decide +kernel`, five permutations): `streamStmt_kat`, three leaves of size `1`, against the
runner's `stream_statements` (`harness/rfh/digest.py`).

Negative: `treeRoot_order`: the order of the leaves matters (`[d₀, d₁]` and `[d₁, d₀]`).
-/
import RecursionFast.Library.Tree
import RecursionFast.Controls.Hex

namespace RecursionFast.Controls.Tree
open RecursionFast
open RecursionFast.Controls.Keccak (hex)

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

/-- `python3 -I -c "import sys; sys.path.insert(0, 'harness'); from rfh.keccak import keccak256 as K;
d=[bytes([i])*32 for i in range(4)]; N=lambda a,b: K(b'N'+a+b)
print(N(N(d[0],d[1]),N(d[2],d[3])).hex())"` -/
theorem treeRoot_kat : (treeRoot [dd 0, dd 1, dd 2, dd 3]).toList =
    hex "9c071ef72d22fc6a33bccbddb23d1cab04714caede2494a44949da613deeeac9" := by decide +kernel

/-- **The stream's statement, known answer**: three leaves of values `dd 0`, `dd 1`, `dd 2` and
size `1`, against the runner's `stream_statements` (`harness/rfh/digest.py`):
`python3 -I -c "import sys; sys.path.insert(0, 'harness'); from rfh.digest import leaf_stmt,
stream_statements as T
print(T([leaf_stmt(bytes([i])*32, 1) for i in range(3)])[0][-1].hex())"` -/
theorem streamStmt_kat : (streamStmt 1 [dd 0, dd 1, dd 2]).toList =
    hex "d9e9b2db11177d30a49c8d7f687160c1f23ec4d2166a09939be3dd5c2c38817c" := by
  decide +kernel

/-- The stream's statement unfolds as the runner's loop: `c_3 = nodeStmt (nodeStmt L_1 L_2) L_3`. -/
theorem streamStmt_three (n : ℕ) (a b c : Digest) :
    streamStmt n [a, b, c] = nodeStmt (nodeStmt (leafStmt a n) (leafStmt b n)) (leafStmt c n) :=
  rfl

/-- **The order of the leaves matters.** -/
theorem treeRoot_order : treeRoot [dd 0, dd 1] ≠ treeRoot [dd 1, dd 0] := by decide +kernel

end RecursionFast.Controls.Tree
