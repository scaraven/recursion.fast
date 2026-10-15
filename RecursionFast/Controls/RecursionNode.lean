/-
# Controls: recursion (`Contract/Recursion.lean`, DESIGN §5), a node child; satisfiability

On the control protocol `cmpToy` at arity 2, with the data of `Controls/RecursionData.lean`. Builds
in parallel with `Controls/Recursion.lean`. The kernel evaluates `nodeRuns` (the aggregate
statement `xR` and the node child's `NARG` run), `keyRuns` (the second key) and `completeRuns`
once; `aggOK` is derived through the library's lemmas (the data file's `#guard`s evaluate every
`aggOK` here directly).

* `aggOK_node_child` (positive): the level-2 node `nwR`, whose first child is the two-leaf node's
  statement `xN` (tag `node`, its honest tape, same keys) and whose second child is the leaf `x0`,
  at its aggregate statement `xR` (`nodeStmt_kat_R`: the Python reference's).
* `node_child_d0`, `node_child_d1` (negatives): a node child whose `d0` (resp. `d1`) differs from
  the parent's in one bit. Its own tape is accepted (`#guard` in the data file), the parent's
  statement is its aggregate statement and the keys have 32-byte roots, so the key check of
  `child` alone rejects it. No hash is evaluated: the parent's `d0`, `d1` are the key digest
  (`nodeStmt_slot`, `digestToSlot_kat`).
* Distinct keys (S5-m7): `distinct_keys` (positive: recursion key `vkc2`, leaf key `vkK`, leaf
  children proved under `vkK`) and `leaf_under_vkC` (negative: leaf children proved under `vkc2`
  only). A `child` that verified leaves under `vkC` would swap both verdicts (`keyRuns.2`).
* `toy_sat_via_complete`: `aggOK_sat_of_complete` is not vacuous. `cmpToy`'s honest compiled
  prover outputs `tape2` and the IOP verifier accepts its Fiat–Shamir transcript (`completeRuns`),
  so the general theorem yields the node of `x0`, `x0` with the indexer's keys.
-/
import RecursionFast.Controls.RecursionData

namespace RecursionFast.Controls.Recursion
open RecursionFast RecursionFast.Controls.Compile

/-! ## Kernel evaluations -/

/-- The level-2 aggregate statement, and the node child's tape accepted under the key. -/
theorem nodeRuns :
    nodeStmt cfg2 vkc2 vkc2 .node .leaf xN x0 = xR ∧ NARG cfg2 cmpToy vkc2 xN tapeXN = true := by
  decide +kernel

/-- `tapeK` is accepted under `vkK` and not under `vkc2`; `tape2` is not accepted under `vkK`. -/
theorem keyRuns : NARG cfg2 cmpToy vkK x0 tapeK = true ∧
    NARG cfg2 cmpToy vkc2 x0 tapeK = false ∧ NARG cfg2 cmpToy vkK x0 tape2 = false := by
  decide +kernel

/-- The honest compiled prover outputs `tape2`, and the IOP verifier accepts its Fiat–Shamir
transcript. -/
theorem completeRuns : prove cfg2 cmpToy L0 x0 [] = some tape2 ∧
    cmpToy.specVerifier (L0, x0) (fsTranscript cfg2 cmpToy L0 x0 []) = some () := by
  decide +kernel

/-! ## A node child -/

/-- Known answer: the aggregate statement of `xN`, `x0` is the Python reference's `xR`. -/
theorem nodeStmt_kat_R : nodeStmt cfg2 vkc2 vkc2 .node .leaf xN x0 = xR := nodeRuns.1

/-- **Positive**: a node with a node child and a leaf child is accepted. -/
theorem aggOK_node_child : aggOK cfg2 cmpToy xR nwR = true := by
  rw [← nodeStmt_kat_R]
  refine (aggOK_nodeStmt_iff cfg2 cmpToy nwR).mpr ⟨vkc2_root, vkc2_root, ?_, runs.1⟩
  change child cfg2 cmpToy vkc2 vkc2 (nodeStmt cfg2 vkc2 vkc2 .node .leaf xN x0) .node xN tapeXN =
    true
  simp only [child, Bool.and_eq_true, decide_eq_true_eq, nodeStmt_slot, digestToSlot_kat,
    nodeRuns.2, and_true]
  decide

/-- A node child with another `d0` is rejected. -/
theorem node_child_d0 :
    aggOK cfg2 cmpToy (nodeStmt cfg2 vkc2 vkc2 .node .leaf xD0 x0) nwD0 = false :=
  Bool.eq_false_iff.mpr fun h => by
    have h0 := (((aggOK_iff cfg2 cmpToy _ _).mp h).2.2.2.2.2.2.2.1 rfl).1
    exact absurd (h0.trans ((nodeStmt_slot ..).1.trans digestToSlot_kat)) (by decide)

/-- A node child with another `d1` is rejected. -/
theorem node_child_d1 :
    aggOK cfg2 cmpToy (nodeStmt cfg2 vkc2 vkc2 .node .leaf xD1 x0) nwD1 = false :=
  Bool.eq_false_iff.mpr fun h => by
    have h1 := (((aggOK_iff cfg2 cmpToy _ _).mp h).2.2.2.2.2.2.2.1 rfl).2.1
    exact absurd (h1.trans ((nodeStmt_slot ..).2.1.trans digestToSlot_kat)) (by decide)

/-! ## Distinct keys (S5-m7) -/

/-- **Positive**: leaf children proved under the leaf key `vkK` are accepted, with the recursion
key `vkc2`. -/
theorem distinct_keys :
    aggOK cfg2 cmpToy (nodeStmt cfg2 vkc2 vkK .leaf .leaf x0 x0) nwK = true :=
  aggOK_leaves cfg2 cmpToy vkc2 vkK vkc2_root x0 x0 tapeK tapeK keyRuns.1 keyRuns.1

/-- **Negative**: leaf children proved under the recursion key only are rejected. -/
theorem leaf_under_vkC :
    aggOK cfg2 cmpToy (nodeStmt cfg2 vkc2 vkK .leaf .leaf x0 x0) nwKC = false := by
  simp only [aggOK, nwKC, child, keyRuns.2.2, Bool.and_false]

/-! ## `aggOK_sat_of_complete` is not vacuous -/

/-- The general satisfiability theorem, instantiated: the node of `x0`, `x0` with the indexer's
keys is accepted at its aggregate statement. -/
theorem toy_sat_via_complete :
    aggOK cfg2 cmpToy
      (nodeStmt cfg2 (index cfg2 cmpToy L0) (index cfg2 cmpToy L0) .leaf .leaf x0 x0)
      ⟨index cfg2 cmpToy L0, index cfg2 cmpToy L0, .leaf, .leaf, x0, x0, tape2, tape2⟩ = true :=
  aggOK_sat_of_complete cfg2 cmpToy L0 L0 x0 x0 [] [] tape2 tape2 completeRuns.1 completeRuns.1
    completeRuns.2 completeRuns.2

end RecursionFast.Controls.Recursion
