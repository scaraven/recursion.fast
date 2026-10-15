/-
# Controls: recursion (`Contract/Recursion.lean`, DESIGN §5), two leaves, layouts, root check

On the control protocol `cmpToy` at arity 2, with the data of `Controls/RecursionData.lean`. The
kernel evaluates each hash-heavy fact once (`x1Runs`: three `NARG` runs on `x1`, which share the
sponge seed; `nodeStmt_kat`; `treeKat`; `rootRuns`); `aggOK` and `rootOK` are then derived through
the library's lemmas (`aggOK_leaves`, `aggOK_iff`, `rootOK_iff`, `treeRoot_two`), and the compiled
code evaluates every `aggOK` directly (`#guard`s of the data file). The level-2 node (a node
child), the key checks of a node child, distinct keys and the satisfiability through
`narg_complete` are in `Controls/RecursionNode.lean`, built in parallel.

* `aggOK_two_leaves` (positive): the two-leaf node `nwN` (children `x0`, `x1`, honest tapes) at
  its aggregate statement `xN`; `cmpToy_live`: `cmpToy` has the field `live` of a recursion entry
  at the indexer's keys (S5-A10).
* `nodeStmt_kat`: the aggregate statement of `x0`, `x1` is the Python reference's `xN` (slots: the
  key digest twice, `cfg2.hash.run` of `x0 ‖ x1` (BLAKE2s-256, S5-A8), the tags `(0, 0, 0, 0)`,
  zeros). `treeKat`: the statement tree of depth 2 over `x0, x1, x0, x1` is the Python reference's
  `xT`. `digestToSlot_kat` (data file): the key digest's bytes `0f4c678b…` as the limbs
  `0x30e57aba8b674c0f, …`.
* Negatives, each one change to `nwN` or `xN`: `child_tape_flip` (bit 0 of byte 40 of the second
  child's tape, a leaf of its oracle 1: the Merkle path fails), `wrong_d1` (bit 0 of `d1`),
  `nonzero_d3` (element 14, the third limb of `d3`, set to `1`), `nonzero_d4` (element 16, `d4`'s
  first limb): a node statement carries no free bits. `root33_rejected` (S5-m7): a recursion key
  with a 33-byte root. `mistag_rejected` (S5-m1): the level-2 node with its node child tagged
  leaf is rejected at `xR`, whose `d3` records the tags.
* Root check (S5-A12): `rootOK_xT` (positive: the tree over `x0, x1, x0, x1`); `rootOK_leaf` (a
  leaf statement is not the root); `rootOK_other_key` (another protocol key); `rootOK_odd` (three
  leaves make no tree).
* `Cbad` (no constraint; its decoder reads `π₂` from unconstrained cells): admissible, satisfied by
  `wGood` and `wBad`; `wGood` decodes to the accepted node, `wBad` to one whose `π₂` is 152 zero
  bytes, which `aggOK` rejects. So `Cbad` fails `sound` (`cbad_not_sound`) and is no entry.
* `unsat` (`Controls/Layout.lean`; `rel` unsatisfiable, admissible at every class): `sound` holds
  vacuously for every decoder, and `complete` fails for every decoder because `nwN` is accepted.
  So a vacuous `sound` does not make an entry (`unsat_no_entry`).
-/
import RecursionFast.Controls.RecursionData

namespace RecursionFast.Controls.Recursion
open RecursionFast RecursionFast.Controls.Compile

/-! ## Kernel evaluations -/

/-- `x1`'s honest tape is accepted; with a flipped leaf, or as 152 zero bytes, it is rejected. -/
theorem x1Runs : NARG cfg2 cmpToy vkc2 x1 tapeX1 = true ∧
    NARG cfg2 cmpToy vkc2 x1 (flip tapeX1 40) = false ∧
    NARG cfg2 cmpToy vkc2 x1 (List.replicate 152 0) = false := by
  decide +kernel

/-- Known answer: the aggregate statement of `x0`, `x1` is the Python reference's `xN`. -/
theorem nodeStmt_kat : nodeStmt cfg2 vkc2 vkc2 .leaf .leaf x0 x1 = xN := by decide +kernel

/-- Known answer: the node over two copies of `xN` is the Python reference's tree root `xT`. -/
theorem treeKat : nodeStmt cfg2 vkc2 vkc2 .node .node xN xN = xT := by decide +kernel

/-- The leaf statements of the depth-2 tree. -/
def leaves4 : List Stmt := [x0, x1, x0, x1]

/-- The root-check negatives. -/
theorem rootRuns : rootOK cfg2 cmpToy L0 L0 2 leaves4 x0 = false ∧
    rootOK cfg2 cmpToyK L0 L0 2 leaves4 xT = false ∧
    rootOK cfg2 cmpToy L0 L0 2 [x0, x1, x0] xT = false := by
  decide +kernel

/-! ## The two-leaf node -/

/-- **Positive**: the two-leaf node is accepted at its aggregate statement. -/
theorem aggOK_two_leaves : aggOK cfg2 cmpToy xN nwN = true :=
  nodeStmt_kat ▸ aggOK_leaves cfg2 cmpToy vkc2 vkc2 vkc2_root x0 x1 tape2 tapeX1 runs.1 x1Runs.1

/-- **`live` for `cmpToy`** (S5-A10; S1-A12(c)): a node keyed by the indexer for `C = L0` and
`L = L0` is accepted. It is the one field of a recursion entry that `cmpToy` can have without a
circuit. -/
theorem cmpToy_live : ∃ L x' nw, nw.vkC = index cfg2 cmpToy L0 ∧ nw.vkL = index cfg2 cmpToy L ∧
    aggOK cfg2 cmpToy x' nw = true :=
  ⟨L0, xN, nwN, index_eq.symm, index_eq.symm, aggOK_two_leaves⟩

/-- A flipped bit in the second child's tape rejects the node. -/
theorem child_tape_flip :
    aggOK cfg2 cmpToy xN ⟨vkc2, vkc2, .leaf, .leaf, x0, x1, tape2, flip tapeX1 40⟩ = false := by
  simp only [aggOK, child, x1Runs.2.1, Bool.and_false]

/-- A flipped bit in `d1` rejects the node. -/
theorem wrong_d1 : aggOK cfg2 cmpToy (bump xN 4) nwN = false :=
  Bool.eq_false_iff.mpr fun h =>
    absurd (((aggOK_iff cfg2 cmpToy _ _).mp h).2.1.trans digestToSlot_kat) (by decide)

/-- A nonzero limb 2 of `d3` (the tag slot's padding) rejects the node. -/
theorem nonzero_d3 : aggOK cfg2 cmpToy (fun i => if i = 14 then 1 else xN i) nwN = false :=
  Bool.eq_false_iff.mpr fun h =>
    absurd (congrFun ((aggOK_iff cfg2 cmpToy _ _).mp h).2.2.2.1 2) (by decide)

/-- A nonzero `d4` rejects the node. -/
theorem nonzero_d4 : aggOK cfg2 cmpToy (fun i => if i = 16 then 1 else xN i) nwN = false :=
  Bool.eq_false_iff.mpr fun h =>
    absurd (((aggOK_iff cfg2 cmpToy _ _).mp h).2.2.2.2.1 4 le_rfl) (by decide)

/-- A recursion key whose index root has 33 bytes rejects the node (S5-A1; the children and the
statement are fine). -/
theorem root33_rejected :
    aggOK cfg2 cmpToy (nodeStmt cfg2 vkC33 vkc2 .leaf .leaf x0 x1) nw33 = false :=
  Bool.eq_false_iff.mpr fun h =>
    absurd ((aggOK_iff cfg2 cmpToy _ _).mp h).2.2.2.2.2.1 (by decide)

/-- **Tags are bound** (S5-A11): the level-2 statement records a node child and a leaf child, so
the same children with the node child tagged leaf are rejected there. -/
theorem mistag_rejected : aggOK cfg2 cmpToy xR nwMis = false :=
  Bool.eq_false_iff.mpr fun h =>
    absurd (congrFun ((aggOK_iff cfg2 cmpToy _ _).mp h).2.2.2.1 0) (by decide)

/-! ## The root check -/

/-- **Positive**: `xT` is the root of the statement tree over `x0, x1, x0, x1`. -/
theorem rootOK_xT : rootOK cfg2 cmpToy L0 L0 2 leaves4 xT = true := by
  have e : treeRoot cfg2 vkc2 vkc2 2 leaves4 = some xT := by
    rw [leaves4, treeRoot_two, nodeStmt_kat, treeKat]
  exact (rootOK_iff cfg2 cmpToy L0 L0 2 leaves4 xT).mpr (index_eq ▸ e)

/-- A leaf statement is not the root. -/
theorem rootOK_leaf : rootOK cfg2 cmpToy L0 L0 2 leaves4 x0 = false := rootRuns.1

/-- The root check depends on the protocol's key. -/
theorem rootOK_other_key : rootOK cfg2 cmpToyK L0 L0 2 leaves4 xT = false := rootRuns.2.1

/-- Three leaves make no tree. -/
theorem rootOK_odd : rootOK cfg2 cmpToy L0 L0 2 [x0, x1, x0] xT = false := rootRuns.2.2

/-! ## `Cbad`: a layout that ignores `π₂` is not sound -/

/-- `Cbad` is admissible at class 20. -/
theorem cbad_admissible : Cbad.Admissible 20 := by decide

/-- Every one-row table with the statement in cells `0 … 31` satisfies `Cbad`. -/
theorem cbad_rel (x' : Stmt) (cs : List K) : Cbad.rel 20 x' (wOf x' cs) := by
  refine ⟨rfl, by simp [Cbad, wOf], by simp [Cbad, wOf, Gadget.holds, freeGadget], fun b => ?_,
    ⟨_, rfl, le_rfl, fun i => by simp⟩, by simp [Cbad, wOf]⟩
  simp [Cbad, wOf, traffic, BusKind.Balanced]

/-- `wGood` decodes to the accepted two-leaf node. -/
theorem decodeBad_good : decodeBad wGood = nwN := by
  simp only [decodeBad, nwN, NodeWitness.mk.injEq, true_and]; decide +kernel

/-- `wBad` decodes to the two-leaf node with 152 zero bytes as `π₂`. -/
theorem decodeBad_bad :
    decodeBad wBad = ⟨vkc2, vkc2, .leaf, .leaf, x0, x1, tape2, List.replicate 152 0⟩ := by
  simp only [decodeBad, NodeWitness.mk.injEq, true_and]; decide +kernel

/-- `Cbad` is satisfiable with an accepted node (`wGood`). -/
theorem cbad_good : Cbad.rel 20 xN wGood ∧ aggOK cfg2 cmpToy xN (decodeBad wGood) = true :=
  ⟨cbad_rel _ _, decodeBad_good ▸ aggOK_two_leaves⟩

/-- **`Cbad` is not sound**: `wBad` satisfies it, and its node is rejected. -/
theorem cbad_not_sound :
    ¬ ∀ x' w, Cbad.rel 20 x' w → aggOK cfg2 cmpToy x' (decodeBad w) = true := fun h => by
  simpa only [decodeBad_bad, aggOK, child, x1Runs.2.2, Bool.and_false, Bool.false_eq_true] using
    h xN wBad (cbad_rel _ _)

/-- `Cbad` with its decoder is not a recursion entry, although it is admissible. -/
theorem cbad_no_entry (e : RecursionEntry cmpToy cfg2) : ¬ (e.C = Cbad ∧ e.decode = decodeBad) :=
  fun ⟨hC, hd⟩ => cbad_not_sound fun x' w hw => hd ▸ e.sound x' w (hC ▸ hw)

/-! ## `unsat`: a vacuous `sound` is not an entry -/

/-- `sound` holds vacuously for `unsat` (`Controls/Layout.lean`: the gadget `1 = 0` on the public
chip; admissible at every class, `unsat_admissible_of`), with any decoder. -/
theorem unsat_sound (decode : List (Table K) → NodeWitness 1) :
    ∀ x' w, unsat.rel 20 x' w → aggOK cfg2 cmpToy x' (decode w) = true :=
  fun x' w hw => absurd hw (unsat_neg 20 x' w)

/-- `complete` fails for `unsat`, with any decoder: the two-leaf node is accepted. -/
theorem unsat_not_complete (decode : List (Table K) → NodeWitness 1) :
    ¬ ∀ x' nw, aggOK cfg2 cmpToy x' nw = true → ∃ w, unsat.rel 20 x' w ∧ decode w = nw :=
  fun h => let ⟨w, hw, _⟩ := h xN nwN aggOK_two_leaves; unsat_neg 20 xN w hw

/-- No recursion entry for `cmpToy` has the layout `unsat`, although it is admissible. -/
theorem unsat_no_entry (e : RecursionEntry cmpToy cfg2) : e.C ≠ unsat :=
  fun hC => unsat_not_complete e.decode fun x' nw h => hC ▸ e.complete x' nw h

end RecursionFast.Controls.Recursion
