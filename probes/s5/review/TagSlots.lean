/-
S5 review probe: what `aggOK` alone does not bind, on `cmpToy` (whose recursion and leaf keys are
the same key `vkc2`, `Controls/RecursionData.lean`).
* `mistag`: the node statement `xN` presented as a **leaf** child (tag `leaf`, verified under
  `vkL`) is accepted at `xR`, the statement of the correctly tagged node `nwR`. Tags are witness;
  the contract does not bind them. In the benchmark `vkL ≠ vkC`, and what rejects a node statement
  under `vkL` is `L_chain`'s public chip (`LchainStmt.lean`), a benchmark property.
* `child_free_d3`: a node child whose own `d3` is nonzero (so it is no aggregate statement) is
  accepted at its parent's aggregate statement: `aggOK` does not pin a child's unused slots; the
  child's own `C_V` soundness (one level down) and the harness's statement tree do.
-/
import RecursionFast.Controls.RecursionData

namespace RecursionFast.Probes.S5Review
open RecursionFast RecursionFast.Controls.Compile RecursionFast.Controls.Recursion

/-- `xN` with element 12 (`d3`'s first limb) set to 1: `d0`, `d1` are still the key digest. -/
def xN3 : Stmt := fun i => if i = 12 then 1 else xN i

/-- The honest tape of `xN3` (`prove cfg2 cmpToy L0 xN3 []`, compiled). -/
def tapeN3 : Tape :=
  [0x60, 0x04, 0xbd, 0xd3, 0x0c, 0xf0, 0x06, 0xe9, 0x2e, 0xc9, 0x66, 0xda,
   0x6a, 0x25, 0x7f, 0x20, 0xf6, 0xf4, 0x2b, 0xa1, 0xca, 0xdd, 0xb6, 0xec,
   0xfb, 0x16, 0x2e, 0x2f, 0x69, 0x8a, 0x6a, 0xef, 0x4a, 0x6f, 0x21, 0xae,
   0x3d, 0xab, 0x13, 0xdd, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x36, 0xe2, 0xe9, 0x20, 0x27, 0x8b, 0x3c, 0x0c, 0x59, 0xfd, 0x9f, 0xa1,
   0x34, 0xc4, 0xa4, 0x10, 0x95, 0x4f, 0x51, 0xc3, 0xa3, 0x66, 0x34, 0x8b,
   0xec, 0x4f, 0xd5, 0x46, 0xa6, 0xbe, 0x98, 0xe9, 0x9a, 0x67, 0xa1, 0x1f,
   0x66, 0x4e, 0x66, 0x67, 0xfb, 0x36, 0x96, 0x36, 0x76, 0x9e, 0x53, 0xfa,
   0x9e, 0x90, 0x0a, 0x3d, 0x9f, 0xbd, 0xcd, 0x7b, 0x11, 0x30, 0x54, 0x38,
   0xc5, 0x37, 0x93, 0x70, 0x64, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x4a, 0x36, 0x50, 0xaa, 0xac, 0x41, 0xfb, 0x21, 0xac, 0x53, 0x74, 0xd5,
   0x56, 0x2e, 0x6c, 0x83, 0x69, 0x97, 0x32, 0x61, 0x09, 0x15, 0x85, 0xe9,
   0x5f, 0x41, 0xed, 0x6e, 0x35, 0xb8, 0x59, 0x5b]

#guard prove cfg2 cmpToy L0 xN3 [] = some tapeN3

theorem kRuns : nodeStmt cfg2 vkc2 vkc2 xN x0 = xR ∧ NARG cfg2 cmpToy vkc2 xN tapeXN = true := by
  decide +kernel

theorem kRunN3 : NARG cfg2 cmpToy vkc2 xN3 tapeN3 = true := by decide +kernel

/-- **A node statement accepted as a leaf child**, at the statement of the correctly tagged node. -/
theorem mistag : aggOK cfg2 cmpToy xR ⟨vkc2, vkc2, .leaf, .leaf, xN, x0, tapeXN, tape2⟩ = true := by
  rw [← kRuns.1]
  exact aggOK_leaves cfg2 cmpToy vkc2 vkc2 rfl xN x0 tapeXN tape2 kRuns.2 runs.1

/-- **A node child with a nonzero `d3`** is accepted at its parent's aggregate statement. -/
def nwN3 : NodeWitness 1 := ⟨vkc2, vkc2, .node, .leaf, xN3, x0, tapeN3, tape2⟩

theorem child_free_d3 : aggOK cfg2 cmpToy (nodeStmt cfg2 vkc2 vkc2 xN3 x0) nwN3 = true := by
  refine (aggOK_nodeStmt_iff cfg2 cmpToy nwN3).mpr ⟨vkc2_root, vkc2_root, ?_, runs.1⟩
  have h0 := (nodeStmt_slot cfg2 vkc2 vkc2 xN3 x0).1
  have h1 := (nodeStmt_slot cfg2 vkc2 vkc2 xN3 x0).2.1
  rw [digestToSlot_kat] at h0 h1
  change child cfg2 cmpToy vkc2 vkc2 (nodeStmt cfg2 vkc2 vkc2 xN3 x0) .node xN3 tapeN3 = true
  exact (child_iff cfg2 cmpToy _ _ _ _ _ _).mpr
    ⟨fun _ => ⟨h0 ▸ by decide, h1 ▸ by decide, kRunN3⟩, fun h => absurd h (by decide)⟩

/-- … although `xN3` is no aggregate statement (for any keys and children). -/
theorem xN3_not_node (vkC vkL : VKc 1) (y z : Stmt) : xN3 ≠ nodeStmt cfg2 vkC vkL y z := by
  intro h
  have := congrArg (fun s : Stmt => s.slot 3 0) h
  simp only [(nodeStmt_slot cfg2 vkC vkL y z).2.2.2 3 (by decide)] at this
  exact absurd this (by decide)

end RecursionFast.Probes.S5Review

#print axioms RecursionFast.Probes.S5Review.mistag
#print axioms RecursionFast.Probes.S5Review.child_free_d3
#print axioms RecursionFast.Probes.S5Review.xN3_not_node
