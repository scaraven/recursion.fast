/- S1 review probe (S1-m: 9 of the 13 clauses of `Admissible` are not pinned by a control).

`Controls/Layout.lean` pins `cols ≤ 2^10`, `32 ≤ pub cols`, entries `≤ 2^(k+4)` and fixed cells
`≤ 2^(k-4)` (accepted at the cap, rejected one above). The clauses below have no control; a
mutation that relaxes any of them (e.g. degree `≤ 9`, `t ≤ 2^7`, `≤ 2^9` chips) breaks neither a
control nor a library proof that only needs the bound below `R k = 2^(k+5)`. Each theorem below
is a ready-made boundary control (accepted at the cap, rejected one above or at the violation);
all hold, which also checks the implemented caps against DESIGN §2.2 and S1-A1/A7. -/
import RecursionFast.Controls

open RecursionFast RecursionFast.Controls

namespace S1Probe

/-- The public chip of `withChip`. -/
def pubC : Chip K := ⟨32, freeGadget _, [], none⟩

/-- A chip of `c` columns with the given ports and the free gadget. -/
def portChip (c : ℕ) (ps : List Port) : Chip K := ⟨c, freeGadget _, ps, none⟩

/-- A one-column chip whose gadget has `t` matrices, `cons` constraints, `q` terms of degree `d`
(every term multiplies matrix 0 `d` times when `t ≥ 1`). -/
def gChip (cons t q d : ℕ) : Chip K :=
  ⟨1, ⟨cons, t, fun _ => [], q, fun _ => if h : 0 < t then List.replicate d ⟨0, h⟩ else [],
    fun _ => 0⟩, [], none⟩

-- chips ≤ 2^8
theorem chips_cap : (⟨List.replicate (2 ^ 8) pubC, fun _ => .eq, 0⟩ : Layout K).Admissible 7 ∧
    ¬ (⟨List.replicate (2 ^ 8 + 1) pubC, fun _ => .eq, 0⟩ : Layout K).Admissible 7 := by
  decide +kernel

-- ports per chip ≤ 2^4
theorem ports_cap : (withChip (portChip 1 (List.replicate 16 ⟨0, true, 0, []⟩))).Admissible 7 ∧
    ¬ (withChip (portChip 1 (List.replicate 17 ⟨0, true, 0, []⟩))).Admissible 7 := by
  decide +kernel

-- message length ≤ 2^4
theorem msg_cap : (withChip (portChip 1 [⟨0, true, 0, List.replicate 16 0⟩])).Admissible 7 ∧
    ¬ (withChip (portChip 1 [⟨0, true, 0, List.replicate 17 0⟩])).Admissible 7 := by
  decide +kernel

-- bus < 2^8
theorem bus_cap : (withChip (portChip 1 [⟨255, true, 0, []⟩])).Admissible 7 ∧
    ¬ (withChip (portChip 1 [⟨256, true, 0, []⟩])).Admissible 7 := by
  decide +kernel

-- the selector and the message columns are the chip's own
theorem sel_own : (withChip (portChip 2 [⟨0, true, 1, [1]⟩])).Admissible 7 ∧
    ¬ (withChip (portChip 2 [⟨0, true, 2, [1]⟩])).Admissible 7 ∧
    ¬ (withChip (portChip 2 [⟨0, true, 1, [2]⟩])).Admissible 7 := by
  decide +kernel

-- 1 ≤ cols
theorem cols_pos : ¬ (withChip ⟨0, freeGadget _, [], none⟩).Admissible 7 := by decide +kernel

-- t ≤ 2^6, cons ≤ 2^8, q ≤ 2^8, degree ≤ 8
theorem t_cap : (withChip (gChip 1 64 1 1)).Admissible 7 ∧
    ¬ (withChip (gChip 1 65 1 1)).Admissible 7 := by decide +kernel

theorem cons_cap : (withChip (gChip 256 1 1 1)).Admissible 7 ∧
    ¬ (withChip (gChip 257 1 1 1)).Admissible 7 := by decide +kernel

theorem q_cap : (withChip (gChip 1 1 256 1)).Admissible 7 ∧
    ¬ (withChip (gChip 1 1 257 1)).Admissible 7 := by decide +kernel

theorem degree_cap : (withChip (gChip 1 1 1 8)).Admissible 7 ∧
    ¬ (withChip (gChip 1 1 1 9)).Admissible 7 := by decide +kernel

end S1Probe
