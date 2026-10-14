/- S1 review probe (S1-m7), updated in the S1 fix pass.

1. Selectors are witness cells and a row takes part in a port iff its `sel` cell *equals* `1`:
   a row whose selector is `el 3` (a non-boolean value) is silent (`sel_nonbool_silent`). This is
   kept (decision S1-m7 (iii)) and now documented in the trusted `Port` / `Table.msgs`
   docstrings: a protocol that weights messages by the selector must have the layout constrain it
   to `0`/`1`.
2. The relation now gives the gadget the row position through three contract cells (`1`,
   `[r = 0]`, `[r + 1 = rows]`, S1-A11): `fib` uses them instead of a witness selector, so the
   table the old `fib` accepted is rejected (`Controls.fib_garbage`, re-checked here).
3. (Checked, intended.) Sparse entries at the same position add up, so in characteristic 2 a
   repeated entry cancels: `dup_cancels`. This is the denoted-matrix semantics (`spToMat`). -/
import RecursionFast.Controls

open RecursionFast RecursionFast.Controls

namespace S1Probe

theorem sel_nonbool_silent : twoChip.rel 7 (stmt [el 5, 1])
    [tab [[el 5, 1], [el 7, 1]], tab [[el 7, 1], [el 5, 1], [el 9, el 3]]] := by
  rw [← relBelow_iff (N := 1) (by decide)]; decide +kernel

theorem fib_garbage_rejected : ¬ fib.rel 7 (stmt [1, 1, 1])
    [tab [[1, 1, 1], [1, 0, 0], [el 5, el 9, 0], [el 3, 1, 0]]] := fib_garbage

/-- `(0, 0, 1)` twice: the denoted entry is `1 + 1 = 0`. -/
def dupGadget : Gadget K (32 + 32 + 3) :=
  ⟨1, 1, ![[(0, 0, 1), (0, 0, 1)]], 1, fun _ => [0], fun _ => 1⟩

def dup : Layout K := ⟨[⟨32, dupGadget, [], none⟩], fun _ => .eq, 0⟩

theorem dup_cancels : dup.rel 7 (stmt [el 5]) [tab [[el 5]]] := by
  rw [← relBelow_iff (N := 0) (by decide)]; decide +kernel

end S1Probe
