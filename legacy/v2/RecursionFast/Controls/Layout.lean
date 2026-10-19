/-
# Controls: the layout relation (`Contract/Layout.lean`), positive and negative   (DESIGN §2.3)

Small explicit layouts over `K`, decided by the kernel (`decide +kernel`; the bus clause through
`relBelow_iff`, `Library/Layout.lean`). `el n` is the element of `K` with bits `n`; `tab` builds
a table from a list of rows (missing cells `0`); `stmt l` is the statement starting with `l`.
Public chips have 32 columns where a layout is meant to be admissible. In a 32-column chip the
view's cells `32 …` are the next row, `64` is `1`, `65` is `[r = 0]`, `66` is `[r + 1 = rows]`.

Positive:
* `r1cs_pos`, `r1cs_one_pos`, `r1cs_iff`, `r1cs_relK`: textbook R1CS `z = (1, x, w)` (the
  constant from the view): booleanity `w₀ · w₀ = w₀` and the affine `w₀ · 1 = 1` hold for
  `w₀ = 1`; `R1CS_iff_layout` at `relK 6`; the control instance is in `relK 6`;
* `twoChip_pos`, `twoChip_admissible`: two chips joined by one `eq` bus, the receiver holding the
  sender's messages in another order;
* `lookup_pos`: a `sub` lookup into a fixed table (`0, 1, 2, 3`), one value looked up twice;
* `wrap_pos`: `a' = a + 1` on every row; the last row's next row is row 0;
* `fib_pos`: XOR-Fibonacci over 4 rows, pinned by the contract cells (`[r = 0]` fixes the first
  row, `[r + 1 = rows]` switches the transition off on the last row).

Negative:
* `r1cs_neg`, `r1cs_one_neg`: `w₀ = x` with `x² ≠ x`; `w₀ = 0` against `w₀ · 1 = 1`;
* `twoChip_neg`: one message changed on the receiving side breaks the `eq` bus; `eqMult_neg`: a
  message sent once and received twice breaks it (multisets, counted in ℕ, not sets);
* `lookup_neg`: a value outside the fixed table breaks the `sub` bus; `lookup_neg_fixed`: the
  prover cannot change a fixed cell instead; `fixedHeight_neg`: nor add a row to the fixed table;
* `wrap_neg`: a sequence that is correct except across the wrap;
* `fib_neg`: one wrong transition; `fib_garbage`: not Fibonacci after row 1;
  `fib_boundary_neg`: valid transitions from a wrong first row; `stmt_neg`: a wrong statement;
* `noPub_neg`: with no public chip, `rel` fails for every statement and witness; `emptyPub_neg`:
  a public table with no row does not carry a statement;
* `unsat_neg`: a gadget no row satisfies (`1 = 0`) on the public chip: no witness for any
  statement, although the layout is admissible (`unsat_admissible`);
* `cells_neg`: the Fibonacci witness (128 cells) is rejected at class 6;
* the caps, each accepted at its bound and rejected one above (same layout otherwise): `cols_neg`,
  `pubCols_neg`, `entries_neg`, `fixedCells_neg`, `chips_cap`, `ports_cap`, `msg_cap`,
  `bus_cap`, `sel_own`, `cols_pos`, `t_cap`, `cons_cap`, `q_cap`, `degree_cap`.
-/
import RecursionFast.Library.R1CS
import RecursionFast.Library.Field

namespace RecursionFast.Controls
open RecursionFast Matrix

/-- The element of `K` with bits `n`. -/
abbrev el (n : ℕ) : K := ⟨BitVec.ofNat 64 n⟩

/-- A gadget with no terms (every row satisfies it). -/
def freeGadget (w : ℕ) : Gadget K w := ⟨0, 0, Fin.elim0, 0, Fin.elim0, Fin.elim0⟩

/-- A table from a list of rows; missing cells are `0`. -/
def tab (rows : List (List K)) : Table K := ⟨rows.length, fun r c => (rows.getD r []).getD c 0⟩

/-- The statement whose first elements are `l`, the rest `0`. -/
def stmt (l : List K) : Fin 32 → K := fun i => l.getD i 0

/-! ## R1CS -/

/-- A one-constraint R1CS on `z = (1, x, w₀)` (`z 0 = 1`, `z 33 = w₀`): `A, B, C` select the
columns `a`, `b`, `c`. -/
def sel3 (a b c : Fin (32 + 1 + 1)) : Fin 3 → Matrix (Fin 1) (Fin (32 + 1 + 1)) K :=
  ![fun _ j => if j = a then 1 else 0, fun _ j => if j = b then 1 else 0,
    fun _ j => if j = c then 1 else 0]

theorem sel_mulVec (a : Fin (32 + 1 + 1)) (z : Fin (32 + 1 + 1) → K) :
    (fun (_ : Fin 1) j => if j = a then (1 : K) else 0 : Matrix (Fin 1) (Fin (32 + 1 + 1)) K) *ᵥ z =
      fun _ => z a := by
  funext i; simp [mulVec, dotProduct]

/-- Booleanity `w₀ · w₀ = w₀`. -/
abbrev boolR := sel3 33 33 33
/-- The affine constraint `w₀ · 1 = 1`, which needs the constant wire. -/
abbrev oneR := sel3 33 0 0

theorem zVec_33 (x : Fin 32 → K) (w : Fin 1 → K) : zVec x w 33 = w 0 := rfl
theorem zVec_0 (x : Fin 32 → K) (w : Fin 1 → K) : zVec x w 0 = 1 := rfl

theorem r1cs_sel_iff (a b c : Fin (32 + 1 + 1)) (x : Fin 32 → K) (w : Fin 1 → K) :
    R1CS (sel3 a b c 0) (sel3 a b c 1) (sel3 a b c 2) x w ↔
      zVec x w a * zVec x w b = zVec x w c := by
  simp [R1CS, R1CSz, sel3, sel_mulVec, funext_iff]

theorem r1cs_pos (x : Fin 32 → K) :
    (r1csLayout (boolR 0) (boolR 1) (boolR 2)).rel 6 x (r1csWit x ![1]) :=
  (rel_r1csWit_iff _ _ _ (by norm_num) x ![1]).mpr ((r1cs_sel_iff 33 33 33 x _).mpr
    (by rw [zVec_33]; decide +kernel))

theorem r1cs_neg (x : Fin 32 → K) :
    ¬ (r1csLayout (boolR 0) (boolR 1) (boolR 2)).rel 6 x (r1csWit x ![el 2]) := fun h =>
  absurd ((r1cs_sel_iff 33 33 33 x _).mp ((rel_r1csWit_iff _ _ _ (by norm_num) x _).mp h))
    (by rw [zVec_33]; decide +kernel)

/-- The constant wire: `w₀ = 1` is expressible (`w₀ · 1 = 1`); `w₀ = 1` satisfies it ... -/
theorem r1cs_one_pos (x : Fin 32 → K) :
    (r1csLayout (oneR 0) (oneR 1) (oneR 2)).rel 6 x (r1csWit x ![1]) :=
  (rel_r1csWit_iff _ _ _ (by norm_num) x ![1]).mpr ((r1cs_sel_iff 33 0 0 x _).mpr
    (by rw [zVec_33, zVec_0]; decide +kernel))

/-- ... and `w₀ = 0` does not (an R1CS without the constant wire is satisfied by `z = 0`). -/
theorem r1cs_one_neg (x : Fin 32 → K) :
    ¬ (r1csLayout (oneR 0) (oneR 1) (oneR 2)).rel 6 x (r1csWit x ![0]) := fun h =>
  absurd ((r1cs_sel_iff 33 0 0 x _).mp ((rel_r1csWit_iff _ _ _ (by norm_num) x _).mp h))
    (by rw [zVec_33, zVec_0]; decide +kernel)

/-- The R1CS special case in `relK 6`: `x` is satisfiable iff some witness satisfies the R1CS. -/
theorem r1cs_iff (x : Stmt) : (∃ t, ((r1csLayout (boolR 0) (boolR 1) (boolR 2), x), t) ∈ relK 6) ↔
    ∃ w, R1CS (boolR 0) (boolR 1) (boolR 2) x w :=
  R1CS_iff_layout _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) x

/-- The control instance is in `relK 6` (the layout is admissible). -/
theorem r1cs_relK (x : Stmt) :
    ((r1csLayout (boolR 0) (boolR 1) (boolR 2), x), r1csWit x ![1]) ∈ relK 6 :=
  ⟨r1csLayout_admissible _ _ _ (by norm_num) (by norm_num) (by norm_num), r1cs_pos x⟩

/-! ## Two chips, one `eq` bus -/

/-- Chip 0 (public, 32 columns) sends column 0 on bus 0 when column 1 is `1`; chip 1 receives
the same way. -/
def twoChip : Layout K :=
  ⟨[⟨32, freeGadget _, [⟨0, true, 1, [0]⟩], none⟩, ⟨2, freeGadget _, [⟨0, false, 1, [0]⟩], none⟩],
   fun _ => .eq, 0⟩

theorem twoChip_admissible : twoChip.Admissible 7 := by decide +kernel

theorem twoChip_pos : twoChip.rel 7 (stmt [el 5, 1])
    [tab [[el 5, 1], [el 7, 1]], tab [[el 7, 1], [el 5, 1], [el 9, 0]]] := by
  rw [← relBelow_iff (N := 1) (by decide)]; decide +kernel

theorem twoChip_neg : ¬ twoChip.rel 7 (stmt [el 5, 1])
    [tab [[el 5, 1], [el 7, 1]], tab [[el 7, 1], [el 6, 1], [el 9, 0]]] := by
  rw [← relBelow_iff (N := 1) (by decide)]; decide +kernel

/-! ## A `sub` lookup into a fixed table -/

/-- The fixed table: rows `(i, 1)` for `i < 4`. -/
def range4 : Table K := tab [[el 0, 1], [el 1, 1], [el 2, 1], [el 3, 1]]

/-- Chip 0 (public) looks its column 0 up on bus 1; chip 1, fixed to `range4`, provides it. -/
def lookup : Layout K :=
  ⟨[⟨32, freeGadget _, [⟨1, false, 1, [0]⟩], none⟩,
    ⟨2, freeGadget _, [⟨1, true, 1, [0]⟩], some range4⟩],
   fun b => if b = 1 then .sub else .eq, 0⟩

theorem lookup_admissible : lookup.Admissible 7 := by decide +kernel

theorem lookup_pos : lookup.rel 7 (stmt [el 2, 1])
    [tab [[el 2, 1], [el 2, 1], [el 3, 1]], range4] := by
  rw [← relBelow_iff (N := 2) (by decide)]; decide +kernel

theorem lookup_neg : ¬ lookup.rel 7 (stmt [el 2, 1]) [tab [[el 2, 1], [el 9, 1]], range4] := by
  rw [← relBelow_iff (N := 2) (by decide)]; decide +kernel

theorem lookup_neg_fixed : ¬ lookup.rel 7 (stmt [el 2, 1])
    [tab [[el 2, 1], [el 9, 1]], tab [[el 0, 1], [el 1, 1], [el 2, 1], [el 9, 1]]] := by
  rw [← relBelow_iff (N := 2) (by decide)]; decide +kernel

/-! ## Multiplicities and heights -/

/-- The sender puts `5` once; the receiver takes it twice: the multisets differ although the
sets agree, so the `eq` bus rejects (counted in ℕ). -/
theorem eqMult_neg : ¬ twoChip.rel 7 (stmt [el 5, 1])
    [tab [[el 5, 1], [el 7, 1]], tab [[el 5, 1], [el 5, 1], [el 7, 1]]] := by
  rw [← relBelow_iff (N := 1) (by decide)]; decide +kernel

/-- The fixed chip's table is `range4` plus a row `(9, 1)`: the cells of `range4`'s rows agree
and the lookup of `9` is served, so only the height equation rejects it. -/
theorem fixedHeight_neg : ¬ lookup.rel 7 (stmt [el 2, 1])
    [tab [[el 2, 1], [el 9, 1]], tab [[el 0, 1], [el 1, 1], [el 2, 1], [el 3, 1], [el 9, 1]]] := by
  rw [← relBelow_iff (N := 2) (by decide)]; decide +kernel

/-! ## The view: the wrap and the contract cells -/

/-- `a' = a + 1` on every row, no selector: `z 0 + z 32 + 1 = 0` (cell 32 is the next row's
column 0; the constant is the empty product). -/
def incGadget : Gadget K (32 + 32 + 3) where
  cons := 1
  t := 1
  M := ![[(0, 0, 1), (0, 32, 1)]]
  q := 2
  S := ![[0], []]
  c := fun _ => 1

/-- The increment chip, public, alone. -/
def inc : Layout K := ⟨[⟨32, incGadget, [], none⟩], fun _ => .eq, 0⟩

/-- Two rows `1, 0`: the last row's next row is row 0 (`0 + 1 = 1`). -/
theorem wrap_pos : inc.rel 7 (stmt [1]) [tab [[1], [0]]] := by
  rw [← relBelow_iff (N := 0) (by decide)]; decide +kernel

/-- Three rows `1, 0, 1`: the wrap `1 ↦ 1` breaks the gadget (a view that did not wrap would
accept). -/
theorem wrap_neg : ¬ inc.rel 7 (stmt [1]) [tab [[1], [0], [1]]] := by
  rw [← relBelow_iff (N := 0) (by decide)]; decide +kernel

/-- XOR-Fibonacci pinned by the contract cells. Columns `a, b` = `0, 1` (of 32); view cells
`32, 33` are the next row's `a', b'`, `64` is `1`, `65` is `[r = 0]`, `66` is `[r + 1 = rows]`.
Constraints, each `(gate) · (linear) = 0`: `(1 + last) · (b + a')`, `(1 + last) · (a + b + b')`
(in characteristic 2: `a' = b`, `b' = a + b` on every row but the last), `first · (a + 1)`,
`first · (b + 1)` (row 0 is `1, 1`). -/
def fibGadget : Gadget K (32 + 32 + 3) where
  cons := 4
  t := 2
  M := ![[(0, 64, 1), (0, 66, 1), (1, 64, 1), (1, 66, 1), (2, 65, 1), (3, 65, 1)],
         [(0, 1, 1), (0, 32, 1), (1, 0, 1), (1, 1, 1), (1, 33, 1), (2, 0, 1), (2, 64, 1),
          (3, 1, 1), (3, 64, 1)]]
  q := 1
  S := fun _ => [0, 1]
  c := fun _ => 1

/-- The Fibonacci chip, public, alone. -/
def fib : Layout K := ⟨[⟨32, fibGadget, [], none⟩], fun _ => .eq, 0⟩

theorem fib_admissible : fib.Admissible 7 := by decide +kernel

/-- The XOR-Fibonacci table `(1, 1), (1, 0), (0, 1), (1, 1)`. -/
def fibTab : Table K := tab [[1, 1], [1, 0], [0, 1], [1, 1]]

theorem fib_pos : fib.rel 7 (stmt [1, 1]) [fibTab] := by
  rw [← relBelow_iff (N := 0) (by decide)]; decide +kernel

/-- One wrong transition (rows 2 → 3). -/
theorem fib_neg : ¬ fib.rel 7 (stmt [1, 1]) [tab [[1, 1], [1, 0], [0, 1], [0, 1]]] := by
  rw [← relBelow_iff (N := 0) (by decide)]; decide +kernel

/-- Not Fibonacci after row 1 (rejected now that no witness selector can switch the
transition off). -/
theorem fib_garbage : ¬ fib.rel 7 (stmt [1, 1, 1])
    [tab [[1, 1, 1], [1, 0, 0], [el 5, el 9, 0], [el 3, 1, 0]]] := by
  rw [← relBelow_iff (N := 0) (by decide)]; decide +kernel

/-- A valid transition sequence that does not start at `(1, 1)`: the first-row flag rejects it. -/
theorem fib_boundary_neg : ¬ fib.rel 7 (stmt [0, 1]) [tab [[0, 1], [1, 1], [1, 0], [0, 1]]] := by
  rw [← relBelow_iff (N := 0) (by decide)]; decide +kernel

theorem stmt_neg : ¬ fib.rel 7 (stmt [1, 0]) [fibTab] := by
  rw [← relBelow_iff (N := 0) (by decide)]; decide +kernel

/-! ## The public chip; an unsatisfiable gadget; the size caps -/

/-- With no public chip (`pub ≥` number of chips), no statement has a witness. -/
theorem noPub_neg (L : Layout K) (hL : L.chips.length ≤ L.pub) (k : ℕ) (x : Fin 32 → K)
    (w : List (Table K)) : ¬ L.rel k x w := by
  rintro ⟨hlen, -, -, -, ⟨T, hT, -⟩, -⟩
  exact absurd (List.getElem?_eq_some_iff.mp hT).1 (by omega)

/-- The two-chip layout with its public index moved past the chips. -/
theorem twoChip_noPub (k : ℕ) (x : Fin 32 → K) (w : List (Table K)) :
    ¬ { twoChip with pub := 2 }.rel k x w :=
  noPub_neg _ (by decide) k x w

/-- A public table with no row carries no statement, not even the all-zero one. -/
theorem emptyPub_neg : ¬ inc.rel 7 (stmt []) [⟨0, fun _ _ => 0⟩] := by
  rw [← relBelow_iff (N := 0) (by decide)]; decide +kernel

/-- The gadget `1 = 0`: one term, the empty product, coefficient `1`. -/
def unsatGadget (w : ℕ) : Gadget K w := ⟨1, 0, Fin.elim0, 1, fun _ => [], fun _ => 1⟩

/-- One public chip whose gadget no row satisfies. -/
def unsat : Layout K := ⟨[⟨32, unsatGadget _, [], none⟩], fun _ => .eq, 0⟩

theorem unsat_admissible : unsat.Admissible 7 := by decide +kernel

theorem unsatGadget_not_holds (w : ℕ) (z : Fin w → K) : ¬ (unsatGadget w).holds z :=
  fun h => by simpa [unsatGadget] using h ⟨0, Nat.one_pos⟩

/-- No witness for any statement: the public chip has a row, which fails the gadget. -/
theorem unsat_neg (k : ℕ) (x : Fin 32 → K) (w : List (Table K)) : ¬ unsat.rel k x w := by
  rintro ⟨-, -, hg, -, ⟨T, hT, h1, -⟩, -⟩
  exact unsatGadget_not_holds _ _
    (hg (unsat.chips[0], T) (List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨rfl, hT⟩)) 0 h1)

theorem cells_neg : ¬ fib.rel 6 (stmt [1, 1]) [fibTab] :=
  fun h => absurd h.2.2.2.2.2 (by decide +kernel)

/-- The public chip `twoChip` uses, then one more chip `C`. -/
def withChip (C : Chip K) : Layout K := ⟨[⟨32, freeGadget _, [], none⟩, C], fun _ => .eq, 0⟩

theorem cols_neg : ¬ (withChip ⟨2 ^ 10 + 1, freeGadget _, [], none⟩).Admissible 7 ∧
    (withChip ⟨2 ^ 10, freeGadget _, [], none⟩).Admissible 7 := by
  decide +kernel

theorem pubCols_neg :
    ¬ (⟨[⟨31, freeGadget _, [], none⟩], fun _ => .eq, 0⟩ : Layout K).Admissible 7 := by
  decide +kernel

/-- A one-matrix gadget with `e` entries, all at `(0, 0)`. -/
def bigGadget (e : ℕ) : Gadget K (1 + 1 + 3) :=
  ⟨1, 1, fun _ => List.replicate e (0, 0, 1), 0, Fin.elim0, Fin.elim0⟩

theorem entries_neg : ¬ (withChip ⟨1, bigGadget 17, [], none⟩).Admissible 0 ∧
    (withChip ⟨1, bigGadget 16, [], none⟩).Admissible 0 := by
  decide +kernel

theorem fixedCells_neg :
    ¬ (withChip ⟨1, freeGadget _, [], some ⟨2 ^ 3 + 1, fun _ _ => 0⟩⟩).Admissible 7 ∧
      (withChip ⟨1, freeGadget _, [], some ⟨2 ^ 3, fun _ _ => 0⟩⟩).Admissible 7 := by
  decide +kernel

/-! ## Boundary controls for the remaining caps (reviewer's `AdmissibleCaps`) -/

/-- A public chip of 32 columns, nothing else. -/
def pubC : Chip K := ⟨32, freeGadget _, [], none⟩

/-- A chip of `c` columns with the given ports and the free gadget. -/
def portChip (c : ℕ) (ps : List Port) : Chip K := ⟨c, freeGadget _, ps, none⟩

/-- A one-column chip whose gadget has `t` matrices, `cons` constraints, `q` terms of degree `d`
(every term multiplies matrix 0 `d` times when `t ≥ 1`). -/
def gChip (cons t q d : ℕ) : Chip K :=
  ⟨1, ⟨cons, t, fun _ => [], q, fun _ => if h : 0 < t then List.replicate d ⟨0, h⟩ else [],
    fun _ => 0⟩, [], none⟩

theorem chips_cap : (⟨List.replicate (2 ^ 8) pubC, fun _ => .eq, 0⟩ : Layout K).Admissible 7 ∧
    ¬ (⟨List.replicate (2 ^ 8 + 1) pubC, fun _ => .eq, 0⟩ : Layout K).Admissible 7 := by
  decide +kernel

theorem ports_cap : (withChip (portChip 1 (List.replicate 32 ⟨0, true, 0, []⟩))).Admissible 7 ∧
    ¬ (withChip (portChip 1 (List.replicate 33 ⟨0, true, 0, []⟩))).Admissible 7 := by
  decide +kernel

theorem msg_cap : (withChip (portChip 1 [⟨0, true, 0, List.replicate 16 0⟩])).Admissible 7 ∧
    ¬ (withChip (portChip 1 [⟨0, true, 0, List.replicate 17 0⟩])).Admissible 7 := by
  decide +kernel

theorem bus_cap : (withChip (portChip 1 [⟨255, true, 0, []⟩])).Admissible 7 ∧
    ¬ (withChip (portChip 1 [⟨256, true, 0, []⟩])).Admissible 7 := by
  decide +kernel

theorem sel_own : (withChip (portChip 2 [⟨0, true, 1, [1]⟩])).Admissible 7 ∧
    ¬ (withChip (portChip 2 [⟨0, true, 2, [1]⟩])).Admissible 7 ∧
    ¬ (withChip (portChip 2 [⟨0, true, 1, [2]⟩])).Admissible 7 := by
  decide +kernel

theorem cols_pos : ¬ (withChip ⟨0, freeGadget _, [], none⟩).Admissible 7 := by decide +kernel

theorem t_cap : (withChip (gChip 1 64 1 1)).Admissible 7 ∧
    ¬ (withChip (gChip 1 65 1 1)).Admissible 7 := by decide +kernel

theorem cons_cap : (withChip (gChip 256 1 1 1)).Admissible 7 ∧
    ¬ (withChip (gChip 257 1 1 1)).Admissible 7 := by decide +kernel

theorem q_cap : (withChip (gChip 1 1 256 1)).Admissible 7 ∧
    ¬ (withChip (gChip 1 1 257 1)).Admissible 7 := by decide +kernel

theorem degree_cap : (withChip (gChip 1 1 1 8)).Admissible 7 ∧
    ¬ (withChip (gChip 1 1 1 9)).Admissible 7 := by decide +kernel

end RecursionFast.Controls
