/-
  RecursionFast.Library.R1CS  (UNTRUSTED, kernel-checked)

  **Textbook R1CS with public input is the special case "one chip, one row, no ports"** of the
  layout relation (DESIGN §2.1, §2.3; amendments S1-A3, S1-A10). A dense R1CS instance is three
  matrices `A, B, C` of size `m × (32 + n + 1)`; the public input `x : Fin 32 → F` and a witness
  `w : Fin n → F` satisfy it when `z = (1, x, w)` has `(A z) ∘ (B z) = C z` (Mathlib's `*ᵥ`,
  entrywise product), as v0.3's `R1CS` (`zVec`).

  `r1csLayout A B C` is one public chip of `32 + n` columns, no ports, no fixed table. Its row is
  `(x, w)` and the constant `1` is the view's constant cell (S1-A10), so its gadget is
  `1 · (A' v)(B' v) + (-1) · (C' v) = 0`, where `A'` lists every entry of `A` with column `0` moved
  to the constant cell and column `j + 1` to row cell `j`. The statement is the first 32 cells of
  row 0, i.e. `x`.

  * `rel_r1csLayout_iff`: the layout relation in full: one table with a row, every row (with the
    constant) an R1CS solution, the first 32 cells of row 0 equal to `x`, at most `2^k` cells.
  * `r1csLayout_admissible`: the layout is admissible for `m ≤ 2^8` constraints,
    `32 + n ≤ 2^10` columns and `3 · m · (32 + n + 1) ≤ 2^(k+4)` entries.
  * `R1CS_iff_layout` (over `K`, for `relK k`): `x` is satisfiable in `relK k` with the R1CS
    layout iff some `w` satisfies the R1CS, with explicit witness maps both ways:
    `rel_r1csWit_iff` (`w ↦ r1csWit x w`, the one-row table of `(x, w)`) and `R1CS_of_rel` (any
    witness `t ↦ r1csAssign t`, cells `32 …` of its row 0).

  A larger R1CS is several one-row chips or a uniform gadget over rows.
-/
import RecursionFast.Library.Layout
import RecursionFast.Library.Field
import RecursionFast.Contract.Protocol

namespace RecursionFast

open Matrix

section R1CSGeneric
variable {F : Type} [CommRing F] [DecidableEq F] {m n : ℕ}

/-! ## Dense R1CS and its layout -/

/-- `z` satisfies the constraints: `(A z) ∘ (B z) = C z`. -/
def R1CSz {N : ℕ} (A B C : Matrix (Fin m) (Fin N) F) (z : Fin N → F) : Prop :=
  (A *ᵥ z) * (B *ᵥ z) = C *ᵥ z

/-- The textbook assignment `z = (1, x, w)`. -/
def zVec (x : Fin 32 → F) (w : Fin n → F) : Fin (32 + n + 1) → F := Fin.cons 1 (Fin.append x w)

/-- **Dense R1CS with public input `x`**: `z = (1, x, w)` satisfies the constraints. -/
def R1CS (A B C : Matrix (Fin m) (Fin (32 + n + 1)) F) (x : Fin 32 → F) (w : Fin n → F) :
    Prop :=
  R1CSz A B C (zVec x w)

/-- Where column `c` of `z = (1, row)` sits in the view of a `(32 + n)`-column chip: the constant
cell for `c = 0`, row cell `j` for `c = j + 1`. -/
def zCol (c : Fin (32 + n + 1)) : Fin (32 + n + (32 + n) + 3) :=
  Fin.cases (Fin.natAdd (32 + n + (32 + n)) 0) (fun j => Fin.castAdd 3 (Fin.castAdd (32 + n) j)) c

/-- Every entry of `M`, as a sparse matrix on the view (columns placed by `col`). -/
def sparseOf {N W : ℕ} (col : Fin N → Fin W) (M : Matrix (Fin m) (Fin N) F) :
    List (Fin m × Fin W × F) :=
  (List.finRange m).flatMap fun r => (List.finRange N).map fun c => (r, col c, M r c)

/-- The R1CS gadget: matrices `A', B', C'`; terms `1 · A'B'` and `-1 · C'`. -/
def r1csGadget (A B C : Matrix (Fin m) (Fin (32 + n + 1)) F) :
    Gadget F (32 + n + (32 + n) + 3) where
  cons := m
  t := 3
  M := ![sparseOf zCol A, sparseOf zCol B, sparseOf zCol C]
  q := 2
  S := ![[0, 1], [2]]
  c := ![1, -1]

/-- The R1CS chip: `32 + n` columns, the R1CS gadget, no ports, no fixed table. -/
def r1csChip (A B C : Matrix (Fin m) (Fin (32 + n + 1)) F) : Chip F :=
  ⟨32 + n, r1csGadget A B C, [], none⟩

/-- **The R1CS layout**: the R1CS chip alone; it is public. -/
def r1csLayout (A B C : Matrix (Fin m) (Fin (32 + n + 1)) F) : Layout F :=
  ⟨[r1csChip A B C], fun _ => .eq, 0⟩

/-- Witness ↦ layout witness: the one-row table holding `(x, w)`. -/
def r1csWit (x : Fin 32 → F) (w : Fin n → F) : List (Table F) :=
  [⟨1, fun _ c => if h : c < 32 + n then Fin.append x w ⟨c, h⟩ else 0⟩]

/-- Layout witness ↦ witness: cells `32, 33, …` of row 0 of the first table. -/
def r1csAssign (t : List (Table F)) : Fin n → F :=
  fun j => (t.head?.map fun T => T.cell 0 (32 + j)).getD 0

/-- Row `r` of a table, as an assignment. -/
def rowOf (N : ℕ) (T : Table F) (r : ℕ) : Fin N → F := fun c => T.cell r c

/-! ## The gadget is R1CS on every row -/

omit [DecidableEq F] in
private theorem rowDot_eq_sum {m' n' : ℕ} (L : List (Fin m' × Fin n' × F)) (v : Fin n' → F)
    (r : Fin m') : rowDot L v r = (L.map fun e => if e.1 = r then e.2.2 * v e.2.1 else 0).sum := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [rowDot, List.filter_cons, List.map_cons, List.sum_cons] at ih ⊢
    split_ifs with h1 h2 h2 <;> simp_all

omit [DecidableEq F] in
theorem rowDot_sparseOf {N W : ℕ} (col : Fin N → Fin W) (M : Matrix (Fin m) (Fin N) F)
    (v : Fin W → F) (r : Fin m) : rowDot (sparseOf col M) v r = (M *ᵥ fun c => v (col c)) r := by
  rw [rowDot_eq_sum, sparseOf, List.map_flatMap, List.flatMap_def, List.sum_flatten]
  simp only [List.map_map, Function.comp_def]
  rw [← Fin.sum_univ_def (f := fun r' => ((List.finRange N).map fun c =>
    if r' = r then M r' c * v (col c) else 0).sum)]
  simp only [← Fin.sum_univ_def (f := fun c => _)]
  rw [Finset.sum_eq_single r (fun b _ hb => by simp [hb]) (by simp)]
  simp [mulVec, dotProduct]

omit [DecidableEq F] in
theorem r1csGadget_holds_iff (A B C : Matrix (Fin m) (Fin (32 + n + 1)) F)
    (v : Fin (32 + n + (32 + n) + 3) → F) :
    (r1csGadget A B C).holds v ↔ R1CSz A B C fun c => v (zCol c) := by
  simp only [Gadget.holds, R1CSz, funext_iff, r1csGadget, List.ofFn_succ, List.ofFn_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.sum_cons,
    List.sum_nil, rowDot_sparseOf, Pi.mul_apply, Fin.succ_zero_eq_one, one_mul, mul_one,
    neg_one_mul, add_zero, ← sub_eq_add_neg, sub_eq_zero]

omit [DecidableEq F] in
theorem holds_r1csChip_iff (A B C : Matrix (Fin m) (Fin (32 + n + 1)) F) (T : Table F) (r : ℕ) :
    (r1csChip A B C).gadget.holds (view (r1csChip A B C) T r) ↔
      R1CSz A B C (Fin.cons 1 (rowOf (32 + n) T r)) := by
  refine (r1csGadget_holds_iff A B C _).trans (iff_of_eq (congrArg _ (funext fun c => ?_)))
  refine Fin.cases ?_ (fun j => ?_) c
  · exact view_one (r1csChip A B C) T r
  · exact view_castAdd (r1csChip A B C) T r j

/-! ## The layout relation of the R1CS layout -/

/-- **The R1CS layout's relation, in full**: one table with a row, every row an R1CS solution,
the first 32 cells of row 0 equal to `x`, at most `2^k` cells. -/
theorem rel_r1csLayout_iff (A B C : Matrix (Fin m) (Fin (32 + n + 1)) F) (k : ℕ) (x : Fin 32 → F)
    (t : List (Table F)) :
    (r1csLayout A B C).rel k x t ↔ ∃ T, t = [T] ∧ 1 ≤ T.rows ∧
      (∀ r < T.rows, R1CSz A B C (Fin.cons 1 (rowOf (32 + n) T r))) ∧
      (∀ i : Fin 32, T.cell 0 i = x i) ∧
      T.rows * (32 + n) ≤ 2 ^ k := by
  rcases t with _ | ⟨T, _ | ⟨T', t⟩⟩
  · exact iff_of_false (fun h => by simpa [r1csLayout] using h.1) (by simp)
  · simp only [Layout.rel, r1csLayout, List.zip_cons_cons, List.zip_nil_right, List.mem_singleton,
      forall_eq, holds_r1csChip_iff, traffic, BusKind.Balanced, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, List.length_singleton, List.getElem?_cons_zero,
      Option.mem_def, Option.some.injEq, exists_eq_left', List.cons.injEq, and_true, true_and]
    simp only [r1csChip, reduceCtorEq, IsEmpty.forall_iff, implies_true, List.filter_nil,
      List.map_nil, List.sum_nil, true_and, and_assoc]
    exact and_left_comm
  · exact iff_of_false (fun h => by simpa [r1csLayout] using h.1) (by simp)

/-! ## R1CS with public input is a special case: both directions, explicit witness maps -/

/-- Forward: the one-row table of `(x, w)` satisfies the layout with statement `x` iff `w`
satisfies the R1CS with public input `x`. -/
theorem rel_r1csWit_iff (A B C : Matrix (Fin m) (Fin (32 + n + 1)) F) {k : ℕ} (hk : 32 + n ≤ 2 ^ k)
    (x : Fin 32 → F) (w : Fin n → F) :
    (r1csLayout A B C).rel k x (r1csWit x w) ↔ R1CS A B C x w := by
  let T0 : Table F := ⟨1, fun _ c => if h : c < 32 + n then Fin.append x w ⟨c, h⟩ else 0⟩
  have hrow : rowOf (32 + n) T0 0 = Fin.append x w := by funext c; simp [rowOf, T0]
  have hx : ∀ i : Fin 32, T0.cell 0 i = x i := fun i => by
    simpa [rowOf] using congrFun hrow (Fin.castAdd n i)
  rw [rel_r1csLayout_iff]
  constructor
  · rintro ⟨T, hT, -, hrows, -, -⟩
    obtain rfl : T = T0 := by simpa [r1csWit] using hT.symm
    exact (congrArg (fun z => R1CSz A B C (Fin.cons 1 z)) hrow).mp (hrows 0 (by simp [T0]))
  · intro h
    refine ⟨T0, rfl, le_refl _, fun r hr => ?_, hx, by simpa [T0] using hk⟩
    obtain rfl : r = 0 := by simpa [T0] using hr
    exact (congrArg (fun z => R1CSz A B C (Fin.cons 1 z)) hrow).mpr h

/-- Backward: any witness of the layout with statement `x` yields, by `r1csAssign`, a witness
of the R1CS with public input `x`. -/
theorem R1CS_of_rel (A B C : Matrix (Fin m) (Fin (32 + n + 1)) F) {k : ℕ} {x : Fin 32 → F}
    {t : List (Table F)} (h : (r1csLayout A B C).rel k x t) : R1CS A B C x (r1csAssign t) := by
  obtain ⟨T, rfl, h1, hrows, hx, -⟩ := (rel_r1csLayout_iff A B C k x t).mp h
  have hz : rowOf (32 + n) T 0 = Fin.append x (r1csAssign [T]) := by
    funext c
    exact Fin.addCases (fun i => by simpa [rowOf] using hx i)
      (fun j => by simp [rowOf, r1csAssign]) c
  exact (congrArg (fun z => R1CSz A B C (Fin.cons 1 z)) hz).mp (hrows 0 h1)

/-- The statement `x` is satisfiable in the R1CS layout's `rel` (at a class that holds one row)
iff some witness satisfies the R1CS with public input `x`. -/
theorem R1CS_iff_rel (A B C : Matrix (Fin m) (Fin (32 + n + 1)) F) {k : ℕ} (hk : 32 + n ≤ 2 ^ k)
    (x : Fin 32 → F) : (∃ t, (r1csLayout A B C).rel k x t) ↔ ∃ w, R1CS A B C x w :=
  ⟨fun ⟨_, ht⟩ => ⟨_, R1CS_of_rel A B C ht⟩,
    fun ⟨w, hw⟩ => ⟨_, (rel_r1csWit_iff A B C hk x w).mpr hw⟩⟩

omit [DecidableEq F] in
/-- The R1CS layout is admissible within the caps. -/
theorem r1csLayout_admissible (A B C : Matrix (Fin m) (Fin (32 + n + 1)) F) {k : ℕ}
    (hm : m ≤ 2 ^ 8) (hn : 32 + n ≤ 2 ^ 10) (he : 3 * (m * (32 + n + 1)) ≤ 2 ^ (k + 4)) :
    (r1csLayout A B C).Admissible k := by
  have hlen : ∀ M : Matrix (Fin m) (Fin (32 + n + 1)) F,
      (sparseOf zCol M).length = m * (32 + n + 1) :=
    fun M => by simp [sparseOf, List.length_flatMap, List.map_const', List.sum_replicate]
  refine ⟨by simp [r1csLayout], ⟨r1csChip A B C, by simp [r1csLayout], by simp [r1csChip]⟩, ?_,
    by simp [r1csLayout, Chip.fixedCells, r1csChip], ?_⟩
  · simp [r1csLayout, Chip.entries, r1csChip, r1csGadget, hlen, List.ofFn_succ]
    omega
  · simp only [r1csLayout, List.mem_singleton, forall_eq]
    refine ⟨by simp [r1csChip]; omega, hn, by simp [r1csChip, r1csGadget],
      by simpa [r1csChip, r1csGadget] using hm,
      by simp [r1csChip, r1csGadget], fun i => ?_, by simp [r1csChip], by simp [r1csChip]⟩
    fin_cases i <;> simp [r1csChip, r1csGadget]

end R1CSGeneric

/-! ## Over `K`: the special case inside the competition relation `relK` -/

/-- **`R1CS_iff_layout`**: with the R1CS layout (within the caps, at a class that holds one row),
the statement `x` is in `relK k` iff some witness satisfies the textbook R1CS with public input
`x`. Witness maps: `rel_r1csWit_iff` (`w ↦ r1csWit x w`) and `R1CS_of_rel` (`t ↦ r1csAssign t`). -/
theorem R1CS_iff_layout {m n k : ℕ} (A B C : Matrix (Fin m) (Fin (32 + n + 1)) K)
    (hm : m ≤ 2 ^ 8) (hn : 32 + n ≤ 2 ^ 10) (he : 3 * (m * (32 + n + 1)) ≤ 2 ^ (k + 4))
    (hk : 32 + n ≤ 2 ^ k) (x : Stmt) :
    (∃ t, ((r1csLayout A B C, x), t) ∈ relK k) ↔ ∃ w, R1CS A B C x w :=
  ⟨fun ⟨_, ht⟩ => ⟨_, R1CS_of_rel A B C ht.2⟩,
    fun ⟨w, hw⟩ => ⟨_, r1csLayout_admissible A B C hm hn he, (rel_r1csWit_iff A B C hk x w).mpr hw⟩⟩

end RecursionFast
