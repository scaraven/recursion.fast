/-
  RecursionFast.Library.Layout  (UNTRUSTED, kernel-checked)

  Facts about the contract relation `Layout.rel` (`Contract/Layout.lean`):

  * `rowDot_eq`, `Gadget.holds_iff`: over a commutative semiring the contract's list folds are
    Mathlib's `Matrix.mulVec` of the dense matrix a sparse one denotes (`spToMat`, entries at
    the same position summed), `∑` and multiset `∏`, i.e. the gadget is the textbook CCS
    `∀ r, ∑_i c_i · ∏_{j ∈ S_i} (M_j z)_r = 0`.
  * `traffic_eq_zero`: a bus that no port uses carries no message; `Layout.relBelow N` is `rel`
    with the bus clause checked for `b < N` only. It is decidable, and `relBelow_iff` shows it is
    `rel` when every port is on a bus `< N` (admissible layouts: `N = 2^8`).
  * `rel_trim_iff`: `rel` reads a witness only through its length, its heights and its cells
    inside `rows × cols`, for layouts whose ports read their own columns, whose chips have a
    column and whose public chip has 32 (`Layout.ReadsOwn`, implied by admissibility).
  * `rel_normal_iff`: nor does `rel` read a fixed table outside `rows × cols`, or the kind of a
    bus no port uses (`Layout.normal`).
-/
import RecursionFast.Contract.Layout
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

namespace RecursionFast

open Matrix

variable {F : Type}

/-! ## The gadget is the textbook CCS -/

/-- The dense matrix a sparse one denotes: entries at the same position are summed. -/
def spToMat [AddCommMonoid F] {m n : ℕ} (M : List (Fin m × Fin n × F)) : Matrix (Fin m) (Fin n) F :=
  Matrix.of fun r c => ((M.filter fun e => e.1 = r ∧ e.2.1 = c).map fun e => e.2.2).sum

/-- The contract's sparse row product is Mathlib's dense `mulVec` of the denoted matrix. -/
theorem rowDot_eq [NonUnitalNonAssocSemiring F] {m n : ℕ} (M : List (Fin m × Fin n × F))
    (z : Fin n → F) (r : Fin m) : rowDot M z r = (spToMat M *ᵥ z) r := by
  induction M with
  | nil => simp [rowDot, spToMat, mulVec, dotProduct]
  | cons e M ih =>
    have hsplit : (spToMat (e :: M) *ᵥ z) r =
        (∑ c, (if e.1 = r ∧ e.2.1 = c then e.2.2 else 0) * z c) + (spToMat M *ᵥ z) r := by
      simp only [mulVec, dotProduct, spToMat, Matrix.of_apply, ← Finset.sum_add_distrib, ← add_mul,
        List.filter_cons]
      exact Finset.sum_congr rfl fun c _ => by split_ifs <;> simp_all
    rw [hsplit, ← ih]
    simp only [rowDot, List.filter_cons]
    by_cases h : e.1 = r <;> simp [h, Finset.sum_ite_eq]

/-- **The contract's gadget is CCS** with Mathlib's sums, multiset products and matrix–vector
product of the denoted dense matrices. -/
theorem Gadget.holds_iff [CommSemiring F] {width : ℕ} (g : Gadget F width) (z : Fin width → F) :
    g.holds z ↔ ∀ r, ∑ i, g.c i * (((g.S i : Multiset (Fin g.t)).map fun j =>
      (spToMat (g.M j) *ᵥ z) r).prod) = 0 := by
  simp only [Gadget.holds, Fin.sum_ofFn, rowDot_eq, Multiset.map_coe, Multiset.prod_coe]

/-- The first `cols` cells of a view are the row itself. -/
theorem view_castAdd [Zero F] [One F] (C : Chip F) (T : Table F) (r : ℕ) (c : Fin C.cols) :
    view C T r (Fin.castAdd 3 (Fin.castAdd C.cols c)) = T.cell r c := by
  simp [view]

/-- Cell `2·cols` of a view is the constant `1`. -/
theorem view_one [Zero F] [One F] (C : Chip F) (T : Table F) (r : ℕ) :
    view C T r (Fin.natAdd (C.cols + C.cols) 0) = 1 := by
  simp [view]

/-! ## Buses that no port uses -/

theorem balanced_zero (kd : BusKind) : kd.Balanced (0 : Multiset (List F)) 0 := by
  cases kd <;> simp [BusKind.Balanced]

instance [DecidableEq F] (kd : BusKind) (s r : Multiset (List F)) :
    Decidable (kd.Balanced s r) := by
  cases kd <;> unfold BusKind.Balanced <;> infer_instance

/-- A bus that no port of the layout uses carries no message. -/
theorem traffic_eq_zero [One F] [DecidableEq F] {L : Layout F} {b : ℕ}
    (h : ∀ C ∈ L.chips, ∀ p ∈ C.ports, p.bus ≠ b) (w : List (Table F)) (s : Bool) :
    traffic L w b s = 0 := by
  simp only [traffic, List.sum_eq_zero_iff, List.forall_mem_map, List.mem_filter, and_imp,
    beq_iff_eq, Bool.and_eq_true]
  exact fun ct hct p hp hb _ => absurd hb (h ct.1 (List.of_mem_zip hct).1 p hp)

section Rel
variable [Zero F] [One F] [Add F] [Mul F] [DecidableEq F]

/-- `rel` with the bus clause checked only for the buses `b < N`. -/
def Layout.relBelow (L : Layout F) (N k : ℕ) (x : Fin 32 → F) (w : List (Table F)) : Prop :=
  w.length = L.chips.length ∧
  (∀ ct ∈ L.chips.zip w, ∀ t ∈ ct.1.fixed,
    ct.2.rows = t.rows ∧ ∀ r < t.rows, ∀ c < ct.1.cols, ct.2.cell r c = t.cell r c) ∧
  (∀ ct ∈ L.chips.zip w, ∀ r < ct.2.rows, ct.1.gadget.holds (view ct.1 ct.2 r)) ∧
  (∀ b < N, (L.bus b).Balanced (traffic L w b true) (traffic L w b false)) ∧
  (∃ T ∈ w[L.pub]?, 1 ≤ T.rows ∧ ∀ i : Fin 32, T.cell 0 i = x i) ∧
  ((L.chips.zip w).map fun ct => ct.2.rows * ct.1.cols).sum ≤ 2 ^ k

instance (L : Layout F) (N k : ℕ) (x : Fin 32 → F) (w : List (Table F)) :
    Decidable (L.relBelow N k x w) := by
  unfold Layout.relBelow Gadget.holds; infer_instance

/-- With every port on a bus `< N`, `relBelow N` is `rel`. -/
theorem relBelow_iff {L : Layout F} {N : ℕ} (h : ∀ C ∈ L.chips, ∀ p ∈ C.ports, p.bus < N)
    (k : ℕ) (x : Fin 32 → F) (w : List (Table F)) : L.relBelow N k x w ↔ L.rel k x w := by
  have hb : (∀ b, (L.bus b).Balanced (traffic L w b true) (traffic L w b false)) ↔
      ∀ b < N, (L.bus b).Balanced (traffic L w b true) (traffic L w b false) := by
    refine ⟨fun hb b _ => hb b, fun hb b => if hbN : b < N then hb b hbN else ?_⟩
    simp only [traffic_eq_zero fun C hC p hp => ((h C hC p hp).trans_le (not_lt.mp hbN)).ne,
      balanced_zero]
  rw [Layout.relBelow, Layout.rel, hb]

/-! ## What `rel` reads -/

/-- The table cut to `rows × cols`: cells outside are `0`. -/
def Table.trim (cols : ℕ) (T : Table F) : Table F :=
  ⟨T.rows, fun r c => if r < T.rows ∧ c < cols then T.cell r c else 0⟩

/-- The witness cut to the layout: table `i` cut to chip `i`'s columns. -/
def Layout.trim (L : Layout F) (w : List (Table F)) : List (Table F) :=
  (L.chips.zip w).map fun ct => ct.2.trim ct.1.cols

/-- Every chip has a column, its ports read only its own columns, and the public chip has the
32 columns of the statement (admissible layouts do). -/
def Layout.ReadsOwn (L : Layout F) : Prop :=
  (∀ C ∈ L.chips, 0 < C.cols ∧ ∀ p ∈ C.ports, p.sel < C.cols ∧ ∀ c ∈ p.msg, c < C.cols) ∧
  ∀ C ∈ L.chips[L.pub]?, 32 ≤ C.cols

/-- `L` with fixed tables cut to their chip's columns and the buses `≥ N` made `eq`. -/
def Layout.normal (L : Layout F) (N : ℕ) : Layout F where
  chips := L.chips.map fun C => { C with fixed := C.fixed.map (Table.trim C.cols) }
  bus b := if b < N then L.bus b else .eq
  pub := L.pub

private theorem zip_map_zip {α β γ : Type} (l : List α) (w : List β) (g : α × β → γ) :
    l.zip ((l.zip w).map g) = (l.zip w).map fun p => (p.1, g p) := by
  induction l generalizing w with
  | nil => simp
  | cons a l ih => cases w <;> simp [ih]

omit [Add F] [Mul F] [DecidableEq F] in
private theorem view_trim {C : Chip F} {T : Table F} {r : ℕ} (hr : r < T.rows) :
    view C (T.trim C.cols) r = view C T r := by
  funext i
  have hm : (r + 1) % T.rows < T.rows := Nat.mod_lt _ (by omega)
  unfold view
  by_cases h1 : (i : ℕ) < C.cols
  · simp [h1, Table.trim, hr]
  · by_cases h2 : (i : ℕ) < C.cols + C.cols
    · simp [h1, h2, Table.trim, hm, show (i : ℕ) - C.cols < C.cols by omega]
    · simp only [h1, h2, ite_false]; rfl

omit [Add F] [Mul F] in
private theorem msgs_trim {C : Chip F} {T : Table F} {p : Port}
    (hp : p.sel < C.cols ∧ ∀ c ∈ p.msg, c < C.cols) : (T.trim C.cols).msgs p = T.msgs p := by
  unfold Table.msgs Table.trim
  congr 1
  rw [List.filter_congr (q := fun r => decide (T.cell r p.sel = 1)) fun r hr => by
    simp [List.mem_range.mp hr, hp.1]]
  exact List.map_congr_left fun r hr => List.map_congr_left fun c hc => by
    simp [List.mem_range.mp (List.mem_filter.mp hr).1, hp.2 c hc]

omit [Add F] [Mul F] in
private theorem traffic_trim {L : Layout F} (hL : L.ReadsOwn) (w : List (Table F)) (b : ℕ)
    (s : Bool) : traffic L (L.trim w) b s = traffic L w b s := by
  unfold traffic Layout.trim
  rw [zip_map_zip, List.map_map]
  exact congrArg _ (List.map_congr_left fun ct hct => congrArg _ (List.map_congr_left fun p hp =>
    msgs_trim ((hL.1 ct.1 (List.of_mem_zip hct).1).2 p (List.mem_filter.mp hp).1)))

/-- **`rel` reads a witness only inside `rows × cols`**: cutting every table to its chip changes
nothing (for layouts whose ports read their own columns and whose chips have a column). -/
theorem rel_trim_iff {L : Layout F} (hL : L.ReadsOwn) {k : ℕ} {x : Fin 32 → F} {w : List (Table F)}
    (hw : w.length = L.chips.length) : L.rel k x (L.trim w) ↔ L.rel k x w := by
  simp only [Layout.rel, traffic_trim hL]
  refine and_congr (by simp [Layout.trim, hw]) ?_
  simp only [Layout.trim, zip_map_zip, List.forall_mem_map, List.map_map, Function.comp_def,
    List.getElem?_map]
  refine and_congr ?_ (and_congr ?_ (and_congr_right' (and_congr ?_ Iff.rfl)))
  · exact forall₂_congr fun ct _ => forall₂_congr fun t _ => and_congr_right fun h =>
      forall₂_congr fun r hr => forall₂_congr fun c hc => by
        simp [Table.trim, show r < ct.2.rows from h ▸ hr, hc]
  · exact forall₂_congr fun ct _ => forall₂_congr fun r (hr : r < ct.2.rows) => by
      rw [view_trim hr]
  · rcases Nat.lt_or_ge L.pub L.chips.length with hp | hp
    · have hc : ∀ i : Fin 32, (i : ℕ) < L.chips[L.pub].cols := fun i =>
        i.2.trans_le (hL.2 _ (List.getElem?_eq_getElem hp))
      simp +contextual [hp, hw, Table.trim, hc, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
    · simp [hp, hw]

/-- **`rel` reads neither fixed tables outside `rows × cols` nor the kinds of unused buses**. -/
theorem rel_normal_iff {L : Layout F} {N : ℕ} (h : ∀ C ∈ L.chips, ∀ p ∈ C.ports, p.bus < N)
    {k : ℕ} {x : Fin 32 → F} {w : List (Table F)} : (L.normal N).rel k x w ↔ L.rel k x w := by
  have htr : ∀ b s, traffic (L.normal N) w b s = traffic L w b s := by
    intro b s; simp [traffic, Layout.normal, List.zip_map_left, List.map_map, Function.comp_def]
  have hbus : ∀ b, ((L.normal N).bus b).Balanced (traffic L w b true) (traffic L w b false) ↔
      (L.bus b).Balanced (traffic L w b true) (traffic L w b false) := by
    intro b
    by_cases hb : b < N
    · simp [Layout.normal, hb]
    · simp only [traffic_eq_zero fun C hC p hp => ((h C hC p hp).trans_le (not_lt.mp hb)).ne,
        balanced_zero]
  simp only [Layout.rel, htr, hbus]
  simp only [Layout.normal, List.length_map, List.zip_map_left, List.forall_mem_map, List.map_map,
    Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq, Option.forall_mem_map]
  refine and_congr_right' (and_congr ?_ Iff.rfl)
  refine forall₂_congr fun ct _ => forall₂_congr fun t _ => and_congr_right' ?_
  exact forall₂_congr fun r (hr : r < t.rows) => forall₂_congr fun c hc => by
    simp [Table.trim, hr, hc]

end Rel

/-! ## Consequences of admissibility -/

theorem Layout.Admissible.readsOwn {L : Layout F} {k : ℕ} (h : L.Admissible k) : L.ReadsOwn := by
  refine ⟨fun C hC => ?_, fun C hC => ?_⟩
  · obtain ⟨h1, -, -, -, -, -, -, hp⟩ := h.2.2.2.2 C hC
    exact ⟨h1, fun p hp' => ⟨(hp p hp').2.1, (hp p hp').2.2.2⟩⟩
  · obtain ⟨C', hC', h32⟩ := h.2.1
    exact Option.mem_unique hC' hC ▸ h32

theorem Layout.Admissible.bus_lt {L : Layout F} {k : ℕ} (h : L.Admissible k) :
    ∀ C ∈ L.chips, ∀ p ∈ C.ports, p.bus < 2 ^ 8 :=
  fun C hC p hp => ((h.2.2.2.2 C hC).2.2.2.2.2.2.2 p hp).1

end RecursionFast
