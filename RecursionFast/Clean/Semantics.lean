/-
  RecursionFast.Clean.Semantics  (UNTRUSTED, kernel-checked; Stage 8, DESIGN §9.3 items 2 and 4)

  `StatementPerm cm ens x`: Clean's `Ensemble.Statement` (`Clean/Air/FlatEnsemble.lean`) with
  its field-sum `BalancedChannels` replaced by a balance counted in ℕ (`BalancedPerm`, leanerVM's
  `BalancedPair` pattern): on every bus (by default, every listed channel **name**) the multiset of
  messages sent equals the multiset received. The direction and the selector of an interaction come
  from Clean's constructors (`readMult`); an interaction contributes its message once when its
  selector evaluates to `1`, nothing otherwise. The constraints are Clean's
  (`EnsembleWitness.Constraints`, assertions and lookups), unchanged.

  A channel is its name. `StatementRaw ens x`, Clean's statement with the ℕ-balance per listed
  `RawChannel` (Clean's own filter), is `StatementPerm ChannelMap.byName ens x` exactly under
  `ChannelsByName` (distinct listed names, and no unlisted channel shares a listed name):
  `statementPerm_byName_iff_raw`, `balancedPerm_byName_iff_raw` (S8-M1).

  The bridge `toLayout_rel_iff`: for an ensemble whose components stay within their widths, whose
  interactions are Clean constructors' outputs and whose map merges no channels silently
  (`Supported cm`, decidable), and whose lookups read registered tables (`LookupsFaithful`), the
  statement `x` has a witness in `(toLayout tabs ens cm).rel k` iff `x` is the padded public input
  of a Clean witness satisfying `HoldsPerm cm` whose translated tables have at most `2^k` cells.
  The witness maps are explicit both ways: `toCleanWit` (`holdsPerm_toCleanWit`, soundness, needs
  only `LookupsFaithful`) and `toLayoutWit` (`rel_toLayoutWit`, completeness). Corollaries:
  `statementPerm_iff` (with at most 32 public elements), and against Clean's channels
  `toLayout_rel_iff_raw`, `statementRaw_iff` (under `ChannelsByName`).
-/
import RecursionFast.Clean.ToLayout

namespace RecursionFast.Clean

open Air.Flat

variable {F : Type} [FiniteField F] [DecidableEq F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-! ## Multiset bookkeeping -/

section Multiset
variable {α β γ : Type}

theorem coe_flatMap_eq_sum (A : List α) (f : α → List β) :
    ((A.flatMap f : List β) : Multiset β) = (A.map fun a => ((f a : List β) : Multiset β)).sum := by
  induction A <;> simp [*, ← Multiset.coe_add]

theorem coe_filter_map_eq_sum (A : List α) (p : α → Prop) [DecidablePred p] (g : α → β) :
    ((((A.filter p).map g : List β)) : Multiset β) =
      (A.map fun r => ((if p r then [g r] else [] : List β) : Multiset β)).sum := by
  induction A with
  | nil => rfl
  | cons a A ih => by_cases h : p a <;> simp [h, ← ih]

/-- Rows outside, interactions inside = interactions outside, rows inside (as multisets). -/
theorem swap_filter (A : List α) (I : List β) (q : β → α → Prop) [∀ i r, Decidable (q i r)]
    (g : β → α → γ) :
    (((A.flatMap fun r => (I.filter fun i => q i r).map fun i => g i r) : List γ) : Multiset γ) =
      (I.map fun i => (((A.filter fun r => q i r).map fun r => g i r : List γ) : Multiset γ)).sum := by
  induction I with
  | nil => simp
  | cons i I ih =>
    rw [List.map_cons, List.sum_cons, ← ih, coe_flatMap_eq_sum, coe_flatMap_eq_sum,
      coe_filter_map_eq_sum, ← List.sum_map_add]
    refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
    by_cases h : q i r <;> simp [h]

end Multiset

/-! ## The statement with the balance counted in ℕ -/

/-- Interaction `i` is on a channel whose **name** is listed (`names`) and that `cm` puts on bus
`b`, in direction `s` (`true`: sends). A channel is its name: an unlisted `RawChannel` with a
listed name counts (exact for Clean under `ChannelsByName`). -/
def OnBus (cm : ChannelMap) (names : List String) (b : ℕ) (s : Bool) (i : AbstractInteraction F) :
    Prop :=
  i.channel.name ∈ names ∧ cm.bus names i.channel.name = b ∧ cm.dir i = s

instance (cm : ChannelMap) (names : List String) (b : ℕ) (s : Bool) (i : AbstractInteraction F) :
    Decidable (OnBus cm names b s i) := by
  unfold OnBus; infer_instance

/-- The messages Clean table `t` puts on bus `b` in direction `s` (`true`: sent, `false`:
received), counted in ℕ: on each row, each interaction on a channel whose name is listed, of bus
`b`, with direction `s` (`OnBus`), whose selector evaluates to `1` contributes its message once. -/
def tableMsgs (cm : ChannelMap) (names : List String) (t : Air.Flat.Table F) (b : ℕ) (s : Bool) :
    Multiset (List F) :=
  ((t.table.flatMap fun row =>
    (t.component.operations.interactions.filter fun i =>
      decide (OnBus cm names b s i ∧ (readMult i).2.eval (t.environment row) = 1)).map
      fun i => i.msg.toList.map (·.eval (t.environment row)) : List (List F)) : Multiset (List F))

/-- **Balance counted in ℕ** (replaces Clean's field-sum `BalancedChannels`, meaningless in
characteristic 2): on every bus of the listed channel names (each name its own bus under the
default `ChannelMap.byName`, `balancedPerm_byName_iff`), the messages sent by all tables, the
verifier's included, equal the messages received, as multisets. -/
def BalancedPerm (cm : ChannelMap) {ens : Ensemble F PublicIO} (w : EnsembleWitness ens) : Prop :=
  ∀ b < cm.nBus (chNames ens),
    (w.allTables.map fun t => tableMsgs cm (chNames ens) t b true).sum =
      (w.allTables.map fun t => tableMsgs cm (chNames ens) t b false).sum

/-- A witness satisfies the ensemble: Clean's constraints on every row of every table and the
verifier, and the ℕ-balance. -/
def HoldsPerm (cm : ChannelMap) {ens : Ensemble F PublicIO} (w : EnsembleWitness ens) : Prop :=
  w.Constraints ∧ BalancedPerm cm w

/-- **`StatementPerm cm ens x`**: Clean's `Ensemble.Statement ens x` with `BalancedChannels`
replaced by `BalancedPerm cm`. For the default map it is exactly Clean's statement with the
ℕ-balance of every listed `RawChannel` (`StatementRaw`) when `ChannelsByName` holds
(`statementPerm_byName_iff_raw`); without it, channels are names (S8-M1: `name_merge_weakens`,
`name_merge_strengthens`). -/
def StatementPerm (cm : ChannelMap) (ens : Ensemble F PublicIO) (x : PublicIO F) : Prop :=
  ∃ w : EnsembleWitness ens, w.publicInput = x ∧ HoldsPerm cm w

/-! ## Hypotheses of the bridge -/

/-- Every expression of the operations reads only the first `w` cells of a row (decidable). -/
def OpsWithin (w : ℕ) (ops : Operations F) : Prop :=
  (∀ e ∈ ops.constraints, within w e = true) ∧
  (∀ l ∈ ops.lookups, ∀ e ∈ l.entry.toList, within w e = true) ∧
  (∀ i ∈ ops.interactions, within w (readMult i).2 = true ∧ ∀ e ∈ i.msg.toList, within w e = true)

instance (w : ℕ) (ops : Operations F) : Decidable (OpsWithin w ops) := by
  unfold OpsWithin; infer_instance

/-- **The syntactic side condition** (decidable): every component's expressions stay within its
width, as Clean's own circuits do (the verifier's row is exactly the public input, so it needs no
width condition); every interaction is a Clean constructor's output (`ShapeOK`: a send, or a
receive written `(-1) · e`); and the map merges no channels silently (`ChannelMap.Separate`). -/
def Supported (cm : ChannelMap) (ens : Ensemble F PublicIO) : Prop :=
  (∀ c ∈ ens.tables, OpsWithin c.width c.rowOperations) ∧
  (∀ c ∈ ens.allTables, ∀ i ∈ c.rowOperations.interactions, ShapeOK i = true) ∧
  cm.Separate (chNames ens)

instance (cm : ChannelMap) (ens : Ensemble F PublicIO) : Decidable (Supported cm ens) := by
  unfold Supported; infer_instance

/-- **The lookups read registered tables**: every lookup of the verifier and the components has
a registered table (`tabIdx`, by name and arity) whose rows are exactly what Clean's `Contains`
accepts, for every prover data. (Lookups whose table is a function of the prover data are not
covered: see `docs/stages/S8-RESULT.md`.) -/
def LookupsFaithful (tabs : List (FixedTable F)) (ens : Ensemble F PublicIO) : Prop :=
  ∀ c ∈ ens.allTables, ∀ l ∈ c.rowOperations.lookups, ∃ t ∈ tabs[tabIdx tabs l]?,
    ∀ (data : ProverData F) (v : Vector F l.table.arity),
      l.table.Contains (data l.table.name l.table.arity) v ↔ v.toList ∈ t.rows.map Vector.toList

/-! ## The witness maps -/

/-- The statement of a public input: its elements, then zeros, in 32 cells. -/
def pubVec (p : PublicIO F) : Fin 32 → F :=
  fun i => if h : (i : ℕ) < size PublicIO then (toElements p)[(i : ℕ)] else 0

/-- No prover data (the translated relation reads none). -/
def data0 : ProverData F := fun _ _ => #[]

/-- The empty layout table. -/
def emptyTable : RecursionFast.Table F := ⟨0, fun _ _ => 0⟩

/-- The Clean rows of a layout table: row `r` is its first `w` cells. -/
def cleanRows (w : ℕ) (T : RecursionFast.Table F) : List (Array F) :=
  (List.range T.rows).map fun r => Array.ofFn fun c : Fin w => T.cell r c

/-- The Clean table of component `c` from a layout table. -/
def cleanTable (c : Component F) (T : RecursionFast.Table F) : Air.Flat.Table F where
  component := c
  width := c.width
  table := cleanRows c.width T
  data := data0
  uniform_width := by simp [cleanRows]

/-- **Layout witness ↦ Clean witness**: the public input is cells `0 … size PublicIO - 1` of
row `0` of table `0`; component `i`'s table is table `i + 1` cut to the component's width. -/
def toCleanWit (ens : Ensemble F PublicIO) (w : List (RecursionFast.Table F)) :
    EnsembleWitness ens where
  tables := List.ofFn fun i : Fin ens.tables.length =>
    cleanTable ens.tables[i] (w.getD (i + 1) emptyTable)
  data := data0
  publicInput :=
    fromElements (Vector.ofFn fun j : Fin (size PublicIO) => (w.getD 0 emptyTable).cell 0 j)
  same_length := by simp
  same_circuits := by simp [cleanTable]
  same_data := by simp [cleanTable]

/-- The layout table of a part from Clean rows: below the width the row's cells (a missing cell
`0`), then the zero padding, then each auxiliary column its expression evaluated on the row cut
to the width. -/
def Part.tableOf (names : List String) (P : Part F) (rows : List (Array F)) (data : ProverData F) :
    RecursionFast.Table F :=
  ⟨rows.length, fun r c =>
    if c < P.width then (rows.getD r #[])[c]?.getD 0
    else if c < P.base then 0
    else (((P.auxs names)[c - P.base]?).map
      (·.eval (Environment.fromArray (trunc P.width (rows.getD r #[])) data))).getD 0⟩

/-- **Clean witness ↦ layout witness**: the verifier's one row, each component's rows, each
registered table, with auxiliary columns filled. -/
def toLayoutWit (tabs : List (FixedTable F)) {ens : Ensemble F PublicIO} (w : EnsembleWitness ens) :
    List (RecursionFast.Table F) :=
  (pubPart ens).tableOf (chNames ens) [(toElements w.publicInput).toArray] w.data ::
    ((ens.tables.zip w.tables).map fun ct =>
      (compPart ct.1).tableOf (chNames ens) ct.2.table w.data) ++
    tabs.map FixedTable.table

/-- The cells of a layout witness (the quantity `rel` bounds by `2^k`). -/
def layoutCells (L : Layout F) (w : List (RecursionFast.Table F)) : ℕ :=
  ((L.chips.zip w).map fun ct => ct.2.rows * ct.1.cols).sum

/-! ## Messages, per part, in one canonical form -/

/-- The messages of a part's interactions on bus `b` in direction `s`, over `n` rows with
environments `E r`. -/
def canonMsgs (cm : ChannelMap) (names : List String) (ops : Operations F) (n : ℕ)
    (E : ℕ → Environment F) (b : ℕ) (s : Bool) : Multiset (List F) :=
  (((List.range n).flatMap fun r => (ops.interactions.filter fun i =>
      decide (OnBus cm names b s i ∧ (readMult i).2.eval (E r) = 1)).map
    fun i => i.msg.toList.map (·.eval (E r)) : List (List F)) : Multiset (List F))

/-- The entries a part looks up in registered table `j`, over `n` rows with environments `E r`. -/
def canonLooks (tabs : List (FixedTable F)) (ops : Operations F) (n : ℕ) (E : ℕ → Environment F)
    (j : ℕ) : Multiset (List F) :=
  (((List.range n).flatMap fun r => (ops.lookups.filter fun l => tabIdx tabs l = j).map
    fun l => l.entry.toList.map (·.eval (E r)) : List (List F)) : Multiset (List F))

/-- The messages chip `C`'s ports put on bus `b` in direction `s` from table `T`. -/
def portMsgs (C : Chip F) (T : RecursionFast.Table F) (b : ℕ) (s : Bool) : Multiset (List F) :=
  ((C.ports.filter fun p => p.bus == b && p.send == s).map T.msgs).sum

theorem traffic_eq (L : Layout F) (w : List (RecursionFast.Table F)) (b : ℕ) (s : Bool) :
    traffic L w b s = ((L.chips.zip w).map fun ct => portMsgs ct.1 ct.2 b s).sum := rfl

/-- In a list, equal indices mean equal members (`b` need not be assumed a member). -/
theorem idxOf_eq_iff {names : List String} {a b : String} (ha : a ∈ names) :
    names.idxOf a = names.idxOf b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have hlt := List.idxOf_lt_length_of_mem ha
  have hb : b ∈ names := List.idxOf_lt_length_iff.mp (h ▸ hlt)
  have h1 := List.getElem_idxOf hlt
  have h2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hb)
  simp only [h] at h1
  exact h1.symm.trans h2

namespace Part
variable {cm : ChannelMap} {names : List String} {tabs : List (FixedTable F)} {P : Part F}

omit [DecidableEq F] in
theorem ints_bus_lt {i : AbstractInteraction F} (hi : i ∈ P.ints names) :
    cm.bus names i.channel.name < cm.nBus names :=
  cm.bus_lt_nBus (by simpa [ints] using (List.mem_filter.mp hi).2)

/-- **A part's ports on a channel bus** carry Clean's messages of that bus. -/
theorem portMsgs_chan {T : RecursionFast.Table F} {data : ProverData F}
    (haux : ∀ r < T.rows, P.AuxOK names T r data) {b : ℕ} (hb : b < cm.nBus names) (s : Bool) :
    portMsgs (P.chip cm names tabs) T b s =
      canonMsgs cm names P.ops T.rows (P.env T · data) b s := by
  unfold portMsgs canonMsgs
  dsimp only [chip]
  rw [List.filter_append, List.map_append, List.sum_append]
  have hl : (P.ops.lookups.map (P.lookPort cm names tabs)).filter
      (fun p => p.bus == b && p.send == s) = [] := by
    refine List.filter_eq_nil_iff.mpr fun p hp => ?_
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hp
    simp [lookPort]; omega
  rw [hl, List.map_nil, List.sum_nil, add_zero, List.filter_map, List.map_map]
  have hI : (P.ints names).filter ((fun p => p.bus == b && p.send == s) ∘ P.intPort cm names) =
      P.ops.interactions.filter fun i => decide (OnBus cm names b s i) := by
    rw [ints, List.filter_filter]
    refine List.filter_congr fun i _ => Bool.eq_iff_iff.mpr ?_
    simp only [Function.comp_apply, intPort, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact and_comm
  rw [hI]
  rw [List.map_congr_left fun i hi => (show (T.msgs ∘ P.intPort cm names) i = _ from
    msgs_intPort haux (List.mem_filter.mp (hI ▸ hi : i ∈ (P.ints names).filter _)).1)]
  refine (swap_filter (List.range T.rows)
    (P.ops.interactions.filter fun i => decide (OnBus cm names b s i))
    (fun i r => (readMult i).2.eval (P.env T r data) = 1)
    (fun i r => i.msg.toList.map (·.eval (P.env T r data)))).symm.trans ?_
  simp only [List.filter_filter, Bool.decide_and, Bool.and_comm]

/-- **A part's ports on a lookup bus** receive the entries it looks up in that table. -/
theorem portMsgs_look {T : RecursionFast.Table F} {data : ProverData F}
    (haux : ∀ r < T.rows, P.AuxOK names T r data) (j : ℕ) (s : Bool) :
    portMsgs (P.chip cm names tabs) T (cm.nBus names + j) s =
      if s then 0 else canonLooks tabs P.ops T.rows (P.env T · data) j := by
  unfold portMsgs canonLooks
  dsimp only [chip]
  rw [List.filter_append, List.map_append, List.sum_append]
  have hi : ((P.ints names).map (P.intPort cm names)).filter
      (fun p => p.bus == cm.nBus names + j && p.send == s) = [] := by
    refine List.filter_eq_nil_iff.mpr fun p hp => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have := ints_bus_lt (cm := cm) hi
    simp [intPort]; omega
  rw [hi, List.map_nil, List.sum_nil, zero_add, List.filter_map, List.map_map]
  cases s
  · have hI : P.ops.lookups.filter ((fun p => p.bus == cm.nBus names + j && p.send == false) ∘
        P.lookPort cm names tabs) = P.ops.lookups.filter fun l => decide (tabIdx tabs l = j) := by
      refine List.filter_congr fun l _ => ?_
      rw [Bool.eq_iff_iff]
      simp [lookPort]
    rw [hI, List.map_congr_left fun l hl => (show (T.msgs ∘ P.lookPort cm names tabs) l = _ from
      msgs_lookPort haux (List.mem_filter.mp (hI ▸ hl : l ∈ P.ops.lookups.filter _)).1)]
    simpa using (swap_filter (List.range T.rows) (P.ops.lookups.filter fun l => tabIdx tabs l = j)
      (fun _ _ => True) (fun l r => l.entry.toList.map (·.eval (P.env T r data)))).symm
  · rw [List.filter_eq_nil_iff.mpr fun l _ => by simp [lookPort]]
    rfl

end Part

theorem portMsgs_none {C : Chip F} {T : RecursionFast.Table F} {b : ℕ}
    (h : ∀ p ∈ C.ports, p.bus ≠ b)
    (s : Bool) : portMsgs C T b s = 0 := by
  unfold portMsgs
  rw [List.filter_eq_nil_iff.mpr fun p hp => by simp [h p hp]]
  rfl

/-- The fixed chip of a registered table sends exactly the table's rows. -/
theorem portMsgs_tab (t : FixedTable F) (b : ℕ) {T : RecursionFast.Table F}
    (hrows : T.rows = t.rows.length)
    (hcell : ∀ r < t.rows.length, ∀ c < t.arity + 1, T.cell r c = t.table.cell r c) (b' : ℕ)
    (s : Bool) :
    portMsgs (t.chip b) T b' s = if b' = b ∧ s = true then ((t.rows.map Vector.toList : List (List F)) : Multiset (List F)) else 0 := by
  unfold portMsgs FixedTable.chip
  dsimp only
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp only [beq_self_eq_true, Bool.and_self, List.filter_cons_of_pos, List.filter_nil,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    unfold Table.msgs
    rw [hrows]
    congr 1
    rw [List.filter_eq_self.mpr fun r hr => by
      rw [hcell r (List.mem_range.mp hr) t.arity (by omega)]; simp [FixedTable.table]]
    refine List.ext_getElem (by simp) fun r h1 _ => List.ext_getElem (by simp) fun c h3 _ => ?_
    simp only [List.getElem_map, List.length_map, List.length_range] at h1 h3
    simp [hcell r h1 c (by omega), FixedTable.table, h3, List.getElem?_eq_getElem h1]
  · simp [eq_comm (a := b), h]

/-! ## Clean tables in the canonical form -/

omit [DecidableEq F] in
theorem map_getD_range {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun r => l.getD r d) = l :=
  List.ext_getElem (by simp) fun _ _ h => by simp [h]

/-- The environment of row `r` of a Clean table. -/
def rowEnv (t : Air.Flat.Table F) (r : ℕ) : Environment F := t.environment (t.table.getD r #[])

theorem tableMsgs_eq (cm : ChannelMap) (names : List String) (t : Air.Flat.Table F) (b : ℕ)
    (s : Bool) :
    tableMsgs cm names t b s =
      canonMsgs cm names t.component.rowOperations t.table.length (rowEnv t) b s := by
  unfold tableMsgs canonMsgs rowEnv
  conv_lhs => rw [← map_getD_range t.table #[]]
  rw [List.flatMap_map, Component.interactions_eq]

omit [DecidableEq F] in
/-- Clean's constraints on a table, row by row: assertions and lookups. -/
theorem table_constraints_iff (t : Air.Flat.Table F) :
    t.Constraints ↔ ∀ r < t.table.length,
      (∀ e ∈ t.component.rowOperations.constraints, e.eval (rowEnv t r) = 0) ∧
      (∀ l ∈ t.component.rowOperations.lookups, l.Contains (rowEnv t r)) := by
  unfold Air.Flat.Table.Constraints rowEnv
  conv_lhs => rw [← map_getD_range t.table #[]]
  simp only [List.forall_mem_map, List.mem_range, Operations.ConstraintsHold,
    Component.constraints_eq, Component.lookups_eq]

theorem canonMsgs_congr {cm : ChannelMap} {names : List String} {ops : Operations F} {n : ℕ}
    {E E' : ℕ → Environment F}
    (h : ∀ r < n, ∀ i ∈ ops.interactions, (readMult i).2.eval (E r) = (readMult i).2.eval (E' r) ∧
      i.msg.toList.map (·.eval (E r)) = i.msg.toList.map (·.eval (E' r))) (b : ℕ) (s : Bool) :
    canonMsgs cm names ops n E b s = canonMsgs cm names ops n E' b s := by
  unfold canonMsgs
  congr 1
  refine List.flatMap_congr fun r hr => ?_
  have hr := List.mem_range.mp hr
  rw [List.filter_congr fun i hi => by rw [(h r hr i hi).1]]
  exact List.map_congr_left fun i hi => (h r hr i (List.mem_filter.mp hi).1).2

omit [DecidableEq F] in
theorem canonLooks_congr {tabs : List (FixedTable F)} {ops : Operations F} {n : ℕ}
    {E E' : ℕ → Environment F}
    (h : ∀ r < n, ∀ l ∈ ops.lookups, l.entry.toList.map (·.eval (E r)) = l.entry.toList.map (·.eval (E' r)))
    (j : ℕ) : canonLooks tabs ops n E j = canonLooks tabs ops n E' j := by
  unfold canonLooks
  congr 1
  refine List.flatMap_congr fun r hr => ?_
  exact List.map_congr_left fun l hl => h r (List.mem_range.mp hr) l (List.mem_filter.mp hl).1

/-! ## The translated layout, chip by chip -/

section Main
variable {cm : ChannelMap} {tabs : List (FixedTable F)} {ens : Ensemble F PublicIO}

/-- The fixed chips of the registered tables. -/
abbrev tabChips (cm : ChannelMap) (tabs : List (FixedTable F)) (ens : Ensemble F PublicIO) :
    List (Chip F) :=
  List.ofFn fun j : Fin tabs.length => tabs[j].chip (cm.nBus (chNames ens) + j)

theorem toLayout_chips : (toLayout tabs ens cm).chips = (pubPart ens).chip cm (chNames ens) tabs ::
    ((ens.tables.map fun c => (compPart c).chip cm (chNames ens) tabs) ++ tabChips cm tabs ens) := rfl

theorem split_wit {w : List (RecursionFast.Table F)}
    (hw : w.length = (toLayout tabs ens cm).chips.length) :
    ∃ w0 wc wt, w = w0 :: (wc ++ wt) ∧ wc.length = ens.tables.length ∧ wt.length = tabs.length := by
  rw [toLayout_chips] at hw
  simp only [List.length_cons, List.length_append, List.length_map, List.length_ofFn] at hw
  obtain ⟨w0, w', rfl⟩ : ∃ w0 w', w = w0 :: w' := List.exists_cons_of_length_eq_add_one hw
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hw
  refine ⟨w0, w'.take ens.tables.length, w'.drop ens.tables.length, by simp, by simp; omega,
    by simp; omega⟩

theorem zip_chips {w0 : RecursionFast.Table F} {wc wt : List (RecursionFast.Table F)}
    (hc : wc.length = ens.tables.length) :
    (toLayout tabs ens cm).chips.zip (w0 :: (wc ++ wt)) =
      ((pubPart ens).chip cm (chNames ens) tabs, w0) ::
        (((ens.tables.zip wc).map fun cT => ((compPart cT.1).chip cm (chNames ens) tabs, cT.2)) ++
          (tabChips cm tabs ens).zip wt) := by
  rw [toLayout_chips, List.zip_cons_cons, List.zip_append (by simp [hc]), List.zip_map_left]
  rfl

omit [FiniteField F] [DecidableEq F] in
theorem sum_zip_ofFn {α β : Type} [AddCommMonoid β] {n : ℕ} (f : Fin n → Chip F)
    {wt : List α} (ht : wt.length = n) (g : Chip F → α → β) :
    (((List.ofFn f).zip wt).map fun ct => g ct.1 ct.2).sum =
      ∑ j : Fin n, g (f j) (wt[(j : ℕ)]'(by rw [ht]; exact j.2)) := by
  rw [← List.sum_ofFn]
  congr 1
  exact List.ext_getElem (by simp [ht]) fun _ _ _ => by simp

/-- **Traffic, chip by chip**: the public chip, the components, the fixed chips. -/
theorem traffic_split {w0 : RecursionFast.Table F} {wc wt : List (RecursionFast.Table F)}
    (hc : wc.length = ens.tables.length) (ht : wt.length = tabs.length) (b : ℕ) (s : Bool) :
    traffic (toLayout tabs ens cm) (w0 :: (wc ++ wt)) b s =
      portMsgs ((pubPart ens).chip cm (chNames ens) tabs) w0 b s +
        ((ens.tables.zip wc).map fun cT => portMsgs ((compPart cT.1).chip cm (chNames ens) tabs) cT.2 b s).sum +
        ∑ j : Fin tabs.length, portMsgs (tabs[j].chip (cm.nBus (chNames ens) + j)) (wt[(j : ℕ)]'(by rw [ht]; exact j.2)) b s := by
  rw [traffic_eq, zip_chips hc, List.map_cons, List.sum_cons, List.map_append, List.sum_append,
    List.map_map, add_assoc]
  congr 2
  exact sum_zip_ofFn _ ht (fun C T => portMsgs C T b s)

/-- The fixed chips carry nothing on a channel bus. -/
theorem tabs_sum_chan {wt : List (RecursionFast.Table F)} (ht : wt.length = tabs.length) {b : ℕ}
    (hb : b < cm.nBus (chNames ens)) (s : Bool) :
    ∑ j : Fin tabs.length, portMsgs (tabs[j].chip (cm.nBus (chNames ens) + j)) (wt[(j : ℕ)]'(by rw [ht]; exact j.2)) b s
      = 0 :=
  Finset.sum_eq_zero fun j _ => portMsgs_none (fun p hp => by
    simp only [FixedTable.chip, List.mem_singleton] at hp; subst hp; dsimp only; omega) s

/-- On a lookup bus the fixed chips send exactly the registered table's rows. -/
theorem tabs_sum_look {wt : List (RecursionFast.Table F)} (ht : wt.length = tabs.length)
    (hfix : ∀ j : Fin tabs.length, (wt[(j : ℕ)]'(by rw [ht]; exact j.2)).rows = tabs[j].rows.length ∧
      ∀ r < tabs[j].rows.length, ∀ c < tabs[j].arity + 1,
        (wt[(j : ℕ)]'(by rw [ht]; exact j.2)).cell r c = tabs[j].table.cell r c)
    (j0 : ℕ) (s : Bool) :
    ∑ j : Fin tabs.length, portMsgs (tabs[j].chip (cm.nBus (chNames ens) + j)) (wt[(j : ℕ)]'(by rw [ht]; exact j.2))
      (cm.nBus (chNames ens) + j0) s =
      if h : j0 < tabs.length ∧ s = true then
        ((tabs[j0].rows.map Vector.toList : List (List F)) : Multiset (List F)) else 0 := by
  simp only [portMsgs_tab _ _ (hfix _).1 (hfix _).2, Nat.add_left_cancel_iff]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j0, h.1⟩]
    · simp [h.2]
    · exact fun j _ hj => ite_eq_right fun h' => (hj (Fin.ext h'.1.symm)).elim
    · simp
  · refine Finset.sum_eq_zero fun j _ => ite_eq_right fun h' => ?_
    exact (h ⟨h'.1 ▸ j.2, h'.2⟩).elim

omit [FiniteField F] [DecidableEq F] in
theorem mem_list_sum {β : Type} {m : β} {L : List (Multiset β)} : m ∈ L.sum ↔ ∃ M ∈ L, m ∈ M := by
  induction L <;> simp [*]

omit [FiniteField F] [DecidableEq F] in
theorem zip_map_zip {α β γ : Type*} (l : List α) (w : List β) (g : α × β → γ) :
    l.zip ((l.zip w).map g) = (l.zip w).map fun p => (p.1, g p) := by
  induction l generalizing w <;> cases w <;> simp [*]

/-- The cells of a witness, chip by chip. -/
theorem cells_split {w0 : RecursionFast.Table F} {wc wt : List (RecursionFast.Table F)}
    (hc : wc.length = ens.tables.length) (ht : wt.length = tabs.length) :
    layoutCells (toLayout tabs ens cm) (w0 :: (wc ++ wt)) =
      w0.rows * (pubPart ens).cols (chNames ens) +
        ((ens.tables.zip wc).map fun cT => cT.2.rows * (compPart cT.1).cols (chNames ens)).sum +
        ∑ j : Fin tabs.length, (wt[(j : ℕ)]'(by rw [ht]; exact j.2)).rows * (tabs[j].arity + 1) := by
  rw [layoutCells, zip_chips hc, List.map_cons, List.sum_cons, List.map_append, List.sum_append,
    List.map_map, add_assoc]
  congr 2
  exact sum_zip_ofFn _ ht (fun C T => T.rows * C.cols)

/-! ## Soundness: a layout witness gives a Clean witness -/

omit [DecidableEq F] in
theorem toCleanWit_tables {w0 : RecursionFast.Table F} {wc wt : List (RecursionFast.Table F)}
    (hc : wc.length = ens.tables.length) :
    (toCleanWit ens (w0 :: (wc ++ wt))).tables = (ens.tables.zip wc).map fun cT => cleanTable cT.1 cT.2 := by
  refine List.ext_getElem (by simp [toCleanWit, hc]) fun i h1 h2 => ?_
  simp only [List.length_map, List.length_zip, hc, min_self] at h2
  simp only [toCleanWit, List.getElem_ofFn, List.getElem_map, List.getElem_zip]
  congr 1
  rw [List.getD_cons_succ, List.getD_eq_getElem _ _ (by simp; omega),
    List.getElem_append_left (by omega)]

omit [DecidableEq F] in
theorem rowEnv_cleanTable (c : Component F) (T : RecursionFast.Table F) {r : ℕ} (hr : r < T.rows) :
    rowEnv (cleanTable c T) r = (compPart c).env T r data0 := by
  simp [rowEnv, cleanTable, cleanRows, List.getD, hr,
    Air.Flat.Table.environment, Part.env, compPart]

omit [DecidableEq F] in
theorem toElements_toCleanWit (w0 : RecursionFast.Table F) (w' : List (RecursionFast.Table F)) :
    (toElements (toCleanWit ens (w0 :: w')).publicInput).toArray =
      Array.ofFn fun c : Fin (size PublicIO) => w0.cell 0 c := by
  simp [toCleanWit, ProvableType.toElements_fromElements]

omit [DecidableEq F] in
theorem rowEnv_verifier (w0 : RecursionFast.Table F) (w' : List (RecursionFast.Table F)) :
    rowEnv (toCleanWit ens (w0 :: w')).verifierTable 0 = (pubPart ens).env w0 0 data0 := by
  simp only [rowEnv, EnsembleWitness.verifierTable, List.getD_cons_zero, toElements_toCleanWit,
    Air.Flat.Table.environment, Part.env]
  rfl

/-- **Soundness of the translation**, with the explicit witness map `toCleanWit`: a layout
witness of `x` gives a Clean witness whose padded public input is `x`, which satisfies Clean's
constraints and the ℕ-balance, and whose translation back has the same number of cells. -/
theorem holdsPerm_toCleanWit (hL : LookupsFaithful tabs ens)
    {k : ℕ} {x : Fin 32 → F} {w : List (RecursionFast.Table F)}
    (h : (toLayout tabs ens cm).rel k x w) :
    x = pubVec (toCleanWit ens w).publicInput ∧ HoldsPerm cm (toCleanWit ens w) ∧
      layoutCells (toLayout tabs ens cm) (toLayoutWit tabs (toCleanWit ens w)) ≤ 2 ^ k := by
  obtain ⟨hlen, hfix, hgad, hbus, hpubc, hsize⟩ := h
  obtain ⟨w0, wc, wt, rfl, hc, ht⟩ := split_wit hlen
  have hz := zip_chips (cm := cm) (tabs := tabs) (w0 := w0) (wt := wt) hc
  set names := chNames ens with hnames
  set P0 := pubPart ens with hP0
  set cw := toCleanWit ens (w0 :: (wc ++ wt)) with hcw
  -- the gadgets
  have hg0 : ∀ r < w0.rows, (P0.chip cm names tabs).gadget.holds (view (P0.chip cm names tabs) w0 r) :=
    hgad _ (by rw [hz]; exact List.mem_cons_self)
  have hgc : ∀ cT ∈ ens.tables.zip wc, ∀ r < cT.2.rows, ((compPart cT.1).chip cm names tabs).gadget.holds
      (view ((compPart cT.1).chip cm names tabs) cT.2 r) := fun cT hcT =>
    hgad _ (by rw [hz]; exact List.mem_cons_of_mem _ (List.mem_append_left _
      (List.mem_map.mpr ⟨cT, hcT, rfl⟩)))
  -- the public chip has exactly one row, whose first cells are `x`
  obtain ⟨T, hT, h1, hx⟩ := hpubc
  obtain rfl : T = w0 := by simpa [toLayout] using hT.symm
  have hrows0 : T.rows = 1 := by
    by_contra hne
    exact one_ne_zero (((P0.holds_chip_iff T 1 data0).mp (hg0 1 (by omega))).2.2.2 rfl)
  -- the fixed chips carry their tables
  have hfixt : ∀ j : Fin tabs.length,
      (wt[(j : ℕ)]'(by rw [ht]; exact j.2)).rows = (tabs[j]'j.2).rows.length ∧
      ∀ r < (tabs[j]'j.2).rows.length, ∀ c < (tabs[j]'j.2).arity + 1,
        (wt[(j : ℕ)]'(by rw [ht]; exact j.2)).cell r c = (tabs[j]'j.2).table.cell r c := by
    intro j
    have hmem : ((tabs[j]'j.2).chip (cm.nBus names + j), wt[(j : ℕ)]'(by rw [ht]; exact j.2)) ∈
        (toLayout tabs ens cm).chips.zip (T :: (wc ++ wt)) := by
      rw [hz]
      refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
      have hj : (j : ℕ) < ((tabChips cm tabs ens).zip wt).length := by simp [ht]
      convert List.getElem_mem hj using 1
      simp [hnames]
    exact hfix _ hmem _ rfl
  -- auxiliary columns hold everywhere
  have haux0 : ∀ r < T.rows, P0.AuxOK names T r data0 := fun r hr =>
    ((P0.holds_chip_iff T r data0).mp (hg0 r hr)).2.2.1
  have hauxc : ∀ cT ∈ ens.tables.zip wc, ∀ r < cT.2.rows,
      (compPart cT.1).AuxOK names cT.2 r data0 := fun cT hcT r hr =>
    (((compPart cT.1).holds_chip_iff cT.2 r data0).mp (hgc cT hcT r hr)).2.2.1
  -- traffic on a channel bus
  have hchan : ∀ b < cm.nBus names, ∀ s, traffic (toLayout tabs ens cm) (T :: (wc ++ wt)) b s =
      (cw.allTables.map fun t => tableMsgs cm names t b s).sum := by
    intro b hb s
    rw [traffic_split hc ht, tabs_sum_chan ht hb, add_zero,
      Part.portMsgs_chan haux0 hb, EnsembleWitness.allTables, List.map_cons, List.sum_cons,
      toCleanWit_tables hc, List.map_map]
    congr 1
    · rw [tableMsgs_eq]
      simp only [EnsembleWitness.verifierTable, List.length_singleton, hrows0]
      refine canonMsgs_congr (fun r hr i _ => ?_) _ _
      obtain rfl : r = 0 := by omega
      have := rowEnv_verifier (ens := ens) T (wc ++ wt)
      simp only [EnsembleWitness.verifierTable] at this
      rw [this]; exact ⟨rfl, rfl⟩
    · refine congrArg List.sum (List.map_congr_left fun cT hcT => ?_)
      rw [Part.portMsgs_chan (hauxc cT hcT) hb, Function.comp_apply, tableMsgs_eq]
      simp only [cleanTable, cleanRows, List.length_map, List.length_range]
      refine canonMsgs_congr (fun r hr i _ => ?_) _ _
      have := rowEnv_cleanTable cT.1 cT.2 hr
      simp only [cleanTable, cleanRows] at this
      rw [this]; exact ⟨rfl, rfl⟩
  -- lookups: through the `sub` buses and the registered tables
  have hlook : ∀ (P : Part F) (Tp : RecursionFast.Table F),
      (P.chip cm names tabs, Tp) ∈ (toLayout tabs ens cm).chips.zip (T :: (wc ++ wt)) →
      (∀ r < Tp.rows, P.AuxOK names Tp r data0) →
      (∀ l ∈ P.ops.lookups, ∃ t ∈ tabs[tabIdx tabs l]?, ∀ (data : ProverData F)
        (v : Vector F l.table.arity), l.table.Contains (data l.table.name l.table.arity) v ↔
          v.toList ∈ t.rows.map Vector.toList) →
      ∀ r < Tp.rows, ∀ l ∈ P.ops.lookups, l.Contains (P.env Tp r data0) := by
    intro P Tp hmem haux hfl r hr l hl
    obtain ⟨t, htj, hfaith⟩ := hfl l hl
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp htj
    have hb := hbus (cm.nBus names + tabIdx tabs l)
    have hkind : (toLayout tabs ens cm).bus (cm.nBus names + tabIdx tabs l) = .sub := by
      simp [toLayout, hnames]
    rw [hkind] at hb
    have hsent : traffic (toLayout tabs ens cm) (T :: (wc ++ wt)) (cm.nBus names + tabIdx tabs l) true =
        ((tabs[tabIdx tabs l].rows.map Vector.toList : List (List F)) : Multiset (List F)) := by
      rw [traffic_split hc ht, Part.portMsgs_look haux0, hnames, tabs_sum_look ht hfixt,
        List.map_congr_left fun cT hcT => Part.portMsgs_look (hauxc cT hcT) _ _]
      simp [hj]
    have hm : l.entry.toList.map (·.eval (P.env Tp r data0)) ∈
        traffic (toLayout tabs ens cm) (T :: (wc ++ wt)) (cm.nBus names + tabIdx tabs l) false := by
      rw [traffic_eq, mem_list_sum]
      refine ⟨_, List.mem_map.mpr ⟨_, hmem, rfl⟩, ?_⟩
      rw [Part.portMsgs_look haux]
      simp only [Bool.false_eq_true, ite_false, canonLooks, Multiset.mem_coe, List.mem_flatMap]
      exact ⟨r, List.mem_range.mpr hr, List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨hl, by simp⟩, rfl⟩⟩
    have := hb _ hm
    rw [hsent, Multiset.mem_coe] at this
    rwa [Lookup.Contains, hfaith, Vector.toList_map]
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · -- the statement is the padded public input
    funext i
    unfold pubVec
    split_ifs with hi
    · rw [← hx i]
      simp [hcw, toCleanWit, ProvableType.toElements_fromElements]
    · have hpad := ((P0.holds_chip_iff T 0 data0).mp (hg0 0 (by omega))).2.1
        (i - size PublicIO) (by simp [hP0, pubPart]; omega)
      rw [← hx i, ← hpad]
      congr 1
      simp only [hP0, pubPart]
      omega
  · -- Clean's constraints
    intro t ht'
    rw [EnsembleWitness.allTables, List.mem_cons] at ht'
    rcases ht' with rfl | ht'
    · refine (table_constraints_iff _).mpr fun r hr => ?_
      obtain rfl : r = 0 := by simpa [EnsembleWitness.verifierTable] using hr
      have h0 := rowEnv_verifier (ens := ens) T (wc ++ wt)
      simp only [EnsembleWitness.verifierTable] at h0 ⊢
      rw [h0]
      exact ⟨((P0.holds_chip_iff T 0 data0).mp (hg0 0 (by omega))).1, hlook P0 T
        (by rw [hz]; exact List.mem_cons_self) haux0 (hL _ Ensemble.mem_allTables_verifierTable) 0
        (by omega)⟩
    · rw [toCleanWit_tables hc] at ht'
      obtain ⟨cT, hcT, rfl⟩ := List.mem_map.mp ht'
      refine (table_constraints_iff _).mpr fun r hr => ?_
      simp only [cleanTable, cleanRows, List.length_map, List.length_range] at hr
      have h0 := rowEnv_cleanTable cT.1 cT.2 hr
      simp only [cleanTable] at h0 ⊢
      rw [h0]
      have hmem : ((compPart cT.1).chip cm names tabs, cT.2) ∈
          (toLayout tabs ens cm).chips.zip (T :: (wc ++ wt)) := by
        rw [hz]; exact List.mem_cons_of_mem _ (List.mem_append_left _
          (List.mem_map.mpr ⟨cT, hcT, rfl⟩))
      exact ⟨(((compPart cT.1).holds_chip_iff cT.2 r data0).mp (hgc cT hcT r hr)).1,
        hlook _ _ hmem (hauxc cT hcT)
          (hL _ (Ensemble.mem_allTables_of_mem_tables (List.of_mem_zip hcT).1)) r hr⟩
  · -- the ℕ-balance
    intro b hb
    have hbal := hbus b
    have hkind : (toLayout tabs ens cm).bus b = .eq := by simp [toLayout, hb]
    rw [hkind] at hbal
    rwa [← hchan b hb true, ← hchan b hb false]
  · -- the cells
    refine le_of_eq_of_le ?_ hsize
    show layoutCells _ _ = layoutCells _ _
    have hcw' : (toLayoutWit tabs cw) = P0.tableOf names [(toElements cw.publicInput).toArray] cw.data ::
        (((ens.tables.zip cw.tables).map fun ct => (compPart ct.1).tableOf names ct.2.table cw.data) ++
          tabs.map FixedTable.table) := rfl
    rw [hcw', cells_split (by simp [← cw.same_length]) (by simp), cells_split hc ht]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) (Finset.sum_congr rfl fun j _ => ?_)
    · simp [Part.tableOf, hrows0]
    · rw [show cw.tables = _ from toCleanWit_tables hc, zip_map_zip, List.map_map, zip_map_zip,
        List.map_map]
      refine congrArg List.sum (List.map_congr_left fun cT _ => ?_)
      simp [Part.tableOf, cleanTable, cleanRows]
    · simp [FixedTable.table, (hfixt j).1]

/-! ## Completeness: a Clean witness gives a layout witness -/

/-- Two environments agree on everything the operations read. -/
def EvalAgree (ops : Operations F) (A B : Environment F) : Prop :=
  A.data = B.data ∧
  (∀ e ∈ ops.constraints, e.eval A = e.eval B) ∧
  (∀ l ∈ ops.lookups, ∀ e ∈ l.entry.toList, e.eval A = e.eval B) ∧
  (∀ i ∈ ops.interactions, (readMult i).2.eval A = (readMult i).2.eval B ∧
    ∀ e ∈ i.msg.toList, e.eval A = e.eval B)

theorem evalAgree_trunc {w : ℕ} {ops : Operations F} (h : OpsWithin w ops) (row : Array F)
    (data : ProverData F) :
    EvalAgree ops (Environment.fromArray (trunc w row) data) (Environment.fromArray row data) :=
  ⟨rfl, fun e he => eval_trunc (h.1 e he) row data,
    fun l hl e he => eval_trunc (h.2.1 l hl e he) row data,
    fun i hi => ⟨eval_trunc (h.2.2 i hi).1 row data, fun e he => eval_trunc ((h.2.2 i hi).2 e he) row data⟩⟩

namespace Part
variable {names : List String} {P : Part F}

theorem tableOf_rows (rows : List (Array F)) (data : ProverData F) :
    (P.tableOf names rows data).rows = rows.length := rfl

theorem env_tableOf (rows : List (Array F)) (data data' : ProverData F) (r : ℕ) :
    P.env (P.tableOf names rows data) r data' =
      Environment.fromArray (trunc P.width (rows.getD r #[])) data' := by
  simp [env, trunc, tableOf]

theorem auxOK_tableOf (rows : List (Array F)) (data : ProverData F) (r : ℕ) :
    P.AuxOK names (P.tableOf names rows data) r data := by
  intro j
  rw [env_tableOf]
  have h1 : ¬ (P.base + (j : ℕ) < P.width) := by have := P.width_le; omega
  have h2 : ¬ (P.base + (j : ℕ) < P.base) := by omega
  simp only [tableOf, h1, h2, ite_false, Nat.add_sub_cancel_left, Fin.getElem_fin]
  rw [List.getElem?_eq_getElem j.2, Option.map_some, Option.getD_some]

theorem pad_tableOf (rows : List (Array F)) (data : ProverData F) (r : ℕ) {j : ℕ}
    (hj : j < P.base - P.width) : (P.tableOf names rows data).cell r (P.width + j) = 0 := by
  have h1 : ¬ (P.width + j < P.width) := by omega
  have h2 : P.width + j < P.base := by omega
  simp [tableOf, h1, h2]

end Part

/-- **One Clean table as its chip's table**, given that the chip's row environments agree with
Clean's on what the operations read: every row satisfies the gadget (except the one-row flag), and
the channel ports carry Clean's messages. -/
theorem part_complete {names : List String} (P : Part F) (t : Air.Flat.Table F)
    (hops : t.component.rowOperations = P.ops)
    (hag : ∀ r < t.table.length, EvalAgree P.ops (P.env (P.tableOf names t.table t.data) r t.data)
      (rowEnv t r))
    (hcons : t.Constraints) {r : ℕ} (hr : r < t.table.length) (h1 : P.oneRow = true → r = 0) :
    (P.chip cm names tabs).gadget.holds (view (P.chip cm names tabs) (P.tableOf names t.table t.data) r) := by
  rw [P.holds_chip_iff _ r t.data]
  refine ⟨fun e he => ?_, fun j hj => Part.pad_tableOf _ _ r hj, Part.auxOK_tableOf _ _ r, h1⟩
  rw [(hag r hr).2.1 e he]
  exact ((table_constraints_iff t).mp hcons r hr).1 e (hops ▸ he)

theorem part_chan {names : List String} (P : Part F) (t : Air.Flat.Table F)
    (hops : t.component.rowOperations = P.ops)
    (hag : ∀ r < t.table.length, EvalAgree P.ops (P.env (P.tableOf names t.table t.data) r t.data)
      (rowEnv t r)) {b : ℕ} (hb : b < cm.nBus names) (s : Bool) :
    portMsgs (P.chip cm names tabs) (P.tableOf names t.table t.data) b s =
      tableMsgs cm names t b s := by
  rw [Part.portMsgs_chan (fun r _ => Part.auxOK_tableOf _ _ r) hb, tableMsgs_eq, hops,
    Part.tableOf_rows]
  exact canonMsgs_congr (fun r hr i hi => ⟨(hag r hr).2.2.2 i hi |>.1,
    List.map_congr_left ((hag r hr).2.2.2 i hi).2⟩) _ _

theorem part_look {names : List String} (P : Part F) (t : Air.Flat.Table F)
    (hops : t.component.rowOperations = P.ops)
    (hag : ∀ r < t.table.length, EvalAgree P.ops (P.env (P.tableOf names t.table t.data) r t.data)
      (rowEnv t r))
    (hcons : t.Constraints)
    (hfl : ∀ l ∈ P.ops.lookups, ∃ t' ∈ tabs[tabIdx tabs l]?, ∀ (data : ProverData F)
      (v : Vector F l.table.arity), l.table.Contains (data l.table.name l.table.arity) v ↔
        v.toList ∈ t'.rows.map Vector.toList)
    {j : ℕ} {m : List F}
    (hm : m ∈ canonLooks tabs P.ops (P.tableOf names t.table t.data).rows
      (P.env (P.tableOf names t.table t.data) · t.data) j) :
    ∃ h : j < tabs.length, m ∈ tabs[j].rows.map Vector.toList := by
  rw [canonLooks, Multiset.mem_coe, List.mem_flatMap] at hm
  obtain ⟨r, hr, hm⟩ := hm
  obtain ⟨l, hlf, rfl⟩ := List.mem_map.mp hm
  obtain ⟨hlm, hlj⟩ := List.mem_filter.mp hlf
  obtain rfl := of_decide_eq_true hlj
  rw [Part.tableOf_rows, List.mem_range] at hr
  obtain ⟨t', ht', hfaith⟩ := hfl l hlm
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp ht'
  refine ⟨hj, ?_⟩
  have hc := ((table_constraints_iff t).mp hcons r hr).2 l (hops ▸ hlm)
  rw [Lookup.Contains, hfaith, Vector.toList_map] at hc
  exact (List.map_congr_left ((hag r hr).2.2.1 l hlm)).symm ▸ hc

theorem EvalAgree.refl (ops : Operations F) (A : Environment F) : EvalAgree ops A A :=
  ⟨rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => ⟨rfl, fun _ _ => rfl⟩⟩

omit [DecidableEq F] in
theorem trunc_of_size {w : ℕ} {row : Array F} (h : row.size = w) : trunc w row = row :=
  Array.ext (by simp [trunc, h]) fun _ _ h2 => by simp [trunc, h2]

omit [DecidableEq F] in
theorem component_of_mem_zip {cw : EnsembleWitness ens} {ct : Component F × Air.Flat.Table F}
    (h : ct ∈ ens.tables.zip cw.tables) : ct.2.component = ct.1 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  simp only [List.getElem_zip]
  exact (cw.same_circuits i (by simp at hi; omega)).symm

/-- **Completeness of the translation**, with the explicit witness map `toLayoutWit`: a Clean
witness satisfying `HoldsPerm`, whose translation has at most `2^k` cells, gives a layout witness
of its padded public input. -/
theorem rel_toLayoutWit (hS : Supported cm ens)
    (hL : LookupsFaithful tabs ens) {k : ℕ} {cw : EnsembleWitness ens} (h : HoldsPerm cm cw)
    (hk : layoutCells (toLayout tabs ens cm) (toLayoutWit tabs cw) ≤ 2 ^ k) :
    (toLayout tabs ens cm).rel k (pubVec cw.publicInput) (toLayoutWit tabs cw) := by
  obtain ⟨hcons, hbal⟩ := h
  set names := chNames ens with hnames
  set P0 := pubPart ens with hP0
  set vt := cw.verifierTable with hvt
  set T0 := P0.tableOf names vt.table vt.data with hT0
  set wc := (ens.tables.zip cw.tables).map fun ct => (compPart ct.1).tableOf names ct.2.table ct.2.data
    with hwc
  set wt := tabs.map FixedTable.table with hwt
  have hdata : ∀ ct ∈ ens.tables.zip cw.tables, ct.2.data = cw.data :=
    fun ct hct => cw.same_data _ (List.of_mem_zip hct).2
  have hW : toLayoutWit tabs cw = T0 :: (wc ++ wt) :=
    congrArg (T0 :: · ++ wt) (List.map_congr_left fun ct hct => by rw [hdata ct hct])
  have hc : wc.length = ens.tables.length := by simp [hwc, ← cw.same_length]
  have ht : wt.length = tabs.length := by simp [hwt]
  rw [hW] at hk ⊢
  have hz := zip_chips (cm := cm) (tabs := tabs) (w0 := T0) (wt := wt) hc
  have hzc : ens.tables.zip wc = (ens.tables.zip cw.tables).map fun ct =>
      (ct.1, (compPart ct.1).tableOf names ct.2.table ct.2.data) := zip_map_zip _ _ _
  -- the environments of the chips agree with Clean's
  have hag0 : ∀ r < vt.table.length, EvalAgree P0.ops (P0.env T0 r vt.data) (rowEnv vt r) := by
    intro r hr
    obtain rfl : r = 0 := by simpa [hvt, EnsembleWitness.verifierTable] using hr
    rw [hT0, Part.env_tableOf]
    have : trunc P0.width (vt.table.getD 0 #[]) = vt.table.getD 0 #[] :=
      trunc_of_size (by simp [hvt, EnsembleWitness.verifierTable, hP0, pubPart])
    rw [this]
    exact EvalAgree.refl _ _
  have hagc : ∀ ct ∈ ens.tables.zip cw.tables, ∀ r < ct.2.table.length,
      EvalAgree (compPart ct.1).ops
        ((compPart ct.1).env ((compPart ct.1).tableOf names ct.2.table ct.2.data) r ct.2.data)
        (rowEnv ct.2 r) := by
    intro ct hct r _
    rw [Part.env_tableOf]
    exact evalAgree_trunc (hS.1 ct.1 (List.of_mem_zip hct).1) _ _
  have hopsc : ∀ ct ∈ ens.tables.zip cw.tables, ct.2.component.rowOperations = (compPart ct.1).ops :=
    fun ct hct => by rw [component_of_mem_zip hct]; rfl
  have hcons0 : vt.Constraints := hcons _ (EnsembleWitness.mem_allTables_verifierTable _)
  have hconsc : ∀ ct ∈ ens.tables.zip cw.tables, ct.2.Constraints := fun ct hct =>
    hcons _ (EnsembleWitness.mem_allTables_of_mem_tables _ (List.of_mem_zip hct).2)
  have hrows0 : T0.rows = 1 := by simp [hT0, Part.tableOf_rows, hvt, EnsembleWitness.verifierTable]
  -- channel traffic is Clean's
  have hchan : ∀ b < cm.nBus names, ∀ s, traffic (toLayout tabs ens cm) (T0 :: (wc ++ wt)) b s =
      (cw.allTables.map fun t => tableMsgs cm names t b s).sum := by
    intro b hb s
    rw [traffic_split hc ht, tabs_sum_chan ht hb, add_zero,
      hT0, part_chan P0 vt rfl hag0 hb, EnsembleWitness.allTables, List.map_cons, List.sum_cons,
      hzc, List.map_map]
    congr 1
    conv_rhs => rw [← List.map_snd_zip (l₁ := ens.tables) (l₂ := cw.tables) (by rw [cw.same_length]),
      List.map_map]
    exact congrArg List.sum (List.map_congr_left fun ct hct =>
      part_chan (compPart ct.1) ct.2 (hopsc ct hct) (hagc ct hct) hb s)
  -- the chips of the zip, by kind
  have hmemz : ∀ ct ∈ (toLayout tabs ens cm).chips.zip (T0 :: (wc ++ wt)),
      ct = (P0.chip cm names tabs, T0) ∨
      (∃ p ∈ ens.tables.zip cw.tables, ct = ((compPart p.1).chip cm names tabs,
        (compPart p.1).tableOf names p.2.table p.2.data)) ∨
      ∃ j : Fin tabs.length,
        ct = ((tabs[j]'j.2).chip (cm.nBus names + j), (tabs[j]'j.2).table) := by
    intro ct hct
    rw [hz, List.mem_cons, List.mem_append, hzc, List.map_map] at hct
    rcases hct with rfl | hct | hct
    · exact Or.inl rfl
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hct
      exact Or.inr (Or.inl ⟨p, hp, rfl⟩)
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hct
      simp only [List.length_zip, List.length_ofFn, hwt, List.length_map, min_self] at hj
      refine Or.inr (Or.inr ⟨⟨j, hj⟩, ?_⟩)
      simp [hwt, hnames]
  refine ⟨by simp [toLayout_chips, hc, ht], ?_, ?_, ?_, ?_, hk⟩
  · -- fixed tables
    intro ct hct t' ht'
    rcases hmemz ct hct with rfl | ⟨p, -, rfl⟩ | ⟨j, rfl⟩ <;> cases ht'
    exact ⟨rfl, fun _ _ _ _ => rfl⟩
  · -- gadgets
    intro ct hct r hr
    rcases hmemz ct hct with rfl | ⟨p, hp, rfl⟩ | ⟨j, rfl⟩
    · rw [hrows0] at hr
      obtain rfl : r = 0 := by omega
      exact part_complete P0 vt rfl hag0 hcons0 (by simp [hvt, EnsembleWitness.verifierTable])
        (fun _ => rfl)
    · exact part_complete (compPart p.1) p.2 (hopsc p hp) (hagc p hp) (hconsc p hp) hr
        (fun h => absurd h (by simp [compPart]))
    · exact fun r' => r'.elim0
  · -- buses
    intro b
    by_cases hb : b < cm.nBus names
    · have hkind : (toLayout tabs ens cm).bus b = .eq := by simp [toLayout, ← hnames, hb]
      rw [hkind, hchan b hb true, hchan b hb false]
      exact hbal b hb
    · have hkind : (toLayout tabs ens cm).bus b = .sub := by simp [toLayout, ← hnames, hb]
      rw [hkind]
      obtain ⟨j, rfl⟩ : ∃ j, b = cm.nBus names + j := ⟨b - cm.nBus names, by omega⟩
      intro m hm
      rw [traffic_split hc ht, hnames, tabs_sum_look ht fun j =>
        ⟨by simp [hwt, FixedTable.table], fun r _ c _ => by simp [hwt]⟩] at hm ⊢
      rw [hT0, Part.portMsgs_look (fun r _ => Part.auxOK_tableOf _ _ r)] at hm
      simp only [Bool.false_eq_true, and_false, dite_false, add_zero, ite_false] at hm
      obtain ⟨hj, hmj⟩ : ∃ h : j < tabs.length, m ∈ tabs[j].rows.map Vector.toList := by
        rcases Multiset.mem_add.mp hm with hm | hm
        · exact part_look P0 vt rfl hag0 hcons0 (hL _ Ensemble.mem_allTables_verifierTable) hm
        · rw [hzc, List.map_map, mem_list_sum] at hm
          obtain ⟨M, hM, hm⟩ := hm
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hM
          rw [Function.comp_apply, Part.portMsgs_look (fun r _ => Part.auxOK_tableOf _ _ r)] at hm
          exact part_look (compPart p.1) p.2 (hopsc p hp) (hagc p hp) (hconsc p hp)
            (hL _ (Ensemble.mem_allTables_of_mem_tables (List.of_mem_zip hp).1)) hm
      rw [dite_eq_left ⟨hj, rfl⟩]
      exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_coe.mpr hmj))
  · -- the public chip: one row, the padded public input
    refine ⟨T0, rfl, by omega, fun i => ?_⟩
    simp only [hT0, Part.tableOf, hvt, EnsembleWitness.verifierTable, hP0, pubPart, pubVec]
    split_ifs with h1 h2
    · simp only [List.getD_cons_zero, Vector.getElem?_toArray, Vector.getElem?_eq_getElem h1,
        Option.getD_some]
    · rfl
    · exact absurd (lt_of_lt_of_le i.2 (le_max_left _ _)) h2

/-! ## The default map: each channel balances on its own -/

/-- The messages Clean table `t` puts on the channel named `nm` in direction `s` (read from the
multiplicity), counted in ℕ. -/
def tableMsgsByName (t : Air.Flat.Table F) (nm : String) (s : Bool) : Multiset (List F) :=
  ((t.table.flatMap fun row =>
    (t.component.operations.interactions.filter fun i =>
      decide (i.channel.name = nm ∧ (readMult i).1 = s ∧
        (readMult i).2.eval (t.environment row) = 1)).map
      fun i => i.msg.toList.map (·.eval (t.environment row)) : List (List F)) : Multiset (List F))

theorem tableMsgs_byName {names : List String} {nm : String} (hnm : nm ∈ names)
    (t : Air.Flat.Table F) (s : Bool) :
    tableMsgs ChannelMap.byName names t (names.idxOf nm) s = tableMsgsByName t nm s := by
  unfold tableMsgs tableMsgsByName
  congr 1
  refine List.flatMap_congr fun row _ => ?_
  congr 1
  refine List.filter_congr fun i _ => Bool.eq_iff_iff.mpr ?_
  simp only [decide_eq_true_eq]
  show (i.channel.name ∈ names ∧ names.idxOf i.channel.name = names.idxOf nm ∧
    (readMult i).1 = s) ∧ _ ↔ _
  exact ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨(idxOf_eq_iff h1).mp h2, h3, h4⟩,
    fun ⟨h1, h3, h4⟩ => ⟨⟨h1 ▸ hnm, by rw [h1], h3⟩, h4⟩⟩

theorem tableMsgs_byName_out {names : List String} {b : ℕ} (hb : names.length ≤ b)
    (t : Air.Flat.Table F) (s : Bool) : tableMsgs ChannelMap.byName names t b s = 0 := by
  unfold tableMsgs
  rw [List.flatMap_eq_nil_iff.mpr fun row _ => ?_]
  · rfl
  refine List.map_eq_nil_iff.mpr (List.filter_eq_nil_iff.mpr fun i _ => ?_)
  simp only [decide_eq_true_eq, not_and]
  rintro ⟨h1, h2, -⟩
  have : names.idxOf i.channel.name < names.length := List.idxOf_lt_length_of_mem h1
  exact absurd (h2 ▸ this : b < names.length) (by omega)

/-- **Under the default map each channel name balances on its own**: with distinct channel
names, `BalancedPerm ChannelMap.byName` is "on every listed channel name, the messages sent equal
the messages received", direction from each interaction's constructor. (Per `RawChannel`, as
Clean filters: `balancedPerm_byName_iff_raw`, under `ChannelsByName`.) -/
theorem balancedPerm_byName_iff {ens : Ensemble F PublicIO} (hnd : (chNames ens).Nodup)
    (w : EnsembleWitness ens) :
    BalancedPerm ChannelMap.byName w ↔ ∀ ch ∈ ens.channels,
      (w.allTables.map fun t => tableMsgsByName t ch.name true).sum =
        (w.allTables.map fun t => tableMsgsByName t ch.name false).sum := by
  constructor
  · intro h ch hch
    have hnm : ch.name ∈ chNames ens := List.mem_map.mpr ⟨ch, hch, rfl⟩
    simpa only [show ChannelMap.byName.bus (chNames ens) ch.name = (chNames ens).idxOf ch.name
      from rfl, tableMsgs_byName hnm] using h _ (ChannelMap.byName.bus_lt_nBus hnm)
  · intro h b _
    by_cases hb : b < (chNames ens).length
    · have hb' : b < ens.channels.length := by simpa [chNames] using hb
      have hidx : (chNames ens).idxOf (ens.channels[b]'hb').name = b := by
        simpa [chNames] using hnd.idxOf_getElem b hb
      have hnm : (ens.channels[b]'hb').name ∈ chNames ens :=
        List.mem_map.mpr ⟨_, List.getElem_mem hb', rfl⟩
      rw [← hidx]
      simpa only [tableMsgs_byName hnm] using h _ (List.getElem_mem hb')
    · simp only [tableMsgs_byName_out (not_lt.mp hb)]

/-! ## Clean's channels are `RawChannel`s: `ChannelsByName` (S8-M1) -/

/-- **Channels are their names**: the listed channels have distinct names, and every interaction
of the verifier and the components whose channel's name is listed is on that listed channel
itself (no unlisted `RawChannel` shares a listed name). Not decidable (a `RawChannel` carries
propositions); proved per ensemble. Without it `StatementPerm` and Clean's statement differ both
ways (`name_merge_weakens`, `name_merge_strengthens` in `Examples.lean`). -/
def ChannelsByName (ens : Ensemble F PublicIO) : Prop :=
  (chNames ens).Nodup ∧ ∀ c ∈ ens.allTables, ∀ i ∈ c.rowOperations.interactions,
    i.channel.name ∈ chNames ens → i.channel ∈ ens.channels

open Classical in
/-- The messages Clean table `t` puts on the `RawChannel` `ch` (Clean's own filter, as
`interactionsWith`) in direction `s`, counted in ℕ. -/
noncomputable def tableMsgsRaw (t : Air.Flat.Table F) (ch : RawChannel F) (s : Bool) :
    Multiset (List F) :=
  ((t.table.flatMap fun row =>
    (t.component.operations.interactions.filter fun i =>
      decide (i.channel = ch ∧ (readMult i).1 = s ∧ (readMult i).2.eval (t.environment row) = 1)).map
      fun i => i.msg.toList.map (·.eval (t.environment row)) : List (List F)) : Multiset (List F))

/-- **Clean's `BalancedChannels`, counted in ℕ**: on every listed `RawChannel`, the messages sent
equal the messages received. -/
def BalancedRaw {ens : Ensemble F PublicIO} (w : EnsembleWitness ens) : Prop :=
  ∀ ch ∈ ens.channels, (w.allTables.map fun t => tableMsgsRaw t ch true).sum =
    (w.allTables.map fun t => tableMsgsRaw t ch false).sum

/-- **Clean's `Ensemble.Statement ens x` with the balance counted in ℕ**, channel by
`RawChannel` (Clean's `BalancedChannels` filter), direction from the constructors. -/
def StatementRaw (ens : Ensemble F PublicIO) (x : PublicIO F) : Prop :=
  ∃ w : EnsembleWitness ens, w.publicInput = x ∧ w.Constraints ∧ BalancedRaw w

theorem tableMsgsByName_eq_raw {ens : Ensemble F PublicIO} (hC : ChannelsByName ens)
    {w : EnsembleWitness ens} {t : Air.Flat.Table F} (ht : t ∈ w.allTables) {ch : RawChannel F}
    (hch : ch ∈ ens.channels) (s : Bool) : tableMsgsByName t ch.name s = tableMsgsRaw t ch s := by
  classical
  have hc : t.component ∈ ens.allTables :=
    EnsembleWitness.mem_allTables_component_of_mem_allTables ht
  unfold tableMsgsByName tableMsgsRaw
  congr 1
  refine List.flatMap_congr fun row _ => ?_
  congr 1
  refine List.filter_congr fun i hi => Bool.eq_iff_iff.mpr ?_
  have hi' : i ∈ t.component.rowOperations.interactions := by
    rw [← Component.interactions_eq]; exact hi
  have key : i.channel.name = ch.name ↔ i.channel = ch := by
    refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
    have hn : i.channel.name ∈ chNames ens := h ▸ List.mem_map.mpr ⟨ch, hch, rfl⟩
    exact List.inj_on_of_nodup_map hC.1 (hC.2 _ hc i hi' hn) hch h
  simp only [decide_eq_true_eq, key]

/-- **Under `ChannelsByName`, the default map's balance is Clean's, counted in ℕ**:
`BalancedPerm ChannelMap.byName` is the per-`RawChannel` ℕ-balance `BalancedRaw`. -/
theorem balancedPerm_byName_iff_raw {ens : Ensemble F PublicIO} (hC : ChannelsByName ens)
    (w : EnsembleWitness ens) : BalancedPerm ChannelMap.byName w ↔ BalancedRaw w := by
  rw [balancedPerm_byName_iff hC.1]
  refine forall₂_congr fun ch hch => ?_
  rw [List.map_congr_left fun t ht => tableMsgsByName_eq_raw hC ht hch true,
    List.map_congr_left fun t ht => tableMsgsByName_eq_raw hC ht hch false]

/-- Under `ChannelsByName`, `StatementPerm ChannelMap.byName` is `StatementRaw`. -/
theorem statementPerm_byName_iff_raw {ens : Ensemble F PublicIO} (hC : ChannelsByName ens)
    (x : PublicIO F) : StatementPerm ChannelMap.byName ens x ↔ StatementRaw ens x :=
  exists_congr fun w => and_congr_right' (and_congr_right' (balancedPerm_byName_iff_raw hC w))

/-! ## The bridge -/

/-- **`toLayout_rel_iff`**: the statement `x` has a witness in `(toLayout tabs ens cm).rel k` iff
it is the padded public input of a Clean witness satisfying `StatementPerm`'s conditions whose
translation has at most `2^k` cells. Witness maps: `toCleanWit` (→, `holdsPerm_toCleanWit`) and
`toLayoutWit` (←, `rel_toLayoutWit`). -/
theorem toLayout_rel_iff (hS : Supported cm ens) (hL : LookupsFaithful tabs ens) (k : ℕ)
    (x : Fin 32 → F) :
    (∃ w, (toLayout tabs ens cm).rel k x w) ↔
      ∃ cw : EnsembleWitness ens, x = pubVec cw.publicInput ∧ HoldsPerm cm cw ∧
        layoutCells (toLayout tabs ens cm) (toLayoutWit tabs cw) ≤ 2 ^ k :=
  ⟨fun ⟨w, hw⟩ => ⟨toCleanWit ens w, holdsPerm_toCleanWit hL hw⟩,
    fun ⟨cw, hx, hh, hk⟩ => ⟨toLayoutWit tabs cw, hx ▸ rel_toLayoutWit hS hL hh hk⟩⟩

omit [DecidableEq F] in
/-- With at most 32 public elements the statement determines the public input. -/
theorem pubVec_injective (hpub : size PublicIO ≤ 32) :
    Function.Injective (pubVec : PublicIO F → Fin 32 → F) := by
  intro p q h
  rw [← ProvableType.fromElements_toElements p, ← ProvableType.fromElements_toElements q]
  congr 1
  apply Vector.ext
  intro i hi
  have := congrFun h ⟨i, by omega⟩
  simpa [pubVec, hi] using this

/-- **`StatementPerm` is the translated relation**: for a public input of at most 32 elements,
`StatementPerm cm ens p` iff its padded statement `pubVec p` has a witness in some size class. -/
theorem statementPerm_iff (hpub : size PublicIO ≤ 32) (hS : Supported cm ens)
    (hL : LookupsFaithful tabs ens) (p : PublicIO F) :
    StatementPerm cm ens p ↔ ∃ k w, (toLayout tabs ens cm).rel k (pubVec p) w :=
  ⟨fun ⟨_, hp, hh⟩ => hp ▸ ⟨_, _, rel_toLayoutWit hS hL hh (Nat.lt_two_pow_self).le⟩,
    fun ⟨_, _, hw⟩ => (holdsPerm_toCleanWit hL hw).elim fun hx hh =>
      ⟨_, pubVec_injective hpub hx.symm, hh.1⟩⟩

/-- **`toLayout_rel_iff` against Clean's channels** (S8-M1): under `ChannelsByName`, with the
default map, the right side is Clean's own statement with the ℕ-balance per `RawChannel`. -/
theorem toLayout_rel_iff_raw (hS : Supported ChannelMap.byName ens) (hL : LookupsFaithful tabs ens)
    (hC : ChannelsByName ens) (k : ℕ) (x : Fin 32 → F) :
    (∃ w, (toLayout tabs ens).rel k x w) ↔
      ∃ cw : EnsembleWitness ens, x = pubVec cw.publicInput ∧ cw.Constraints ∧ BalancedRaw cw ∧
        layoutCells (toLayout tabs ens) (toLayoutWit tabs cw) ≤ 2 ^ k := by
  rw [toLayout_rel_iff hS hL]
  exact exists_congr fun cw => and_congr_right' (by
    rw [HoldsPerm, balancedPerm_byName_iff_raw hC, and_assoc])

/-- **`statementPerm_iff` against Clean's channels** (S8-M1): under `ChannelsByName`, Clean's
`Ensemble.Statement` with the ℕ-balance per `RawChannel` (`StatementRaw`) is the translated
relation. -/
theorem statementRaw_iff (hpub : size PublicIO ≤ 32) (hS : Supported ChannelMap.byName ens)
    (hL : LookupsFaithful tabs ens) (hC : ChannelsByName ens) (p : PublicIO F) :
    StatementRaw ens p ↔ ∃ k w, (toLayout tabs ens).rel k (pubVec p) w :=
  (statementPerm_byName_iff_raw hC p).symm.trans (statementPerm_iff hpub hS hL p)

end Main

end RecursionFast.Clean
