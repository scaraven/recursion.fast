/-
  RecursionFast.Clean.ToLayout  (UNTRUSTED, kernel-checked; Stage 8, DESIGN §9.3 item 2)

  `toLayout tabs ens : Layout F`, a Clean flat ensemble as the contract's chips + CCS + bus
  relation (`Contract/Layout.lean`), generic over Clean's `FiniteField F` (in particular `K`).

  The translation, Clean construct ↦ layout construct:
  * the verifier (one row: the public input) ↦ chip `0`, the public chip:
    `max 32 (size PublicIO)` columns (the public input, then zero columns), a gadget forcing
    exactly one row (`[r = 0] = 1`);
  * component `i` of `ens.tables` ↦ chip `i + 1`: `width` columns (the row), then auxiliary
    columns;
  * `assert e` ↦ the polynomial `e` as a sum of products of linear forms (`ofExpr`), one CCS
    constraint (`gadgetOf`);
  * variable `v` ↦ row cell `v` (`v < width`; a variable at or beyond the width reads `0`, as
    Clean reads a missing cell);
  * a message coordinate or selector that is not a row variable (`n + 1`, `fp * o`, a constant) ↦
    an auxiliary column constrained to equal it (one per distinct expression);
  * an interaction whose channel's **name** `c` is listed ↦ a port on bus `cm.bus c` (kind `eq`;
    by default `c`'s index), message = its coordinates' columns;
  * its constructor, `pull`/`pulled(If)` (`assumeGuarantees`, multiplicity `(-1) · e`) or
    `push`/`pushed(If)`/`emit` (multiplicity `m`) ↦ receive with selector `e` or send with
    selector `m` (unless `cm` fixes the channel's direction), the selector's column (`readMult`);
  * an interaction whose channel's name is not listed ↦ nothing. A channel is its **name**: an
    unlisted `RawChannel` sharing a listed name is on that name's bus (S8-M1; exact for Clean
    under `ChannelsByName`);
  * `lookup` into a registered table `tabs[j]` (by name and arity) ↦ a receiving port on bus
    `nBus + j` (kind `sub`), selector the constant-`1` column;
  * registered table `tabs[j]` ↦ a chip with that fixed table (its rows, then a constant-`1`
    selector column) sending every row on bus `nBus + j`;
  * `lookup` into an unregistered table ↦ a receiving port on bus `nBus + tabs.length`, which
    nobody sends on.

  The direction of an interaction is read from Clean's constructors (`readMult`: the
  `assumeGuarantees` bit that `pull`/`pulled` set and `push`/`pushed`/`emit` clear, and the pull's
  `(-1) · e` form), never from a value: in characteristic 2, `-1 = 1`. A message is on the bus once
  when its selector evaluates to `1` and is silent otherwise, as `Table.msgs` reads a selector cell.

  The two `deriving instance DecidableEq` below are global instances on Clean's `Variable` and
  `Expression`; they will clash if Clean derives them upstream (then delete them here).

  `Part` is what the translation reads off one Clean component: width, base (columns before the
  auxiliary ones), whether the chip has exactly one row, and the row operations. The per-chip
  lemmas: `holds_chip_iff` (the gadget is Clean's assertions, the padding columns zero, the
  auxiliary columns their expressions, and the one-row flag), `cell_colOf` (a port column reads
  its expression), `msgs_intPort`, `msgs_lookPort` (a port's messages are Clean's).
-/
import RecursionFast.Clean.Gadget
import RecursionFast.Clean.FiniteField
import Clean.Air.FlatEnsemble

deriving instance DecidableEq for Variable
deriving instance DecidableEq for Expression

namespace RecursionFast.Clean

open Air.Flat

variable {F : Type} [FiniteField F] [DecidableEq F]

/-! ## Reading multiplicities, widths, lookups -/

/-- `e'` when `e` is written `(-1) · e'`, the form of Clean's `Neg` (`- e'`). -/
def negArg? : Expression F → Option (Expression F)
  | .mul (.const c) e => if c = -1 then some e else none
  | _ => none

/-- **The direction and selector of an interaction, from Clean's constructors.**
* `pulled msg`, `pulledIf en msg`, `Channel.pull`, `Channel.pullIf` set `assumeGuarantees` and
  write the multiplicity `-e = (-1) · e` (`e = 1` or `en`): they **receive** (`false`) with
  selector `e`.
* `pushed msg`, `pushedIf en msg`, `Channel.push`, `Channel.pushIf`, `emitted`/`emit m` clear
  `assumeGuarantees` and write the multiplicity `m` (`1`, `en`, `m`): they **send** (`true`) with
  selector `m`.
No value is compared: in `K`, `-1 = 1`, and a push written `pushedIf ((1 : K) · en)` is a send
with selector `1 · en`. An interaction that assumes guarantees but whose multiplicity is not of
the form `(-1) · e` is no constructor's output: `Supported` (`ShapeOK`) rejects it; here it reads
as a receive with the whole multiplicity as selector. -/
def readMult (i : AbstractInteraction F) : Bool × Expression F :=
  if i.assumeGuarantees then (false, (negArg? i.mult).getD i.mult) else (true, i.mult)

/-- The interaction is a Clean constructor's output: a send, or a receive written `(-1) · e`. -/
def ShapeOK (i : AbstractInteraction F) : Bool := !i.assumeGuarantees || (negArg? i.mult).isSome

/-- Every variable of `e` is below `w`. -/
def within (w : ℕ) : Expression F → Bool
  | .var v => decide (v.index < w)
  | .const _ => true
  | .add a b => within w a && within w b
  | .mul a b => within w a && within w b

/-- A row truncated (or padded with `0`) to `w` cells. -/
def trunc (w : ℕ) (row : Array F) : Array F := Array.ofFn fun c : Fin w => row[(c : ℕ)]?.getD 0

omit [DecidableEq F] in
/-- An expression within width `w` reads only the first `w` cells of a row. -/
theorem eval_trunc {w : ℕ} {e : Expression F} (h : within w e = true) (row : Array F)
    (data : ProverData F) :
    e.eval (Environment.fromArray (trunc w row) data) =
      e.eval (Environment.fromArray row data) := by
  induction e with
  | var v =>
    simp only [within, decide_eq_true_eq] at h
    simp [Expression.eval, trunc, h]
  | const c => rfl
  | add a b ha hb | mul a b ha hb =>
    simp only [within, Bool.and_eq_true] at h
    simp only [Expression.eval, ha h.1, hb h.2]

/-- A lookup table of the index: its name and arity (as Clean's `ProverData` keys tables) and
its rows. -/
structure FixedTable (F : Type) where
  /-- The name. -/
  name : String
  /-- The arity. -/
  arity : ℕ
  /-- The rows. -/
  rows : List (Vector F arity)

/-- The registered table a lookup reads: the first of `tabs` with its name and arity
(`tabs.length` if none). -/
def tabIdx (tabs : List (FixedTable F)) (l : Lookup F) : ℕ :=
  tabs.findIdx fun t => t.name = l.table.name ∧ t.arity = l.table.arity

/-! ## Channels and buses (S8-A11) -/

/-- **How a channel meets the buses.** `none`: the channel is its own bus, the index of its name
among the ensemble's channel names, and each interaction's direction is its constructor's
(`readMult`). `some (b, s)`: the channel is bus `b`, and **every** interaction on it sends if `s`,
receives otherwise (a channel that both pulls and pushes must not be mapped). This joins pull/push
channel pairs into one bus, as leanerVM writes them (`"st.pull" ↦ (0, false)`,
`"st.push" ↦ (0, true)`). Two listed names may share a bus only as such a pair:
`ChannelMap.Separate`, part of `Supported`, excludes every other coincidence (a default bus that
equals a mapped one, two mapped channels of one direction). -/
abbrev ChannelMap := String → Option (ℕ × Bool)

/-- The default map: every channel is its own bus, direction from the multiplicity. -/
def ChannelMap.byName : ChannelMap := fun _ => none

/-- The bus of the channel named `nm`. -/
def ChannelMap.bus (cm : ChannelMap) (names : List String) (nm : String) : ℕ :=
  match cm nm with
  | some (b, _) => b
  | none => names.idxOf nm

/-- The direction of an interaction: the map's, or else its multiplicity's. -/
def ChannelMap.dir (cm : ChannelMap) (i : AbstractInteraction F) : Bool :=
  match cm i.channel.name with
  | some (_, s) => s
  | none => (readMult i).1

/-- The number of channel buses: every listed channel's bus is below it (kind `eq`); the lookup
buses start there (kind `sub`). -/
def ChannelMap.nBus (cm : ChannelMap) (names : List String) : ℕ :=
  (names.map fun nm => cm.bus names nm + 1).foldr max 0

/-- **No silent merging**: two distinct listed names share a bus only as a declared pull/push
pair (both mapped, opposite directions). Decidable; part of `Supported`. -/
def ChannelMap.Separate (cm : ChannelMap) (names : List String) : Prop :=
  ∀ a ∈ names, ∀ b ∈ names, a ≠ b → cm.bus names a = cm.bus names b →
    ∃ s : Bool, cm a = some (cm.bus names a, s) ∧ cm b = some (cm.bus names a, !s)

instance (cm : ChannelMap) (names : List String) : Decidable (cm.Separate names) := by
  unfold ChannelMap.Separate; infer_instance

theorem ChannelMap.bus_lt_nBus (cm : ChannelMap) {names : List String} {nm : String}
    (h : nm ∈ names) : cm.bus names nm < cm.nBus names :=
  Nat.lt_of_succ_le (le_foldr_max (List.mem_map.mpr ⟨nm, h, rfl⟩))

/-! ## One component as a chip -/

/-- What the translation reads off one Clean component: its `width` (the row cells its
expressions read), `base ≥ width` (the chip's columns before the auxiliary ones; the columns in
between are constrained to `0`), whether the chip has exactly one row, and its row operations. -/
structure Part (F : Type) [FiniteField F] where
  /-- The row cells. -/
  width : ℕ
  /-- The columns before the auxiliary ones. -/
  base : ℕ
  /-- Exactly one row (the public chip). -/
  oneRow : Bool
  /-- The row operations. -/
  ops : Operations F
  /-- The row fits in the base columns. -/
  width_le : width ≤ base

namespace Part

variable (cm : ChannelMap) (names : List String) (tabs : List (FixedTable F)) (P : Part F)

/-- The interactions on a listed channel. -/
def ints : List (AbstractInteraction F) :=
  P.ops.interactions.filter fun i => decide (i.channel.name ∈ names)

/-- Every expression a port reads: each listed interaction's selector and message, each
lookup's constant-`1` selector and entry. -/
def pexprs : List (Expression F) :=
  (P.ints names).flatMap (fun i => (readMult i).2 :: i.msg.toList) ++
    P.ops.lookups.flatMap fun l => .const 1 :: l.entry.toList

/-- A row variable: read in place, no auxiliary column. -/
def direct (w : ℕ) : Expression F → Bool
  | .var v => decide (v.index < w)
  | _ => false

/-- The index of a variable (`0` for anything else). -/
def varIdx : Expression F → ℕ
  | .var v => v.index
  | _ => 0

/-- The expressions with an auxiliary column: the port expressions that are not row variables,
each once. -/
def auxs : List (Expression F) := ((P.pexprs names).filter fun e => !direct P.width e).dedup

/-- The number of columns: base columns, then one per auxiliary expression. -/
def cols : ℕ := P.base + (P.auxs names).length

/-- The column a port reads for expression `e`: a row variable in place, otherwise its
auxiliary column. -/
def colOf (e : Expression F) : ℕ :=
  if direct P.width e then varIdx e else P.base + (P.auxs names).idxOf e

/-- The linear form reading view cell `c` (the zero form if out of range). -/
def cellLin {n : ℕ} (c : ℕ) : Lin F n := if h : c < n then [(⟨c, h⟩, 1)] else []

/-- The view width of the chip. -/
abbrev vw : ℕ := P.cols names + P.cols names + 3

/-- Clean variable `v` on the view: row cell `v` below the width, `0` beyond. -/
def xLin (v : ℕ) : Lin F (P.vw names) := if v < P.width then cellLin v else []

/-- The view's constant cell. -/
def oneLin : Lin F (P.vw names) := cellLin (P.cols names + P.cols names)

/-- The constraint "view cell `c` is `0`". -/
def zeroSOP (c : ℕ) : SOP F (P.vw names) := [[cellLin c]]

/-- The constraint "auxiliary column `j` equals its expression `e`". -/
def auxSOP (j : ℕ) (e : Expression F) : SOP F (P.vw names) :=
  SOP.merge ([[cellLin (P.base + j)]] ++
    (ofExpr (P.xLin names) (P.oneLin names) e).map (scaleProd (P.oneLin names) (-1)))

/-- The constraint "`[r = 0] = 1`". -/
def firstSOP : SOP F (P.vw names) :=
  [[cellLin (P.cols names + P.cols names + 1) ++ (P.oneLin names).smul (-1)]]

/-- The gadget's constraints: Clean's assertions; the padding columns are `0`; each auxiliary
column equals its expression; for a one-row chip, `[r = 0] = 1`. -/
def sops : List (SOP F (P.vw names)) :=
  (P.ops.constraints.map fun e => (ofExpr (P.xLin names) (P.oneLin names) e).merge) ++
  ((List.range (P.base - P.width)).map fun j => P.zeroSOP names (P.width + j)) ++
  (List.ofFn fun j : Fin (P.auxs names).length => P.auxSOP names j (P.auxs names)[j]) ++
  (if P.oneRow then [P.firstSOP names] else [])

/-- The port of a listed interaction: its channel's bus (`cm.bus`), direction from `cm.dir`,
selector from `readMult`, message = its coordinates' columns. -/
def intPort (i : AbstractInteraction F) : Port :=
  ⟨cm.bus names i.channel.name, cm.dir i, P.colOf names (readMult i).2,
    i.msg.toList.map (P.colOf names)⟩

/-- The port of a lookup: receives on the bus of its registered table (after the channel buses),
selector the constant `1`, message = its entry's columns. -/
def lookPort (l : Lookup F) : Port :=
  ⟨cm.nBus names + tabIdx tabs l, false, P.colOf names (.const 1),
    l.entry.toList.map (P.colOf names)⟩

/-- **The chip of a component.** -/
@[reducible] def chip : Chip F :=
  ⟨P.cols names, gadgetOf (P.oneLin names) (P.sops names),
    (P.ints names).map (P.intPort cm names) ++ P.ops.lookups.map (P.lookPort cm names tabs), none⟩

end Part

/-! ## Registered lookup tables as fixed chips -/

/-- The fixed table of a registered lookup table: its rows, then a constant-`1` column. -/
def FixedTable.table (t : FixedTable F) : Table F :=
  ⟨t.rows.length, fun r c => if h : c < t.arity then ((t.rows[r]?).map fun v => v[c]).getD 0 else 1⟩

/-- The chip of a registered lookup table: its fixed table, sending every row on bus `b`. -/
def FixedTable.chip (t : FixedTable F) (b : ℕ) : Chip F :=
  ⟨t.arity + 1, gadgetOf [] [], [⟨b, true, t.arity, List.range t.arity⟩], some t.table⟩

/-! ## The ensemble -/

variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- The channel names, in order (by default, bus `b` is channel `b`). -/
def chNames (ens : Ensemble F PublicIO) : List String := ens.channels.map (·.name)

/-- The verifier as the public chip: `max 32 (size PublicIO)` base columns (the public input,
then zero columns up to 32), exactly one row. -/
def pubPart (ens : Ensemble F PublicIO) : Part F :=
  ⟨size PublicIO, max 32 (size PublicIO), true, ens.verifierTable.rowOperations, le_max_right _ _⟩

/-- A component as a chip's part: its width, no padding, any number of rows. -/
def compPart (c : Component F) : Part F := ⟨c.width, c.width, false, c.rowOperations, le_rfl⟩

/-- **`toLayout tabs ens cm`**: chip `0` the verifier (public), chip `i + 1` component `i`, then
one fixed chip per registered lookup table; buses `< cm.nBus` are the channels as `cm` maps them
(kind `eq`), the others lookups (kind `sub`). The default map is `ChannelMap.byName`. -/
def toLayout (tabs : List (FixedTable F)) (ens : Ensemble F PublicIO)
    (cm : ChannelMap := ChannelMap.byName) : Layout F where
  chips := (pubPart ens).chip cm (chNames ens) tabs ::
    (ens.tables.map fun c => (compPart c).chip cm (chNames ens) tabs) ++
    List.ofFn fun j : Fin tabs.length => tabs[j].chip (cm.nBus (chNames ens) + j)
  bus b := if b < cm.nBus (chNames ens) then .eq else .sub
  pub := 0

/-! ## Per-chip lemmas -/

namespace Part

variable {cm : ChannelMap} {names : List String} {tabs : List (FixedTable F)} {P : Part F}

/-- The environment of row `r` of a chip table: its first `width` cells (Clean's row). -/
def env (P : Part F) (T : Table F) (r : ℕ) (data : ProverData F) : Environment F :=
  Environment.fromArray (Array.ofFn fun c : Fin P.width => T.cell r c) data

omit [DecidableEq F] in
theorem env_get (T : Table F) (r : ℕ) (data : ProverData F) (v : ℕ) :
    (P.env T r data).get v = if v < P.width then T.cell r v else 0 := by
  unfold env
  split_ifs with h <;> simp [h]

theorem width_le_cols : P.width ≤ P.cols names := (P.width_le).trans (Nat.le_add_right _ _)

theorem view_lt (T : Table F) (r : ℕ) {c : ℕ} (hc : c < P.cols names) :
    view (P.chip cm names tabs) T r ⟨c, by show c < P.cols names + P.cols names + 3; omega⟩ =
      T.cell r c := by
  simp [view, hc]

theorem eval_cellLin (T : Table F) (r : ℕ) {c : ℕ} (hc : c < P.cols names) :
    (cellLin c : Lin F (P.vw names)).eval (view (P.chip cm names tabs) T r) = T.cell r c := by
  have : c < P.vw names := by unfold vw; omega
  simp only [cellLin, this, dite_true, Lin.eval_single, one_mul]
  exact view_lt T r hc

theorem eval_oneLin (T : Table F) (r : ℕ) :
    (P.oneLin names).eval (view (P.chip cm names tabs) T r) = 1 := by
  have h : P.cols names + P.cols names < P.vw names := by unfold vw; omega
  simp only [oneLin, cellLin, h, dite_true, Lin.eval_single, one_mul]
  simp [view]

theorem eval_firstLin (T : Table F) (r : ℕ) :
    (cellLin (P.cols names + P.cols names + 1) : Lin F (P.vw names)).eval
      (view (P.chip cm names tabs) T r) = if r = 0 then 1 else 0 := by
  have h : P.cols names + P.cols names + 1 < P.vw names := by unfold vw; omega
  simp [cellLin, h, Lin.eval_single, view,
    show ¬ P.cols names + P.cols names + 1 < P.cols names by omega]

theorem eval_xLin (T : Table F) (r : ℕ) (data : ProverData F) (v : ℕ) :
    (P.xLin names v).eval (view (P.chip cm names tabs) T r) = (P.env T r data).get v := by
  rw [env_get, xLin]
  split_ifs with h
  · exact eval_cellLin T r (lt_of_lt_of_le h width_le_cols)
  · rfl

theorem eval_ofExpr_view (T : Table F) (r : ℕ) (data : ProverData F) (e : Expression F) :
    (ofExpr (P.xLin names) (P.oneLin names) e).eval (view (P.chip cm names tabs) T r) =
      e.eval (P.env T r data) :=
  eval_ofExpr (eval_xLin T r data) (eval_oneLin T r) e

/-- The auxiliary columns of row `r` hold their expressions. -/
def AuxOK (names : List String) (P : Part F) (T : Table F) (r : ℕ) (data : ProverData F) : Prop :=
  ∀ j : Fin (P.auxs names).length, T.cell r (P.base + j) = (P.auxs names)[j].eval (P.env T r data)

/-- **The chip's gadget on row `r`**: Clean's assertions hold on the row, the padding columns
are `0`, the auxiliary columns hold their expressions, and a one-row chip is at row `0`. -/
theorem holds_chip_iff (T : Table F) (r : ℕ) (data : ProverData F) :
    (P.chip cm names tabs).gadget.holds (view (P.chip cm names tabs) T r) ↔
      (∀ e ∈ P.ops.constraints, e.eval (P.env T r data) = 0) ∧
      (∀ j < P.base - P.width, T.cell r (P.width + j) = 0) ∧
      P.AuxOK names T r data ∧ (P.oneRow = true → r = 0) := by
  have hb : P.base ≤ P.cols names := Nat.le_add_right _ _
  show (gadgetOf (P.oneLin names) (P.sops names)).holds _ ↔ _
  rw [holds_gadgetOf (eval_oneLin T r)]
  simp only [sops, List.mem_append, or_imp, forall_and, List.forall_mem_map, SOP.eval_merge,
    eval_ofExpr_view T r data, List.mem_range, List.mem_ofFn, forall_exists_index,
    forall_apply_eq_imp_iff, and_assoc]
  refine and_congr Iff.rfl (and_congr ?_ (and_congr ?_ ?_))
  · refine forall₂_congr fun j hj => ?_
    simp [zeroSOP, SOP.eval, prodEval, eval_cellLin T r (show P.width + j < P.cols names by omega)]
  · refine forall_congr' fun j => ?_
    simp only [auxSOP, SOP.eval_merge, SOP.eval_append, SOP.eval_scale (eval_oneLin T r),
      eval_ofExpr_view T r data]
    simp only [SOP.eval, prodEval, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, List.sum_cons, List.sum_nil, add_zero]
    rw [eval_cellLin T r (by unfold cols; omega), neg_one_mul, ← sub_eq_add_neg, sub_eq_zero]
  · cases P.oneRow <;> simp [firstSOP, SOP.eval, prodEval, Lin.eval_append, Lin.eval_smul,
      eval_firstLin, eval_oneLin, add_neg_eq_zero]

/-- **A port column reads its expression**, on a row whose auxiliary columns hold. -/
theorem cell_colOf {T : Table F} {r : ℕ} {data : ProverData F} (h : P.AuxOK names T r data)
    {e : Expression F} (he : e ∈ P.pexprs names) :
    T.cell r (P.colOf names e) = e.eval (P.env T r data) := by
  unfold colOf
  split_ifs with hd
  · cases e with
    | var v =>
      simp only [direct, decide_eq_true_eq] at hd
      simp [varIdx, Expression.eval, env_get, hd]
    | _ => simp [direct] at hd
  · have hmem : e ∈ P.auxs names := List.mem_dedup.mpr (List.mem_filter.mpr ⟨he, by simpa using hd⟩)
    simpa only [Fin.getElem_fin, List.getElem_idxOf] using h ⟨_, List.idxOf_lt_length_of_mem hmem⟩

end Part



/-! ## Messages of a chip's ports -/

namespace Part

variable {cm : ChannelMap} {names : List String} {tabs : List (FixedTable F)} {P : Part F}

theorem sel_mem_pexprs {i : AbstractInteraction F} (hi : i ∈ P.ints names) :
    (readMult i).2 ∈ P.pexprs names :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨i, hi, List.mem_cons_self⟩)

theorem msg_mem_pexprs {i : AbstractInteraction F} (hi : i ∈ P.ints names) {e : Expression F}
    (he : e ∈ i.msg.toList) : e ∈ P.pexprs names :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨i, hi, List.mem_cons_of_mem _ he⟩)

theorem one_mem_pexprs {l : Lookup F} (hl : l ∈ P.ops.lookups) :
    (.const 1 : Expression F) ∈ P.pexprs names :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨l, hl, List.mem_cons_self⟩)

theorem entry_mem_pexprs {l : Lookup F} (hl : l ∈ P.ops.lookups) {e : Expression F}
    (he : e ∈ l.entry.toList) : e ∈ P.pexprs names :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨l, hl, List.mem_cons_of_mem _ he⟩)

/-- **The messages of an interaction's port** are Clean's: one per row whose selector
evaluates to `1`, the message evaluated on the row (auxiliary columns holding). -/
theorem msgs_intPort {T : Table F} {data : ProverData F}
    (h : ∀ r < T.rows, P.AuxOK names T r data) {i : AbstractInteraction F} (hi : i ∈ P.ints names) :
    T.msgs (P.intPort cm names i) =
      (((List.range T.rows).filter fun r => (readMult i).2.eval (P.env T r data) = 1).map
        fun r => i.msg.toList.map (·.eval (P.env T r data)) :) := by
  unfold Table.msgs intPort
  dsimp only
  congr 1
  rw [List.filter_congr fun r hr => by
    rw [cell_colOf (h r (List.mem_range.mp hr)) (sel_mem_pexprs hi)]]
  refine List.map_congr_left fun r hr => ?_
  rw [List.map_map]
  exact List.map_congr_left fun e he =>
    cell_colOf (h r (List.mem_range.mp (List.mem_filter.mp hr).1)) (msg_mem_pexprs hi he)

/-- **The messages of a lookup's port**: every row's entry (the selector is the constant `1`). -/
theorem msgs_lookPort {T : Table F} {data : ProverData F}
    (h : ∀ r < T.rows, P.AuxOK names T r data) {l : Lookup F} (hl : l ∈ P.ops.lookups) :
    T.msgs (P.lookPort cm names tabs l) =
      (((List.range T.rows).map fun r => l.entry.toList.map (·.eval (P.env T r data))) :) := by
  unfold Table.msgs lookPort
  dsimp only
  congr 1
  rw [List.filter_congr fun r hr => by
    rw [cell_colOf (h r (List.mem_range.mp hr)) (one_mem_pexprs hl)]]
  simp only [Expression.eval, decide_true, List.filter_true]
  refine List.map_congr_left fun r hr => ?_
  rw [List.map_map]
  exact List.map_congr_left fun e he =>
    cell_colOf (h r (List.mem_range.mp hr)) (entry_mem_pexprs hl he)

end Part
end RecursionFast.Clean
