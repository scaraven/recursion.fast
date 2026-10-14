/-
# Contract: the relation — chips, CCS row gadgets, buses                         (TRUSTED)

DESIGN §2. The **index** is a `Layout`: a list of chips, the kind of every bus, and which chip is
public. The **witness** is one `Table` per chip; the prover chooses each table's height. The
layout is satisfied at size class `k` by statement `x` and witness `w` (`Layout.rel`) when

* every chip with a fixed (preprocessed) table carries that table: same height, same cells;
* every row of every chip satisfies the chip's CCS gadget, which sees the row, the next row
  (cyclically: row 0 follows the last row) and three contract cells: `1`, `[r = 0]` and
  `[r + 1 = rows]` (the constant, the first-row flag, the last-row flag);
* every bus balances, counted as multisets in ℕ (never in the field: in characteristic 2 a
  field-valued count makes `2 = 0`): on an `eq` bus the messages sent and received are equal as
  multisets (interaction, permutation); on a `sub` bus every received message was sent (lookup);
* the statement `x` (32 elements) is cells `0 … 31` of row 0 of the public chip;
* the tables have at most `2^k` cells (`rows · cols`) in total.

A table is read only inside `rows × cols` of its chip, for admissible layouts (ports read their
own columns, every chip has a column, the public chip has 32): `Library/Layout.lean`,
`rel_trim_iff`. Textbook R1CS, `z = (1, x, w)` with the constant from the view and `x` in the
first 32 columns, is the special case "one chip, one row, no ports" (`Library/R1CS.lean`,
`R1CS_iff_layout`, over `relK`); an AIR with boundary constraints on the first or last row (the
flags) and a transition on every row is "one chip, many rows, no ports"; a multi-chip zkVM is the
general case. Gadget matrices are sparse (entry lists), so the index size is bounded by the caps
independently of the table heights. Heights are arbitrary (not powers of two) and the wrap is
modulo the height.

The arithmetic is the carrier's own `+`, `*`, `0`, `1`; over `K` these are `Field.lean`'s (xor,
reduced carry-less product). Sums and products are written as list folds because the trusted
contract proves no ring axioms for `K` (they are library theorems). Over any commutative ring the
folds are Mathlib's `∑`, multiset `∏` and dense `Matrix.mulVec` (`Library/Layout.lean`,
`Gadget.holds_iff`). The class range `20 ≤ k ≤ 28` is a field of `Protocol` (`Protocol.lean`).
-/
import RecursionFast.Contract.Field
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Multiset.AddSub

namespace RecursionFast

variable {F : Type}

/-! ## Index and witness -/

/-- A CCS row gadget (Setty–Thaler–Wahby 2023) on vectors of length `width`: `t` sparse matrices
of `cons` rows and `q` terms; term `i` is `c i · ∏_{j ∈ S i} (M j · z)`, `S i` a multiset. -/
structure Gadget (F : Type) (width : ℕ) where
  /-- Number of constraints (rows of every matrix). -/
  cons : ℕ
  /-- Number of matrices. -/
  t : ℕ
  /-- The matrices, each `cons × width`, as lists of entries `(row, column, value)`; entries at
  the same position add up. -/
  M : Fin t → List (Fin cons × Fin width × F)
  /-- Number of terms. -/
  q : ℕ
  /-- The matrices multiplied in term `i`, with repetition (a multiset, listed; its length is
  the degree). -/
  S : Fin q → List (Fin t)
  /-- The coefficient of term `i`. -/
  c : Fin q → F

/-- A bus port of a chip: every row whose cell in column `sel` is `1` puts one message, the
cells of the columns `msg` in order, on bus `bus`; it sends if `send`, otherwise it receives.
(a) A row whose selector is any other value, `0` or not, is silent: a protocol that weights
messages by the selector cell must have the layout constrain it to `0`/`1`. (b) Selectors are
witness cells: a fixed row pattern comes from the view's flags `[r = 0]`, `[r + 1 = rows]` or a
fixed table. (c) Heights are arbitrary, not powers of two. -/
structure Port where
  /-- The bus. -/
  bus : ℕ
  /-- Direction: `true` sends, `false` receives. -/
  send : Bool
  /-- The selector column. -/
  sel : ℕ
  /-- The message columns. -/
  msg : List ℕ
  deriving DecidableEq

/-- How a bus balances: `eq` (interaction) sent = received as multisets; `sub` (lookup) every
received message is among the sent ones. -/
inductive BusKind where
  /-- Interaction: the sent and received multisets are equal. -/
  | eq
  /-- Lookup: every received message is also sent. -/
  | sub
  deriving DecidableEq

/-- A table of `rows` rows; `cell r c` is the entry in row `r`, column `c`. Only cells with
`r < rows` and `c` below its chip's `cols` are read by `Layout.rel` when the layout is admissible
(`Library/Layout.lean`, `rel_trim_iff`). -/
structure Table (F : Type) where
  /-- The height. -/
  rows : ℕ
  /-- The entries. -/
  cell : ℕ → ℕ → F

/-- A chip: tables of `cols` columns, a gadget applied to every row together with the next row
and three contract cells (so it sees `2·cols + 3` cells, `view`), the chip's bus ports, and
optionally a fixed table that is part of the index (preprocessed, e.g. a lookup table). -/
structure Chip (F : Type) where
  /-- Number of columns. -/
  cols : ℕ
  /-- The gadget every row satisfies, on the row's `view`. -/
  gadget : Gadget F (cols + cols + 3)
  /-- The bus ports. -/
  ports : List Port
  /-- The fixed table, if any: the witness table of this chip must be this table. -/
  fixed : Option (Table F)

/-- The index: the chips, the kind of every bus, and which chip holds the public input. -/
structure Layout (F : Type) where
  /-- The chips; the witness has one table per chip, in this order. -/
  chips : List (Chip F)
  /-- The kind of bus `b`. -/
  bus : ℕ → BusKind
  /-- The public chip: cells `0 … 31` of row 0 of its table are the statement. -/
  pub : ℕ

/-- A statement of the contract: 32 elements of `K`, i.e. 8 digests of 4 elements (32 bytes) each
(DESIGN §5.1), so `nx = 32` (§2.2) holds by its type. -/
abbrev Stmt := Fin 32 → K

/-! ## The relation -/

section Rel
variable [Zero F] [One F] [Add F] [Mul F] [DecidableEq F]

/-- Entry `r` of the product `M · z` of a sparse matrix and a vector: `∑ v · z c` over the
entries `(r, c, v)` of row `r`. -/
def rowDot {m n : ℕ} (M : List (Fin m × Fin n × F)) (z : Fin n → F) (r : Fin m) : F :=
  ((M.filter fun e => e.1 = r).map fun e => e.2.2 * z e.2.1).sum

/-- `z` satisfies the gadget: for every constraint `r`, `∑_i c i · ∏_{j ∈ S i} (M j · z) r = 0`. -/
def Gadget.holds {width : ℕ} (g : Gadget F width) (z : Fin width → F) : Prop :=
  ∀ r, (List.ofFn fun i => g.c i * ((g.S i).map fun j => rowDot (g.M j) z r).prod).sum = 0

/-- What chip `C`'s gadget sees at row `r` of table `T`: the row's `cols` cells, those of the
next row (row `0` after the last), then `1`, `[r = 0]` and `[r + 1 = rows]`. -/
def view (C : Chip F) (T : Table F) (r : ℕ) : Fin (C.cols + C.cols + 3) → F := fun i =>
  if i.val < C.cols then T.cell r i
  else if i.val < C.cols + C.cols then T.cell ((r + 1) % T.rows) (i - C.cols)
  else match i.val - (C.cols + C.cols) with
    | 0 => 1
    | 1 => if r = 0 then 1 else 0
    | _ => if r + 1 = T.rows then 1 else 0

/-- The messages port `p` puts on its bus from table `T`: one per row whose `sel` cell is `1`
(other selector values are silent). -/
def Table.msgs (T : Table F) (p : Port) : Multiset (List F) :=
  (((List.range T.rows).filter fun r => T.cell r p.sel = 1).map fun r => p.msg.map (T.cell r) :)

/-- All messages sent (`send = true`) or received (`send = false`) on bus `b`, over all chips. -/
def traffic (L : Layout F) (w : List (Table F)) (b : ℕ) (send : Bool) : Multiset (List F) :=
  ((L.chips.zip w).map fun ct =>
    ((ct.1.ports.filter fun p => p.bus == b && p.send == send).map ct.2.msgs).sum).sum

/-- Whether the messages sent `s` and received `r` on a bus of this kind balance. -/
def BusKind.Balanced : BusKind → Multiset (List F) → Multiset (List F) → Prop
  | .eq, s, r => s = r
  | .sub, s, r => ∀ m ∈ r, m ∈ s

/-- **The relation**: `w` has one table per chip; a chip with a fixed table has that table's
height and cells; every row of every table satisfies its chip's gadget on its `view` (the row,
the next row cyclically, `1`, `[r = 0]`, `[r + 1 = rows]`); on every `eq` bus the messages sent
and received are equal as multisets, and on every `sub` bus every received message is sent; the
public table has a row whose cells `0 … 31` are `x`; the tables have at most `2^k` cells. -/
def Layout.rel (L : Layout F) (k : ℕ) (x : Fin 32 → F) (w : List (Table F)) : Prop :=
  w.length = L.chips.length ∧
  -- fixed tables: same height, same cells
  (∀ ct ∈ L.chips.zip w, ∀ t ∈ ct.1.fixed,
    ct.2.rows = t.rows ∧ ∀ r < t.rows, ∀ c < ct.1.cols, ct.2.cell r c = t.cell r c) ∧
  -- the gadget, on every row
  (∀ ct ∈ L.chips.zip w, ∀ r < ct.2.rows, ct.1.gadget.holds (view ct.1 ct.2 r)) ∧
  -- every bus balances
  (∀ b, (L.bus b).Balanced (traffic L w b true) (traffic L w b false)) ∧
  -- the public chip has a row; cells 0 … 31 of its row 0 are `x`
  (∃ T ∈ w[L.pub]?, 1 ≤ T.rows ∧ ∀ i : Fin 32, T.cell 0 i = x i) ∧
  -- size class
  ((L.chips.zip w).map fun ct => ct.2.rows * ct.1.cols).sum ≤ 2 ^ k

end Rel

/-! ## Admission caps (DESIGN §2.2) -/

/-- Caps on one chip: `1 ≤ cols ≤ 2^10`; gadget `t ≤ 2^6`, `cons ≤ 2^8`, `q ≤ 2^8`, degree
`|S i| ≤ 8`; at most `2^4` ports, each on a bus `< 2^8`, with a message of at most `2^4` cells;
ports read only the chip's own columns. -/
def Chip.Admissible (C : Chip F) : Prop :=
  1 ≤ C.cols ∧ C.cols ≤ 2 ^ 10 ∧
  C.gadget.t ≤ 2 ^ 6 ∧ C.gadget.cons ≤ 2 ^ 8 ∧ C.gadget.q ≤ 2 ^ 8 ∧
  (∀ i, (C.gadget.S i).length ≤ 8) ∧
  C.ports.length ≤ 2 ^ 4 ∧
  ∀ p ∈ C.ports, p.bus < 2 ^ 8 ∧ p.sel < C.cols ∧ p.msg.length ≤ 2 ^ 4 ∧ ∀ c ∈ p.msg, c < C.cols

/-- Number of entries of a chip's gadget matrices. -/
def Chip.entries (C : Chip F) : ℕ := (List.ofFn fun j => (C.gadget.M j).length).sum

/-- Number of cells of a chip's fixed table (`0` if it has none). -/
def Chip.fixedCells (C : Chip F) : ℕ := (C.fixed.map fun t => t.rows * C.cols).getD 0

/-- **Admissible layouts of class `k`**: at most `2^8` chips, each admissible; a public chip of at
least 32 columns; at most `2^(k+4)` matrix entries and `2^(k-4)` fixed cells in total. (Buses:
`< 2^8`, by the ports. Statement: 32 elements, by the type `Stmt`. Witness cells `≤ 2^k`: checked
by `Layout.rel`. Class range: a field of `Protocol`.) -/
def Layout.Admissible (L : Layout F) (k : ℕ) : Prop :=
  L.chips.length ≤ 2 ^ 8 ∧ (∃ C ∈ L.chips[L.pub]?, 32 ≤ C.cols) ∧
  (L.chips.map Chip.entries).sum ≤ 2 ^ (k + 4) ∧ (L.chips.map Chip.fixedCells).sum ≤ 2 ^ (k - 4) ∧
  ∀ C ∈ L.chips, C.Admissible

/-- Chip admissibility is decidable. -/
instance (C : Chip F) : Decidable C.Admissible := inferInstanceAs (Decidable (_ ∧ _))

/-- Layout admissibility is decidable. -/
instance (L : Layout F) (k : ℕ) : Decidable (L.Admissible k) := inferInstanceAs (Decidable (_ ∧ _))

end RecursionFast
