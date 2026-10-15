<!-- Copied from CambridgePQ/recursion.fast/design/DESIGN-v2-chips-walltime.md (2026-10-14). This copy is the one this repository implements; keep the two in sync. -->
# recursion.fast v2: chips + CCS relation, verifier-as-circuit recursion, wall-time scoring

Status: **design in force for the v2 contract** (user decisions of 2026-10-14; amended 2026-10-15
after Stages 1–8 (see docs/DESIGN-AMENDMENTS.md); this file supersedes `DESIGN.md` wherever the two
disagree). Written for the agent that builds the v2 contract, harness and baseline. Read
`CLAUDE.md` first, then this file, then `contract-v03/RESULT.md` for the harness that carries over.

What changed against the report (v1.0) and `DESIGN.md` v0.3, in one paragraph: the relation is
no longer a flat R1CS but a *structured* constraint system (chips, each a uniform CCS row gadget,
connected by buses); the verifier is no longer a RISC-V image with proved cycle counters but a
Lean IOP verifier whose compiled form is *executed and timed* on one reference machine; recursion
is no longer the typed accumulation track (T2) but *verifier-as-circuit*: the agent supplies the
layout `C_V` of their own compiled verifier and proves it correct, and the headline score is the
measured wall time of one 2→1 recursion step. The RISC-V machine remains only as the extractor's
machine (Q1). Binary fields, the bounded extractor (Q1) and the universal relation (Q4-A) stay.

Decision IDs used below: `V2-x` (new), `Q-n` (`DISCUSSION.md`), `A-n`/`D-n` (reviews, design notes).

---

## 1. Objective and the one-line pitch

Agents submit a hash-based SNARK (prover, verifier, extractor, security proofs in Lean 4) for a
universal structured relation over GF(2^64), plus the arithmetisation of their own verifier.
Ranked by **the wall time of one 2→1 recursion step** on the organiser's machine. Security is
kernel-checked; cost is measured. The design space is the whole of "how to build a fast recursive
hash-based SNARK over a binary field": chips, buses, lookups, hash choice, commitment layout,
query patterns, folding, prover engineering.

Non-goals: zero knowledge; a proved cost model for the verifier; proving the native prover
correct; a composition theorem across recursion levels (ROM heuristic, §6.6).

---

## 2. Relation (trusted): chips + CCS + bus

### 2.1 Definition

Field: `K = GF(2^64) = GF(2)[x]/(x^64+x^4+x^3+x+1)` (`Contract/Field.lean`, unchanged);
challenges from `E = K[y]/(y^3+y+1)`. Never prime fields (user requirement).

The relation is `Layout.rel k x w`, implemented in `Contract/Layout.lean` (Stage 1; 80 code lines,
caps included). The block below is that file abridged: the admission caps (§2.2) and the
`Decidable` instances are left out and every docstring is cut to one line. The structures are
generic over a carrier `F` (`relK`, §3.1, takes `F := K`); the definitions after `Stmt` need only
`+`, `*`, `0`, `1` and `DecidableEq` on `F`.

```lean
/-- CCS row gadget (Setty–Thaler–Wahby 2023): term `i` is `c i · ∏_{j ∈ S i} (M j · z)`, row by row. -/
structure Gadget (F : Type) (width : ℕ) where
  cons : ℕ
  t : ℕ
  M : Fin t → List (Fin cons × Fin width × F)   -- sparse: entries (row, column, value); the same position adds up
  q : ℕ
  S : Fin q → List (Fin t)                       -- a multiset, listed; its length is the degree
  c : Fin q → F

/-- A bus port: a row whose `sel` cell is `1` puts the message `msg` on `bus`; it sends if `send`. -/
structure Port where
  bus : ℕ
  send : Bool
  sel : ℕ
  msg : List ℕ
  deriving DecidableEq

/-- How a bus balances: `eq` interaction (sent = received), `sub` lookup (received ⊆ sent). -/
inductive BusKind where
  | eq
  | sub
  deriving DecidableEq

/-- The witness of one chip: `rows` rows; `cell r c` is the entry in row `r`, column `c`. -/
structure Table (F : Type) where
  rows : ℕ
  cell : ℕ → ℕ → F

/-- A chip: `cols` columns, a gadget on each row's `view` (`2·cols + 3` cells), its ports, a fixed table. -/
structure Chip (F : Type) where
  cols : ℕ
  gadget : Gadget F (cols + cols + 3)
  ports : List Port
  fixed : Option (Table F)      -- a preprocessed table (part of the index)

/-- The index: the chips, the kind of each bus, which chip holds the public input. -/
structure Layout (F : Type) where
  chips : List (Chip F)
  bus : ℕ → BusKind
  pub : ℕ

/-- A statement: 32 elements of `K`, i.e. 8 digests of 4 elements (32 bytes) each (§5.1). -/
abbrev Stmt := Fin 32 → K

variable [Zero F] [One F] [Add F] [Mul F] [DecidableEq F]

/-- Entry `r` of the sparse product `M · z`: `∑ v · z c` over the entries `(r, c, v)` of row `r`. -/
def rowDot {m n : ℕ} (M : List (Fin m × Fin n × F)) (z : Fin n → F) (r : Fin m) : F :=
  ((M.filter fun e => e.1 = r).map fun e => e.2.2 * z e.2.1).sum

/-- `z` satisfies the gadget: for every constraint `r`, `∑_i c i · ∏_{j ∈ S i} (M j · z) r = 0`. -/
def Gadget.holds {width : ℕ} (g : Gadget F width) (z : Fin width → F) : Prop :=
  ∀ r, (List.ofFn fun i => g.c i * ((g.S i).map fun j => rowDot (g.M j) z r).prod).sum = 0

/-- What the gadget sees at row `r`: the row, the next row (row 0 after the last), `1`, `[r = 0]`, `[r + 1 = rows]`. -/
def view (C : Chip F) (T : Table F) (r : ℕ) : Fin (C.cols + C.cols + 3) → F := fun i =>
  if i.val < C.cols then T.cell r i
  else if i.val < C.cols + C.cols then T.cell ((r + 1) % T.rows) (i - C.cols)
  else match i.val - (C.cols + C.cols) with
    | 0 => 1
    | 1 => if r = 0 then 1 else 0
    | _ => if r + 1 = T.rows then 1 else 0

/-- The messages port `p` puts on its bus: one per row whose `sel` cell is `1`. -/
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

/-- **The relation**: one table per chip; fixed tables; every row's gadget on its `view`; every bus
balances; the public table carries `x` in cells `0 … 31` of row 0; at most `2^k` cells. -/
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
```

Reading guide for the builder:

- The **index** is `Layout`: gadgets, ports, bus kinds, fixed tables. Matrices are sparse (entry
  lists; entries at the same position are summed, the v0.3 `SpMat` convention), so the index size
  is bounded by the caps independently of the row counts (only a fixed table grows with its own
  rows, and fixed tables are capped). A universal verifier can therefore read the index in full.
  The sparse-matrix evaluation argument that the flat-R1CS design forced (Q4) is gone.
- The **witness** is the list of tables; the prover chooses each chip's height, as in a zkVM.
- The **statement** `x : Fin 32 → K` is cells `0 … 31` of row 0 of the public chip (`pub`), not
  column 0 over 32 rows: the public table has a row, and `T.cell 0 i = x i` for `i < 32`.
- The **view** of a row has width `cols + cols + 3`. It holds the row, the next row (row 0 after
  the last), then three contract cells: the constant `1`, `[r = 0]` and `[r + 1 = rows]`. A
  verifier computes these cells from the height. They let a gadget state boundary constraints
  without a witness column for the row position.
- A **gadget** term is `c i` times the product, over the ordered multiset `S i` (a `List`: the
  trusted `K` has no `CommMonoid`, which `Multiset.prod` would need), of the rows `M j · z`; its
  length is the degree. `rowDot M z r` sums `v · z c` over the entries `(r, c, v)` of row `r`.
- The **bus** is a deterministic multiset predicate, counted in ℕ. LogUp/permutation challenges
  belong to the agent's proof system. The balance is *not* a field sum (see §9.2: in
  characteristic 2 a field-sum balance is meaningless).
- The **fixed-table clause** compares the height and the cells in `rows × cols`, not full
  function equality (a `Table` is a function on all of `ℕ × ℕ`; cells outside `rows × cols` are
  not part of any finite index).
- **Notation.** The trusted relation is written with list folds over `Field.lean`'s `+`, `*`, `0`,
  `1`, not with Mathlib's `∑`, `∏`, `mulVec`, because the trusted `K` carries no ring structure.
  The library proves the equivalence: `Gadget.holds_iff` (`Library/Layout.lean`) is the bridge to
  Mathlib's dense `Matrix.mulVec` through the denoted matrix (`spToMat`, duplicates summed).
  `rel` reads a table only inside `rows × cols` (`rel_trim_iff`, O-1).
- Textbook **R1CS** with public input `x` (`z = (1, x, w)`, the `1` being the view's constant cell)
  is one chip, one row, no ports, `pub = 0`, with `x` in the first 32 columns. This holds without
  qualification for `≤ 2^8` constraints and `≤ 2^10` columns. A larger R1CS is several one-row
  chips or a uniform gadget over rows. A flat **AIR** (boundary constraints on the first or last
  row, through the flags, and a transition on every row) is one chip with `rows` rows and no
  ports. A multi-chip **zkVM** is the general case. All three are admissible.
- Multiplicities: a row contributes one message when `sel = 1`. Multiplicity `m > 1` is `m`
  rows or `m` ports; it is not a cell value (a cell value is a field element, and `2 = 0`).
  Three consequences. (a) A port's selector is a witness cell compared with `1`, and any other
  value is silent, so a protocol that weights messages by the selector must have the layout
  constrain it to `0`/`1`. (b) Fixed row patterns come from the flags or from a fixed table.
  (c) Heights are arbitrary (not powers of two), and the wrap is modulo the height.

### 2.2 Admission caps (`Layout.Admissible`, pass/fail, trusted)

| Quantity | Cap (default) | Why |
|---|---|---|
| cells `Σ rows·cols` | `≤ 2^k` | the class (a witness quantity: checked by `rel`, not by `Admissible`) |
| chips | `≤ 2^8` | index reading cost |
| columns per chip | `1 ≤ cols ≤ 2^10` | bounded index; dense views (`1 ≤ cols`: a zero-column chip would have unbounded rows at zero cell cost) |
| matrix entries, Σ over all chips and matrices | `≤ 2^(k+4)` | a layout-independent index oracle of `2^(k+8)` K-elements suffices at every class; the orchestrator's Stages 4 and 7 rely on this |
| ports per chip | `≤ 2^5`; message length `≤ 2^4`; bus `< 2^8` | index reading cost; `2^5` since the Stage 8 decision pass (S8-A9): leanerVM's BLAKE2s row has 22 bus interactions (§9.3), and Stage 6a's G chip had to be split for the same reason |
| port columns | `sel` and every `msg` column `< cols` (ports read their own columns) | a port never reads an unpaid cell |
| gadget | `t ≤ 2^6`, `cons ≤ 2^8`, `q ≤ 2^8`, `(S i).length ≤ 8` (degree ≤ 8) | index reading cost; degree bound for the agent's proof system |
| buses | `≤ 2^8` (every port's bus is `< 2^8`) | index reading cost |
| fixed tables | `Σ cells ≤ 2^(k−4)` | the verifier commits to them once (holographic) |
| statement `nx` | exactly `32` K-elements = 8 digests of 32 bytes (the type `Stmt`); the public chip has `≥ 32` columns | Q4: a few digests; FS absorption cost is fixed |

There is no row for the class range. The relation and `Layout.Admissible` are defined at every `k`;
`20 ≤ k ≤ 28` is a field of `Protocol` (`k_range`, §3.1), stated once, there. The range itself
comes from the leaf benchmark, which fits at `k ≥ 24` (§7.2), and from `C_V`, which must fit (§5.2).

The sum of these bounds is what makes "the verifier reads the index" cheap and index-independent;
agents cannot blow up the index to hide work (the index is committed in `VK`, §3.2).

### 2.3 Controls (`Controls/Layout.lean`, CI)

Every control is a small explicit layout over `K` decided by the kernel (`decide +kernel`); public
chips have 32 columns wherever a layout is meant to be admissible.

Positive:

- Textbook R1CS, `z = (1, x, w)`, satisfies `rel` iff the R1CS does: `R1CS_iff_layout` relates the
  layout to `R1CS A B C x w` and is stated for `relK k` (one chip, one row, no ports, `pub = 0`,
  admissible for `≤ 2^8` constraints, `≤ 2^10` columns and `3·m·(32+n+1) ≤ 2^(k+4)` entries).
  Controls `r1cs_pos`, `r1cs_one_pos` (the affine `w₀·1 = 1`, expressible only with the constant
  cell), `r1cs_iff`, `r1cs_relK`.
- A two-chip layout with one `.eq` bus, the receiver holding the messages in another order
  (`twoChip_pos`); a `.sub` lookup against a fixed table, one value looked up twice
  (`lookup_pos`).
- The cyclic wrap: `a' = a + 1` on every row, the last row's next row being row 0 (`wrap_pos`).
- A chip with a transition gadget, XOR-Fibonacci, pinned by the flags (`fib_pos`: `[r = 0]` fixes
  the first row, `[r + 1 = rows]` switches the transition off on the last).
- `toy_secure` (`Controls/Toy.lean`): `Protocol.Secure` is inhabited at every class in range.
  `hit_secure` (`Controls/Hit.lean`, ported from v0.3 with `Library/RbrSound.lean` and
  `Controls/FieldSpec.lean`): the positive control with challenge rounds.

Negative:

- R1CS: `w₀ = x` with `x² ≠ x`; `w₀ = 0` against `w₀·1 = 1` (`r1cs_neg`, `r1cs_one_neg`).
- Buses: one swapped message breaks the `.eq` bus (`twoChip_neg`); a message sent once and
  received twice breaks it, so multiplicity is counted in ℕ (`eqMult_neg`); one value outside the
  fixed table breaks `.sub` (`lookup_neg`).
- Fixed tables: the prover cannot put the value into the fixed table instead (`lookup_neg_fixed`),
  nor add a row to it (`fixedHeight_neg`).
- Wrap: a sequence correct except across the wrap (`wrap_neg`).
- Fibonacci and the statement: one wrong transition (`fib_neg`); not Fibonacci after row 1
  (`fib_garbage`); valid transitions from a wrong first row (`fib_boundary_neg`); a wrong
  statement (`stmt_neg`).
- No public chip (or an empty public table) ⇒ `rel` false for every `x` (`noPub_neg`,
  `twoChip_noPub`, `emptyPub_neg`); a gadget no row satisfies, in a layout that is admissible
  (`unsat_neg`, `unsat_admissible`); cells `> 2^k` (`cells_neg`).
- A boundary control for every cap in §2.2, each accepted at its bound and rejected one above,
  with the same layout otherwise: `cols_neg`, `pubCols_neg`, `entries_neg`, `fixedCells_neg`,
  `chips_cap`, `ports_cap`, `msg_cap`, `bus_cap`, `sel_own`, `cols_pos`, `t_cap`, `cons_cap`,
  `q_cap`, `degree_cap` (`ports_cap` accepts 32 ports and rejects 33).
- A protocol whose verifier rejects everything is not `Secure` (`rejectAll_not_secure`, for any
  `Protocol k`; also `rejectAll_not_complete`).

The accept-all / reject-all controls of v0.3 (`Controls/Negative.lean`) carry over, migrated to
`relK` and to the query-program verifier of §3.1.

---

## 3. Protocol model and what the agent submits

### 3.1 Proved object: a holographic public-coin IOP (carried over from v0.3)

`Contract/Shapes.lean` (round shapes, oracles, transcripts) and `Contract/Security.lean`
(`PerfectComplete`, `Extractor`, `KSF`, `KSF.Bad`, `RbrKS`, `SecureWith`, `errorCap = 2^-128`)
are reused with no declaration changed (`Security.lean` has one reworded header sentence, §4).
`Contract/Protocol.lean` (Stages 1 and 4; 45 code lines) changes `Index sz` to `Layout K` and
`rel sz` to `relK k`, makes the verifier a query program, states the class range and the shape
caps as fields, and takes the extractor as an image (§4 item 3). The block below is that file
abridged, docstrings cut to one line:

```lean
/-- The relation of class `k`: an admissible layout and a statement, with a witness satisfying it. -/
def relK (k : ℕ) : Set ((Layout K × Stmt) × List (Table K)) :=
  {p | p.1.1.Admissible k ∧ p.1.1.rel k p.1.2 p.2}

/-- A query program: stop with a result, or read one leaf of one oracle and continue (adaptive). -/
inductive QProg (α : Type) where
  | done (a : α)
  | query (j l : ℕ) (cont : List K → QProg α)

/-- Run on the oracles `os`; an out-of-range oracle or leaf is `none` (reject). -/
def QProg.eval {α : Type} : QProg α → List Oracle → Option α
  | .done a, _ => some a
  | .query j l cont, os =>
    match os[j]? with
    | some o => if l < o.shape.leaves then (cont (o.leaf l)).eval os else none
    | none => none

/-- The challenges of a full transcript. -/
def chalOf {n : ℕ} {sh : Fin n → Round} (tr : FullTranscript sh) : Challenges sh :=
  fun c => tr c.1

/-- Shape cap of a round at class `k`: message oracles `≤ 2^(k+10)` elements, index challenges `≤ 64` bits. -/
def Round.Admissible (k : ℕ) : Round → Prop
  | .msg o => o.logLeaf ≤ o.logLen ∧ o.logLen ≤ k + 10
  | .chal _ idx => ∀ b ∈ idx, b ≤ 64

/-- A holographic public-coin IOP for `relK k`. -/
structure Protocol (k : ℕ) where
  k_range : 20 ≤ k ∧ k ≤ 28                          -- the class is in range (stated once, here)
  n : ℕ;  n_le : n ≤ roundCap                         -- 2^14
  shape : Fin n → Round
  vkLen : ℕ;  vkLen_le : vkLen ≤ vkCap                -- 2^10 K-elements
  VK : Layout K → (Fin vkLen → K)                     -- computable
  idxShape : OShape
  IDX : Layout K → OVal idxShape                       -- computable
  shape_ok : (∀ j, (shape j).Admissible k) ∧ idxShape.logLeaf ≤ idxShape.logLen ∧
    idxShape.logLen ≤ k + 8                            -- shape caps; the index oracle has ≤ 2^(k+8) elements
  prover : Strategy shape (Layout K × Stmt) (List (Table K)) Unit Unit   -- Lean spec, may be noncomputable
  verify : (Fin vkLen → K) → Stmt → Challenges shape → QProg Bool   -- computable (v2: it is executed)
  extractor : ExtractorImage k n                      -- §4 item 3 (Q1): the image and the split of `B(k)` over its `n + 1` calls
  ε : ChallengeIdx shape → ℝ≥0

namespace Protocol
variable {k : ℕ} (P : Protocol k)

/-- The verifier as a pure verifier on `(L, x)`: run the query program on `IDX L` and the transcript's oracles. -/
def specVerifier : PureVerifier P.shape (Layout K × Stmt) Unit := fun s tr =>
  if (P.verify (P.VK s.1) s.2 (chalOf tr)).eval (⟨P.idxShape, P.IDX s.1⟩ :: tr.oracles) = some true
  then some () else none

/-- Security: perfect completeness for `relK k`, worst-case RBR knowledge soundness (extractor: the image, `B(k)` steps in all) at the declared errors, `ε ≤ 2^-128`. -/
def Secure : Prop :=
  SecureWith (relK k) Set.univ P.prover P.specVerifier (P.extractor.toExtractor P.shape) P.ε

end Protocol
```

- **`Stmt := Fin 32 → K`** (§2.1). The verifier reads the layout only through `VK L` and the
  index oracle `IDX L` (holography, as in v0.3).
- **The verifier is a query program.** It sees an oracle's contents only through `query`, leaf
  by leaf; this is exactly what the compiled argument opens (§3.2). Oracle 0 is the index oracle,
  then the prover's oracles in round order; an out-of-range oracle or leaf rejects.
  `specVerifier s tr` accepts iff `(P.verify (P.VK s.1) s.2 (chalOf tr)).eval
  (⟨P.idxShape, P.IDX s.1⟩ :: tr.oracles) = some true`. The result depends only on the leaves the
  run reads (`probes/s1/VerifyNotLocal.lean`, `eval_local`).
- **The class is in range** (`k_range`): stated once, in the protocol. The relation and
  admissibility are defined at every `k` (§2.2).
- **Shape caps** (`shape_ok`): every round is `Round.Admissible k` (a message oracle has
  `logLeaf ≤ logLen ≤ k + 10`, an index challenge `≤ 64` bits), and the index oracle has
  `logLeaf ≤ logLen ≤ k + 8`. These are v0.3's `OShape.Admissible`, `IdxAdmissible` and
  `Round.Admissible`, now stated once, as a field. The tape cap of v0.3's `ShapeAdmissible`
  belongs to `Compile`'s proof format (§3.2); its blow-up cap is not adopted (S3-A5). The
  compile and harness stages rely on `2^(k+8)` for the index oracle, which the entries cap of
  §2.2 makes sufficient at every class.
- **The extractor** field is an `ExtractorImage k n` (§4 item 3, Q1): a machine image and the
  split of the budget `B(k)` over the `n + 1` calls of the round-by-round extractor. `Protocol`
  has no `WitMid` field: the type of the intermediate witnesses is the contract's (`Mid`, S4-A1).
  `Secure` uses `P.extractor.toExtractor P.shape` (S4-A13), with `k` the structure's class and
  `n` its round count.

### 3.2 Executed objects: the compiled argument

The IOP is compiled to a non-interactive argument by the **organiser's** transform, a Lean
function (`Contract/Compile.lean`, Stage 3; 128 code lines (actual); trusted by review, §8). The
header of that file holds the byte grammar and is **normative**; this section summarises it.

- **`Cfg` is a hash and an arity, nothing else** (S3-A4): `hash : HashId` and `arity ∈
  {2, 4, 8, 16}`. The menu has the single constructor `blake2s` (`HashId.run = blake2s256`); it
  grows only by organiser PRs that add a Lean specification (`sha256`, `keccak256`, `blake3`), and
  every menu hash must have 32-byte digests. Leaf packing is the declared `OShape.logLeaf`, not
  a `Cfg` field. Query batching is off: every query consumes one opening, in query order, and a
  repeated query is opened again (a multi-opening format changes the grammar and is a later
  organiser PR). No grinding (the proved `ε` is the IOP's; a nonce buys nothing here).
- **BCS.** The index oracle `IDX L` is committed once by the indexer, `index cfg P L`, which
  returns the compiled key `VKc vkLen = (Fin vkLen → K) × Digest`: the protocol key `VK L` and the
  index root (the same `cfg` as the prover's oracles). A prover oracle with a **single leaf**
  (`logLeaf = logLen`) is sent **in the clear** (S3-A1): its `8·2^logLen` bytes go in the rounds
  section in place of a root, they are absorbed, and a query of it reads them with no opening. A
  query of a one-leaf oracle opens the whole oracle anyway, so committing it would cost a root, its
  absorption and a leaf hash per query for nothing; this is where small messages go (sumcheck
  polynomials, a FRI final layer). Every other prover oracle, and the index oracle always, is
  Merkle-committed. Each `query` of the verifier's query program (§3.1) on the honest oracles
  becomes a leaf plus an authentication path on the tape; the result depends only on those
  leaves (`probes/s1/VerifyNotLocal.lean`, `eval_local`; `narg_local`, below).
- **Merkle trees** (S3-A2, S3-A11). A leaf's digest is `H(leaf bytes)`, a node's is `H(child₀ ‖ … ‖
  child_{A-1})` (`H = cfg.hash.run`), and the leaves are padded with the zero digest (32 zero
  bytes) to `A^depth`, `depth = ⌈(logLen − logLeaf) / log₂ A⌉` (`Cfg.depth`; `depth_spec` proves
  it is the least `d` with `2^(logLen − logLeaf) ≤ A^d`). Every internal node is hashed from its
  children, one whose children are all padding included. There is **no leaf/node tag**. The
  reason: the depth is fixed by the shape, so a path has a known length and every level's input
  length is fixed, and binding at a fixed depth then reduces to collision resistance
  (`opening_binding`, `probes/s3/RevBinding.lean`: kernel-checked, general in `cfg` and the shape).
  Tree inputs have length `0 mod 8` and absorb/squeeze inputs `1 mod 8` (they carry a tag byte);
  the key digest `D` is in the tree's length domain, which is harmless because the indexer fixes
  its input. A one-byte tag would add a compression to every leaf whose size is a multiple of 64
  bytes (every leaf of ≥ 8 elements), which doubles leaf hashing at 8 elements. This departs from
  the brief's "leaves hashed with domain separation".
- **The key and its digest.** The key bytes (`VKc.toBytes`) are the `vkLen` elements of `VK L`
  (8 bytes each, little-endian: `K.bytes`) then the 32-byte index root. `NARG` rejects a key whose
  root is not 32 bytes (S3-A9). The key digest is `D = VKc.digest cfg := H(key bytes)` (S3-A8,
  §5.1).
- **Fiat–Shamir** (S3-A3). The sponge is a hash chain whose state is a digest, **seeded from the
  key digest**: `s₀ = D`, then the statement `x` (256 bytes) is absorbed. Absorbing `m` sets
  `s ← H(0x00 ‖ s ‖ m)`. Squeezing `b` bytes runs `⌈b/32⌉` steps `s ← H(0x01 ‖ s)` and outputs the
  successive states, truncated to `b`. A prover round absorbs its root or its plain elements. A
  challenge round `chal nE idx` squeezes `24·nE + 8·|idx|` bytes: `E` element `j` is bytes
  `24j … 24j+23` (limbs `c0, c1, c2`, little-endian), and index `j` is the little-endian word at
  `24·nE + 8j` reduced mod `2^b` (its low `b` bits), exactly uniform for `b ≤ 64`, so there is no
  rejection sampling. Challenges are derived, not sent. This departs from "absorbing `VK ‖ x`
  first": a recursion circuit `C_V` computes `D(vk)` anyway (to compare it with `d0`, `d1`), so it
  never re-absorbs a VK of up to 8 KiB; the native cost is the same, one compression per 64 VK
  bytes.
- **The proof format (the tape)** is capped at `tapeCap = 2^20` bytes (1 MiB), checked by `NARG`,
  and leftover bytes reject. v0.3's blow-up cap is not adopted (S3-A5): it priced prover work
  under the static cost model, and v2 measures prover time; the message size is already capped at
  `2^(k+10)`. The grammar, abridged (the header of `Compile.lean` is normative):

  ```
  tape     ::= rounds openings
  rounds   ::= for each prover round, in order: its plain elements | its root
  openings ::= for each query (j, l) of the run of P.verify, in order:
                 nothing if oracle j ≥ 1 is plain, else  leaf path
  path     ::= depth levels, leaf level first; each level the A − 1 sibling digests
  ```

  A query of an oracle that does not exist, or of a leaf `l ≥ 2^(logLen − logLeaf)`, rejects, so
  a padding position is never opened.
- **`NARG cfg P : VKc P.vkLen → Stmt → Tape → Bool`**, deterministic and total, accepts iff the
  tape is within the cap, the key's root has 32 bytes, the rounds section parses, and the query
  program, on the Fiat–Shamir challenges, accepts against the openings with no bytes left over.

Naming: the one-argument `blake2s(·)` / `Blake2s(·)` of this design is `RecursionFast.blake2s256`
(`Contract/Hash/Blake2s.lean`; unkeyed, 32-byte digest). `RecursionFast.blake2s` is the general
keyed function `blake2s key nn msg` of RFC 7693 §3.3.

The **honest compiled prover** `prove cfg P L x w : Option Tape` is a Lean specification in
`Library/Compile.lean`, not in the contract, because no trusted statement uses it (S3-A10; moving
it took `Compile.lean` from 159 to 128 code lines). It returns `none` only if the verifier's run
on the honest oracles leaves its range or the tape exceeds the cap. Kernel-checked there, for every
protocol, `cfg` and instance:

- `narg_complete`, `narg_complete_of_secure`, `prove_isSome` (S3-A6, S3-A13): if `prove` outputs a
  tape and the IOP verifier accepts the honest transcript, `NARG` accepts it under the indexer's
  key; for a secure protocol this holds on every instance of `relK k`. Compile completeness is a
  theorem **provided the honest tapes fit `tapeCap`** (otherwise `prove` is `none`); that proviso
  is the vacuity concern of §5.3.
- `narg_local` (from `runQ_local`): an accepted tape determines the Fiat–Shamir challenges, and on
  them the query program accepts every oracle list consistent with the roots, the plain oracles
  and the authenticated openings. This is the deterministic core of BCS soundness; the binding of
  the openings to the roots is collision resistance (`opening_binding`).
- `NARG_eq_true_iff`: the acceptance condition unfolded, the form that a recursion circuit `C_V`
  must force (§5.3).

The **executed verifier** is `NARG cfg P` compiled by the Lean compiler (`lake exe verify`,
organiser `Main.lean` importing the agent's module, built in the gate tree). There is no second
verifier artefact and no `Agrees` theorem in v2: the thing timed is the thing proved, up to the
Lean compiler and `compile` (§8).

The **executed prover** is the agent's native program (any language; built from source in the
sandbox with the pinned toolchains). It is *not proved*. It must: read `(L, VK, x, w)` from
files, write a tape that `NARG cfg P` accepts, and do so for every benchmark instance within
budget. The **executed indexer** is the Lean-compiled `VK`/`IDX` (untimed, §7.4); a native
indexer may be used by the prover but the resulting `VK` bytes must be identical.

### 3.3 Submission contents

| Item | Form | Checked by |
|---|---|---|
| `P : Protocol k`, `cfg : Cfg` | Lean | gate (computable `VK`, `IDX`, `verify`, extractor image; `--computable` rule updated) |
| `secure : P.Secure` | Lean theorem | comparator (two kernels), axiom audit |
| leaf entry (board L, optional) | nothing extra | benchmark runner |
| recursion entry (board R): `entry : RecursionEntry` = `C`, `fits`, `decode`, `sound`, `complete`, `live` (§5.3) | Lean | comparator, gate |
| native prover (+ optional indexer) | source + build script | sandbox build, benchmark runner |
| claim JSON (`k`, `cfg` = hash and arity, the extractor image, chips and matrix entries of `C_V`, the key digests of `C_V` and `L_chain`) | rendered into the challenge stub (v0.3 renderer) | comparator (`submission = rendered`); the digests by the harness |

**The certificate** (`Contract/Certificate.lean`, Stage 5 and S7-A5; 25 code lines (actual);
trusted, §8) is split by board, as the claim is:

- `Submission k := {P : Protocol k, cfg : Cfg, secure : P.Secure}` (board L), and `SubmissionR k
  extends Submission k` with `entry : RecursionEntry P cfg` (board R; the field is `entry`, not
  `rec`, which would clash with the recursor). The class is pinned by the type `Submission D.k`.
- `Declared := {k, hash, arity, img : Image}` is organiser data rendered from the claim JSON, and
  `DeclaredR extends Declared` adds the **static** size of `C_V` (`chips`, `entries`: the chip
  count and the matrix-entry count) and the two key digests `digestC`, `digestL`.
- `Certificate D S` (board L): the submission's configuration is the declared one, and
  `S.P.extractor.img = D.img`, so the image `Secure` is about is the literal rendered from the
  submitted files (S4-A2, S7-A1/A5). `CertificateR D S` extends it by `size`: `C_V` has the
  declared chip and entry counts. Adding a field to a `Prop` structure only adds a conjunct, so
  nothing weakens.
- **The cells of `C_V` are not declared.** They depend on the witness and are bounded through
  `complete` (S1-A6, §5.3). The declared size is static, certified by evaluation.
- **The key digests are declared, not certified.** `D (index cfg P C_V)` commits an index oracle
  of up to `2^(k+8)` elements, beyond the kernel except for toys. The harness computes both
  digests with the compiled indexer (§6.3 step 2, untimed): `D (index cfg P S.entry.C)` from the
  *submitted* `C_V`, never from a layout the prover supplies, and `D (index cfg P (L_chain 2^10))`
  (the recursion tree's `n`, not the rendered `L_chain(16)`). It rejects a claim whose digests
  differ, and uses its own values in `rootOK` and as the key of every node's and leaf's `NARG` run,
  never the declared ones (S5-A13).

---

## 4. Security definitions (trusted)

All statements are the v0.3 ones over the new relation; nothing here is new except the extractor
image (Q1) and the recursion entry (§5).

1. **Perfect completeness** (`PerfectComplete (relK k) Set.univ P.prover P.specVerifier`): for
   every admissible layout, statement and satisfying witness, and *every* challenge vector, the
   Lean prover's transcript is accepted.
2. **Round-by-round knowledge soundness** (`RbrKS`): a knowledge state function `KSF` for the
   named extractor with per-round errors `ε c ≤ 2^-128`, in counting form
   (`#bad ≤ ε · #challenges`). Worst case per prefix; no probability measure in the trusted base.
3. **Bounded extractor** (Q1, decided 2026-10-13; `Contract/Extractor.lean`, Stage 4). The
   extractor is a RISC-V image (`ExtractorImage k n`) run on the vendored Rv64, and the
   round-by-round extractor (`toExtractor`) is *defined* as running it: `extractMid m s tr w` runs
   the image on `⟦m, s, tr, w⟧` and decodes the output, and a fault, a trap, fuel exhaustion or an
   output of more than `witCap k = 2^(k+12)` words yields the empty witness `[]`. There is no
   separate agreement theorem and no separate step bound; the `KSF` laws are stated about this
   function. This is what makes "knowledge" mean something for the hash-chain leaves
   (preimage-hard: accept-all would need a provable preimage finder within `B(k)`) and what gives
   recursion its `N · t_E` bound. The laws force a witness in `relK` only before round 0, where
   `[]` fails (`nil_not_relK`); after round 0 the submitter's state function says what an output
   must satisfy, `[]` included.
   - **The serialisation is the contract's** (S4-A1; this resolves O-1). A submitter-supplied
     encoder or decoder of the intermediate witness would be unbounded Lean computation on the
     extractor's path: an encoder could append a brute-forced hash preimage to the tape, for the
     image to copy, and that voids the fuel bound. Requiring `dec ∘ enc = id` does not help, nor
     does a size bound, since a preimage is a few words. So the witness type is fixed:
     `Mid n j := List (Fin.cases (Table K) (fun _ => Word) j)`, the witness tables before round 0
     and words after it (a submitter's `KSF` reads structure into those words as it likes, and its
     laws are about the words). The input tape is `extractorTape j (L, x) rounds w = frame [[j],
     L.words, x, round₀, …, w]`: a directory first (the section count, then the start and length of
     each section), then the layout as words (`Layout.words`), the 32 statement words, one section
     per transcript round (an oracle's elements; a challenge's tape words), and the witness after
     round `j`. The extractor sees `L`, not `VK L` or `IDX L` (S4-A5): `IDX` is submitter code and
     could carry precomputation keyed on `L`, and the knowledge claim is about `(L, x)`. Before
     round 0 the output is decoded by `decTables` (a missing word reads as `0`, leftover words are
     ignored); after round 0 the witness is the output words, unchanged.
   - **The machine** (`Contract/Machine.lean`, trimmed from v0.3; S4-A3, S4-A4). RV64IM + W-ops +
     Zbc. The address space is all `2^64` bytes. The input tape is read-only from `TAPE_BASE =
     2^63` (an extractor reads the whole transcript prefix: up to `2^14` rounds of `2^(k+10)`
     elements), and data memory is `[0, 2^63)` with the image's data words from address 0. `ECALL`
     with `t0 = 0` halts and returns the `a1` doublewords at `a0` (8-aligned); every other `t0`
     traps. So an extractor can output a region of the tape without a copy loop (the toy's
     `firstMsgImage` is 8 instructions), and there is no accept/reject: an image gives up by
     trapping.
   - **The budget is a total** (S4-A9, S4-A14). `B(k) = 2^(2k+16)` **steps** is the total over the
     `n + 1` calls of the round-by-round extractor of an `n`-round protocol. A step is one
     instruction (`div`, `clmul` and `ECALL` included): there is no cost model. The submitter
     chooses how the total is split over the calls (`ExtractorImage.fuel : Fin (n + 1) → ℕ`,
     `fuel_le : (List.ofFn fuel).sum ≤ extractorBudget k`; a round-0 decoder may take almost all of
     it), and the contract bounds the total, not the split. The reason: knowledge comes from the
     composed extractor (`Library/RbrSound.lean`'s `chain`), whose calls may pass state through
     the witness words, and rounds are free (`padShape`: empty challenge rounds). Under a per-call
     budget a one-word secret was enumerable at every class (`chain_secure`,
     `probes/s4/ChainBudget.lean`, with `2^10` rounds at class 20). Now the whole extraction has at
     most `B(k)` steps whatever `n` (`composed_fuel_le`), and adding rounds buys nothing. Two
     ready-made splits: `even` (`B(k)/(n+1)` each, at least `2^(2k+1)` within the round cap,
     `even_fuel_ge`) and `atZero` (all of it on the call before round 0, which the toy uses; `P_triv`
     declares only the 8 steps it needs there, §7.3). Extraction work concentrated in one round must fit the fuel the submission declares for
     that call.
   - **Why `B(k) = 2^(2k+16)`** (S4-A10; the user's value is kept). `B(k)` is `2^16` times the
     square of the witness-cell cap `2^k`; the longest admissible oracle squared is `16·B(k)`
     (`oracle_sq`). It is not "quadratic in the oracle length", and it does not admit
     Berlekamp–Welch by Gaussian elimination: cubic elimination on `2^k` unknowns exceeds `B(k)`
     from `k = 17` (`cube_gt`). At about 10 steps per `K` multiply–add the whole budget admits
     O(N²) decoding up to about `2^(k+6)` elements (`quadratic_fits`) and quasi-linear decoding of
     every admissible oracle. Whether the Johnson-regime decoder that Q1 relies on fits is O-11.
   - **The image and the output** (S4-A2, S4-A12). `img_le : img.byteSize ≤ imageCap = 2^20`
     bytes: without a cap `img.data` could be a lazily defined table of `2^64` precomputed
     preimages, computable and never evaluated by a symbolic proof. The image is the literal
     rendered from the claim, and the certificate checks `P.extractor.img = D.img` (§3.3), so a
     data word cannot be an expensive Lean term. `witCap` is an interface cap, not a security
     bound: the largest intermediate witness an extraction passes between calls (four maximum-size
     oracles); the fuel already bounds what an output can contain.
   - **What the bound guarantees.**

     > Each extractor call runs the submitted image (≤ `2^20` bytes, the same for every
     > statement) on a tape the contract builds from `(j, L, x, transcript prefix, next
     > witness)` alone, for the number of steps the submission declares for that call; the
     > declared fuels sum to at most `B(k) = 2^(2k+16)`. Its output (≤ `2^(k+12)` words, else
     > empty) is decoded by trusted code that adds only zeros. The laws force a valid witness
     > only before round 0, where `[]` fails `relK`, so knowledge comes from the composed
     > extractor: `n + 1 ≤ 2^14 + 1` calls that may pass state through the witness words, which
     > run for at most `B(k)` steps in all (`composed_fuel_le`), whatever `n`. Brute force is
     > therefore excluded for witnesses of two or more `K` elements at every class, and for one
     > `K` element up to `k = 23`; at `k ≥ 24` it is possible only if a candidate costs at most
     > `2^(2k−48)` steps, loop control included. `B(k)` admits O(N²) decoding up to about
     > `2^(k+6)` elements and quasi-linear decoding of every oracle, not Gaussian elimination.

   - **Thresholds for a one-word secret** (S4-A9, S4-A14; supersedes S4-A7). A secret of one `K`
     element is enumerable only if `2^(2k+16) ≥ 2^64 · c`, `c` being the steps per candidate
     including loop control. That never happens for `k ≤ 23` (`composed_lt_word`). At `k = 24`
     it needs `c = 1`, which no loop achieves (`B(24) < 2·2^64`, `budget_24_25`); at `k = 25`,
     `c ≤ 4`. So in practice the boundary is `k ≥ 25` for cheap tests (`k ≥ 26` for any
     non-trivial test). Two `K` elements are never enumerable: `2^72 < 2^128`
     (`composed_lt_two_words`). The negative control is `chain_search_fails`
     (`Controls/Extractor.lean`): at class 20, for any image and any split, a chained search that
     tests fewer than 256 candidates per step of each call's fuel (bit-slicing included) covers at
     most `255·2^56 < 2^64 − 1` candidates and is not an extractor. The benchmark's hash-chain
     start is 256 bits, so nothing changes there; a relation whose hardness rests on a single `K`
     element is not protected at `k ≥ 25`.
4. **Rejecting runs** (Q3): v2 has no proved cost counters, so the all-runs bound becomes
   *totality*: `verify` is a total Lean function and `compile` is total, so every tape
   terminates; the measured verification time on random tapes is an unranked DoS column (§7.5).
5. **Why the relation is hard where it must be** (Q4): the leaf benchmark is "hash chain with
   private start" (§7.2), preimage-hard, so (2)+(3) are non-vacuous; the recursion relation is
   deterministic given the proofs (§5), so there soundness carries the content and (3) supplies
   the proofs to the next level's argument.

`Contract/Security.lean` has one comment-only edit (S4-A11), the only change to a carried-over
trusted file: its header loses the sentence "At L1 the extractor is unconstrained … labelled
'RBR-sound'", which is replaced by "For an unconstrained extractor `RbrKS` is equivalent to RBR
*soundness* (`Library/RbrSound.lean`, A2-M2); `Protocol.Secure` names the submitted image
(`Contract/Extractor.lean`, Q1), to which the collapse does not apply." No declaration changes and
the code-line count is unchanged (55).

The ArkLib bridge (`Bridge/ArkLib.lean`, one-directional `RbrKS.toArk`) carries over unchanged
and stays untrusted.

---

## 5. Recursion: verifier-as-circuit (replaces track T2)

### 5.1 Statement format (trusted, `Contract/Recursion.lean`; 67 code lines (actual))

`Stmt = 8 digests`, `d0..d7`, each 4 K-elements = 32 bytes (cells `0 … 31` of row 0 of the public
chip, §2.1).

| Kind | `d0` | `d1` | `d2` | `d3` | `d4 … d7` |
|---|---|---|---|---|---|
| leaf (hash chain, §7.2) | `y` (chain end) | `n` (chain length, one element) | 0 | 0 | 0 |
| node | `D(VKc C_V)` | `D(VKc L_chain)` | `H(x₁ ‖ x₂)` | `(tag₁, tag₂, 0, 0)` | 0 |

`H = cfg.hash.run` is the same hash as `D` and the sponge (S5-A8), so a recursion circuit needs
exactly one hash gadget; `x₁ ‖ x₂` is the children's statement bytes (`stmtBytes`, 256 + 256). With
the one-element menu `H` is `blake2s256`. A tag is `leaf ↦ 0`, `node ↦ 1` (`tagK`).

`D` is the trusted `VKc.digest cfg vkc := cfg.hash.run vkc.toBytes` (S3-A8, `Compile.lean`): it
hashes the compiled key, the `VK` elements (8 bytes each, little-endian, `K.bytes`) and then the
32-byte index root, and it is also the sponge's seed (§3.2). `D` over the elements alone (S2-A1)
would let a node witness choose its own index root. A 32-byte digest becomes a statement slot
`d_i` of 4 K-elements, limb `j` being digest bytes `8j … 8j + 7` read little-endian
(`digestToSlot`, which uses `K.ofBytes`, the inverse of `K.bytes`; Rust `u64::from_le_bytes`). The
byte round trips are in `Library/Compile.lean`, `blake2s256_length` (`Library/Blake2s.lean`) gives
the 32 bytes, and `digest_kat` pins `D` to `hashlib.blake2s(vk ‖ root)`.

A node's statement is the trusted function `nodeStmt` (§5.2). It commits to both keys, to its two
children's statements and to their tags, and carries no free bits (a node statement with `d3` or
`d4` set is rejected: `nonzero_d3`, `nonzero_d4`). The tags are bound to tree positions at the
contract level, for every leaf layout, not as a property of `L_chain`'s public chip: by induction
from the recomputed root, `d2` fixes each child and `d3` its tag (S5-A11). The cost is no hash; in
`C_V` it is one linear constraint per tag, the tags being already the witness bits that select the
keys. A node *child's* statement is pinned by its parent's `d2` (collision resistance) and by its
own proof (the `C_V` relation), not by `aggOK`.

**The statement tree and the root check** (S5-A5, S5-A12; trusted). `pairUp` (one level: adjacent
statements, all tagged `t`, aggregated in order; `none` on an odd count) and `treeRoot cfg vkC vkL
d xs` (the root of the complete tree of depth `d` over the leaf statements `xs`: level 1 over
leaves, every level above over nodes) are definitions of the contract. The organiser's root check
is

```lean
/-- `x` is the root of the statement tree over the leaf statements `xs`, keyed by the indexer for `C` and `L`. -/
def rootOK (cfg : Cfg) (P : Protocol k) (C L : Layout K) (d : ℕ) (xs : List Stmt) (x : Stmt) : Bool :=
  decide (treeRoot cfg (index cfg P C) (index cfg P L) d xs = some x)
```

It pins `d0` and `d1` (the keys), `d2` (the children, level by level) and `d3` (the tags, by
position). For the benchmark `d = 6` and `xs` are the 64 leaf statements in order (§6.3 step 5).
With `aggOK` it pins the node's keys (`keys_of_root`: their digests are the indexer's, by
`digestToSlot_inj` on 32-byte digests). Library: `rootOK_iff`, `treeRoot_one`, `treeRoot_two`,
`treeRoot_node`. Controls: `rootOK_xT` (the depth-2 tree over `x0, x1, x0, x1`, with the KAT
`treeKat` against Python's `xT`), `rootOK_leaf`, `rootOK_other_key`, `rootOK_odd`, and
`mistag_rejected` (the level-2 node with its node child tagged leaf is rejected).

### 5.2 The recursion layout and the fixed point

The agent supplies `C_V : Layout K` whose satisfiability means "the compiled verifier accepts two
children". Its witness (`NodeWitness`) holds the two compiled keys `vkC`, `vkL : VKc` as cells, the
child tags `t₁, t₂ ∈ {leaf, node}`, and each child's statement and proof `x₁, π₁, x₂, π₂`. The
organiser's specification of what `C_V` must enforce:

```lean
/-- The aggregate statement of a node: the keys' digests, the hash of the children, their tags, zeros. -/
def nodeStmt (cfg : Cfg) (vkC vkL : VKc vkLen) (t₁ t₂ : Tag) (x₁ x₂ : Stmt) : Stmt :=
  Stmt.ofSlots fun i => match i.val with
    | 0 => digestToSlot (vkC.digest cfg)
    | 1 => digestToSlot (vkL.digest cfg)
    | 2 => digestToSlot (cfg.hash.run (stmtBytes x₁ ++ stmtBytes x₂))
    | 3 => tagSlot t₁ t₂                                  -- (tag₁, tag₂, 0, 0)
    | _ => fun _ => 0

/-- What a node proves: the aggregate statement, 32-byte index roots, both children accepted. (Trusted.) -/
def aggOK (cfg : Cfg) (P : Protocol k) (x' : Stmt) (nw : NodeWitness P.vkLen) : Bool :=
  decide (x' = nodeStmt cfg nw.vkC nw.vkL nw.t₁ nw.t₂ nw.x₁ nw.x₂) &&
    nw.vkC.2.length == 32 && nw.vkL.2.length == 32 &&
    child cfg P nw.vkC nw.vkL x' nw.t₁ nw.x₁ nw.π₁ && child cfg P nw.vkC nw.vkL x' nw.t₂ nw.x₂ nw.π₂

/-- A child is accepted: a node child carries the parent's `d0`, `d1` and verifies under `vkC`; a leaf under `vkL`. -/
def child cfg P vkC vkL x' : Tag → Stmt → Tape → Bool
  | .node, x, π => decide (x.slot 0 = x'.slot 0) && decide (x.slot 1 = x'.slot 1) && NARG cfg P vkC x π
  | .leaf, x, π => NARG cfg P vkL x π
```

**Bounded node witnesses (S5-A1).** `aggOK` requires both keys' index roots to be 32 bytes, the
check `NARG` makes on the key it uses (S3-A9). Without it, in a node whose children are both leaves
`vkC` is constrained only by its digest `d0`, and a key's root is a `List UInt8` of any length: `C_V`
would have to decode, from a witness of at most `2^k` cells, every `vkC` whose digest is `d0`,
arbitrarily long preimages included, an unsatisfiable obligation. With the check every part of an
accepted node is bounded: keys (`vkLen ≤ 2^10` elements and 32 bytes), statements (32 elements),
tapes (`≤ tapeCap`, by `NARG`) and tags.

**Fixed point (V2-1).** `C_V.Admissible k ∧ C_V.cells ≤ 2^k` for the *same* `k` at which `P` is
secure (the cell bound is on the honest node witness and is enforced through `complete`, §5.3). The
trivial verifier (check every constraint; linear in the index) has no fixed point, so it is
excluded from board R without a proof-size cap. Smaller `C_V` is the whole game.

**VK cycle.** `VK C_V` depends on `C_V`, which verifies proofs under `VK C_V`. The cycle is broken
the standard way: the VK enters `C_V` as *witness cells* checked against the public digest `d0`;
nothing inside `C_V` depends on the value of `VK C_V`. A node child must carry the parent's `d0`,
`d1`, so the keys are the same at every level.

### 5.3 The agent's circuit-correctness theorems

```lean
structure RecursionEntry (P : Protocol k) (cfg : Cfg) where
  C : Layout K
  fits : C.Admissible k                                   -- the index is within the caps; the cell bound is in `C.rel k`
  decode : List (Table K) → NodeWitness P.vkLen           -- computable: reads the node witness out of the tables
  sound : ∀ x' w, C.rel k x' w → aggOK cfg P x' (decode w) = true
  complete : ∀ x' nw, aggOK cfg P x' nw = true → ∃ w, C.rel k x' w ∧ decode w = nw
  live : ∃ L x' nw, nw.vkC = index cfg P C ∧ nw.vkL = index cfg P L ∧ aggOK cfg P x' nw = true
    -- the compiled argument accepts a node keyed by the indexer: `C`'s key and the key of some layout `L`
```

`sound` is the load-bearing one: any satisfying assignment of `C_V` contains two accepted child
proofs, and `decode` names them (no existential), so the extractor chain is explicit:
root proof → (KS of `P` on `C_V`) tables → (`decode`) child proofs → … → leaf proofs → (KS of `P`
on `L_chain`) chain preimages. `complete` keeps the honest path inhabited. It ranges over every
accepted node, whatever its keys, so `verify` must bound its own work and its tape on every key
(e.g. reject keys outside the format of `VK`); and since every accepted node is decoded from a
satisfying witness, every accepted statement has a witness of at most `2^k` cells (`decode` may
also read cells outside `rows × cols`).

`fits` does not bound the cells: cells depend on the witness and are bounded by `rel` (its
size-class clause), not by `Admissible`. The fixed point "`C_V` fits class `k`" (§5.2) is enforced
by `complete`, since an honest node witness must satisfy `C.rel k`, which contains the cell bound.

**`live`** (S5-A7, S5-A10) keeps `complete`, and with it the cell bound, from being vacuous.
Compile completeness is a theorem (`narg_complete_of_secure`, §3.2) but only for honest tapes that
fit `tapeCap`; a secure protocol whose proofs exceed the cap has no accepted node at all, so
`complete` holds for it trivially and, with an unsatisfiable layout, so does `sound`. The toy
protocol is such a protocol (it sends `8·2^(k+10)` bytes in the clear), and it has no recursion
entry for any layout and decoder (`toy_no_entry`; `toy_vacuous_fields` shows every other field
would hold with `unsat`; `toy_no_submissionR`). `live` is stated **at the indexer's keys** because
`Secure` constrains `P.verify` only on keys `P.VK L`: with a bare `∃ x' nw`, a secure protocol
could meet `live` with a "magic" key that no layout has, while accepting nothing under any indexer
key (`toyCM`; `magic_not_live`, `magic_no_entry`), and `complete` would then constrain `C` only on
nodes that need three hashes and no verification. A submitter proves `live` with `live_of_secure`
or `aggOK_sat_of_secure` (`Library/Recursion.lean`) from one instance of `relK k` (any small
layout), its honest tape, and a bound that the tape fits `tapeCap` (a size bound on its own proof
format); no kernel evaluation of the tape is needed. **Remaining gap:** a protocol that
special-cases the key of a trivially satisfiable layout can still meet `live` without accepting
any proof of a hard layout; that the benchmark's nodes are provable is shown by the benchmark run
(§6.3, a node step must produce a verifying proof). A `live` at `L_chain` itself would close it
but needs a completeness theorem for whole chains, which does not exist. No positive
`RecursionEntry` exists in the repository (§7.3); `cmpToy_live` (`Controls/Certificate.lean`)
shows the field satisfiable for the non-secure compile toy.

**Why `sound` + `complete` + `live` force a real circuit.** Let `Acc = {(x', nw) | aggOK cfg P x'
nw = true}`.

1. *Exact image.* `sound` and `complete` together say that at every statement `x'`, `decode` maps
   the satisfying witnesses of `C` *onto* `Acc(x')`. So `C`'s language at class `k` is exactly
   `{x' | Acc(x') ≠ ∅}`, and each such statement has a witness of at most `2^k` cells.
2. *`sound` puts `NARG` in the constraints.* `sound` quantifies over every `w`, and `rel` sees only
   `C`'s constraints, so the claim that `NARG` accepts `decode w`'s tapes must *follow from* those
   constraints. `decode` may compute, but it cannot make an unconstrained tape accept. For a
   concrete hash, Lean establishes "this path climbs to that root" or "this challenge is that
   squeeze" only through constraints that entail the computation.
3. *`complete` admits nothing stronger than `NARG`.* It quantifies over every `nw`, so `C` must
   accept every tape `NARG` accepts, Fiat–Shamir forgeries that no one can find included. A `C`
   that checked anything stronger, such as the truth of the child statement in the trivial
   verifier, would need a proof that every accepted tape has a true statement, which is
   standard-model knowledge soundness of BLAKE2s and is not provable. A `C` that checked anything
   weaker breaks `sound`.
4. *The fixed point.* The decoded predicate is therefore `NARG` itself, and the fixed point is that
   its trace on two tapes of at most 1 MiB fits `2^k` cells.
5. *`live` rules out degenerate decoders.* `live` makes `Acc ≠ ∅`; then `Acc` is infinite, because
   the recursion key of a two-leaf node is free (`live_family`). So no constant or finitely valued
   `decode` passes `complete` (`decode_not_const`, kernel, for every `P`; both in the review probe
   `probes/s5/review/LiveFamily.lean`). A constant decoder would also need `C` to pin its
   statement, since `aggOK x' nw₀` forces `x' = nodeStmt(nw₀)`.
6. *Where `Secure` stops.* `Secure` constrains `P.verify` only on keys `P.VK L`. On such keys an
   accept-all verifier contradicts round-by-round knowledge soundness with the bounded extractor;
   on other keys it may accept everything (`toyCM`). `live` must therefore name indexer keys, or
   the "trace" of step 4 can be three hashes.
7. *What is not forced, and is the benchmark's job.* `live` does not force `Acc` to contain the
   benchmark's nodes, and `decode` need not be efficient. Composition across levels (§5.4) is
   Fiat–Shamir and BCS knowledge soundness in the random-oracle model, applied once per level;
   `rootOK`, the collision resistance of `d2` and the tags in `d3` do the bookkeeping.

The theorem is about `aggOK`, which calls `NARG cfg P`, i.e. Merkle verification, Fiat–Shamir
and the IOP verifier's arithmetic all have to be arithmetised and proved (`NARG_eq_true_iff` is
the unfolded form to force). This is the heaviest obligation in v2 and the reason for the Clean
frontend (§9).

Controls (`Controls/Recursion.lean`, `Controls/Certificate.lean`, `Controls/MagicKey.lean`) run on
`cmpToy` (§3.2, not secure, tiny shapes): `aggOK` is satisfiable directly (`aggOK_two_leaves`,
`aggOK_node_child`) and through compile completeness (`toy_sat_via_complete`, from
`aggOK_sat_of_complete`); the general `aggOK_sat_of_secure` has no instance in the repository,
because the only `Protocol` proved secure, the toy, has tapes beyond the cap.

### 5.4 What is *not* claimed

No theorem composes levels. `sound` and `Secure` are per level; the step "NARG accepted ⇒ the
prover knew a witness" is the BCS/Fiat–Shamir transformation in the random-oracle model, applied
with the hash instantiated inside `C_V`. This is the same heuristic every deployed recursive SNARK
relies on and the open problem leanerVM documents. The report's §8.4 wording stands.

---

## 6. Scoring: wall time on the reference machine

### 6.1 Principle (Q2, resolved 2026-10-14)

Measured wall time on **one organiser-run reference machine**, accepted with its known
weaknesses (one-machine overfitting; noise) because it prices the whole design, prover included,
and needs no cost model to audit. The proved objects (`Secure`, `RecursionEntry`) do not depend
on any price, so a change of machine never invalidates a record, only re-ranks it.

### 6.2 Boards

| Board | Score (lower is better) | Ranked? |
|---|---|---|
| **R** recursion | `S_rec` = median over node steps with two *node* children (tree levels ≥ 2) of: prover wall time on `C_V` (inputs: two child proofs) **+** `NARG` wall time on the output proof | **headline** |
| **W** wrap | `S_wrap` = the same over level-1 steps (two *leaf* children) | published, unranked (shows how recursion-friendly the leaf proofs are) |
| **L** leaf | `S_leaf` = median over benchmark chains of: prover wall time on `L_chain(n)` **+** `NARG` wall time on the proof; **proof size ≤ 2^17 bytes** | ranked, secondary |
| DoS column | `NARG` wall time on 1,000 random tapes, max | published, unranked |

Why these: on R the prover is timed *because* the fixed point excludes the trivial protocol, so
prover time is honest (it is the recursion cost); on L the proof-size cap plays that role, since a
leaf has no fixed point (proof = witness is 78 MiB for `L_chain(2^10)`, 10.2 M cells; the cap is
128 KiB). The verifier is timed on both so that work cannot be shifted into it for free.

**The 128 KiB cap is a runner check** (S7-A3, S7-A7): the benchmark runner rejects a board-L
evaluation in which any measured leaf tape has more than `2^17` bytes. The certificate cannot
state it (it says nothing about the native prover's tapes), and `NARG` itself enforces only
`tapeCap = 2^20`; there is no contract change.

**The class of a board** (S6-A1, S7-A6). Every `L_chain(n)` needs `k ≥ 24` (§7.2), so `k_min = 24`:
the recursion tree's `L_chain(2^10)` fits class 24, and a board-L entry needs the class of its
largest leaf layout (24 for `n ∈ {2^8, 2^10}`, 26 for `L_chain(2^12)`).

### 6.3 Benchmark run (one evaluation)

1. **Instances.** `N = 64` chains, fresh random secret starts `s_i` per evaluation, length
   `n = 2^10` for the recursion tree (`L_chain(2^10)` fits class 24). The leaf board is
   `n ∈ {2^8, 2^10}` at class 24 (the 64 tree chains are its `2^10` instances, plus 16 chains of
   `2^8`), and optionally `n = 2^12` at class 26 (16 chains; `k_range` allows it, and an entry at a
   lower class does not run it). Secrets are never written to the sandbox the verifier runs in. The
   chain generator reads a secret from a file or stdin, never from a command-line argument, and a
   witness file holds `s` (row 0 of `S0`), so it is secret material too (S6-A9).
2. **Indexing** (untimed, budget 1 h total): Lean-compiled `VK`/`IDX` on `L_chain(n)` and `C_V`.
   The harness computes the key digests of the submitted `C_V` and of `L_chain(2^10)` here and
   compares them with the claim (§3.3, S5-A13).
3. **Leaves**: the native prover on each chain (budget 120 s each, 48 GB). Every proof must
   verify.
4. **Tree**: 32 wrap steps, then 16 + 8 + 4 + 2 + 1 = 31 node steps. Each step is a fresh
   process in a fresh working directory, inputs on local disk (warm page cache allowed), all cores
   available, no network, no GPU, budget 600 s. Every output must verify.
5. **Root**: organiser checks `rootOK` (§5.1: the statement tree recomputed over the 64 leaf
   statements with its own key digests, which pins `d0 … d3`); `NARG` on the root proof
   (budget 60 s).
6. **Repeat** the whole run 3 times; `S_rec`, `S_wrap`, `S_leaf` are medians of per-run medians.

Any failure anywhere (a proof that does not verify, a timeout, a crash, memory above 48 GB)
rejects the evaluation; there is no partial credit.

### 6.4 Measurement policy

- Reference machine: x86-64, ≥ 32 cores, 64 GB, NVMe, idle during evaluation; exact SKU, kernel,
  glibc, Rust/gcc/Lean versions published per season in `harness/reference-machine.md`.
- Timed region: process start to output file closed, `perf stat`-style wall clock from the
  runner. Builds and indexing are outside it.
- Record rule: a new record must beat the standing one by **≥ 3 %** (above the measured noise).
- Re-runs: all standing records are re-measured each season and whenever the machine changes;
  the scoreboard shows the hardware id next to every number. A record is never invalidated by a
  re-run, only re-ranked.
- Prover nondeterminism: allowed (randomised algorithms), but every instance must succeed.
  Variance is the agent's problem: medians over 31 steps × 3 runs.

### 6.5 Caps (pass/fail, never scored)

| Cap | Default |
|---|---|
| `lake build` of the submission on the reference machine | ≤ 1 h, ≤ 48 GB |
| harness (comparator + nanoda + gate + axiom audit) | ≤ 2 h |
| tape (proof) | ≤ 1 MiB (R, W), checked by `NARG` (`tapeCap`); ≤ 128 KiB (L), checked by the benchmark runner on every measured leaf tape |
| VK | ≤ 2^10 K-elements |
| rounds | ≤ 2^14 |
| message oracle | ≤ 2^(k+10) elements |
| index oracle | ≤ 2^(k+8) elements |
| index challenge | ≤ 64 bits |
| extractor steps | `B(k) = 2^(2k+16)` **in all**, over the `n + 1` calls, split as the submission declares (`fuel_le`) |
| extractor image | ≤ `2^20` bytes (`imageCap`) |
| extractor output | ≤ `2^(k+12)` words per call (`witCap`: an interface cap, not a security bound) |
| indexing | ≤ 1 h total |
| leaf proving | ≤ 120 s per chain |
| a recursion step | ≤ 600 s |
| whole evaluation | ≤ 6 h |

Build time is a cap, not a score term (the earlier regulariser idea): it measures proof
engineering, not design, and has no exchange rate against seconds of proving.

### 6.6 Incentive analysis (every channel we could think of, and what closes it)

| Gaming channel | Closed by |
|---|---|
| trivial protocol (proof = witness) | R: fixed point (§5.2); L: proof-size cap |
| accept-all / accept-most verifier | `RbrKS` + bounded extractor on a preimage-hard leaf relation (§4) |
| verifier special-cases `C_V` | allowed and intended (that *is* recursion efficiency); `Secure` quantifies over all admissible layouts, so the special case must still be sound |
| overfit to benchmark inputs | secrets fresh per evaluation; leaf proofs are inputs to R, not a score; the only "input" to R the agent controls is `C_V`, which they are supposed to optimise |
| precomputation outside the timed region | fresh process per step, no persistent state; indexing is untimed but bounded and digest-checked; fixed tables capped |
| move work verifier ↔ prover | both timed on every board |
| move work into the leaf proofs ("pre-digested" proofs that make nodes cheap) | leaf budget + 1 MiB tape + `C_V` must read them within `2^k` cells; allowed within those bounds, and legitimate |
| lucky runs / noise | medians of medians, 3 % record margin, isolated machine |
| one-machine overfitting | accepted; seasonal re-runs, hardware id, SKU published |
| huge index / VK to hide work | admission caps (§2.2), `vkCap` |
| prover-chosen table heights | counted in cells ≤ `2^k` |
| exotic hash with no Lean spec | `Cfg` menu; adding a hash is an organiser PR with a Lean spec |
| nondeterministic prover that sometimes fails | every instance must succeed |
| parallelism | wall time on a fixed core count; multi-threaded provers are expected |
| rejecting-run DoS | totality (§4.4) + published DoS column |
| extractor exhausts fuel on honest inputs | caught by the `KSF` laws at round 0, where `[]` fails `relK` (Q1, S4-A12); after round 0 by the submitter's own state function |
| `compile` tampering | organiser code, fixed; the gate's trust-by-hash covers it |
| proof engineering tricks to pass build caps | caps are generous; not scored |
| Lean-compiled verifier is slow | same for every entry; verifier time is a small share of `S_rec`; the agent chooses `cfg` to keep it small |

---

## 7. Benchmark and baseline

### 7.1 Why hash chains with a private start

`R_chain(y, n; s) := blake2s256^n(s) = y`, `s ∈ {0,1}^256` private (`blake2s256` is the
one-argument hash of §3.2). Hard (preimage), cheap to
state, one parameter `n` for scaling, and representative of the application (hash-based
signatures, Merkle paths). "Public start" is rejected: witness-free, so knowledge is vacuous.

### 7.2 The leaf layout `L_chain(n)`

Generated by `harness/gen-chain-layout.py` as a `Layout` JSON (the schema of `harness/README.md`: K
elements as 16 hex digits, the closed-form table kind `add8`) and rendered into Lean by
`harness/render-layout.py` (S6-A6). The arithmetisation is `harness/CHAIN-LAYOUT.md` and the
measurements are `docs/stages/S6a-RESULT.md`.

- **Chips.** A G chip with two rows per G-call (one half of `G` per row; 53 columns). A fixed
  `add8` table of `2^17` rows (an 8-bit add with carry) and a 16-row nibble table. Twenty state chips
  `S0 … S19`, one row per compression, holding the state before each half-round and the message
  words. A `FINAL` chip (finalisation, a byte range check of `H₄ … H₇`, and the chain link) and the
  public chip.
- **Buses.** Four `sub` buses: `ADD`, `ADDTOP`, `PAIR`, `NIB`. Four `eq` buses: G inputs, G
  outputs, message words, output.
- **Why two rows per G-call.** One `G` needs 24 byte lookups. When the layout was designed a chip
  had at most `2^4` ports (§2.2), so one row per G-call or per round was inadmissible; a row of one
  half-`G` uses 15 ports. The cap is `2^5` since S8-A9, which would admit one row; the layout is
  unchanged.
- **Arithmetic.** XOR is field addition. Additions mod `2^32` are bytewise lookups into `add8`;
  byte 3 uses a second port of the same table without the carry-out, so the discarded carry is not
  a cell. `rotr 16` and `rotr 8` permute bytes. `rotr 12` and `rotr 7` cost one wrap cell each
  (`(1 + X^32)·W`, `W` range-checked as a nibble); this is sound because every packed word is later
  decomposed into range-checked bytes. Every chip's gadget has the form `gate · linear = 0`: CCS
  with `t = 2`, `q = 1`, degree 2, the gates being the view's constant and flags and the G chip's
  phase cell.
- **Statement and boundaries** (S6-A3). The statement is `x = (y₀, y₁, y₂, y₃, n, 0, …, 0)`, `y_j`
  being digest bytes `8j … 8j+7` little-endian (§5.1). The public chip constrains all 32 cells, so
  a statement with another `n` or a nonzero tail has no witness. The start `s` is the free message
  of `S0`'s row 0. The digest words `H₄ … H₇` are range-checked in `FINAL` (byte pairs on `PAIR`);
  otherwise a wrong `rot 7` wrap bit in the last compression would alias across the 64-bit limb
  packing of `y`.
- **Routing by tags** (S6-A4; no contract change). `eq`-bus messages carry tags `γ^r` with `γ = X`,
  a generator of `K*` (order `2^64 − 1`): row `r` of the G chip has tag `γ^r`, and the state chips
  use `κ = γ^{160i + 8(s−1)}`. Every tag chain is pinned at its first row (`[r = 0]`) and its last
  row (`[r + 1 = rows]`), which fixes every height, so a prover cannot add, drop or reorder
  compressions. The witness is unique given `s`.
- **Size and class** (S6-A1). `L_chain(n)` has `9,225·n + 786,505` cells. The fixed `add8` table is
  786,464 fixed cells, above `2^19`, so the fixed-table cap `2^(k−4)` forces `k ≥ 24` for every `n`.

  | n | cells | `k_min` |
  |---|---|---|
  | 2^8 | 3.1 M | 24 |
  | 2^10 | 10.2 M | 24 |
  | 2^11 | 19.7 M | 25 |
  | 2^12 | 38.6 M | 26 |

  The largest chain at class 24 is `n = 1,733`. `n = 2^12` does not fit class 24: it would need at
  most about 3,904 cells per compression (about 49 per G-call), while the 24 add lookups of one
  G-call already produce 24 result bytes and 18 carries; class 25 would need at most about 7,999
  (13 % below this layout). So `k_min = 24` (O-3), the recursion tree's `n = 2^10` fits class 24,
  and the `2^12` leaves run at class 26, which `k_range` allows. `L_chain(n)` depends on `n` only
  through three constants (the last-row pins of the G chip, of `S0 … S19` and of `FINAL`, and
  `x₄ = n`); the `L_chain(16)` rendered for the controls is `harness/examples/chain-n16.layout.json`.
- **4-bit limbs were analysed and rejected** (S6-A7). Any arithmetisation whose additions are table
  lookups needs at least 58 cells per G-call (`6 × (4 result bytes + 3 carries) = 42`, plus 16
  operand bytes); with nibbles the floor is `6 × 15 = 90`. At `n = 2^12` class 24 leaves about 49
  per G-call, so no byte-or-narrower table fits it. With 4-bit limbs the add table shrinks to `2^9`
  rows and the fixed-cell floor from `k = 24` to 16, but each half-`G` needs 24 lookups, so 4 rows
  per G-call and about 16.4 k cells per compression against 9,225: `k_min` becomes 23, 25 and 27 for
  `n = 2^8, 2^10, 2^12`. It helps only the smallest leaf, so the 8-bit table and the sizes above
  stay.

Fidelity is **tested, not proved**, and the generator is checked three ways. (1) The generator
asserts every compression against `hashlib.blake2s` and every G-call against RFC 7693 `G`. (2) The
independent Python evaluator `harness/check-chain.py` evaluates the contract's `rel` on whole
chains (`n = 4, 16, 256`) against `hashlib`, with single-cell mutations of the witness (no
sampled change survives) and one layout mutant per load-bearing mechanism, eight in all (`gate`, `addport`,
`nibport`, `gouttag`, `fixed`, `nolast`, `selpin`, `pairport`), each of which must admit a wrong
witness: without `nolast` the `(n−1)`-chain is accepted for `n`; without `selpin` the value `X`
makes a selector port silent (§2.1) and the chain restarts from a fresh `s'`; without `pairport` a
wrong wrap bit aliases into `y`. (3) The kernel checks completeness of one G-call of the generated
G chip and named faults (`Controls/Chain.lean`; `decide +kernel` costs about 40 ms per `K` product,
about 10 s per G row, and a compression is 160 G rows, about 27 min, so one G-call is the
kernel's unit): the one-G-call harness on two calls of the chain, one with the full `add8` table;
single-cell faults, each rejected by the clause it names (gadget `in_A`, the add lookups, `GOUT`);
the wrap attack, rejected only by `PAIR` (`LG0_neg_wrap`, `LG0_wrap_rest`); `G_link`, that the
harness's G chip is `L_chain`'s except for the last-row pin's constant; and the admissibility of
`L_chain(16)` at class 24 and not at 23 (`Lchain_admissible`, `Lchain_not_admissible_23`). The
harness checks its outputs (its public chip decomposes the four output words into bytes checked
on `PAIR`, as `FINAL` does). The kernel does **not** prove that the generated layout computes `G`
(`rel → MixStmt`); soundness is tested by the Python evaluator on whole chains, where the next
decomposition range-checks every output. The security theorems quantify over all layouts, so a
benchmark bug affects only the benchmark's meaning, never soundness. Upgrade path: produce
`L_chain` from leanerVM's Clean Blake2s table through `toLayout` (§9.3), which turns fidelity into
a theorem; what remains is the `BF64 → K` transport and the compression gadget, which the table
does not constrain.

### 7.3 Baseline (phase 1, < 1 h to check)

`P_triv` (`submissions/baseline/`, Stage 7): one prover round sends the tables as oracles; the
verifier queries every leaf and decides `rel` directly. It has no challenge rounds, so the counting
bound `RbrKS` and the error cap are vacuous for every `ε` (`ε` is a function on an empty type, so
`fun _ => 0` and `fun _ => errorCap` are the same protocol); the knowledge content is the `KSF` and
its `next`/`full` laws. The extractor is the 8-instruction image `firstMsgImg`: it outputs round 0
in place, in 8 steps, and the declared split is `![8, 0]` (`trivExtractor_fuel_tight`: 8 steps
suffice and 7 do not). A starved extractor makes `P_triv` insecure (`split0_not_secure`). `Secure`
is the v0.3 toy proof over the new relation (`toy_secure`, `triv_secure`).

The baseline is **listed, unranked**, exactly like Q1's L1 level, and that is a theorem:

> The compiled `P_triv` accepts no tape at any class (`triv_narg`). Its honest tape has
> `5 · 2^(k+11)` bytes on every instance (`triv_uncapped_length`), 160 GiB at `k = 24`. The
> witness of `L_chain(2^10)` alone is 78 MiB, 78× the 1 MiB cap and 625× the 128 KiB cap, so no
> protocol that sends the witness fits, whatever its shapes. It has no `RecursionEntry`
> (`triv_no_entry`: `live` fails).

So it cannot run the badge path at all (O-10), and it is certified at class 24 by the leaf-board
certificate (`Certificate`, `claim.json`: `k = 24`, `blake2s`, arity 2, the image `firstMsgImg`).

There is **no recursion baseline**. The first ranked R entry needs a real SNARK (FRI/STIR/WHIR-
style over `K`, or a binary-field sumcheck design) *and* its verifier as a layout *and* the
circuit theorems. This is the main feasibility risk of v2 and is accepted: the gap is "write a
known verifier as a circuit with a verified gadget library", not "build a zkVM" (the RISC-V
variant's problem). Phase 2 may fund a reference entry; it is not required to open the boards.

### 7.4 What the organiser runs per submission (harness order, carried over: A6-G0)

1. Comparator first in a fresh sandboxed tree (default kernel + nanoda), manifest checked.
2. Gate in a second fresh tree, build bound byte-for-byte to the comparator's (A7-M3), trust by
   `.olean` hash; `--computable` on `VK`, `IDX`, `verify`, `decode`, the extractor image.
3. Badge path: build `lake exe verify`; index; benchmark run (§6.3) under the sandbox with the
   agent's native prover; publish numbers.

---

## 8. Trusted base (what a human must read)

| File | Code lines | Status |
|---|---:|---|
| `Contract.lean` (the reading order: imports) | 11 (actual) | **new** |
| `Contract/Field.lean` | 36 (actual) | unchanged |
| `Contract/Layout.lean` (§2) | 80 (actual) | **new**, replaces `R1CS.lean` (36) |
| `Contract/Shapes.lean` | 50 (actual) | unchanged |
| `Contract/Security.lean` | 55 (actual) | unchanged but for one header sentence (S4-A11, §4) |
| `Contract/Protocol.lean` | 45 (actual) | `Index` → `Layout`; query-program verifier (`QProg`, `chalOf`), shape caps and `k_range` as fields; the extractor is an `ExtractorImage` |
| `Contract/Extractor.lean` (Q1 image, fuel split, `toExtractor`, the contract's serialisation) | 65 (actual) | **new** |
| `Contract/Machine.lean` | 109 (actual) | **trimmed**: plain Rv64 run with fuel; counters, timer, harts, `Acct` deleted |
| `Contract/Recursion.lean` (§5.1–5.3) | 67 (actual) | **new** |
| `Contract/Certificate.lean` (`Submission`/`SubmissionR`, `Declared`/`DeclaredR`, `Certificate`/`CertificateR`) | 25 (actual) | rewritten |
| `Contract/Compile.lean` (§3.2) | 128 (actual) | **new; trusted by review** (deployment security is heuristic anyway; it is in the cone of `aggOK`) |
| `Contract/Hash/Blake2s.lean` | 68 (actual) | **new**; Lean core only, vendored from leanerVM with changes (header of the file); required by `aggOK`, `D`, and `cfg.hash = blake2s256` |
| vendored Rv64 | 205 declarations reached (930 lines), 0 theorems (actual, Stage 4) | unchanged, now serves only the extractor (v0.3 reached 474) |
| **deleted** | | `Cost.lean` 72, `Timer.lean` 22, `Accumulation.lean` 77, `QProg.lean` 21 (the query program now lives in `Protocol.lean`), `Agrees.lean` 18, most of `Machine.lean` |

Every row of the contract is now an implemented file: the counts are `scripts/loc.py` over
`Contract.lean`, `Contract/*.lean` and `Contract/Hash/*.lean`. The contract **excluding
`Compile.lean` and the hash spec** is 543 lines against the budget of 850; the **total trusted
contract** is 739 lines (Stage 8 changed one number in `Layout.lean`, S8-A9, and no line count),
plus the vendored machine's 205 reached declarations, against v0.3's 795 + 930. The trust is
reshaped rather than shrunk: less "cost accounting", more "protocol compilation".

**`Compile.lean` as built.** It is the one trusted file whose correctness is argued by review, not
by a theorem, and it is read against its own header: the byte grammar there is normative (§3.2).
What is kernel-checked about it is completeness and locality (`narg_complete`, `narg_local`, §3.2);
the binding of openings to roots is collision resistance (`opening_binding`, a review probe);
soundness of the compiled argument is the Fiat–Shamir / BCS heuristic in the random-oracle model
(§5.4). An independent encoder written from the header alone (`probes/s3/indep_encoder.py`) matches
the Lean byte for byte at arity 2, 4, 8 and 16, and known-answer controls pin the digest, the
challenge decoding and the openings (`digest_kat`, `decode_kat`, `idx_path_flip`, `oob_rejected`,
`pfs_honest`/`pfs_cheat`, S3-A14). The honest prover is not in the contract (S3-A10).

Everything else is untrusted and kernel-checked: `Library/` (padding, dense equivalence, field
facts, `FiniteField K` instance, compile and recursion facts), `Clean/` (§9), `Bridge/`,
`Controls/`, the benchmark generator, the runner.

---

## 9. Clean as the circuit frontend (untrusted)

Findings from the pinned checkout (`42fe4b26`, 2026-09-29, in leanerVM's `.lake`; builds on
Lean v4.34.1 with Mathlib v4.34.1 there, although its own `lean-toolchain` says v4.33.1). Stage 8
built the frontend on it (§9.3).

### 9.1 What it gives

- `Clean.Air.FlatEnsemble`: table ensembles with channels; `Ensemble.Statement ens x :=
  ∃ w, constraints on every row ∧ channels balance` — the chips + bus relation.
- `FormalCircuit` / `GeneralFormalCircuit`: per-gadget soundness and completeness, subcircuits,
  loops, proof automation (`circuit_norm`, `circuit_proof_start`), `Vm.lean`'s pull/push
  state-chaining theorem.
- Field-generic core: `[FiniteField F]` is Clean's own class, documented to admit `GF(2^n)`;
  only `ZMod p` instances ship.
- Hygiene: the only `sorry`s are in a tactic test file.
- Precedent: leanerVM uses Clean ensembles over a binary field with a BLAKE2s table
  (`LeanerVM/Arithmetization/Tables/Blake2s.lean`) and translates components to computable
  CompPoly polynomial tables (`LeanerVM/Protocol/ToClean/*`, no `sorry`).

### 9.2 The characteristic-2 catch

Clean's `BalancedInteractions` is a sum of multiplicities **in the field** with the side condition
`length < ringChar F`. In characteristic 2 that admits at most one interaction per channel, and
"pushed twice, never pulled" balances as `2 = 0`. Over `K` the side condition is exact: a balanced
list is empty or one silent interaction (`clean_balance_K`; the weaker `clean_balance_vacuous`:
no list of two or more interactions is balanced), so Clean's own `Ensemble.Statement` over `K`
says that no listed channel carries any message, and is unusable (S8-A7). The direction of an
interaction cannot be read from its value either, since `-1 = 1` in `K`. The bus-composition
theorems carry `ringChar F ≠ 2` (11 occurrences in `Air/Balance.lean`, `Air/Vm.lean`). leanerVM
hit this (their finding C2) and defines balance as a `List.Perm` counted in ℕ while using Clean's
tables and constraints unchanged. Our `Layout.rel` does the same with `Multiset`, and
`StatementPerm` (§9.3) is Clean's statement with that balance. The upstream proposal (a multiplicity
in ℤ, or a direction bit) is `docs/upstream/clean-char2-balance.md`; whether to open the PR is
the user's decision (O-5).

### 9.3 Decision (V2-2) and what Stage 8 built

- Clean is **never in the trusted base** (the cone of `Ensemble.Statement` is 39 modules, 15.6k
  lines) and the contract never mentions it.
- `Layout` is **Clean-shaped by construction**: a Clean component is one chip whose assertions
  form one CCS gadget (see "Gadgets" below), one port per channel interaction, a lookup into a
  static table a `.sub` bus against a fixed table, multiset balance in ℕ.
- Agents may bypass Clean and hand-write `C_V` with their own `sound`/`complete` proofs.

**Built (Stage 8; `RecursionFast/Clean/`, the lean_lib `RecursionFastClean`, untrusted and
kernel-checked).** Every constant of a `RecursionFast.Clean*` module depends on at most `propext`,
`Classical.choice` and `Quot.sound` (739 constants audited, `probes/s8/review/P3Axioms.lean`, about
2 min 15 s; it must print `non-standard: 0; sorryAx: 0`).

- **Location and build** (S8-A1, S8-A16). The frontend is `RecursionFastClean`, not a default
  target and not part of `RecursionFastLibrary` or the organiser package (`scripts/org-build.sh`
  drops the `Clean` require and the lib). Clean `42fe4b26` is required by path from the gitignored
  `ext/Clean`. `scripts/setup-clean.sh` fetches it (a clone at the rev, or a local git checkout
  given as argument, for offline use) and verifies it: `.git` present, `HEAD` = `42fe4b26…`, no
  modified or staged tracked file; every fresh clone runs it before any root-level `lake` call.
  The cone is 39 modules and `RecursionFastClean` builds in **3 min 34 s cold** (the Clean cone and
  our six modules) and **3.4 s warm**; `import RecursionFast.Clean` takes 7.2 s and 3.2 GB. Clean
  is built in a separate CI step after the organiser steps, never in the organiser package (S8-A12).
- **`FiniteField K`** (`Clean/FiniteField.lean`): the instance that lets Clean's field-generic core
  run over the contract's `K`.
- **`toLayout tabs ens cm : Layout F`** (`Clean/ToLayout.lean`, generic over `FiniteField F`). The
  verifier is chip 0, the **public chip**, with `max 32 (size PublicIO)` base columns (the public
  input, then columns constrained to `0`) and a gadget `[r = 0] = 1` that gives it exactly one row
  (S8-A2); component `i` is chip `i + 1`. The statement is `pubVec p`, the public input's elements
  then zeros.
- **Gadgets** (S8-A4). An `assert` of degree `d` is *not* one CCS term: each becomes a sum of
  products of linear forms (`ofExpr`), a chip's constraints form one gadget with `Q` terms of
  degree `D` (`gadgetOf`, `holds_gadgetOf`), and every product has at most `max 1 (degreeBound e)`
  factors (`length_ofExpr_le`). So the degree cap `|S_i| ≤ 8` (§2.2) holds when every assertion and
  every auxiliary message expression has `degreeBound ≤ 8`. A message coordinate or selector that
  is not a row variable gets an auxiliary column constrained to equal it.
- **`StatementPerm cm ens x`** (`Clean/Semantics.lean`): Clean's `Ensemble.Statement` with the
  ℕ-multiset balance per bus (`BalancedPerm cm`). It replaces the vacuous balance (§9.2).
- **The bridge `toLayout_rel_iff`, in both directions**, lookups included, with explicit witness
  maps (`toCleanWit`, `toLayoutWit`) and no `sorry`: `x` has a witness in `(toLayout tabs ens
  cm).rel k` iff `StatementPerm cm ens x`. With `size PublicIO ≤ 32` the statement determines the
  public input (`pubVec_injective`) and `statementPerm_iff` says `StatementPerm ens p ↔ ∃ k w, rel
  k (pubVec p) w`. Its hypotheses are `Supported cm ens` (decidable: every component expression
  stays within its width, every interaction is a Clean constructor's output, and the channel map
  merges nothing silently) and `LookupsFaithful tabs ens`. `relK_toLayoutWit` takes a witness of
  `HoldsPerm` into the contract's `relK k`; admissibility is a hypothesis, decided per instance
  (`fibK_admissible`, `fibK_relK_roundtrip`), since no theorem bounds the caps by Clean quantities.
  Negative controls: `fibK_not_faithful_unregistered`, `wide_not_supported`, and `wide_holdsPerm`
  with `wide_rejected` (so `Supported` is necessary).
- **Channels are names** (S8-A5, S8-A13). A channel is identified by its name, as in leanerVM
  (Clean's `RawChannel` carries propositions and has no decidable equality). Clean filters by
  `RawChannel` instead, so the two statements agree only under the hypothesis
  `ChannelsByName ens` (the listed names are `Nodup`, and every interaction on a listed name is on
  a listed `RawChannel`). Under it, `statementPerm_byName_iff_raw` and `toLayout_rel_iff_raw` say
  the bridge is exact against Clean's own channels; the hypothesis is not decidable and is proved
  per ensemble (`fibK_channelsByName`). Without it the two differ in both directions
  (`Names.name_merge_weakens`, `Names.name_merge_strengthens`, `Names.not_channelsByName`).
- **The direction rule** (S8-A3, S8-A14). The direction of an interaction comes from the
  constructor that wrote it (`readMult`), never from a value: `pull`, `pulled(If)` set
  `assumeGuarantees` and write multiplicity `(-1) · e`, so they receive with selector `e`; `push`,
  `pushed(If)` and `emit` clear it and send with the multiplicity as selector. Anything else is
  rejected by `Supported`. A message counts once in ℕ when its selector evaluates to `1` and is
  silent otherwise, as `Table.msgs` reads a selector cell; so a variable multiplicity meant as a
  count (LogUp's `emit m`) is not `m` copies, and a lookup into a registered table with a `sub`
  bus is the way to write one.
- **The channel map** (S8-A11, S8-A15). `ChannelMap := String → Option (ℕ × Bool)`, default
  `byName = fun _ => none`. `none`: the channel is its own bus (the index of its name) and the
  direction comes from `readMult`. `some (b, s)`: the channel is bus `b` and every interaction on it
  sends iff `s` (leanerVM's `st.pull`/`st.push` pairs). Channel buses lie below `cm.nBus` and have
  kind `eq`; lookup bus `j` is `cm.nBus + j`, kind `sub`. `Separate` (part of `Supported`): two
  distinct listed names may share a bus only as a declared pull/push pair. Controls: `pair_rel`,
  `pair_statement`, `pair_byName_neg`.
- **Fixed tables** (S8-A6, S8-A10). A lookup into a table registered in `tabs` (by name and arity;
  `StaticTable`/`Table.fromStatic`) receives on a `sub` bus, and a fixed chip holding the table's
  rows sends them: static lookup tables are **fixed** tables, part of the index. `ProverData`
  tables are to become **witness** chips whose rows the prover chooses and sends on the lookup's
  bus; this is a stated gap, not covered by the bridge: (a) tables whose `Contains` reads the prover
  data (a witness-chip translation, about 250 lines, modelled on the fixed case; in Clean
  `42fe4b26` `ProverData` is witness, so the committed form needs Clean PR #446), and (b)
  `StaticLookupChannel`, which today is translated as an ordinary `eq` channel (a lookup mode in the
  channel map is a semantic choice for `StatementPerm`); until then write static lookups as
  `lookup (Table.fromStatic …)`.
- **The BLAKE2s port** (S8-A8, S8-A9). leanerVM's BLAKE2s table (13 modules, `485d0465`) builds
  unmodified on our pins (1 min 43 s cold) and translates through the generic `toLayout`, with the
  pair map of S8-A11, to **one admissible chip**: 60 cells per row (37 row cells and 23 auxiliary),
  23 constraints, degree 2, and 22 ports, which is why the ports cap rose to `2^5` (§2.2); it is
  admissible at class 24 and at 20. Remaining work for a faithful port: a transport from leanerVM's
  `BF64` to our `K`, and the compression gadget itself, which the table does not constrain (Flock
  proves it in leanerVM) and which belongs with Stage 6a's G chip.
- **Characteristic-2 balance upstream** (O-5): `StatementPerm` is the in-repository solution; the
  proposal for Clean is `docs/upstream/clean-char2-balance.md`.

Risks: Clean API churn (module system, 4.33→4.34 branch) and no written documentation remain. The
build time of the cone against our pins is measured (3 min 34 s cold, 3.4 s warm; O-4). The full
`Clean` library does not build on the pins without 3 small patches, so the library imports only
the cone.

---

## 10. What carries over from `contract-v03/` and what does not

| v0.3 component | v2 |
|---|---|
| `Field.lean`, `Shapes.lean`, `Security.lean` | unchanged (`Security.lean`: one header sentence reworded, S4-A11) |
| `R1CS.lean` (`SpMat`, `Index`, padding) | replaced by `Layout.lean`; R1CS becomes a Library special case (`R1CS_iff_layout`) |
| `Protocol.lean` | `Index sz` → `Layout K`; `verify` must be computable and is a query program (`QProg` moves here from `QProg.lean`); `k_range` and the shape caps are fields; the extractor is an `ExtractorImage` (no `WitMid` field) |
| `Machine.lean`, `Timer.lean`, `Cost.lean`, `Agrees.lean`, `QProg.lean` | counters, timer, harts, cost profiles, score functions, `Agrees`: deleted; plain `run` with fuel kept for the extractor; the query program is kept, inside `Protocol.lean` |
| `Accumulation.lean` (T2) | deleted; recursion is §5 |
| `Certificate.lean` | **rewritten** (25 lines): `Submission`/`SubmissionR`, `Declared`/`DeclaredR` (static counts, the image, the key digests), `Certificate`/`CertificateR` (§3.3) |
| challenge stubs, `render-challenge.py` | kept; new stubs `L.lean.in`, `R.lean.in` |
| `scripts/Gate.lean`, `AxiomAudit.lean`, `harness.sh`, `ci.sh`, manifest, sandbox, comparator, nanoda | kept; `--computable` set updated; badge path = benchmark runner |
| `Library/` (`RbrSound`, `Transfer`, `Field`, `Image`, `Pad`) | `RbrSound` (verbatim) and `Field` kept; `Transfer.lean` **dropped** (it imports the deleted `Accumulation.lean`); `Image`, `Timer`, `Seq`, `V02` deleted; `Pad` rewritten for `Layout`; new: `Layout`, `R1CS`, `Codec`, `Compile`, `Extractor`, `Recursion`, `Blake2s`, `Challenges` |
| `Bridge/ArkLib.lean` | kept |
| `Controls/` | `Toy` migrated to `relK` and to the image extractor (`firstMsgImage`, S4-A13), `Negative` migrated to `relK`; `FieldSpec` and `Hit` carried over verbatim (`hit_secure` is the positive control with challenge rounds); `MachineSmoke`, `Harts`, `Accumulation` deleted; `Layout`, `Recursion`, `Compile`, `Extractor`, `Certificate`, `MagicKey`, `Chain`, `Blake2s` controls added |
| `submissions/baseline-v03` | migrated to `P_triv` over `Layout` (§7.3; `submissions/baseline/`, Stage 7); image, emulator, counters dropped |

---

## 11. Build order for the organiser (P0 first)

Status (2026-10-15): steps 1–6, 8 and 9 are **done** (Stages 1–5, 7, 8); step 7 (the harness) is
**in progress** (Stage 6a done, Stage 6b under way); step 10 is **pending**. A stage's result is
`docs/stages/S<n>-RESULT.md` and its adversarial review `docs/reviews/S<n>-review.md`.

1. **Done (Stage 1).** `Contract/Layout.lean` + `Controls/Layout.lean` + `Library/R1CS_iff_layout`;
   line count 80 (≤ 90).
2. **Done (Stage 1).** `Protocol.lean` over `Layout`; the toy protocol and `Controls/Negative.lean`
   migrated.
3. **Done (Stage 2).** `Contract/Hash/Blake2s.lean` (spec, tested against a reference on known
   vectors, mutants and an 8,432-case `hashlib` differential test).
4. **Done (Stage 3).** `Contract/Compile.lean` (BCS + FS, `Cfg` menu) + controls: honest compiled
   toy accepted; one flipped bit in a path, a root or the statement rejected (challenges are
   derived, not sent, S3-A7); tape cap enforced; and `pfs_honest`/`pfs_cheat`, `decode_kat`,
   `idx_path_flip`, `oob_rejected`, `toy_local` (S3-A14). Every `Protocol k` has `k ≥ 20`
   (`k_range`) and shapes within the caps of §3.1, so a protocol that sends the witness (the toy,
   `P_triv`) sends oracles of `2^(k+8)` to `2^(k+10)` elements, which the kernel cannot evaluate.
   The controls therefore run on `cmpToy : Protocol 20` (not `Secure`, which a compile control does
   not need): a 4-leaf committed oracle, one challenge round (one `E` element, one 2-bit index),
   one plain element and a 2-leaf index oracle; an honest run is about 15 BLAKE2s compressions,
   about 35 s and 5 GB in the kernel. The general facts are theorems (`Library/Compile.lean`,
   §3.2).
5. **Done (Stage 4).** `Contract/Extractor.lean` (Q1) + `Machine.lean` trim; negative controls:
   brute force exceeds `B(k)` (`brute_extractMid_nil`, `chain_search_fails`), and a looping image
   makes the toy insecure (`toy_spin_not_secure`).
6. **Done (Stage 5).** `Contract/Recursion.lean` (`Stmt` digests, `aggOK`, `rootOK`,
   `RecursionEntry`) and `Certificate.lean` + controls, with the same restriction as step 4: on
   `cmpToy`, a hand-made two-leaf node (`aggOK_two_leaves`, `aggOK_node_child`,
   `toy_sat_via_complete`); a layout that ignores `π₂` cannot satisfy `sound` (`cbad_not_sound`);
   `mistag_rejected`, `rootOK_xT`; `toy_no_entry` and `magic_no_entry` for `live` (§5.3).
7. **In progress.** Harness. Stage 6a is done: the leaf layout generator `harness/gen-chain-layout.py`,
   its independent Python evaluator `check-chain.py` and mutant suite, and the one-G-call kernel
   control (§7.2). Stage 6b is under way: gate `--computable` update, challenge stubs, `lake exe
   verify`, the benchmark runner, timing policy and the reference-machine document (the `S6b-A`
   items of the amendments file, applied to this document in a later pass).
8. **Done (Stage 7).** Baseline `P_triv` (`submissions/baseline/`), certified at class 24 and
   listed, unranked (§7.3); `scripts/check.sh` takes 6 min 27 s, the production harness alone
   298 s.
9. **Done (Stage 8).** `RecursionFast/Clean/`: `FiniteField K`, `toLayout` and the bridge
   `toLayout_rel_iff` in both directions, the characteristic-2 balance as `StatementPerm`, and the
   BLAKE2s port analysis (§9.3). The BLAKE2s compression gadget itself and the `BF64 → K` transport
   remain (with `L_chain`, §7.2). Clean's build time is measured (O-4).
10. **Pending.** Adversarial reviews (incentives, definitions, feasibility) before opening the
    boards; the report's §6–§12 are rewritten from this file afterwards.

---

## 12. Open items

| Id | Item | Owner |
|---|---|---|
| O-1 | ~~`WitMid` serialisation and size bound for the extractor image (Q1)~~ **resolved** by Stage 4 (S4-A1): the serialisation is the contract's (`Mid n j`, `extractorTape`, `Layout.words`, `decTables`; §4 item 3), because a submitter-supplied encoder voids the fuel bound; the output cap is `witCap k = 2^(k+12)` words. The witness tables are functions `ℕ → ℕ → K`, but `rel` reads them only inside `rows × cols` (`rel_trim_iff`), so the output decodes to trimmed tables | contract |
| O-2 | ~~Blake2s Lean spec: find/verify an existing one or write it~~ **resolved** by Stage 2: `Contract/Hash/Blake2s.lean` (68 lines, Lean core only; compression function vendored from leanerVM `485d0465`, constants from the RFC text), KATs in `Controls/Blake2s.lean`, mutants and an 8,432-case `hashlib` differential test in `probes/s2/` | contract |
| O-3 | ~~Exact `L_chain` gadget design and measured cell counts per `n`; fix `k_min`~~ **resolved** by Stage 6a (S6-A1, S6-A2): `L_chain(n)` has `9,225·n + 786,505` cells and `k_min = 24` for every `n` (the `add8` table exceeds the fixed-table cap below it); `n = 2^8, 2^10` fit class 24, `2^11` needs 25 and `2^12` needs 26 (§7.2) | harness |
| O-4 | ~~Clean build time against the v4.34.1 pins~~ **resolved** by `probes/clean-build/RESULT.md`: the `Clean.Air.FlatEnsemble` cone (39 modules, 15.6k lines by the probe's count of the imports) builds as a plain `require` on our pins in 2 min 19 s cold, 2.5 s warm; the full `Clean` library needs 3 small patches (≈ 20 lines) and is not needed. `toLayout` and its bridge were built in Stage 8 (§9.3, §11 step 9) | library |
| O-5 | Characteristic-2 balance upstream to Clean. Open; the proposal and the working model are in `docs/upstream/clean-char2-balance.md`, and `StatementPerm` (§9.3) is the in-repository solution. Whether to open the PR is the user's decision | library / external |
| O-6 | Reference machine SKU and toolchain pins; noise measurement to justify the 3 % margin | organiser |
| O-7 | Whether to fund a reference R entry (phase 2) | user |
| O-8 | Report rewrite (§6–§12, Appendix A regenerated from the v2 sources) | report |
| O-9 | The compiled trusted `K.mul` (`Field.lean`, carry-less product over `BitVec 128`) costs ≈ 27 µs (`logs/S2/bench-kmul.lean`), about 4.5 one-block `blake2s256` hashes; the executed verifier is timed (§6), so a fast pure definition of the `K` arithmetic, proved equal to the spec, is needed in the Library before the executed verifier is timed | library |
| O-10 | ~~A protocol that sends the witness has oracles of `2^(k+8)` … `2^(k+10)` elements, so the trivial baseline `P_triv` cannot run the badge path~~ **resolved as a theorem** by Stage 7 (S7-A2): the compiled `P_triv` accepts no tape at any class (`triv_narg`); its honest tape has `5·2^(k+11)` bytes (`triv_uncapped_length`), 160 GiB at `k = 24`; it has no `RecursionEntry` (`triv_no_entry`). It is listed, unranked (§7.3). The kernel-evaluation restriction on compile controls is handled with `cmpToy` (§11 step 4) | harness |
| O-11 | Whether CompPoly's Guruswami–Sudan decoder (the Johnson-regime decoder Q1 relies on) fits `B(k)` at the benchmark's oracle sizes: measure at `k = 20` against `B(20) = 2^56` steps over the whole extraction (S4-A10). `B(k)` admits O(N²) decoding up to about `2^(k+6)` elements and quasi-linear decoding of every oracle (§4 item 3), not Gaussian elimination | user / library |
