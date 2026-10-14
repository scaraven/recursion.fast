<!-- Copied from CambridgePQ/recursion.fast/design/DESIGN-v2-chips-walltime.md (2026-10-14). This copy is the one this repository implements; keep the two in sync. -->
# recursion.fast v2: chips + CCS relation, verifier-as-circuit recursion, wall-time scoring

Status: **design in force for the v2 contract** (user decisions of 2026-10-14; amended 2026-10-14
after Stages 1–2 (see docs/DESIGN-AMENDMENTS.md); this file supersedes `DESIGN.md` wherever the two
disagree). Written for the agent that builds the v2 contract, harness and baseline. Read
`CLAUDE.md` first, then this file, then `contract-v03/RESULT.md` for the harness that carries over.

What changed against the report (v1.0) and `DESIGN.md` v0.3, in one paragraph: the relation is
no longer a flat R1CS but a *structured* constraint system (chips, each a uniform CCS row gadget,
connected by buses); the verifier is no longer a RISC-V image with proved cycle counters but a
Lean IOP verifier whose compiled form is *executed and timed* on one reference machine; recursion
is no longer the typed accumulation track (T2) but *verifier-as-circuit*: the agent supplies the
layout `C_V` of their own compiled verifier and proves it correct, and the headline score is the
measured wall time of one 2→1 recursion step. The RISC-V machine remains only as the extractor's
cost model (Q1). Binary fields, the bounded extractor (Q1) and the universal relation (Q4-A) stay.

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
| ports per chip | `≤ 2^4`; message length `≤ 2^4`; bus `< 2^8` | index reading cost |
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
  `q_cap`, `degree_cap`.
- A protocol whose verifier rejects everything is not `Secure` (`rejectAll_not_secure`, for any
  `Protocol k`; also `rejectAll_not_complete`).

The accept-all / reject-all controls of v0.3 (`Controls/Negative.lean`) carry over, migrated to
`relK` and to the query-program verifier of §3.1.

---

## 3. Protocol model and what the agent submits

### 3.1 Proved object: a holographic public-coin IOP (carried over from v0.3)

`Contract/Shapes.lean` (round shapes, oracles, transcripts) and `Contract/Security.lean`
(`PerfectComplete`, `Extractor`, `KSF`, `KSF.Bad`, `RbrKS`, `SecureWith`, `errorCap = 2^-128`)
are reused **verbatim**. `Contract/Protocol.lean` (Stage 1; 47 code lines) changes `Index sz` to
`Layout K` and `rel sz` to `relK k`, makes the verifier a query program, and states the class
range and the shape caps as fields. The block below is that file abridged, docstrings cut to one
line:

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
  WitMid : Fin (n + 1) → Type
  -- Stage 5: ExtractorImage (DESIGN §4.3, Q1), the bounded extractor run on Rv64.
  extractor : Extractor shape (Layout K × Stmt) (List (Table K)) Unit WitMid
  ε : ChallengeIdx shape → ℝ≥0

namespace Protocol
variable {k : ℕ} (P : Protocol k)

/-- The verifier as a pure verifier on `(L, x)`: run the query program on `IDX L` and the transcript's oracles. -/
def specVerifier : PureVerifier P.shape (Layout K × Stmt) Unit := fun s tr =>
  if (P.verify (P.VK s.1) s.2 (chalOf tr)).eval (⟨P.idxShape, P.IDX s.1⟩ :: tr.oracles) = some true
  then some () else none

/-- Security: perfect completeness for `relK k`, worst-case RBR knowledge soundness at the declared errors, `ε ≤ 2^-128`. -/
def Secure : Prop :=
  SecureWith (relK k) Set.univ P.prover P.specVerifier P.extractor P.ε

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
  `Round.Admissible`, now stated once, as a field. The tape cap and the blow-up cap of v0.3's
  `ShapeAdmissible` belong to `Compile`'s proof format (§3.2). The compile and harness stages
  rely on `2^(k+8)` for the index oracle, which the entries cap of §2.2 makes sufficient at
  every class.
- **The extractor** field is v0.3's `Extractor` for now. Stage 5 (§11 step 5) replaces it by the
  `ExtractorImage` of §4 item 3 (Q1), and `Secure` then uses `P.extractor.toExtractor`.

### 3.2 Executed objects: the compiled argument

The IOP is compiled to a non-interactive argument by the **organiser's** transform
`compile : Cfg → Protocol k → NARG`, a Lean function (`Contract/Compile.lean`, estimate 400
lines; trusted by review, §8):

- BCS: each prover round's oracles are Merkle-committed with `cfg.hash` at arity `cfg.arity`;
  the index oracle `IDX L` is committed once by the indexer and its root is part of `VK`;
  `compile` opens the leaves that the run (of the verifier's query program, §3.1) on the honest
  oracles reads, each with an authentication path in the proof. The result depends only on those
  leaves (`probes/s1/VerifyNotLocal.lean`, `eval_local`).
- Fiat–Shamir: challenges are squeezed from a sponge over `cfg.hash`, domain-separated,
  absorbing `VK ‖ x` first, then each round's root.
- `NARG cfg P : VKBytes → Stmt → Tape → Bool`, deterministic, total; the proof format (tape) is
  defined here and capped at 1 MiB (`tapeCap`, carried over).

`Cfg` is a menu, chosen by the agent: `hash ∈ {blake2s256, sha256, keccak256, blake3}` (only
functions with a Lean spec in the repository; blake2s256 is the required first one), `arity ∈
{2, 4, 8, 16}`, leaf packing (K-elements per leaf, from the declared `OShape.logLeaf`), query
batching on/off. No grinding (the proved `ε` is the IOP's; a nonce buys nothing here).

Naming: the one-argument `blake2s(·)` / `Blake2s(·)` of this design is `RecursionFast.blake2s256`
(`Contract/Hash/Blake2s.lean`; unkeyed, 32-byte digest). `RecursionFast.blake2s` is the general
keyed function `blake2s key nn msg` of RFC 7693 §3.3.

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
| recursion entry (board R): `C_V`, `decode`, `rec_sound`, `rec_complete` (§5.3) | Lean | comparator, gate |
| native prover (+ optional indexer) | source + build script | sandbox build, benchmark runner |
| claim JSON (`k`, `cfg`, cells of `C_V`, declared budgets) | rendered into the challenge stub (v0.3 renderer) | comparator (`submission = rendered`) |

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
3. **Bounded extractor** (Q1, decided 2026-10-13): the extractor is a RISC-V image run on the
   vendored Rv64 with fuel `B(k) = 2^(2k+16)` cycles per call; `extractMid` is *defined* as
   "decode the image's output, default witness on fuel exhaustion", so the `KSF.next`/`full` laws
   force the bound exactly where extraction must succeed. This is what makes "knowledge" mean
   something for the hash-chain leaves (preimage-hard: accept-all would need a provable preimage
   finder within `B(k)`) and what gives recursion its `N · t_E` bound. Open organiser item: the
   serialisation and size bound of the agent-chosen `WitMid m` types (Q1 contract change).
4. **Rejecting runs** (Q3): v2 has no proved cost counters, so the all-runs bound becomes
   *totality*: `verify` is a total Lean function and `compile` is total, so every tape
   terminates; the measured verification time on random tapes is an unranked DoS column (§7.5).
5. **Why the relation is hard where it must be** (Q4): the leaf benchmark is "hash chain with
   private start" (§7.2), preimage-hard, so (2)+(3) are non-vacuous; the recursion relation is
   deterministic given the proofs (§5), so there soundness carries the content and (3) supplies
   the proofs to the next level's argument.

The ArkLib bridge (`Bridge/ArkLib.lean`, one-directional `RbrKS.toArk`) carries over unchanged
and stays untrusted.

---

## 5. Recursion: verifier-as-circuit (replaces track T2)

### 5.1 Statement format (trusted, `Contract/Recursion.lean`)

`Stmt = 8 digests`, `d0..d7`, each 4 K-elements = 32 bytes (cells `0 … 31` of row 0 of the public
chip, §2.1).

| Kind | `d0` | `d1` | `d2` | `d3..d7` |
|---|---|---|---|---|
| leaf (hash chain, §7.2) | `y` (chain end) | `n` (chain length, one element) | 0 | 0 |
| node | `D(VK C_V)` | `D(VK L_chain)` | `blake2s256(x₁ ‖ x₂)` | 0 |

`D` hashes the VK's canonical bytes: `D vk := blake2s256 ((vk.flatMap K.toBytes).map
UInt8.ofBitVec)`. `K.toBytes` gives `BitVec 8`; `UInt8.ofBitVec` is `UInt8`'s constructor, so the
bridge is definitional. A digest becomes a statement slot `d_i` of 4 K-elements, limb `j` being
digest bytes `8j … 8j + 7` read little-endian (Rust `u64::from_le_bytes`, the inverse of
`K.toBytes`). `K.ofBytes` (or `Digest.toK`) is to be added in Stage 5, with a round-trip control
and a KAT on `D`. `blake2s256_length` (`Library/Blake2s.lean`) gives the 32 bytes.

A node's statement commits to both verification keys and to
its two children's statements; the organiser checks at the root that `d0 = D(VK C_V)` and
`d1 = D(VK L_chain)` for the submitted protocol and the benchmark layout, and recomputes the
statement tree over the leaf statements.

### 5.2 The recursion layout and the fixed point

The agent supplies `C_V : Layout K` whose satisfiability means "the compiled verifier accepts two
children". Its witness (`NodeWitness`) holds `x₁, π₁, x₂, π₂`, the child tags `t₁, t₂ ∈ {leaf,
node}`, and the two VKs as cells. The organiser's specification of what `C_V` must enforce:

```lean
/-- What a node proves: both children verify under the right key, keys match the digests,
and the statement is the aggregate. (Trusted, ≈ 40 lines.) -/
def aggOK (cfg : Cfg) (P : Protocol k) (x' : Stmt) (nw : NodeWitness) : Bool :=
  D nw.vkC = x'.d0 && D nw.vkL = x'.d1 && x'.d2 = blake2s256 (nw.x₁ ++ nw.x₂) &&
  child cfg P nw.vkC nw.vkL x' nw.t₁ nw.x₁ nw.π₁ && child cfg P nw.vkC nw.vkL x' nw.t₂ nw.x₂ nw.π₂

def child cfg P vkC vkL x' tag x π : Bool :=
  match tag with
  | .node => x.d0 = x'.d0 && x.d1 = x'.d1 && NARG cfg P vkC x π
  | .leaf => NARG cfg P vkL x π
```

**Fixed point (V2-1).** `C_V.Admissible k ∧ C_V.cells ≤ 2^k` for the *same* `k` at which `P` is
secure (the cell bound is on the honest node witness and is enforced through `complete`, §5.3). The trivial verifier (check every constraint; linear in the index) has no fixed point, so
it is excluded from board R without a proof-size cap. Smaller `C_V` is the whole game.

**VK cycle.** `VK C_V` depends on `C_V`, which verifies proofs under `VK C_V`. The cycle is broken
the standard way: the VK enters `C_V` as *witness cells* checked against the public digest `d0`;
nothing inside `C_V` depends on the value of `VK C_V`.

### 5.3 The agent's circuit-correctness theorems

```lean
structure RecursionEntry (P : Protocol k) (cfg : Cfg) where
  C : Layout K
  fits : C.Admissible k                                   -- the index is within the caps; the cell bound is in `C.rel k`
  decode : List (Table K) → NodeWitness                   -- computable: reads the node witness out of the tables
  sound : ∀ x' w, C.rel k x' w → aggOK cfg P x' (decode w) = true
  complete : ∀ x' nw, aggOK cfg P x' nw = true → ∃ w, C.rel k x' w ∧ decode w = nw
```

`sound` is the load-bearing one: any satisfying assignment of `C_V` contains two accepted child
proofs, and `decode` names them (no existential), so the extractor chain is explicit:
root proof → (KS of `P` on `C_V`) tables → (`decode`) child proofs → … → leaf proofs → (KS of `P`
on `L_chain`) chain preimages. `complete` keeps the honest path inhabited.

`fits` does not bound the cells: cells depend on the witness and are bounded by `rel` (its
size-class clause), not by `Admissible`. The fixed point "`C_V` fits class `k`" (§5.2) is enforced
by `complete`, since an honest node witness must satisfy `C.rel k`, which contains the cell bound.
That clause is vacuous if `aggOK cfg P` is never true, and compile completeness is not a theorem
in the design. The benchmark run is what catches it: a node step must produce a verifying proof
(§6.3).

The theorem is about `aggOK`, which calls `NARG cfg P`, i.e. Merkle verification, Fiat–Shamir
and the IOP verifier's arithmetic all have to be arithmetised and proved. This is the heaviest
obligation in v2 and the reason for the Clean frontend (§9).

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
leaf has no fixed point (proof = witness is 32 MiB at `k = 22`, the cap is 128 KiB). The verifier
is timed on both so that work cannot be shifted into it for free.

### 6.3 Benchmark run (one evaluation)

1. **Instances.** `N = 64` chains, fresh random secret starts `s_i` per evaluation, length
   `n = 2^10` for the recursion tree; the leaf board additionally uses `n ∈ {2^8, 2^12}` (16
   chains each). Secrets are never written to the sandbox the verifier runs in.
2. **Indexing** (untimed, budget 1 h total): Lean-compiled `VK`/`IDX` on `L_chain(n)` and `C_V`.
3. **Leaves**: the native prover on each chain (budget 120 s each, 48 GB). Every proof must
   verify.
4. **Tree**: 32 wrap steps, then 16 + 8 + 4 + 2 + 1 = 31 node steps. Each step is a fresh
   process in a fresh working directory, inputs on local disk (warm page cache allowed), all cores
   available, no network, no GPU, budget 600 s. Every output must verify.
5. **Root**: organiser checks `d0, d1` and the statement tree; `NARG` on the root proof
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
| tape (proof) | ≤ 1 MiB (R, W); ≤ 128 KiB (L) |
| VK | ≤ 2^10 K-elements |
| rounds | ≤ 2^14 |
| message oracle | ≤ 2^(k+10) elements |
| index oracle | ≤ 2^(k+8) elements |
| index challenge | ≤ 64 bits |
| extractor fuel | `2^(2k+16)` cycles per call |
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
| extractor exhausts fuel on honest inputs | caught by the `KSF.next`/`full` laws (Q1) |
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

Generated by `harness/gen-chain-layout.py` as a `Layout` JSON rendered into Lean by the v0.3
renderer: a Blake2s chip (one row per compression round or per G-function, agent-independent),
an 8-bit limb table chip for additions mod 2^32 with a `.sub` bus (XOR is free over `K`), a
chain chip with a `.eq` bus linking compression `i`'s output to `i+1`'s input, and the public
chip holding `(y, n)`. Cell count measured at generation; `n` is chosen so that `n = 2^12` fits
class 24 (defaults `n ∈ {2^8, 2^10, 2^12}`; adjust after measuring).

Fidelity is **tested, not proved**: the generator is differentially tested against a reference
Blake2s on random `(s, n)` (satisfying witness found ⇔ `y = blake2s256^n(s)`), and a mutated
layout (one constraint dropped) must admit a wrong witness. The security theorems quantify over
all layouts, so a benchmark bug affects only the benchmark's meaning, never soundness. Upgrade
path: produce `L_chain` from leanerVM's Clean Blake2s table through `toLayout` (§9.3), which
turns fidelity into a theorem.

### 7.3 Baseline (phase 1, < 1 h to check)

`P_triv`: one prover round sends the tables as oracles; the verifier queries every leaf and
decides `rel` directly; `ε = 0`; the extractor image copies the tables out of the transcript
(well within `B(k)`). `Secure` is the v0.3 toy proof over the new relation (`toy_secure`). It is a
valid **L** entry only if it meets the 128 KiB cap, which it does not at the benchmark sizes, so
the baseline is **listed, unranked**, exactly like Q1's L1 level (it cannot run the badge path at
all, O-10). It has no `RecursionEntry` (no fixed point).

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
| `Contract/Field.lean` | 36 (actual) | unchanged |
| `Contract/Layout.lean` (§2) | 80 (actual) | **new**, replaces `R1CS.lean` (36) |
| `Contract/Shapes.lean` | 50 (actual) | unchanged |
| `Contract/Security.lean` | 55 (actual) | unchanged |
| `Contract/Protocol.lean` | 47 (actual) | `Index` → `Layout`; query-program verifier (`QProg`, `chalOf`), shape caps and `k_range` as fields |
| `Contract/Extractor.lean` (Q1 image, fuel, `toExtractor`, `WitMid` serialisation) | ≈ 60 (est.) | **new** |
| `Contract/Machine.lean` | ≈ 120 (est.) | **trimmed**: plain Rv64 run with fuel; counters, timer, harts, `Acct` deleted |
| `Contract/Recursion.lean` (§5.1–5.3) | ≈ 70 (est.) | **new** |
| `Contract/Certificate.lean` (leaf/recursion entries, rendered claim) | ≈ 60 (est.) | rewritten |
| `Contract/Compile.lean` (§3.2) | ≈ 400 (est.) | **new; trusted by review** (deployment security is heuristic anyway; it is in the cone of `aggOK`) |
| `Contract/Hash/Blake2s.lean` | 68 (actual) | **new**; Lean core only, vendored from leanerVM with changes (header of the file); required by `aggOK`, `D`, and `cfg.hash = blake2s256` |
| vendored Rv64 | ≈ 930 reached (est.) | unchanged, now serves only the extractor |
| **deleted** | | `Cost.lean` 72, `Timer.lean` 22, `Accumulation.lean` 77, `QProg.lean` 21 (the query program now lives in `Protocol.lean`), `Agrees.lean` 18, most of `Machine.lean` |

The "actual" rows are `scripts/loc.py` counts of the implemented files (Stages 1–2); every other
row is an estimate.

Total ≈ 1,000 lines of contract Lean plus the vendored machine, against v0.3's 795 + 930. The
trust is reshaped rather than shrunk: less "cost accounting", more "protocol compilation". The
budget of 850 for `Contract/` excluding `Compile.lean` and the hash spec still holds.

Everything else is untrusted and kernel-checked: `Library/` (padding, dense equivalence, field
facts, `FiniteField K` instance, Clean bridge), `Bridge/`, `Controls/`, the benchmark generator,
the runner.

---

## 9. Clean as the circuit frontend (untrusted)

Findings from the pinned checkout (`42fe4b26`, 2026-09-29, in leanerVM's `.lake`; builds on
Lean v4.34.1 with Mathlib v4.34.1 there, although its own `lean-toolchain` says v4.33.1).

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
"pushed twice, never pulled" balances as `2 = 0`. The bus-composition theorems carry
`ringChar F ≠ 2` (11 occurrences in `Air/Balance.lean`, `Air/Vm.lean`). leanerVM hit this
(their finding C2) and defines balance as a `List.Perm` counted in ℕ while using Clean's tables
and constraints unchanged. Our `Layout.rel` does the same with `Multiset`.

### 9.3 Decision (V2-2)

- Clean is **never in the trusted base** (the cone of `Ensemble.Statement` is 37 modules,
  15.4k lines) and the contract never mentions it.
- `Layout` is **Clean-shaped by construction**: one row-gadget per Clean component (a Clean
  `assert` of degree `d` is one CCS term with `∣S_i∣ = d`), one port per channel interaction
  (`mult = ±1` ⇒ send/receive), `Lookup`/`StaticLookupChannel` ⇒ a `.sub` bus against a fixed
  table, `ProverData` tables ⇒ fixed tables, multiset balance in ℕ.
- Organiser deliverables in `Library/Clean/` (untrusted): (1) `FiniteField K` instance;
  (2) `toLayout : Ensemble K PublicIO → Layout K` with
  `(toLayout ens).rel k x w ↔ ens.StatementPerm x` where `StatementPerm` is `Statement` with the
  ℕ-multiset balance (template: leanerVM's `ToClean`); (3) binary-field hash gadgets, starting
  from leanerVM's BLAKE2s table; (4) the characteristic-safe balance, with an upstream PR to
  Clean (multiplicity in ℤ or a direction bit) as the long-term route.
- Agents may bypass Clean and hand-write `C_V` with their own `sound`/`complete` proofs.

Risks: Clean API churn (module system, 4.33→4.34 branch), no written documentation. The build
time of the cone against our pins is measured (O-4: 2 min 19 s cold, 2.5 s warm; the full `Clean`
library does not build on the pins without 3 small patches, so the library must import only the
cone).

---

## 10. What carries over from `contract-v03/` and what does not

| v0.3 component | v2 |
|---|---|
| `Field.lean`, `Shapes.lean`, `Security.lean` | unchanged |
| `R1CS.lean` (`SpMat`, `Index`, padding) | replaced by `Layout.lean`; R1CS becomes a Library special case (`R1CS_iff_layout`) |
| `Protocol.lean` | `Index sz` → `Layout K`; `verify` must be computable and is a query program (`QProg` moves here from `QProg.lean`); `k_range` and the shape caps are fields |
| `Machine.lean`, `Timer.lean`, `Cost.lean`, `Agrees.lean`, `QProg.lean` | counters, timer, harts, cost profiles, score functions, `Agrees`: deleted; plain `run` with fuel kept for the extractor; the query program is kept, inside `Protocol.lean` |
| `Accumulation.lean` (T2) | deleted; recursion is §5 |
| `Certificate.lean`, challenge stubs, `render-challenge.py` | kept; new stubs `L.lean.in`, `R.lean.in` |
| `scripts/Gate.lean`, `AxiomAudit.lean`, `harness.sh`, `ci.sh`, manifest, sandbox, comparator, nanoda | kept; `--computable` set updated; badge path = benchmark runner |
| `Library/` (`RbrSound`, `Transfer`, `Field`, `Image`, `Pad`) | `RbrSound` (verbatim) and `Field` kept; `Transfer` not carried over (it imports the deleted `Accumulation.lean`); `Image`, `Timer`, `Seq`, `V02` deleted; `Pad` rewritten for `Layout` |
| `Bridge/ArkLib.lean` | kept |
| `Controls/` | `Toy`, `Negative` migrated to `relK`; `FieldSpec` and `Hit` carried over verbatim (`hit_secure` is the positive control with challenge rounds); `MachineSmoke`, `Harts`, `Accumulation` deleted; `Layout`, `Recursion`, `Compile` controls added |
| `submissions/baseline-v03` | migrated to `P_triv` over `Layout` (§7.3); image, emulator, counters dropped |

---

## 11. Build order for the organiser (P0 first)

1. `Contract/Layout.lean` + `Controls/Layout.lean` + `Library/R1CS_iff_layout`; line count ≤ 90.
2. `Protocol.lean` over `Layout`; migrate the toy protocol and `Controls/Negative.lean`.
3. `Contract/Hash/Blake2s.lean` (spec, tested against a reference on known vectors).
4. `Contract/Compile.lean` (BCS + FS, `Cfg` menu) + controls: honest compiled toy accepted; one
   flipped bit in a path, a root, or a challenge rejected; tape cap enforced. Every `Protocol k`
   has `k ≥ 20` (`k_range`) and shapes within the caps of §3.1, so a protocol that sends the
   witness (the toy, `P_triv`) sends oracles of `2^(k+8)` to `2^(k+10)` elements, which the kernel
   cannot evaluate. These controls therefore need either a small, non-`Secure` `Protocol 20` with
   tiny shapes (`Secure` is not required of a compile control) or general theorems.
5. `Contract/Extractor.lean` (Q1) + `Machine.lean` trim; negative control: brute force exceeds
   `B(k)`.
6. `Contract/Recursion.lean` (`Stmt` digests, `aggOK`, `RecursionEntry`) + controls: a hand-made
   two-leaf node with the toy protocol (with the same restriction as step 4: a small non-`Secure`
   `Protocol 20` or general theorems); a layout that ignores `π₂` cannot satisfy `sound`.
7. Harness: gate `--computable` update; `lake exe verify`; benchmark runner (`gen-chain-layout.py`,
   differential test, tree runner, timing policy, reference-machine doc).
8. Baseline `P_triv`, rendered L stub, full CI under 1 h.
9. `Library/Clean/`: `FiniteField K`, `toLayout` + lemma, BLAKE2s gadget port, char-2 balance
   (Clean's build time is measured: O-4).
10. Adversarial reviews (incentives, definitions, feasibility) before opening the boards; the
    report's §6–§12 are rewritten from this file afterwards.

---

## 12. Open items

| Id | Item | Owner |
|---|---|---|
| O-1 | `WitMid` serialisation and size bound for the extractor image (Q1). Note: witness tables are functions `ℕ → ℕ → K`, but `rel` reads them only inside `rows × cols` (`rel_trim_iff`), so the image's `WitMid` serialisation can output trimmed tables; `Library/Codec.lean` (`eWit`, `pWit`, `pWit_eWit`) is a template | contract |
| O-2 | ~~Blake2s Lean spec: find/verify an existing one or write it~~ **resolved** by Stage 2: `Contract/Hash/Blake2s.lean` (68 lines, Lean core only; compression function vendored from leanerVM `485d0465`, constants from the RFC text), KATs in `Controls/Blake2s.lean`, mutants and an 8,432-case `hashlib` differential test in `probes/s2/` | contract |
| O-3 | Exact `L_chain` gadget design and measured cell counts per `n`; fix `k_min` | harness |
| O-4 | ~~Clean build time against the v4.34.1 pins~~ **resolved** by `probes/clean-build/RESULT.md`: the `Clean.Air.FlatEnsemble` cone (39 modules, 15.6k lines by the probe's count of the imports; §9.3 quotes the earlier 37 / 15.4k) builds as a plain `require` on our pins in 2 min 19 s cold, 2.5 s warm; the full `Clean` library needs 3 small patches (≈ 20 lines) and is not needed. The `toLayout` prototype on one component is §11 step 9 | library |
| O-5 | Characteristic-2 balance upstream to Clean | library / external |
| O-6 | Reference machine SKU and toolchain pins; noise measurement to justify the 3 % margin | organiser |
| O-7 | Whether to fund a reference R entry (phase 2) | user |
| O-8 | Report rewrite (§6–§12, Appendix A regenerated from the v2 sources) | report |
| O-9 | The compiled trusted `K.mul` (`Field.lean`, carry-less product over `BitVec 128`) costs ≈ 27 µs (`logs/S2/bench-kmul.lean`), about 4.5 one-block `blake2s256` hashes; the executed verifier is timed (§6), so a fast pure definition of the `K` arithmetic, proved equal to the spec, is needed in the Library before the executed verifier is timed | library |
| O-10 | A protocol that sends the witness has oracles of `2^(k+8)` … `2^(k+10)` elements (`k ≥ 20`, shape caps of §3.1), so the trivial baseline `P_triv` cannot run the badge path (`lake exe verify`, index, benchmark run, §7.4): it is listed, unranked only, as §7.3 says. The same size rules out kernel-evaluated compile controls with the toy (§11 step 4) | harness |
