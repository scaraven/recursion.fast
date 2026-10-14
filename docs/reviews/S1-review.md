# S1 review: the layout relation, `Protocol` over `Layout`, library bridges, controls

**Verdict: ACCEPT WITH FIXES.** The trusted relation holds up: I found no unpaid cell, no
vacuous clause and no admissible layout that a universal verifier could not commit to. One major
finding is a design gap in the trusted `Protocol` type, and it needs an orchestrator decision
before commit (S1-M1). There are eight minor findings: control gaps, docstrings, one library
special case, and cross-stage tracking.

Date: 2026-10-14. Scope:
- the trusted files `Contract/Layout.lean` and `Contract/Protocol.lean`;
- the uses Stage 1 makes of `Field`, `Shapes` and `Security`;
- `Library/{Layout,R1CS,Codec}.lean`;
- `Controls/{Layout,Toy,Negative}.lean`;
- `docs/stages/S1-RESULT.md` and `docs/DESIGN-AMENDMENTS.md`.

I read these against DESIGN §1–§4, §8, §10–§12 and against v0.3. Every claim below is backed by a
probe under `probes/s1/`. Run a probe from the repository root with
`lake env lean probes/s1/<Name>.lean`; each takes 5–13 s, all pass, and the log is
`logs/S1-review-probes.log`. The golf agent was editing `Library/Layout.lean` while I worked. I
re-read its statements after its 18:12 edit, and none of them changed. `lake build --no-build`
reported the default targets up to date at the time of the review.

The passes are kept separate:
- **Pass A (specification: non-vacuity, tightness)** produced S1-m1 to S1-m5.
- **Pass B (fidelity to DESIGN)** produced S1-M1, S1-m5, S1-m7 and S1-m8.
- **Pass C (hygiene and trust)** produced S1-m4 and S1-m6.

## Findings

### S1-M1 (major; design decision before commit): `Protocol.verify` has no query structure, so the designed compiler has nothing to open

- **Declarations.**
  - `Protocol.verify` and `Protocol.specVerifier` (`Contract/Protocol.lean`).
  - DESIGN §3.1 gives the signature. DESIGN §3.2 says "a QUERY becomes a leaf plus an
    authentication path".
  - `Shapes.lean` provides `Oracle.leaf`, `Oracle.get` ("QUERY never reads there") and
    `FullTranscript.oracles`. These were built for a query interface that v2 no longer has.
- **Problem.**
  - `verify` receives the index oracle and every prover oracle as total functions. No field says
    which positions it reads.
  - v0.3 had two mechanisms that did say so: the RISC-V `QUERY` together with `Agrees`, and
    `QProg`. Both are deleted (DESIGN §10).
  - So a BCS `compile` (Stage 4) cannot be both succinct and sound. It has two options:
    - Put whole oracles on the tape. No entry then meets the 1 MiB or 128 KiB cap, and the boards
      cannot open.
    - Run `verify` on oracles whose unopened positions hold a default value. This is unsound for
      any verifier that reads those positions, because a cheating prover simply opens nothing.
- **Evidence.** `probes/s1/VerifyNotLocal.lean`:
  - `readsAll` is a computable value of the `verify` field's type (one 16-element message,
    `vkLen = 0`).
  - `readsAll_depends` shows its verdict changes when any single position changes, so no proper
    subset of positions determines it.
  - Compile does not exist yet, so I cannot prove "compile is impossible" as a theorem. The gap
    is in the type.
- **Why decide now.** Every later trusted object (`NARG`, `aggOK`, the certificate) and every
  submission is written against this structure. Today its only users are the toy and
  `rejectAll_not_secure`.
- **Fix.** Typechecked against this contract in `probes/s1/QProgFix.lean`. In
  `Contract/Protocol.lean` (about 15 trusted lines):
  1. Reinstate v0.3's adaptive `QProg` with `QProg.eval`, dropping `cost`.
  2. Add `chalOf (tr : FullTranscript sh) : Challenges sh := fun c => tr c.1`.
  3. Change the field to `verify : (Fin vkLen → K) → Stmt → Challenges shape → QProg Bool`.
  4. Define `specVerifier s tr` as
     `if (P.verify (P.VK s.1) s.2 (chalOf tr)).eval (⟨P.idxShape, P.IDX s.1⟩ :: tr.oracles) = some true then some () else none`.
     Oracle 0 is the index, and oracles 1, 2, … are the messages, numbered as
     `FullTranscript.oracles` already does.

  `Secure` is unchanged. Adapt the following:
  - **The toy:** re-express `toyVerify` as a `QProg` that queries the leaves it decodes. With
    `logLeaf = logLen` that is one query per oracle; `logs/S1/toy-eval` stays executable only
    with `logLeaf = 0` and adaptive decoding.
  - **`rejectAll_not_secure`:** the hypothesis becomes `∀ vk x ρ os, (P.verify vk x ρ).eval os ≠ some true`.
  - **The Protocol.lean header:** it should say "reads the oracles only through queries".
  - **DESIGN §3.1:** update the signature, and record the change as amendment S1-A8.

  The alternative keeps a black-box `verify` and adds a `reads` field with a locality theorem. It
  is heavier for submitters and is not adaptive. If the decision is deferred to Stage 4, record
  now in `DESIGN-AMENDMENTS.md` that this trusted field's type will change.

### S1-m1: the cyclic wrap of `view` is pinned by no control

- **Declarations.** `view`; the controls `fib_pos`, `fib_neg`, `stmt_neg`.
- **Problem.** `fib` switches its gadget off on the last row. So the only transition-gadget
  controls never evaluate `(r + 1) % T.rows`, and a mutant `view` that reads row `rows` instead of
  row 0 gets the same verdict on every control.
- **Probe.** `WrapUntested.lean`:
  - `relNW` is `relBelow` with the non-wrapping `viewNW`. It reproduces `fib_pos`, `fib_neg` and
    `stmt_neg` (`*_NW`).
  - The proposed `wrap_pos` and `wrap_neg` use `inc`: `a' = a + 1` on every row, with no
    selector.
  - They separate `rel` from the mutant in both directions (`wrap_pos_NW`, `wrap_neg_NW`).
- **Fix.** Copy `incGadget`, `inc`, `wrap_pos` and `wrap_neg` into `Controls/Layout.lean`, and add
  them to its header and to the RESULT's control table.

### S1-m2: `eq`-bus multiplicity and the fixed-table height are pinned by no control

- **Declarations.**
  - `BusKind.Balanced` (case `.eq`), against the control `twoChip_neg`.
  - The fixed-table clause of `Layout.rel` (`ct.2.rows = t.rows`), against the control
    `lookup_neg_fixed`.
- **Problem.** §2.1 rests on two points: buses are counted "in ℕ", and a fixed chip carries exactly
  the fixed table. The existing controls do not test either.
  - `twoChip_neg` changes a value, so the supports differ. It does not distinguish multiset
    equality from set equality.
  - `lookup_neg_fixed` changes a cell. A mutation that weakens the height equation to `≥` would
    survive it.
- **Probe.** `BusAndFixed.lean`:
  - `eqMult_neg`: the sender sends `5` once and the receiver takes it twice, and `rel` rejects.
  - `eqMult_sameSupport`: yet the supports are equal.
  - `twoChip_controls_support`: on both existing controls, the support test agrees with `rel`.
  - `fixedHeight_neg`: the fixed chip's table is `range4` plus a fifth row `(9, 1)`, and `rel`
    rejects.
  - `fixedHeight_only`: the cells agree on `range4`'s rows and the lookup of `9` is served, so the
    height is the only difference.
- **Fix.** Add `eqMult_neg` and `fixedHeight_neg`, with their witnesses, to `Controls/Layout.lean`.

### S1-m3: nine `Admissible` clauses have no boundary control

- **Declarations.** `Chip.Admissible`, `Layout.Admissible`; the RESULT's sentence "each rejection
  is paired with the same layout at the cap".
- **Problem.** The pairing exists only for `cols ≤ 2^10`, `32 ≤` public columns, entries and fixed
  cells. These clauses have none: chips, ports, message length, bus, own columns (`sel` and
  `msg`), `1 ≤ cols`, `t`, `cons`, `q`, degree.
  - Relaxing `t`, `cons`, `q`, the degree or the chip count (for example degree `≤ 9`) fails no
    control.
  - It fails no library proof either: those bounds are used only to place values below
    `R k = 2^(k+5)` in `Codec`.
- **Probe.** `AdmissibleCaps.lean` gives ten boundary theorems (`chips_cap`, `ports_cap`,
  `msg_cap`, `bus_cap`, `sel_own`, `cols_pos`, `t_cap`, `cons_cap`, `q_cap`, `degree_cap`). Each
  accepts at the cap and rejects one above it. All hold, which also confirms that the implemented
  caps match §2.2, S1-A1 and S1-A7 exactly.
- **Fix.** Move these theorems into `Controls/Layout.lean`, together with their helpers `pubC`,
  `portChip` and `gChip`.

### S1-m4: `Secure` has no positive control with a challenge round, and a trusted header cites a missing file

- **Declarations.**
  - `SecureWith` and `RbrKS` (`Security.lean`, verbatim).
  - `toy_secure`: it has no challenges, so for it `RbrKS` and the cap are vacuous.
  - DESIGN §10, which keeps `Controls/{Hit,FieldSpec}` and `Library/{RbrSound,Transfer}`.
- **Problem.**
  - Nothing in the repository shows that `#bad ≤ ε · #challenges` with `ε ≤ 2^-128` can be met
    once a challenge round exists. If it could not, every interactive protocol would be excluded.
  - v0.3 proved exactly this (`hit_secure`), but Stage 1 did not migrate it, and no stage in §11
    is assigned to do so.
  - The trusted `Security.lean` header points to `Library/RbrSound.lean`, which is absent here.
- **Probe.** `HitV03.lean` concatenates v0.3's `Library/RbrSound.lean` and `Controls/Hit.lean`,
  unchanged except for the imports. It compiles against this contract. `hit_secure` (`ε = 2^-192`)
  uses only the standard axioms.
- **Fix.**
  - Migrate `Library/RbrSound.lean`, `Controls/Hit.lean` and `Controls/FieldSpec.lean` verbatim,
    and register them in `Library.lean` and `Controls.lean`.
  - Decide what to do with `Library/Transfer.lean`, which imports the deleted `Accumulation.lean`.

### S1-m5: the library's R1CS has no constant wire, and the special case is shown for `rel`, not `relK`

- **Declarations.**
  - `R1CS`, `R1CS_iff_layout`, `rel_r1csWit_iff`, `R1CS_of_rel` and the module header of
    `Library/R1CS.lean`.
  - DESIGN §2.3: "iff the v0.3 R1CS does".
  - Amendment S1-A3.
- **Problem.**
  - `R1CS` uses `z = (x, w)`. v0.3 (`Contract/R1CS.lean`, `zVec`) and the textbook use
    `z = (1, x, w)`.
  - Without the constant wire, every instance is satisfied by `x = 0, w = 0`, and no instance
    expresses `w₀ = 1`. `R1CS_iff_layout` therefore covers homogeneous R1CS only.
  - S1-A3 wrote `z = (x, w)` without saying that this drops the constant wire. That changes what
    the §2.3 control means, so I am flagging it for the orchestrator.
  - Separately, the header states that `r1csLayout` is admissible, but no theorem proves it.
- **Probe.** `R1CSConstant.lean`:
  - `R1CS_zero` and `R1CS_not_affine` show the homogeneity.
  - `affine_pos` and `affine_neg` show the layout relation expresses `w₀ = 1` itself, with a
    constant term `S i = []`.
  - `r1cs_admissible` and `r1cs_relK` show the control instance is in `relK 6`.
- **Fix.** Choose one of:
  - **(a) Faithful to §2.3.** Use `z = (1, x, w)`, with matrices of width `1 + 32 + n`, plus:
    - an extra column `one` at index `32 + n` in the chip;
    - a gadget with `cons = m + 1` and `t = 4`;
    - matrices `A'', B'', C''`, which are `A, B, C` with column 0 remapped to `one`;
    - a matrix `D` with an entry `(r, one, 1)` for every `r ≤ m`;
    - terms `[0, 1]·1`, `[2]·(−1)`, `[3]·1`, `[]·(−1)`.

    Row `m` then forces `one = 1`, and each row `r < m` reduces to `(A z)_r (B z)_r = (C z)_r`.
  - **(b) Homogeneity intended.** Rename to `R1CSHom` and write "homogeneous (no constant wire)" in
    the docstrings, the RESULT, S1-A3 and §2.3.

  Either way, add
  `r1csLayout_admissible (hm : m ≤ 2^8) (hn : 32 + n ≤ 2^10) (he : 3 * (m * (32 + n)) ≤ 2^(k+4)) : (r1csLayout A B C).Admissible k`,
  adjusted to the chosen shape, and add `r1cs_admissible` to the controls.

### S1-m6: trusted docstrings that misstate or understate the meaning

- **`Layout.pub`.** The docstring says "The public chip (its column 0 is the statement)." That has
  been wrong since S1-A3. Replace it with: "The public chip: cells `0 … 31` of row 0 of its table
  are the statement."
- **`Table`.** The docstring says "Only cells with `r < rows` and `c` below its chip's `cols` are
  ever read." That holds only for admissible layouts. Replace "are ever read" with "are read by
  `Layout.rel` when the layout is admissible (`Library/Layout.lean`, `rel_trim_iff`)".
- **`Layout.rel`.** The docstring states no meaning; the clauses live in `--` comments and the
  module header, and hover and doc-gen do not show those. Replace it with:

  > **The relation**: `w` has one table per chip; a chip with a fixed table has that table's height
  > and cells; every row of every table satisfies its chip's gadget on (the row, the next row,
  > cyclically); on every `eq` bus the messages sent and received are equal as multisets, and on
  > every `sub` bus every received message is sent; the public table has a row whose cells
  > `0 … 31` are `x`; and the tables have at most `2^k` cells.
- **Module header of `Layout.lean`.**
  - "R1CS with public input `x` is the special case …" should follow the decision in S1-m5.
  - "an AIR is 'one chip, many rows, no ports'" should become: "an AIR whose boundary constraints
    are on row 0 (through the statement) and whose transition holds on every row, the wrap
    included, is 'one chip, many rows, no ports'".
- **`Protocol.k_range`.** "(DESIGN §2.2)" should be "(DESIGN §3.1, S1-A2)".

### S1-m7 (design question, not a defect): selectors are witness cells compared to `1`, and a gadget has no row position

- **Declarations.** `Table.msgs` (`T.cell r p.sel = 1`), `view`, and the `fib` docstring; DESIGN
  §2.1 as written.
- **Problem.**
  - **(a) The selector test is "equals 1".** A row with a non-boolean selector is silent
    (`sel_nonbool_silent`). A protocol that weights messages by the selector (in a grand product
    or LogUp) is therefore incomplete for `relK`. Every protocol must commit to `[sel = 1]` with an
    inverse witness, for each port and each row.
  - **(b) There is no first-row, last-row or transition selector.** A transition is either
    enforced across the wrap or gated by a witness selector, which the prover may clear on any row
    other than row 0.
    - `fib_garbage`: `fib` accepts a table that is not Fibonacci after row 1.
    - The `fib` docstring says "a selector switching it off on the last row". In fact the prover
      can switch it off on any row except row 0.
    - Pinning a selector costs a fixed chip plus an `eq` bus.
  - **(c) Heights are arbitrary.** The wrap is cyclic modulo a height that need not be a power of
    two, which protocols built on power-of-two domains must emulate.
- **Options for the orchestrator.**
  - **(i)** Keep the semantics, document (a)–(c) in §2.1, and fix the `fib` docstring.
  - **(ii)** Require every selector cell to be `0` or `1` in `rel`. Protocols can then use `sel`
    as a factor after a degree-2 booleanity check.
  - **(iii)** Extend the view with three contract cells: `1`, `[r = 0]` and `[r + 1 = rows]`
    (width `cols + cols + 3`). A verifier can compute these from the height in `O(log rows)`. This
    also gives R1CS its constant wire (S1-m5).

### S1-m8 (tracking): Stage-1 consequences for later stages that are not recorded

- **(a) v0.3's shape admission was lost.**
  - The rules lived in the deleted `Cost.lean`: `Round.Admissible` (index challenges `≤ 64`
    bits), oracle length `≤ 2^(k+10)`, and index oracle `≤ 2^(k+8)`.
  - Stage 1's `Protocol` has none of them, and §6.5 lists none.
  - Yet the trusted `Shapes.lean` still says "`b ≤ 64` is an admission rule", and
    `Round.tapeWords` truncates wider indices (`setWidth 64`).
  - S1-A1 says that Stages 4 and 7 rely on `2^(k+8)`.
  - Record the owner (a `Protocol` field or `Compile`) in `DESIGN-AMENDMENTS.md` and §6.5.
- **(b) S1-A2 limits which protocols exist.** Every `Protocol k` has `k ≥ 20`, and a protocol's
  shapes are fixed. So any protocol that sends the witness (the toy, the baseline `P_triv`) sends
  oracles of at least `2^k ≥ 2^20` elements; the toy's are `2^(4(k+5))` and `2^(5(k+5))`, each in
  a single leaf.
  - The controls Stage 4 plans ("honest compiled toy accepted") and Stage 6 plans ("two-leaf node
    with the toy protocol") cannot be evaluated in the kernel with the toy.
  - They need a small, non-Secure `Protocol 20` with tiny shapes, or general theorems. Say so in
    §11.
- **(c) S1-A6 can be vacuous.** It enforces the cell bound of `C_V` through `complete`. That
  clause is vacuous if `aggOK cfg P` is never true, and nothing proves that it is ever true:
  compile completeness is not a theorem in the design. The benchmark run is what catches this.
  Record it in §5.3.

## What I checked and found clean

| Area (pass) | Check | Result |
|---|---|---|
| Unpaid cells (A) | Every read of `rel` checked by hand (`view`, `Table.msgs`, statement, fixed clause), and `rel_trim_iff` | For admissible layouts every read is inside `rows × cols`; `ReadsOwn` is implied by `Admissible` |
| `rows = 0`, `rows = 1` (A) | The gadget and ports are vacuous at 0 rows. The public table needs a row (`emptyPub_neg`). At 1 row the view is (row, row), the cyclic convention | Clean |
| Zero-column chip (A) | Excluded by `1 ≤ cols` (`AdmissibleCaps.cols_pos`); otherwise it would allow unbounded rows at zero cost | Clean |
| Ports (A) | `sel` equal to a message column, or a port listed twice (multiplicity `m` = `m` ports, §2.1); a public chip with ports; a fixed public chip | Intended |
| Degenerate buses (A) | A `sub` bus with no sender forces no receipts. An `eq` bus with no ports balances. The kinds of unused buses are not read (`rel_normal_iff`) | Intended |
| Duplicate sparse entries (A) | They add up, and cancel in characteristic 2 (`Selectors.dup_cancels`). This is the denoted-matrix semantics (`spToMat`); duplicates cost entries | Intended, not exploitable |
| Cells cap against the 2·cols view (A) | The next row belongs to the same table, so it is already paid for | Clean |
| `1` in `sel = 1` (A) | It is `Field.lean`'s `⟨⟨1⟩⟩`. The library's `Field K` is `Function.Injective.field` over the contract's own operations, and `r1cs_iff` typechecks at `K` | Clean |
| §2.2 against `Admissible` (B) | Every row is present or relocated: class → `Protocol.k_range` (S1-A2), cells → `rel`, `nx` → `Stmt`. The extra clauses (`1 ≤ cols`, own columns, public chip `≥ 32`, `cols ≤ 2^10`, entries `≤ 2^(k+4)`) are all in S1-A1, S1-A3 and S1-A7. Every value is confirmed at its boundary by `AdmissibleCaps.lean`. Decidable instances are present | Clean |
| Committable index (A) | An admissible layout at class `k` has at most `3·2^(k+4)` (entries) + `2^(k-4)` (fixed) + `2^19` (S) + `2^16` (`c`) + `20·2^12` (ports) + `2^11` (headers and bus kinds) `< 2^(k+6)` K-elements for `k ≥ 20`, under S1-A1's `2^(k+8)`. `decLayout_idxOracle` recovers it exactly, up to `normal`, from a fixed-shape oracle | Clean |
| `relK` non-vacuity (A) | `triv_relK` (+) and `unsat_not_relK` (−), both on admissible layouts, for every `k ≥ 5` | Clean |
| `Secure` on degenerate protocols (A) | `n = 0`: the verifier must decide satisfiability and `extractOut` must output a witness (the extractor is unbounded until Stage 5, by plan). `vkLen = 0` or a one-element `IDX`: layouts the verifier cannot tell apart force rejection by the union bound over at most `2^14` rounds. Not vacuous | Clean |
| `toy_secure` (A) | Real `relK` and the real `errorCap` (vacuous without challenges, see S1-m4). After the message the KSF says "decoded tables ∈ relK", which is not trivial; `empty`, `next` and `full` hold; the extractor decodes the tables | Clean |
| Negative controls (A) | `rejectAll_not_secure` fails by completeness on `triv`, with `k ≥ 5` from `k_range`. `acceptAll_no_KSF` uses the admissible `unsat`. `acceptAllChal_*` shows the cap is load-bearing | Clean |
| Library bridges (A) | `rowDot_eq` and `Gadget.holds_iff` are iffs over any commutative semiring. `rel_trim_iff` and `rel_normal_iff` are iffs whose hypotheses `Admissible` implies. `R1CS_iff_layout` has both directions with explicit maps, and `hk` is necessary. The codec round trips are exact equalities | Clean (R1CS semantics: S1-m5) |
| Trusted imports (C) | `Layout`: `Contract.Field`, `Mathlib.Data.Fintype.Basic`, `Mathlib.Data.Multiset.AddSub`. `Protocol`: `Security`, `Layout`. The contract never imports the library | Clean |
| Verbatim files (B) | `Field`, `Shapes` and `Security` are byte-identical to v0.3, and so are `Library/Field` and `Library/Challenges` (`diff`) | Clean (stale cross-references: S1-m4, S1-m8a) |
| Axioms (C) | `Axioms.lean`: all 49 Stage-1 theorems and controls use only `{propext, Classical.choice, Quot.sound}`, matching the RESULT | Clean |
| Forbidden constructs (C) | `check-hygiene.sh` reports OK. `grep` finds no `decide +native`, `ofReduceBool`, `unsafe`, `opaque` or `set_option` in `RecursionFast/`. Note: the lint's regex does not match `decide +native`, but the axiom audit would (`Lean.ofReduceBool`) | Clean |
| Line budget (C) | `loc.py`: 253 trusted code lines (`Layout` 77, `Protocol` 30), matching the RESULT | Clean |
| Docstrings and placement (C) | Every trusted definition has a docstring (wording: S1-m6). Nothing in `Contract/` belongs in `Library/`: the two `Decidable` instances are used by computable `VK`s | Clean |
| Amendments that change meaning (B) | S1-A1: the index can be 16× the witness, so holography is required (consistent with §3.2). S1-A3: the public chip needs `≥ 32` columns (harmless), and the R1CS constant wire is dropped (S1-m5). S1-A2 and S1-A6 have consequences in S1-m8. S1-A4, S1-A5 and S1-A7 are wording | Flagged where meaning changes |

## Probe files (`probes/s1/`)

| File | Shows |
|---|---|
| `Axioms.lean` | `#print axioms` for every Stage-1 theorem and control; signatures of `rel`, `holds`, `msgs`, `Admissible`, `relK` |
| `VerifyNotLocal.lean` | S1-M1: a legal `verify` whose verdict depends on every oracle position |
| `QProgFix.lean` | S1-M1 fix: `QProg`, `QProg.eval`, `chalOf`, a `Protocol'` with a query-program verifier, its `specVerifier` and `Secure` (typechecks) |
| `WrapUntested.lean` | S1-m1: the non-wrapping mutant passes every gadget control; `wrap_pos`/`wrap_neg` separate it |
| `BusAndFixed.lean` | S1-m2: `eqMult_neg` (with the support mutant) and `fixedHeight_neg` (only the height differs) |
| `AdmissibleCaps.lean` | S1-m3: ten boundary controls, all hold |
| `HitV03.lean` | S1-m4: v0.3 `RbrSound` + `Hit` compile unchanged; `hit_secure` meets the cap with challenge rounds |
| `R1CSConstant.lean` | S1-m5: `R1CS_zero`, `R1CS_not_affine`, `affine_pos`/`neg`, `r1cs_admissible`, `r1cs_relK` |
| `Selectors.lean` | S1-m7: `sel_nonbool_silent`, `fib_garbage`; `dup_cancels` (intended semantics) |
