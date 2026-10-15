# S1 RESULT: the layout relation, `Protocol` over `Layout`, R1CS special case, toy, controls

Stage 1 = DESIGN §11 steps 1 and 2. Implemented by one agent on 2026-10-14. Nothing committed.
This file describes the tree **after the orchestrator's decision pass** (section "Decision pass"
below; design wording changes in `docs/DESIGN-AMENDMENTS.md`, S1-A1 … S1-A6).

## Headline

- **Trusted contract: 253 code lines** (budget ≤ 850). The new files are `Contract/Layout.lean` at **77**
  (target ≤ 90, hard cap 100) and `Contract/Protocol.lean` at **30**. `Field`, `Shapes`, `Security` are unchanged.
- **Proved, with no `sorry`:**
  - `toy_secure k hk : (toy k hk).Secure` at every class `20 ≤ k ≤ 28`. This is the full `SecureWith`:
    perfect completeness, `RbrKS` (vacuous, no challenges), and the cap. Nothing was cut.
  - `R1CS_iff_layout`: R1CS **with public input** `x` is one chip, one row, no ports, with explicit
    witness maps both ways.
  - `Gadget.holds_iff`: the contract's sparse gadget is textbook CCS, i.e. Mathlib's dense
    `*ᵥ` of the denoted matrices, `∑` and multiset `∏`.
  - Two theorems on what `rel` reads (`rel_trim_iff`, `rel_normal_iff`).
  - The index and witness oracle round trips.
  - Every control in §2.3, plus the migrated v0.3 accept-all, reject-all and cap controls, including
    `rejectAll_not_secure` for any `Protocol k`.
- **Build:** a clean `lake build RecursionFastContract RecursionFastLibrary RecursionFastControls` takes
  **33.8 s** wall time with 2.8 GB peak RSS (`logs/S1/build-clean.log`). There are no warnings.
  `lake build RecursionFastBridge gate axiomaudit` builds.
- **Axioms:** `lake exe axiomaudit` reports **PASS** on 648 declarations, all within `propext`,
  `Classical.choice`, `Quot.sound` (`logs/S1/axiomaudit.log`). `scripts/check-hygiene.sh` reports OK.

## First check: what ring structure does the trusted `K` have?

The trusted `K` has only `Zero`, `One`, `Add`, `Sub`, `Neg`, `Mul` (from `Field.lean`) and `DecidableEq`.
It has **no** `AddCommMonoid`, `CommMonoid`, `Semiring` or `Field` instance:
`#synth AddCommMonoid K` fails. `Field K` is a theorem of the untrusted library (v0.3
`Library/Field.lean`, through CompPoly).

The consequence is that Mathlib's `∑`, `∏`, `Multiset.prod` and `Matrix.mulVec` **cannot be stated over
the trusted `K`**. Adding those instances to the trusted base would mean proving the ring axioms for the
reduced carry-less product there, or importing CompPoly. Neither is acceptable.

What I did instead:

- **The relation uses list folds over the carrier's own operations.** `List.sum` needs only `Add`
  and `Zero`; `List.prod` needs only `Mul` and `One`. Concretely:
  - `rowDot M z r = ((M.filter (·.1 = r)).map fun e => e.2.2 * z e.2.1).sum` over the sparse entries;
  - the gadget term is `c i * ((S i).map fun j => rowDot (M j) z r).prod`.
- **The structures are generic over a carrier `F`.** `rel` needs `[Zero F] [One F] [Add F] [Mul F] [DecidableEq F]`.
  `relK` instantiates them at `K`, so the meaning is fixed by `Field.lean`'s operations alone.
- **The library proves the folds equal Mathlib's forms.** Over any commutative semiring,
  `rowDot_eq` gives `rowDot M z r = (spToMat M *ᵥ z) r`, where `spToMat` is the dense denotation with
  duplicates summed (v0.3's `SpMat.toMat`). `Gadget.holds_iff` gives
  `g.holds z ↔ ∀ r, ∑ i, c i * ((S i : Multiset _).map fun j => (spToMat (M j) *ᵥ z) r).prod = 0`.
- **The library's `Field K` operations are the contract's.** I checked this with
  `with_reducible_and_instances rfl`, so the generic library theorems apply to `relK`.

## Files

Code lines are from `scripts/loc.py` (`logs/S1/loc-trusted.log`, `logs/S1/loc-all.log`).

| File | Status | Code | What it is |
|---|---|---:|---|
| `Contract/Layout.lean` | **TRUSTED, new** | 77 | `Gadget` (sparse `M`, list `S`), `Port`, `BusKind`, `Table`, `Chip` (with `fixed`), `Layout`, `Stmt`; `rowDot`, `Gadget.holds`, `view`, `Table.msgs`, `traffic`, `BusKind.Balanced`, `Layout.rel`; `Chip.Admissible`, `Chip.entries`, `Chip.fixedCells`, `Layout.Admissible` and their `Decidable` instances |
| `Contract/Protocol.lean` | **TRUSTED, new** | 30 | `vkCap`, `relK k`, `Protocol k` (with field `k_range : 20 ≤ k ∧ k ≤ 28` and `Layout K` in place of `Index sz`; `extractor` keeps the v0.3 `Extractor` and carries a `-- Stage 5: ExtractorImage` comment), `specVerifier`, `Secure` |
| `Contract.lean` | trusted root | 5 | imports in reading order: Field, Layout, Shapes, Security, Protocol |
| `Library/Field.lean` | untrusted, verbatim from v0.3 | 161 | `Field K`, `Fintype K`, `CharP K 2`, `K_spec`, `E` |
| `Library/Challenges.lean` | untrusted, verbatim from v0.3 | 33 | round types are finite and nonempty (`natCard_pos`) |
| `Library/Layout.lean` | untrusted, new | 179 | `spToMat`, `rowDot_eq`, `Gadget.holds_iff`; `traffic_eq_zero`; `relBelow` with its decidability and `relBelow_iff`; `Table.trim`, `Layout.trim`, `Layout.ReadsOwn`, `Layout.normal`; **`rel_trim_iff`**, **`rel_normal_iff`**; `Admissible.readsOwn` and `Admissible.bus_lt` |
| `Library/R1CS.lean` | untrusted, new | 119 | dense `R1CS A B C x w` (`z = (x, w)`); `sparseOf`, `r1csLayout`; `rel_r1csLayout_iff`, **`R1CS_iff_layout`**, `rel_r1csWit_iff`, `R1CS_of_rel` |
| `Library/Codec.lean` | untrusted, new | 360 | layouts and witnesses as oracles (base-`2^(k+5)` digit addresses): `idxOracle`, `decLayout`, **`decLayout_idxOracle`**; `wOracle`, `decWit`, **`trim_decWit_wOracle`**. This is the encoding the baseline `P_triv` needs. |
| `Controls/Layout.lean` | controls, new | 108 | every control in §2.3 (table below) |
| `Controls/Toy.lean` | controls, migrated | 86 | `toy k hk : Protocol k`, `toyVerify_iff`, **`toy_secure`**, `toy20_secure` |
| `Controls/Negative.lean` | controls, migrated | 98 | accept-all has no KSF, reject-all is neither complete nor secure, the cap control; over `relK` |
| `Library.lean`, `Controls.lean` | roots | 5, 3 | updated |

Per-module build times from the clean log:

| Module | Time |
|---|---:|
| `Library.Codec` | 10 s |
| `Controls.Layout` | 10 s |
| `Library.Field` | 5.4 s |
| `Controls.Negative` | 4.7 s |
| Every other module | ≈ 2–4 s each (mostly import cost) |

The concrete controls are closed by `decide +kernel`, a plain kernel check with no
`ofReduceBool`. The kernel costs about 40 ms per `K` multiplication. Sparse matrices keep the gadget
controls cheap, because only actual entries are multiplied.

## What each main theorem says

- **`Gadget.holds_iff`** (over any commutative semiring): the gadget is
  `∀ r, ∑ i, c i * ∏_{j ∈ S i as a multiset} (spToMat (M j) *ᵥ z) r = 0`.
- **`rel_trim_iff`** (for `L.ReadsOwn`, implied by `Admissible`): `rel` reads a witness only
  through its length, the table heights, and the cells inside `rows × cols`. A port and the
  statement never read an unpaid cell.
- **`rel_normal_iff`**: `rel` does not read fixed-table cells outside the table, nor the kind of
  a bus that no port uses.
- **`R1CS_iff_layout`** (generic `CommRing F`, instantiated at `K` in the controls):
  `(∃ t, (r1csLayout A B C).rel k x t) ↔ ∃ w, R1CS A B C x w`, where `A B C : Matrix (Fin m) (Fin (32+n)) F`
  and `32 + n ≤ 2^k`. The layout is one public chip of `32 + n` columns, one row, no ports. The two
  directions come with explicit maps:
  - forward, `rel_r1csWit_iff`: `w ↦ r1csWit x w`, the one-row table of `(x, w)`;
  - backward, `R1CS_of_rel`: `t ↦ r1csAssign t`, cells `32…` of row 0.

  `rel_r1csLayout_iff` describes the layout's relation in full: one table with a row, every row an R1CS
  solution, the first 32 cells of row 0 equal to `x`, and cells ≤ `2^k`.
- **`decLayout_idxOracle hk h`**: for an admissible `L` and `20 ≤ k ≤ 28`,
  `decLayout k (idxOracle k L) = L.normal (2^8)`, an exact equality. **`trim_decWit_wOracle`**: for
  `L.rel k x w` with `L` admissible, `L.trim (decWit k (wOracle k w) n) = L.trim w`.
- **`toy_secure k hk`**: the full `Protocol.Secure`. Its pieces:
  - `VK L = [1 if admissible else 0]`;
  - `IDX = idxOracle k`;
  - one message, `wOracle k w`;
  - `verify` is the key flag plus `decide (relBelow 2^8 …)` on the decoded layout and tables;
  - the extractor decodes the tables;
  - the KSF is v0.3's.

  The verifier is computable and runs (`logs/S1/toy-eval.lean`, `.log`): it returns true on two satisfying
  instances, and false for a wrong statement, a public table without a row, and an unsatisfiable layout.
  The toy's oracles are `2^(5(k+5))`- and `2^(4(k+5))`-slot functions (simple digit addressing, not
  compact). A real protocol lays the index out in `2^(k+8)` elements (S1-A1).

## Controls (DESIGN §2.3) and what each shows

All of these are over `K`. Unless stated otherwise they are closed by `decide +kernel`, with the bus
clause going through `relBelow_iff`. Public chips have 32 columns wherever a layout is meant to be
admissible.

| Control | Kind | Shows |
|---|---|---|
| `r1cs_pos`, `r1cs_iff` | + | R1CS with public input at `K`, on booleanity `w₀·w₀ = w₀` (`A = B = C` select column 32): `w = (1)` satisfies the layout for every `x`; `R1CS_iff_layout` instantiated at `K`. |
| `twoChip_pos`, `twoChip_admissible` | + | Two chips and one `eq` bus. The receiver holds the sender's messages in another order, plus a row with `sel = 0`. The layout is admissible at class 7. |
| `lookup_pos`, `lookup_admissible` | + | A `sub` lookup into a fixed table `{0,1,2,3}`, with one value looked up twice. |
| `fib_pos`, `fib_admissible` | + | A transition gadget (sparse, 7 entries): XOR-Fibonacci over 4 rows. It reads the next row, and a selector switches it off on the wrapping row. |
| `triv_relK` (in Negative) | + | `relK k` is nonempty for every `k ≥ 5`: a 32-column public chip, one row, no constraint. Proved for general `k`. |
| `r1cs_neg` | − | `w = (x)` with `x² ≠ x` fails the R1CS layout. |
| `twoChip_neg` | − | One changed received message breaks the `eq` bus. |
| `lookup_neg` | − | A value outside the fixed table breaks the `sub` bus. |
| `lookup_neg_fixed` | − | Putting the value into the fixed chip's table instead breaks the fixed-table clause. |
| `fib_neg` | − | One wrong transition breaks the gadget. |
| `stmt_neg` | − | A wrong statement fails. |
| `noPub_neg`, `twoChip_noPub` | − | With no public chip, `¬ rel` holds for every `k`, `x` and `w`. Proved, not decided. |
| `emptyPub_neg` | − | A public table with no row carries no statement, not even the all-zero one. |
| `unsat_neg`, `unsatGadget_not_holds`, `unsat_admissible`, `unsat_admissible_of` | − | A gadget that no row satisfies (`1 = 0`, the empty product). No witness exists for any statement, yet the layout is admissible at every class. |
| `cells_neg` | − | The Fibonacci witness (128 cells) is rejected by `rel` at class 6. |
| `cols_neg`, `pubCols_neg`, `entries_neg`, `fixedCells_neg` | − | `Admissible` rejects each of: cols `> 2^10`, a public chip with fewer than 32 columns, more than `2^(k+4)` matrix entries, fixed cells `> 2^(k-4)`. Each rejection is paired with the same layout at the cap being accepted, so each control isolates one clause. |
| `acceptAll_no_KSF` | − | On a one-message schedule, the accept-all verifier has no KSF for `relK k`, at any `k`. |
| `rejectAll_not_complete`, `rejectAll_not_secure` | − | The reject-all verifier is not complete (`k ≥ 5`), and no `Protocol k` whose `verify` always rejects is `Secure`. |
| `acceptAllChal_rbr_one`, `acceptAllChal_complete`, `acceptAllChal_err_ge_one`, `acceptAllChal_not_secure` | ± | The cap is load-bearing: accept-all is RBR-KS at error 1 and at no error below 1. |
| `toy_secure`, `toy20_secure` | + | `Protocol.Secure` is inhabited at every class in range. |

## `#print axioms` (`logs/S1/axioms.log`)

Each of the following reports `[propext, Classical.choice, Quot.sound]`:

- library theorems: `rowDot_eq`, `Gadget.holds_iff`, `relBelow_iff`, `rel_trim_iff`, `rel_normal_iff`,
  `R1CS_iff_layout`, `rel_r1csWit_iff`, `R1CS_of_rel`, `rel_r1csLayout_iff`, `decLayout_idxOracle`,
  `trim_decWit_wOracle`;
- toy: `toy_secure`, `toy20_secure`, `toyVerify_iff`;
- controls: `r1cs_pos`, `r1cs_neg`, `twoChip_pos`, `twoChip_neg`, `lookup_pos`, `lookup_neg`,
  `lookup_neg_fixed`, `fib_pos`, `fib_neg`, `stmt_neg`, `emptyPub_neg`, `unsat_neg`, `acceptAll_no_KSF`,
  `rejectAll_not_complete`, `rejectAll_not_secure`, `acceptAllChal_not_secure`, `triv_relK`.

The rest use fewer axioms:

- `[propext, Quot.sound]`: `noPub_neg`, `cells_neg`;
- `[propext]`: `twoChip_admissible`, `cols_neg`, `pubCols_neg`, `entries_neg`, `fixedCells_neg`,
  `unsat_admissible_of`.

The repository audit reports PASS.

## Deviations from DESIGN §2.1–§3.1, with reasons

Items 1–8 are from the implementation; items 9–12 are the orchestrator's decisions (S1-A1 … S1-A4).

1. **Folds instead of `∑`, `∏` and `Matrix.mulVec`.** This is forced: the trusted `K` has no ring
   structure (see the first check). The library proves the equivalence with the textbook form
   (`Gadget.holds_iff`).
2. **Carrier `F` instead of `K` as the structure parameter.** The draft's binder `(K : Type)`
   shadows the contract's `K`.
3. **The fixed-table clause compares height and the cells in `rows × cols`.** The draft's
   `ct.1.fixed.all (· = ct.2)` does not typecheck (`Option.all` takes a `Bool` predicate, and `Table` has
   no `DecidableEq`). As full function equality it would also constrain cells that no finite index can
   carry.
4. **`BusKind.Balanced`** replaces the inline `match`. This is cosmetic.
5. **`Admissible` adds three well-formedness conditions:**
   - **`1 ≤ cols`**: otherwise a zero-column chip has unbounded rows at zero cell cost;
   - **ports read their own columns**: otherwise a port reads unpaid, unconstrained cells;
   - **a public chip exists** (folded into S1-A3's "public chip has ≥ 32 columns").

   "Buses ≤ 2^8" is implemented as "every port's bus `< 2^8`". "Cells ≤ 2^k" is a witness quantity and
   stays in `rel`, as in the draft. The earlier `cols ≤ 2^k` was replaced by S1-A1's `cols ≤ 2^10`.
6. **`Stmt := Fin 32 → K`**, so `nx = 32` holds by its type.
7. **The library carries over v0.3 `Library/Field.lean` and `Library/Challenges.lean` verbatim**, for
   `CommRing K` in the R1CS controls and `natCard_pos` in the cap control.
8. **`Controls/Negative.lean` drops v0.3's A2-C1 control**, because `Agrees` and `Image` no longer exist
   (§10).
9. **S1-A1: sparse gadget matrices.** Each matrix is `List (Fin cons × Fin width × F)`, with duplicates
   summed. The caps are `cols ≤ 2^10` per chip and at most `2^(k+4)` entries over the layout
   (`Chip.entries`). Reason: dense matrices made the index `t·cons·2·cols` per chip, unbounded in
   practice.
10. **S1-A2: the class range is a `Protocol` field** (`k_range`), removed from `Layout.Admissible`. Reason:
    the relation is defined at every `k`; only the protocol must be in range, stated once. The Codec
    round trips and the toy now take `20 ≤ k ≤ 28` as an explicit hypothesis, and `rejectAll_not_secure`
    covers any `Protocol k`.
11. **S1-A3: the statement is cells `0…31` of row 0 of the public chip.** `rel` takes `x : Fin 32 → F`
    directly, and the clause is `∃ T ∈ w[L.pub]?, 1 ≤ T.rows ∧ ∀ i : Fin 32, T.cell 0 i = x i`. This is the
    orchestrator's `map … = some x` with the required `1 ≤ T.rows`, folded into one existential that is
    equivalent. `Admissible` requires the public chip to have `32 ≤ cols`. `R1CS_iff_layout` is restated
    with the public input as the first 32 entries of `z`.
12. **S1-A4: `S i : List (Fin t)`** (an ordered multiset) with degree cap `(S i).length ≤ 8`. `holds` uses
    `((S i).map …).prod`, so the `if j ∈ S i … else 1` fold is gone.

## Open questions

- **O-S1-1 … O-S1-4: resolved** by the decision pass (S1-A1 … S1-A4).
- **O-S1-5, O-S1-6: noted for Stage 5 and Stage 6** (`DESIGN-AMENDMENTS.md`, S1-A5 and S1-A6).
- **O-S1-7:** kernel cost is about 40 ms per `K` product; every control is kept tiny. Nanoda replay
  time will be measured in Stage 7.
- **New, minor:** `Layout.Admissible`'s `2^(k-4)` uses ℕ subtraction. It matters only for `k < 4`,
  which no protocol can have (`k_range`); `entries_neg` uses `k = 0` deliberately, to keep its list short.

## Decision pass (orchestrator decisions on O-S1-1 … O-S1-4, applied 2026-10-14)

All four decisions were applied as stated, with one choice of form: the S1-A3 clause was written as the
single existential above, which is equivalent to `map … = some x` plus `1 ≤ T.rows`.

Downstream changes the decisions forced:

- **Codec digit base:** raised to `2^(k+5)`, because entry indices go up to `2^(k+4)`.
- **Codec matrices and term lists:** encoded as length plus entries, and decoded with `filterMap`.
- **Codec round trips:** `decLayout_idxOracle` and `trim_decWit_wOracle` take `hk : 20 ≤ k ∧ k ≤ 28`.
- **Toy:** became `toy k hk`, with `k_range := hk`.
- **`triv_relK`:** now proved for every `k ≥ 5` (one row, 32 columns), not only for `k = 20`.

Nothing else depended on the range that used to be in `Admissible`.

## Commands run

- `lake build` (default targets) and the clean timed build: `logs/S1/build-clean.log` (33.8 s, no warnings).
- `lake build RecursionFastBridge gate axiomaudit`: builds; `lake env .lake/build/bin/axiomaudit`: PASS on 648
  declarations (`logs/S1/axiomaudit.log`).
- `scripts/check-hygiene.sh`: OK (`logs/S1/hygiene.log`).
- `python3 scripts/loc.py …`: `logs/S1/loc-trusted.log`, `logs/S1/loc-all.log`.
- `lake env lean logs/S1/toy-eval.lean`: `logs/S1/toy-eval.log`.

## Fix pass (2026-10-14, after `docs/reviews/S1-review.md` and `docs/reviews/S1-golf.md`)

The review's verdict was ACCEPT WITH FIXES. I applied the orchestrator's decisions on every finding,
on top of the golfed tree; the golf changed proofs only. Nothing is committed. `docs/DESIGN.md` is
untouched, and the new wording is in `docs/DESIGN-AMENDMENTS.md` (S1-A8 … S1-A13). The Stage-2
files (`Contract/Hash/`, `Library/Blake2s.lean`, `Controls/Blake2s.lean`, `probes/s2`) were not
touched.

### Headline after the fix pass

- **Trusted:** 274 code lines (`logs/S1/loc-trusted-fix.log`).
  - `Contract/Layout.lean`: 80.
  - `Contract/Protocol.lean`: 47 (the query program, `chalOf`, `Round.Admissible`, `shape_ok`).
- **Build:** a clean default `lake build` takes **59.5 s** wall time with 2.9 GB peak RSS and no
  warnings (`logs/S1/build-clean-fix.log`).
  - Stage 2's `Controls.Blake2s` takes 47 s of that, running in parallel.
  - Of the S1 modules, the slowest is `Controls.Layout` at 17 s.
- **Other targets:** `lake build RecursionFastBridge gate axiomaudit` is green.
- **Axioms:** the audit reports **PASS** on 843 declarations (`logs/S1/axiomaudit-fix.log`).
  `check-hygiene.sh` reports OK.
- **Proved:** `toy_secure k hk` is still the full `Secure`, now with a query-program verifier and
  within the shape caps.

### Findings and what was done

| Finding | Action |
|---|---|
| **S1-M1** (no query structure) | **Fixed.** `Contract/Protocol.lean` now has v0.3's adaptive `QProg` (`done`, `query j l cont`) and `QProg.eval` over `List Oracle` (an out-of-range oracle or leaf gives `none`, i.e. reject). It also adds `chalOf`, and `verify` becomes `(Fin vkLen → K) → Stmt → Challenges shape → QProg Bool`. `specVerifier s tr` runs the program on `⟨idxShape, IDX s.1⟩ :: tr.oracles` and accepts iff `eval = some true`. The header and docstrings say that the verifier sees oracle contents only through `query`, which is what the compiled argument opens; leaves are the unit of a query. **Toy:** its verifier queries every leaf, which with one-leaf oracles is leaf 0 of the index and of the message, and then decides (`toyDecide`). **`rejectAll_not_secure`:** the hypothesis is now `∀ vk x ρ os, (P.verify vk x ρ).eval os ≠ some true`. |
| **S1-m8** (shape caps lost) | **Fixed** with v0.3's `OShape.Admissible` / `IdxAdmissible` / `Round.Admissible` at class `k`: message oracle `logLeaf ≤ logLen ≤ k + 10`, index challenges `≤ 64` bits (`Round.Admissible k`), index oracle `logLeaf ≤ logLen ≤ k + 8` (field `shape_ok`). v0.3's tape cap and blow-up cap were cost-model and tape rules (`ShapeAdmissible`). They belong to `Compile`'s proof format, so I did not add them (S1-A9). **Consequence:** the old toy's digit-addressed oracles (`2^(5(k+5))`, `2^(4(k+5))`) broke the caps, so `Library/Codec.lean` was rewritten as serialisers and parsers (`eLayout`/`pLayout`, `eWit`/`pWit`) with round trips (`pLayout_eLayout`, `pWit_eWit`) and length bounds (`eLayout_length ≤ 2^(k+8)`, `eWit_length ≤ 2^(k+10)`). The cross-stage notes are S1-A9 and S1-A12. |
| **S1-m7** (selectors, no row position) | **Option (iii).** `view` gains three contract cells after the two rows: `1`, `[r = 0]`, `[r + 1 = rows]`. `Chip.gadget : Gadget F (cols + cols + 3)`. Ports keep the "selector cell = 1" semantics, and (a)–(c) of the finding are documented in the `Port` and `Table.msgs` docstrings. **`fib`** is now pinned: `[r = 0]` fixes row 0 to `(1, 1)` and `(1 + [last])` gates the transition. `fib_garbage` (the reviewer's table) and `fib_boundary_neg` are negative controls. |
| **S1-m5** (no constant wire) | **Fixed: textbook R1CS.** `z = (1, x, w)` (`zVec`), where `1` is the view's constant cell, `x` the public row's cells `0…31` and `w` the remaining columns. `r1csLayout_admissible` (under `m ≤ 2^8`, `32 + n ≤ 2^10`, `3·m·(32+n+1) ≤ 2^(k+4)`) is a theorem. `R1CS_iff_layout` is stated **for `relK k`** at `K`, both directions with explicit maps (`rel_r1csWit_iff`, `R1CS_of_rel`). The generic `rel` version is `R1CS_iff_rel`. New controls: `r1cs_one_pos` and `r1cs_one_neg` (`w₀ · 1 = 1`, expressible only with the constant) and `r1cs_relK`. The `LinearCombination` import is gone. |
| **S1-m1** (wrap untested) | **Fixed:** `incGadget`, `inc`, `wrap_pos`, `wrap_neg` are in `Controls/Layout.lean`. The probe `WrapUntested.lean` still shows that the non-wrapping mutant agrees on `fib` and is separated by the two wrap controls. |
| **S1-m2** (multiplicity, fixed height) | **Fixed:** `eqMult_neg` (a message sent once and received twice) and `fixedHeight_neg` (a fifth row added to the fixed table). |
| **S1-m3** (cap boundaries) | **Fixed:** the reviewer's ten boundary controls are now in `Controls/Layout.lean`, with helpers `pubC`, `portChip`, `gChip`: `chips_cap`, `ports_cap`, `msg_cap`, `bus_cap`, `sel_own`, `cols_pos`, `t_cap`, `cons_cap`, `q_cap`, `degree_cap`. |
| **S1-m4** (no challenge-round control) | **Fixed:** v0.3's `Library/RbrSound.lean`, `Controls/Hit.lean` and `Controls/FieldSpec.lean` are ported verbatim and registered. `hit_secure` (`ε = 2^-192`, rounds with challenges) is the positive control the review asked for, and `Security.lean`'s header reference now resolves. `Library/Transfer.lean` is not ported, because it imports the deleted `Accumulation.lean`. |
| **S1-m6** (docstrings) | **Fixed:** `Layout.pub` (row 0 wording), `Table` ("read by `Layout.rel` when the layout is admissible"), `Layout.rel` (meaning in one sentence, including the view), the module header (R1CS and AIR wording, arbitrary heights), and `Protocol.k_range` ("DESIGN §3.1, S1-A2"). |

No finding is argued against. One deviation from a letter of a decision: the orchestrator asked for
`QProg.query (j l k)`. The continuation is named `cont`, because `k` is the class throughout the
contract.

### Probes (`probes/s1/`, `logs/S1-fix-probes.log`): all compile against the new types

- `QProgFix.lean`: **deleted**. Its content is now the contract.
- `VerifyNotLocal.lean`: **turned positive**. It defines `QProg.reads p os` (the `(oracle, leaf)`
  pairs a run reads) and proves `eval_local`: two oracle lists that show the same leaves (and leaf
  counts) at every read position give the same result.
- `WrapUntested.lean`, `Selectors.lean` and `R1CSConstant.lean` are updated to the wider view, the
  pinned `fib` and the constant wire:
  - `fib_garbage_rejected`;
  - `oneR_not_zero` (the homogeneity is gone);
  - `oneR_affine`;
  - `r1cs_admissible` (now via the library theorem).
- `Axioms.lean` is updated for the renamed and new theorems.
- `AdmissibleCaps.lean`, `BusAndFixed.lean` and `HitV03.lean` compile unchanged.

### Toy executability

The toy's oracles are `2^(k+8)` and `2^(k+10)` elements in one leaf each, so the full query program
is not run at `k = 20`. The decision it runs on the queried leaves, `toyDecide`, is evaluated on the
serialisations (`logs/S1/toy-eval.lean`, `logs/S1/toy-eval.log`):
- **true:** `triv`, `fib`, `lookup`;
- **false:** a wrong statement, a public table with no row, `unsat`, a value outside the lookup table.

### Files after golf and fix pass

Code lines are from `scripts/loc.py` (`logs/S1/loc-all-fix.log`).

| File | Code | Change in this pass |
|---|---:|---|
| `Contract/Layout.lean` (TRUSTED) | 80 | view `+3` contract cells, docstrings (S1-m6, S1-m7) |
| `Contract/Protocol.lean` (TRUSTED) | 47 | `QProg`, `QProg.eval`, `chalOf`, `Round.Admissible`, `shape_ok`, `verify`/`specVerifier` (S1-M1, S1-m8) |
| `Library/Field.lean`, `Library/Challenges.lean` | 161, 33 | unchanged (verbatim v0.3) |
| `Library/RbrSound.lean` | 113 | **new**, verbatim v0.3 (S1-m4) |
| `Library/Layout.lean` | 152 | golfed; `view_castAdd`/`view_trim` for the wider view, `view_one` |
| `Library/R1CS.lean` | 138 | constant wire, `r1csLayout_admissible`, `R1CS_iff_layout` over `relK` |
| `Library/Codec.lean` | 356 | **rewritten**: serialisers, parsers, round trips, length bounds, `toOracle` |
| `Controls/Layout.lean` | 177 | wrap, multiplicity, fixed height, pinned `fib`, R1CS with constant, ten cap boundaries |
| `Controls/Toy.lean` | 81 | query-program verifier, caps |
| `Controls/Negative.lean` | 85 | `rejectAll_not_secure` over query programs |
| `Controls/Hit.lean`, `Controls/FieldSpec.lean` | 101, 13 | **new**, verbatim v0.3 (S1-m4) |

## S9 cleanup (2026-10-15; `docs/reviews/S9-definitions.md`, `S9-feasibility.md`)

**Scope.** Edited: `Field`, `Shapes`, `Security`, `Protocol` (trusted); `Library/Field.lean`;
`Bridge/`; and one harness line forced by a deletion (`Twin.lean`). Not edited: `Compile`,
`Recursion`, `Certificate`, `Extractor`, `Machine`. Nothing is committed. The amendments are
S9-A1 … S9-A5 in `docs/DESIGN-AMENDMENTS.md`.

### S9D-m1: deletions (S9-A1)

- **What was deleted.** Nine trusted declarations that certify nothing:
  - `K`'s `Sub` and `Neg`;
  - `E`'s `Zero`, `One`, `Add`, `Mul` and `E.toBytes`;
  - `FullTranscript.tapeWords`;
  - `Inhabited Oracle`.
- **Where they went.** They moved, unchanged, to `Library/Field.lean`.
- **What stayed.** Everything a challenge type or the extractor tape depends on: `E`, `E.toWords`,
  `Round.Ty`, `Round.tapeWords`.
- **Results.**
  - The contract builds without them.
  - The certificate-cone probe now lists 8 declarations outside the cone (it listed 17). Seven
    of these are in `Compile`/`Recursion`; the eighth is `unpack`, which is load-bearing through
    the rendered image.
  - The contract has 1,071 constants (it had 1,080).

### S9D-m3 and S9D-m6 (S9-A2, S9-A3)

- **S9D-m3.** The `Protocol.lean` header, `Protocol.Secure` (rewrite 2) and `Security.lean`'s
  reading guide now state two things:
  - a secure verifier must reject non-admissible layouts, which it learns only through `VK L`;
  - the error is per challenge round, so the total is at most `2^14 · 2^-128 = 2^-114`.
- **S9D-m6.** The stale v0.3 docstrings in `Shapes` and `Security` are rewritten (rewrites 1
  and 5, plus `RbrKS`'s finiteness reference). The `Protocol.lean` header's computable list now
  matches gate rule 4.

### The ArkLib bridge (S9-A4)

- **Port.** v0.3's `Bridge/ArkLib.lean` is ported verbatim apart from its header and one import,
  and it compiles against v2's `Security`.
- **New.** `Protocol.secure_toArk`: a `Secure` protocol is ArkLib worst-case RBR knowledge sound
  for `relK k`, with the image's extractor.
- **Control.** `Bridge/ArkLibToy.lean`, `toy20_arkRbrKS`.
- **Gaps, stated in the header.** The bridge goes contract → ArkLib only. It forgets `B(k)`. It
  does not restate completeness.

### S9D-m7 (S9-A5)

Analysis only. Copying the live part of `execInstrBr` into `Machine.lean` would cost about 140
trusted lines and remove about 340 lines from the reading. The recommendation is to document
now and split upstream later.

### Numbers

| Measure | Before | After |
|---|---:|---|
| Trusted code, all files | 739 | **724** from this pass; the tree measures **737**, because the `Compile.lean` owner's concurrent edit adds 13 lines (`logs/S1/loc-trusted-s9.log`) |
| Trusted code, excluding `Compile`/`Hash` | 543 | **528** |
| `Field.lean` | 36 | **24** |
| `Shapes.lean` | 50 | **47** |
| `Protocol.lean` | 45 | 45 (comments only) |
| `Security.lean` | 55 | 55 (comments only) |

### Checks

- **Builds.** With this pass's edits the default `lake build`, `lake build RecursionFastBridge
  gate axiomaudit`, and the other targets (`RecursionFastCandidate`, `RecursionFastHarness`,
  `harness-linkcheck`, `RecursionFastSmoke`, `smoke-verify`, `smoke-index`, `RecursionFastClean`)
  were green.
- **Default build now red, but not from this pass.** At hand-off the default build fails in
  `Library/Recursion.lean:219, 230` (`node_length` against `index`). The cause is the
  `Compile.lean`/`Library/Compile.lean` owner's concurrent, uncommitted edit. Every module this
  pass owns, and `RecursionFastBridge`, still build green.
- **Axioms.** The audit reports PASS (`logs/S1/axiomaudit-s9.log`).
- **Hygiene.** OK.
- **Organiser build.** `scripts/org-build.sh .lake/org` succeeds, and the regenerated import
  allowlist and frontend list are identical to the committed ones.
- **Manifest.** `olean-manifest.py check` fails on exactly the 4 changed contract `.olean`s. It
  must be regenerated once all S9 trusted edits are in. I did not regenerate it, because other
  owners are editing trusted files and `olean-manifest.py` concurrently.
