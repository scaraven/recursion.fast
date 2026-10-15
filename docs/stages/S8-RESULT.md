# S8 RESULT: Clean as the untrusted circuit frontend

Stage 8 implements DESIGN §9.3 and §11 step 9. One agent built it on 2026-10-15; nothing is
committed.

- **New:**
  - `RecursionFast/Clean.lean` and `RecursionFast/Clean/{FiniteField,Gadget,ToLayout,Semantics,Examples}.lean`,
    all untrusted.
  - `scripts/setup-clean.sh`.
  - `probes/s8/` (axiom audit, import-time files, and the BLAKE2s probe `blake2s/`).
- **Appended or changed:**
  - To `lakefile.toml`: one `[[require]]` and one `[[lean_lib]]`, at the end.
  - In `scripts/org-build.sh`: the `drop` set gains `Clean` and `RecursionFastClean`, and the
    `Clean` manifest entry is filtered out (see Setup).
  - To `lake-manifest.json`: one path entry.
  - To `.gitignore`: `ext/` and the two probe copy directories.
  - S8-A1 … S8-A8 to `docs/DESIGN-AMENDMENTS.md`.
- **Not touched:** the Stage 5 files, the roots `Contract.lean`, `Library.lean` and
  `Controls.lean`, `docs/DESIGN.md`, and leanerVM. Under `RecursionFast/Contract/` exactly one
  number changed, in the decision pass: the ports cap in `Contract/Layout.lean` (S8-A9).

## Headline

- **The full equivalence is proved.** Both directions hold, lookups included, with explicit
  witness maps both ways and no `sorry`. The main statement is `toLayout_rel_iff`; with
  `statementPerm_iff`, `StatementPerm ens p ↔ ∃ k w, (toLayout tabs ens).rel k (pubVec p) w`.
  Its hypotheses are:
  - **`Supported cm`** (decidable; as amended by the fix pass): every component expression
    stays within its width, every interaction is a Clean constructor's output (`ShapeOK`), and
    the channel map merges nothing silently (`ChannelMap.Separate`).
  - **`LookupsFaithful`**: every lookup reads a registered table whose rows are exactly what
    Clean's `Contains` accepts.
  - **`size PublicIO ≤ 32`**, needed only for the corollary `statementPerm_iff`.
- **Axioms.** Every Stage 8 declaration depends on at most `propext`, `Classical.choice` and
  `Quot.sound` (25 declarations audited, `logs/S8/36-axioms.log`). Clean adds no axiom to them.
- **Builds.**
  - `RecursionFastClean` builds in **3 min 34 s cold**, which includes the 39-module Clean cone,
    and in **3.9 s warm**.
  - Importing `RecursionFast.Clean` takes 7.2 s and 3.2 GB.
  - The default targets are unchanged.
    - **Evidence.** Dry runs (`lake build --no-build`) before and after the lakefile edit list
      the same out-of-date targets, and only modules from the concurrent Stage 5 edits. They show
      no warnings and no new rebuilds (`logs/S8/00`–`02`, `34`).
    - **Not run.** A full default `lake build`, because the Stage 5 files were being edited
      concurrently.
- **Example.** XOR-Fibonacci with a state channel and a static `bits` lookup over `K` is
  translated and decided by the kernel:
  - **Admissible:** `Admissible 20`.
  - **Positive controls:** `rel` and `relK 20`; then `StatementPerm` through the bridge.
  - **Negative controls:** wrong final state, a mutated cell, a lookup outside the table, and the
    characteristic-2 junk rows. Each is rejected.
- **BLAKE2s.** leanerVM's BLAKE2s table **builds on our pins**: its 13 modules, unmodified, build
  in 1 min 43 s. It **is not admissible**:
  - Its translated chip has **22 ports**, against the cap of 16. Every other cap holds.
  - It uses 60 cells per row: 37 row cells and 23 auxiliary cells.
  - Its pull/push channel pairing needs a channel-to-bus map (S8-A8).

## Setup (local-only, documented)

- **Clean location.** Clean is required by path, as `ext/Clean` (gitignored), not
  `probes/clean-build/Clean-src`.
  - **Why not the probe copy:** a production lakefile should not point into a probe.
  - **The copy:** `ext/Clean` holds the probe's sources (`Clean/`, `Clean.lean`,
    `lakefile.lean`, byte-identical to leanerVM's checkout of `42fe4b26`) and its prebuilt cone.
  - **Fresh clones** run `scripts/setup-clean.sh`. It clones
    `https://github.com/Verified-zkEVM/clean` and checks out `42fe4b26`. With an argument, it
    instead copies a local checkout, which it checks to be at that revision.
  - **Why every clone needs it:** Lake resolves every `require` when it loads the workspace, so
    even the default targets need `ext/Clean` to exist.
  - **Tested:** the copy mode (against the shared tree's Clean checkout) and the idempotent case.
    The network clone was not run here.
- **Manifest.** One entry, the probe's format:
  `{"type": "path", "name": "Clean", "dir": "./ext/Clean", "inherited": false, …}`. Lake did
  not rewrite the manifest. The root pins of mathlib v4.34.1 and CompPoly 572f997 silently
  override Clean's own v4.33.1 requires, as in the probe.
- **Library.** `[[lean_lib]] RecursionFastClean`: roots `RecursionFast.Clean`, globs
  `RecursionFast.Clean.*`. It is not a default target.
  - **Deviation (srcDir):** the brief says `srcDir = "RecursionFast/Clean"`. With roots named
    `RecursionFast.Clean`, that would place the root at
    `RecursionFast/Clean/RecursionFast/Clean.lean`. So the default `srcDir` is kept and the files
    are under `RecursionFast/Clean/`.
  - **`allowNonModules = true`** silences Lake's per-file warning "imports … designed for use
    with the module system". Our files cannot be `module`s, because they import the non-module
    contract and library.
- **First config load.** The first `lake` invocation after the edit takes about 26 s once
  (Lake elaborates Clean's `lakefile.lean`). After that, a dry run of the default targets takes
  3.6 s, as before.
- **Fresh clones.** Without `ext/Clean` the workspace no longer loads at all
  (`error: Clean: package directory not found`, tested on a copy of the lakefile and
  manifest). Every fresh clone and every root-level `lake` call needs `scripts/setup-clean.sh`
  first.
- **The organiser package stays Clean-free.**
  - **The problem.** `scripts/org-build.sh` copies the lakefile and manifest into the organiser
    package (`.lake/org`), on which CI and the harness rely. Without a change, it would have
    carried the `Clean` path require there, where `ext/Clean` does not exist, and broken CI.
  - **The fix.** Its `drop` set now also removes the `Clean` require, the `RecursionFastClean`
    lib and Clean's manifest entry. The comments of both blocks sit inside the blocks, so they
    are dropped too.
  - **Checked.** The script's transformation produced a lakefile with no mention of Clean and
    a manifest without the entry.
  - **Not run.** The full `org-build.sh`, which rebuilds the organiser package.
  - `ci.sh` and `harness.sh` call `lake` only in the organiser package, so they need nothing else.

## Files

Line counts are from `scripts/loc.py` (`logs/S8/33-loc.txt`); build times are from the cold
build (`logs/S8/30-cold-build.log`).

| File | Code | Thm | Build | Contents |
|---|---:|---:|---:|---|
| `Clean.lean` | 5 | 0 | 4.8 s | root |
| `Clean/FiniteField.lean` | 23 | 4 | 3.6 s | `FiniteField K`: `K.instField`; `val a = a.bits.toNat`, `fromNat n = ⟨BitVec.ofNat 64 n⟩`, `size = 2^64`; all six laws proved. `natCast_two`: `Nat.cast` is not the embedding. |
| `Clean/Gadget.lean` | 346 | 27 | 3.7 s | `Lin`, `SOP`, `ofExpr` (Clean `Expression` → sum of products of linear forms), `merge`, `degreeBound`. `eval_ofExpr`, `length_ofExpr_le` (the degree limit), `gadgetOf` (constraints → one CCS gadget), `holds_gadgetOf`. |
| `Clean/ToLayout.lean` | 232 | 17 | 6.8 s | `readMult`, `within`, `trunc`, `FixedTable`, `tabIdx`, `Part` (ports, auxiliary columns, `sops`, `chip`), `pubPart`, `compPart`, **`toLayout`**. Per-chip lemmas: `holds_chip_iff`, `cell_colOf`, `msgs_intPort`, `msgs_lookPort`. |
| `Clean/Semantics.lean` | 826 | 45 | 17 s | `tableMsgs`, `BalancedPerm`, `HoldsPerm`, **`StatementPerm`**, `Supported`, `LookupsFaithful`, `pubVec`. Witness maps `toCleanWit`, `toLayoutWit`. Canonical message forms; **`holdsPerm_toCleanWit`**, **`rel_toLayoutWit`**, **`toLayout_rel_iff`**, `pubVec_injective`, **`statementPerm_iff`**. |
| `Clean/Examples.lean` | 129 | 18 | 41 s | `holdsPerm_of_relK`; the `FibK` ensemble with positive and negative controls (below). |
| **Total** | **1561** | **111** | | |

Clean modules reached:
- **Our imports.** We import exactly `Clean.Air.FlatEnsemble`, `Clean.Circuit.Expression` and
  `Clean.Utils.FiniteField`.
- **Cone size.** The cold build compiled **39 Clean modules**, the same cone the probe measured.
  The slowest were `Circuit.Loops` (22 s), `Air.Balance` (16 s), `Circuit.Operations` (15 s),
  `Circuit.Theorems` (12 s) and `Circuit.Explicit` (10 s).
- **Outside the cone:** no Clean module.
- **Warnings.** Clean emits 2 deprecation warnings (`Gadgets/Conditional.lean`); our modules
  emit none.

## The translation `toLayout tabs ens` (generic over Clean's `FiniteField F`)

| Clean | Layout |
|---|---|
| Verifier (one row = `toElements publicInput`) | Chip 0, the public chip. `base = max 32 (size PublicIO)` columns: the public input, then columns constrained to `0`. The constraint `[r = 0] = 1` forces exactly one row. Statement = cells `0 … 31` of row 0 = `pubVec publicInput`. |
| Component `i` of `ens.tables` (`width = circuit.size`) | Chip `i + 1`: `width` row columns, then auxiliary columns. |
| `assert e` (in `rowOperations.constraints`, subcircuits flattened) | One CCS constraint. The polynomial `e` becomes a sum of products of linear forms (`ofExpr`, then `merge`). All constraints of a chip become one gadget (`gadgetOf`). |
| Variable `v` | Row cell `v` if `v < width`, else `0` (as Clean's `Environment.fromArray` reads a missing cell). |
| Message coordinate or selector that is not a row variable (`n + 1`, `fp * o`, `X · n`, a constant) | An auxiliary column constrained to equal it. There is one column per distinct expression; the expressions are deduplicated. |
| Interaction on channel `ens.channels[b]` (matched by name) | A port on bus `b`, kind `eq`. Message = the coordinates' columns. |
| Constructor `pull`/`pulled(If)` (`assumeGuarantees`, multiplicity `(-1) · e`) / `push`/`pushed(If)`/`emit` (multiplicity `m`); superseded reading, see Fix pass | Receives with selector `e` / sends with selector `m`. Selector column = `e`'s column, so the message counts once when `e = 1` and is otherwise silent (`readMult`). |
| Interaction whose channel's **name** is not listed | Nothing. A channel is its name: an unlisted `RawChannel` sharing a listed name is on that name's bus (S8-M1; exact for Clean's `RawChannel` filter only under `ChannelsByName`). |
| `lookup` into a registered table `tabs[j]` (by name and arity) | A receiving port on bus `nch + j`, kind `sub`. Selector = the constant-`1` auxiliary column; message = the entry's columns. |
| Registered table `tabs[j]` | A chip with that **fixed** table (its rows, then a constant-`1` column) sending every row on bus `nch + j`. |
| `lookup` into an unregistered table | A receiving port on bus `nch + tabs.length`. Nobody sends on it, so the lookup is unsatisfiable. |
| Witness, `data` | Not translated. The relation reads no prover data. |

The CCS encoding (`gadgetOf`): for a chip's constraints `P_r = ∑_k ∏_l L_{r,k,l}`:
- **Sizes.** `D` is the longest product (at least 1) and `Q` the most products in one
  constraint. The gadget has `cons = #constraints`, `q = Q` terms with coefficient `1`, each of
  degree `D`, and `t = Q · D` matrices.
- **Rows.** Row `r` of matrix `k·D + l` is factor `l` of product `k` of `P_r`. A product
  shorter than `D` is padded with the constant cell; an absent product contributes empty rows.
- **Degree limit** (`length_ofExpr_le`). A Clean assertion `e` yields products of at most
  `max 1 (degreeBound e)` factors, `degreeBound` being Clean's syntactic degree (variable 1,
  constant 0, sum max, product sum).
  - A product with a variable-free side scales instead of multiplying.
  - The two sides of any other product are merged first, so `x · (x − 1)` is one product of two
    factors.
  - Admission requires `D ≤ 8`. It suffices that every assertion and every auxiliary
    expression has `degreeBound ≤ 8`: an auxiliary constraint is its cell (one factor) minus its
    expression.
- **The other caps** (`t ≤ 64`, `q ≤ 256`, `cons ≤ 256`, `≤ 16` ports, message `≤ 16`) are
  checked per instance by `decide`; `toLayout` does not guarantee them.

## The theorem statements

```lean
/-- Clean's statement with the field-sum balance replaced by the ℕ-balance. -/
def StatementPerm (ens : Ensemble F PublicIO) (x : PublicIO F) : Prop :=
  ∃ w : EnsembleWitness ens, w.publicInput = x ∧ HoldsPerm w      -- HoldsPerm w := w.Constraints ∧ BalancedPerm w

def BalancedPerm (w : EnsembleWitness ens) : Prop :=
  ∀ ch ∈ ens.channels, (w.allTables.map fun t => tableMsgs t ch.name true).sum =
    (w.allTables.map fun t => tableMsgs t ch.name false).sum   -- Multiset (List F), counted in ℕ

theorem toLayout_rel_iff (hS : Supported ens) (hL : LookupsFaithful tabs ens) (k : ℕ) (x : Fin 32 → F) :
    (∃ w, (toLayout tabs ens).rel k x w) ↔
      ∃ cw : EnsembleWitness ens, x = pubVec cw.publicInput ∧ HoldsPerm cw ∧
        layoutCells (toLayout tabs ens) (toLayoutWit tabs cw) ≤ 2 ^ k

theorem holdsPerm_toCleanWit (hL : LookupsFaithful tabs ens) (h : (toLayout tabs ens).rel k x w) :
    x = pubVec (toCleanWit ens w).publicInput ∧ HoldsPerm (toCleanWit ens w) ∧
      layoutCells (toLayout tabs ens) (toLayoutWit tabs (toCleanWit ens w)) ≤ 2 ^ k

theorem rel_toLayoutWit (hS : Supported ens) (hL : LookupsFaithful tabs ens) (h : HoldsPerm cw)
    (hk : layoutCells (toLayout tabs ens) (toLayoutWit tabs cw) ≤ 2 ^ k) :
    (toLayout tabs ens).rel k (pubVec cw.publicInput) (toLayoutWit tabs cw)

theorem statementPerm_iff (hpub : size PublicIO ≤ 32) (hS : Supported ens) (hL : LookupsFaithful tabs ens)
    (p : PublicIO F) : StatementPerm ens p ↔ ∃ k w, (toLayout tabs ens).rel k (pubVec p) w

theorem holdsPerm_of_relK (hL : LookupsFaithful tabs ens) (h : ((toLayout tabs ens, x), w) ∈ relK k) :
    x = pubVec (toCleanWit ens w).publicInput ∧ HoldsPerm (toCleanWit ens w)       -- over K
```

What each part means:
- **The witness maps.**
  - `toCleanWit` reads the public input from cells `0 … size−1` of row 0 of table 0. Component
    `i`'s rows are table `i + 1` cut to the component's width.
  - `toLayoutWit` writes the Clean rows (a missing cell is `0`), the zero padding, the auxiliary
    columns (evaluated on the row cut to the width) and the registered tables.
- **Where the hypotheses are used.**
  - Soundness (`holdsPerm_toCleanWit`) needs only `LookupsFaithful`.
  - Completeness also needs `Supported`, because a Clean row may be wider than its component
    (`OpsWithin`; the controls `wide_holdsPerm` and `wide_rejected` show the need).
- **Why `hpub` appears only in the corollary.** Both directions hold for any `size PublicIO`.
  Past 32 elements the statement fixes only the first 32, and `pubVec_injective` needs `hpub`.

## Controls (`Clean/Examples.lean`)

The ensemble `FibK.ens`:
- **Source.** It is the structure of Clean's `FibonacciWithChannels` in characteristic 2. Clean's
  own example is over `F p` with `p > 512`: its bytes are `.val < 256` and its addition is mod 256.
- **Step chip.** Pull `(n, x, y)`, look up `x ∈ bits = {0, 1}`, push `(n·X, y, x + y)`.
- **Verifier.** Pull the final state (the public input), push `(1, 0, 1)`.

`toLayout tabs ens` has three chips:

| Chip | Columns | Constraints | Matrices | Terms | Ports |
|---|---:|---:|---:|---:|---:|
| public | 34 | 32 | 1 | 1 | 2 |
| step | 6 | 3 | 1 | 1 | 3 |
| `bits` (fixed) | 2 | 0 | 0 | 0 | 1 |

The honest three-step witness has 56 cells.

| Control | Kind | What it shows |
|---|---|---|
| `fibK_admissible` | + (`decide +kernel`) | `Admissible 20` |
| `fibK_cols`, `fibK_buses` | + | columns `[34, 6, 2]`; buses `< 2` |
| `fibK_supported` | + | the side condition, decided |
| `fibK_faithful` | + (proof) | `Contains` of `Table.fromStatic Bits` is membership in `[[0], [1]]` |
| `fibK_rel` | + (`decide +kernel` via `relBelow`) | the honest witness through `toLayoutWit` satisfies `rel 6` |
| `fibK_relK` | + | it is in the contract's `relK 20`, so the generic instances meet the contract's |
| `fibK_statement` | + (bridge) | `StatementPerm ens final`, Clean's side, from the layout's `rel` |
| `fibK_wrong_final` | − | the verifier pulls `(X³, 1, 1)`, which no step pushed |
| `fibK_mutated` | − | one cell (`y` of step 2) changed |
| `fibK_lookup_neg` | − | `bits` registered as `{0}`; the honest rows look up `1` |
| `fibK_junk_neg` | − | honest rows plus two copies of an unchained row: each of its messages appears twice unmatched; a field sum gives `1 + 1 = 0` (`two_eq_zero`), the ℕ-balance rejects it |
| `clean_balance_vacuous` | finding | Clean's `BalancedInteractions` over `K` rejects every list of `≥ 2` interactions (`ringChar K = 2`), so Clean's own `Statement` over `K` is unusable |
| `neg_one_eq_one`, `readMult_pull`, `readMult_push` | direction | `(-1 : K) = 1`, yet `pull` reads as receive and `push` as send |

**Clean's own `FibonacciWithChannels`, over `F 521`** (probe `probes/s8/blake2s/ProbeFib.lean`,
`logs/S8/14-cleanfib-probe.log`):
- **Genericity.** `toLayout` is generic over `FiniteField F`, so it also translates Clean's
  prime-field example unchanged (`p = 521 > 512`, prime). The example and its dependencies
  build on our pins.
- **The four chips:**

  | Chip | Columns | Constraints | Ports | Degree | Admissible |
  |---|---:|---:|---:|---:|---|
  | public | 34 | 32 | 2 | 1 | yes |
  | `fib8` | 6 | 2 | 3 | 2 | yes |
  | `add8` | 6 | 3 | 2 | 2 | yes |
  | `pushBytes` | 512 | 256 | 256 | 1 | **no** |

  `pushBytes` is 256 variable multiplicities plus 256 constant messages.
- **It shows S8-A3 and the ports cap.** Clean's byte range check is a channel whose 256 messages
  are pushed with variable multiplicities (LogUp style):
  - It exceeds the ports cap.
  - Read through `readMult`, a multiplicity is a selector (once if `1`), not a count. Over our
    relation that check belongs in a registered table with a `sub` bus.

Kernel time: `Examples.lean` builds in 41–50 s, almost all of it the eight `decide +kernel`
calls on the layout.

## The BLAKE2s table (first step of the hash port)

Probe `probes/s8/blake2s/`. To reproduce:
- `setup.sh LEANERVM_CHECKOUT` copies the 13 modules of the table's import closure (2,258
  lines, leanerVM `485d0465`, unmodified) and our 7 modules.
- `lake build` then builds them; `.lake/packages` is the shared tree, and Clean comes from
  `ext/Clean`.

Logs are `logs/S8/10`–`13`.

- **It builds on our pins:** all 13 modules in 1 min 43 s cold, with no edit. leanerVM's
  `K = BF64` has its own `FiniteField` instance, and `toLayout` is generic, so it applies
  directly.
- **The translated chip** (`toLayout [] ens`, the table alone with its six channels):
  - **Width:** 37 row cells plus 23 auxiliary cells, so **60 cells per row**.
  - **Gadget:** 23 constraints, `t = 4`, `q = 2`, degree 2, 78 matrix entries.
  - **Ports:** 22, with messages of at most 10 cells.
  - **Auxiliary columns.** These hold the products `fp · o`, `g · o`, the constants `0` and the
    opcode, the scaled counts `g · count`, and the constant-1 selector.
- **Not admissible.** It breaks one cap: **22 ports > 2^4**. There are 2 state, 2 bytecode and
  9 × 2 memory pull/push ports. Every other cap holds; the public chip is admissible.
- **Not kernel-checked.** The admission check was evaluated with `#eval decide …`, the compiled
  `Decidable` instance. `decide +kernel` gets stuck, apparently on leanerVM definitions that its
  `module` files do not expose to the kernel; this was not investigated further.
- **Further gaps found:**
  1. **Channel pairing.** leanerVM gives a direction to each channel: `st.pull` only receives,
     `st.push` only sends. Our buses are channels by name, so each of the six buses would carry
     one direction only, and an `eq` bus could balance only when empty. A faithful port needs a
     channel-to-bus key, e.g. `"st.pull" ↦ "st"`, `"st.push" ↦ "st"` (S8-A8).
  2. **No compression constraint.** The table has no constraint on its 18 limbs; leanerVM's
     Flock proves the compression elsewhere. The table only binds memory cells, so the
     compression gadget itself does not exist yet.
- **Port estimate:**
  - **(a)** A key map `chanKey : String → String` in `toLayout` and `BalancedPerm`: about 40
    lines plus proof updates (the name-equality steps).
  - **(b)** Either split the row into two or three chips linked by internal channels, or raise
    the ports cap to `2^5`. This is a design decision.
  - **(c)** Moving from `BF64` to our `K`: a `Layout.map` along `K.ringEquivBF64` with a `rel`
    transport lemma, about 150 lines. Alternatively, rewrite the table over `K`.
  - **(d)** The compression itself: the real work. It belongs with Stage 6a's G chip, not
    leanerVM's table.
  - **Total:** (a) to (c) are about one stage-day; (d) is a stage of its own.

## Not covered

1. **Lookups whose table depends on the prover data.** These are `Table`s whose `Contains`
   reads `data name arity`.
   - In Clean `42fe4b26`, `ProverData` is part of the witness, so such a table is
     prover-chosen. §9.3's "ProverData tables ⇒ fixed tables" holds only once Clean commits the
     data (its PR #446).
   - `LookupsFaithful` excludes these tables, because its condition must hold for all data.
   - The faithful translation of today's semantics would be a witness chip sending its rows on
     the `sub` bus, but only when `Contains` is membership in the data. (Question 2.)
2. **Variable multiplicities** (`emit m msg`, LogUp counts). `StatementPerm` counts a message
   once when the selector is `1`; Clean's intent is `m` copies.
   - A Clean ensemble that sends counts through multiplicities is translated faithfully to
     `StatementPerm`, but `StatementPerm` is then not what its author meant.
   - Clean's own `pushBytes` (256 interactions) also exceeds the ports cap. Use a registered
     table instead.
3. **Admissibility is not part of the bridge.** It is a property of each instance, decided by
   `decide`. There is no theorem bounding `t`, `q`, ports or cells in terms of Clean
   quantities.
4. **Direction comes from Clean's constructors (fix pass).** An interaction that assumes
   guarantees with a multiplicity not written `(-1) · e` is no constructor's output; `Supported`
   rejects it. A hand-written `emit (-1 * e)` is a send whose selector is `(-1) · e`, not a
   pull.
5. **Channels are names.** Interactions whose channel's name is listed are on that name's bus,
   even when the `RawChannel` itself is not listed, and same-named listed channels share a bus.
   Clean filters by `RawChannel` instead. The two agree exactly under `ChannelsByName`
   (`statementRaw_iff`); otherwise they differ both ways (`name_merge_weakens`,
   `name_merge_strengthens`).
6. **Clean's `Assumptions`, `Spec` and guarantees are not part of `StatementPerm`**, exactly as
   with Clean's `Statement`. Clean's soundness theorems are not transported, because they
   consume `BalancedChannels`.

## Deviations from DESIGN, with their reasons (amendments S8-A1 … S8-A8)

- **S8-A1 (location).** `RecursionFast/Clean/` and the lib `RecursionFastClean`, not
  `Library/Clean/` (§9.3). Reason: the brief asked for it, and keeping Clean out of
  `RecursionFastLibrary` keeps the default build free of Clean.
- **S8-A2.** The `PublicIO` restriction (32 elements).
- **S8-A3.** Direction from syntax.
- **S8-A4.** The degree limit.
- **S8-A5.** Channels by name.
- **S8-A6.** Lookups: registered static tables only.
- **S8-A7.** Clean's balance is vacuous over `K`.
- **S8-A8.** The BLAKE2s findings.

The full text of each is in `docs/DESIGN-AMENDMENTS.md`.

## Open questions for the orchestrator

(All six were decided; see "Decision pass" below.)

1. **Ports cap.** Raise `ports ≤ 2^4` to `2^5`? leanerVM's BLAKE2s row has 22 interactions,
   each memory read being a pull and a push. Splitting the row instead costs an internal channel
   per split, plus the columns the parts share.
2. **ProverData tables.** Should they be fixed (committed, the design's reading) or witness
   (Clean's current semantics)? This decides the translation of data-dependent lookups.
3. **Channel pairing.** Add a channel-to-bus key map (`chanKey`) to `toLayout`/`StatementPerm`
   now (leanerVM's convention), or require one channel per bus with both directions (Clean's
   convention)?
4. **Upstream (O-5).** Clean's `BalancedInteractions` is vacuous in characteristic 2
   (`clean_balance_vacuous`). `StatementPerm` and `readMult` are a ready proposal: ℕ-multisets
   with a direction bit. Should one be filed with Clean?
5. **CI.** Should `lake build RecursionFastClean` (3.5 min cold, about 4 s warm) join CI?
   - It needs `scripts/setup-clean.sh`, which root-level `lake` needs anyway now.
   - The organiser package is unaffected, after the `org-build.sh` change.
   - Alternative: if a root workspace that loads without Clean matters more, move
     `RecursionFastClean` into a sub-workspace (say `frontend/`) that requires this package by
     path. The brief asked for the root lakefile.

## Decision pass (orchestrator decisions 1–6, applied 2026-10-15)

Amendments S8-A9 … S8-A12 are in `docs/DESIGN-AMENDMENTS.md`. Where this pass and the sections
above disagree, this pass wins. In particular, `Supported` no longer requires distinct names,
and `StatementPerm`, `BalancedPerm` and `HoldsPerm` now take a `ChannelMap`.

1. **Ports cap: `2^4` → `2^5` (S8-A9). Applied.**
   - **Contract.** One number in `Contract/Layout.lean` (`C.ports.length ≤ 2 ^ 5`), plus its
     docstring. Messages stay `≤ 2^4`.
   - **Controls.** `ports_cap` now accepts 32 ports and rejects 33. No other control mentions
     the cap.
   - **Library.** `Library/Codec.lean`'s `eChip_length` constant goes 3000 → 3300 (ports
     ≤ 640 words). `eLayout_length` keeps `2^(k+8)`, so the extractor budgets are unchanged.
   - **Builds.**
     - Default `lake build`: green, 3 min 47 s (`logs/S8/40`).
     - Full organiser build (`scripts/org-build.sh .lake/org-s8-check`): green, **5 min 18 s**,
       9.1 GB peak (`logs/S8/41`).
     - `axiomaudit` there: **PASS** (`logs/S8/44`).
   - **Not mine to change:** `harness/check-chain.py:201` (`len(C.ports) <= 2 ** 4`) belongs to
     Stage 6b.
   - **leanerVM's BLAKE2s table under the new cap.** With the pair map below, `toLayout` gives:
     - **Admissible:** yes, `Admissible 24` (and 20), evaluated by `#eval decide …`. The kernel
       `decide` is still stuck on leanerVM's unexposed `module` definitions.
     - **Cells per row: 60**, of which 37 are row cells and 23 auxiliary.
     - **Gadget and ports:** 23 constraints, `t = 4`, `q = 2`, degree 2, 22 ports on 3 buses,
       both directions on each.
     - **What remains:** only the `BF64 → K` transport and the compression constraints
       (`logs/S8/15-blake2s-probe-cap32.log`).
2. **Tables (S8-A10).**
   - **Covered:** static `lookup`s into registered tables, which become fixed chips. This was
     already proved by the bridge.
   - **Stated gaps:**
     - `ProverData` tables as witness chips (about 250 lines, sketched in S8-A10).
     - `StaticLookupChannel`, which today is an ordinary `eq` channel. Making it a fixed table
       needs a lookup mode in the map and a membership clause in `StatementPerm`. Until then,
       write static lookups as `lookup (Table.fromStatic …)`.
3. **Channel-to-bus map (S8-A11). Applied.**
   - **The map.** `toLayout tabs ens (cm : ChannelMap := ChannelMap.byName)` with
     `ChannelMap := String → Option (ℕ × Bool)`.
     - `none`: the channel's own bus (its name's index), with direction from `readMult`.
     - `some (b, s)`: bus `b`, with every interaction sending iff `s`.
   - **Buses.** Channel buses are `< cm.nBus` (kind `eq`). Lookup bus `j` is `cm.nBus + j`
     (kind `sub`).
   - **Semantics.** `BalancedPerm cm` balances per bus. `balancedPerm_byName_iff` shows that,
     under the default map with distinct names, it is "every channel balances".
   - **Bridge re-proved.** `toLayout_rel_iff`, `statementPerm_iff`, `holdsPerm_toCleanWit`,
     `rel_toLayoutWit` and `holdsPerm_of_relK` now hold for every map. `Supported` dropped its
     `Nodup`; it is only `OpsWithin`.
   - **New controls** (`decide +kernel`): FibK written leanerVM's way (`fib.pull`/`fib.push`):
     - `pair_rel` and `pair_statement`: accepted with the pair map.
     - `pair_byName_neg`: the same witness is rejected by name.
4. **Upstream (O-5).** `docs/upstream/clean-char2-balance.md` covers:
   - **The problem:** `clean_balance_vacuous`, the field-sum cancellation, and direction read
     from the value. The last includes a new finding, proved as
     `clean_push_requirement_vacuous`: `Channel.toRaw` puts **no requirement on a push in
     `K`**, because `1 = -1`.
   - **The proposal:** variant A, a direction bit plus ℕ-multiset balance, mirroring
     `StatementPerm`, recommended over variant B (multiplicity in ℤ).
   - **The affected Clean files**, and a diff sketch.
   - The PR itself is the user's call; O-5 stays open.
5. **CI (S8-A12).**
   - **Command for Stage 6b:** `scripts/setup-clean.sh && lake build RecursionFastClean`.
     - Warm: **3.4 s**.
     - Cold: **4 min 0 s**, which is 39 Clean modules plus 6 of ours, measured at load average
       6–8. `Examples.lean` alone takes 63 s (`logs/S8/45`).
   - **`scripts/org-build.sh` is kept**, and the scratch run above proves it. Its output
     lakefile and manifest mention Clean 0 times.
   - **Pre-existing warning.** That run prints Lake's "manifest out of date: packages directory
     changed". It comes from the script's absolute `packagesDir` in the manifest, not from the
     Clean filter.
   - **The olean manifest must be regenerated** after Stage 6b's changes (and S8-A9's
     `Layout.lean` change).
6. **srcDir.** Confirmed: default `srcDir`, root `RecursionFast/Clean.lean`, files under
   `RecursionFast/Clean/`.

**After the pass:**
- **Files** (`logs/S8/43-loc.txt`): `RecursionFastClean` is 1,690 code lines and 121
  theorems.
  - `Semantics` 881, `ToLayout` 249, `Gadget` 346, `Examples` 186, `FiniteField` 23.
- **Builds.** `lake build RecursionFastClean` is green, also after Stage 6b's concurrent
  `Library/Field.lean` edit (`Fintype` made noncomputable).
- **Default build.** It was green after the cap change. At the end of this pass, a dry run
  marks only modules downstream of the other agents' current edits as out of date
  (`Library/Field.lean`, `scripts/Gate.lean`). None of those modules is touched by Stage 8.
- **Axioms.** `#print axioms` on 31 Stage 8 declarations, including `toLayout_rel_iff`,
  `statementPerm_iff`, `balancedPerm_byName_iff`, the `pair_*` controls and
  `clean_push_requirement_vacuous`: all within `propext`, `Classical.choice` and `Quot.sound`
  (`logs/S8/42-axioms.log`).
- **Hygiene.** `check-hygiene.sh` reports OK.

## Fix pass (after `docs/reviews/S8-review.md`, verdict "pass after one major fix")

I re-read every file after the golf pass (`Clean/*` was 1,521 code lines after golf). Amendments
S8-A13 … S8-A19 are in `docs/DESIGN-AMENDMENTS.md`. Where this pass and the sections above
disagree, this pass wins. The sentences the reviewer listed as stale were corrected in place
(S8-m2).

### S8-M1 (major): fixed

Channels are names, which Clean's `RawChannel` filter is not.
- **Docs.** The `ToLayout` header, the translation table above, "Not covered" 5, S8-A5, and the
  docstrings of `OnBus`, `tableMsgs`, `BalancedPerm` and `StatementPerm` now say: an interaction
  whose channel's **name** is listed is on that name's bus, even when its `RawChannel` is not
  listed.
- **The exact correspondence under a stated hypothesis.**
  - `ChannelsByName ens`: distinct listed names, and every interaction whose channel's name is
    listed is on that very listed `RawChannel`.
  - `StatementRaw`: Clean's `Ensemble.Statement` with `BalancedChannels` replaced by the
    ℕ-balance **per `RawChannel`** (`BalancedRaw`, Clean's own `i.channel = ch` filter).
  - **Proved:**
    - `balancedPerm_byName_iff_raw`: under the hypothesis, `BalancedPerm byName ↔ BalancedRaw`;
    - `statementPerm_byName_iff_raw`;
    - `toLayout_rel_iff_raw` and `statementRaw_iff`: the bridge with the hypothesis, stated
      against Clean's channels.
  - The general `toLayout_rel_iff` and `statementPerm_iff` (any `ChannelMap`, name semantics)
    are kept; they do not need the hypothesis.
  - Positive control: `fibK_channelsByName`, and from it `fibK_statementRaw`.
- **Negative controls** (the reviewer's P2, adopted in `Examples.lean`, namespace `Names`):
  - `name_merge_weakens`: `StatementPerm byName ens 1 ∧ ¬ ens.Statement 1`;
  - `name_merge_strengthens`: `ens2.Statement 1 ∧ ¬ StatementPerm byName ens2 1`;
  - `not_channelsByName`: the hypothesis fails there.

### Minors

- **S8-m1, fixed (statement change to `readMult`, S8-A14).**
  - The direction now comes from Clean's constructors only:
    - `assumeGuarantees` with multiplicity `(-1) · e` receives, selector `e`;
    - otherwise the interaction sends, with the multiplicity as selector.
  - `ShapeOK`, now in `Supported`, rejects every other shape.
  - In `K`, `pushedIf ((1 : K) · en)` stays a send (`readMult_pushIf_one`).
- **S8-m2, fixed.** The stale sentences are corrected: "Contract not touched", "`Supported` =
  distinct names", the unlisted-channel rows, and `pubPart`/header "32 columns".
- **S8-m3, fixed (S8-A16).**
  - `scripts/setup-clean.sh` now requires a git checkout at `42fe4b26` with no modified or
    staged tracked file, and fails otherwise. It creates `ext/Clean` only by clone, from
    upstream or a local checkout.
  - Tested in a scratch tree: a tampered copy, another revision, a copy without `.git` and a
    staged change are each rejected (`logs/S8/50-setup-clean-tests.log`).
  - This repository's `ext/Clean` is now such a clone, with byte-identical sources and the
    prebuilt `.lake` kept. A warm `lake build RecursionFastClean` is 3.4 s.
- **S8-m4.** Stage 6b's and Stage 7's (`harness.sh` default `--org`, baseline `check.sh`):
  nothing for this stage.
- **S8-m5, fixed (S8-A17).**
  - `fibK_not_faithful_unregistered` shows that `LookupsFaithful` can fail.
  - `wide_not_supported` shows that `Supported` can fail.
  - `wide_holdsPerm` with `wide_rejected` shows completeness needs `Supported`: Clean accepts a
    6-cell row, and its translation is rejected (witness-level).
  - `mixedMap_not_separate` shows the map condition can fail.
- **S8-m6, fixed (S8-A17).**
  - `relK_toLayoutWit` (over `K`): `HoldsPerm cm cw` → translation `∈ relK k`, **with
    admissibility as a hypothesis**.
  - Used in `fibK_relK_roundtrip`, with `fibK_admissible` decided by the kernel.
- **S8-m7, fixed.** The upstream note now states the exact vacuity (`clean_balance_K`, adopted
  from P4: a balanced list over `K` is empty or one interaction of multiplicity `0`) and corrects
  the `OrderedChannel.lean` row.
- **S8-m8, fixed (S8-A15).** `ChannelMap.Separate` (decidable, part of `Supported`) makes a
  silent merge an error: two listed names share a bus only as a declared opposite-direction
  pair. Controls: `mixedMap_not_separate`, `pairs_separate`.
- **S8-m9.** Stage 6b's: the exact command is in S8-A18. I ran it here:
  `audited 739 constants … non-standard: 0; sorryAx: 0` (`logs/S8/53-axioms-all-clean.log`,
  2 min 15 s).
- **S8-m10, partly fixed.**
  - **Lines over 100 characters:** 59 → 26. The `ToLayout` header table became a list; the
    remaining 26 are proof-internal or signature lines in `Semantics` and `Gadget`.
  - **The derived `DecidableEq` orphans** are documented in the `ToLayout` header (clash risk).
  - **Statement change, allowed in a fix pass:** `idxOf_eq_iff` drops its unused hypothesis
    `b ∈ names`.

### State after the fix pass

- **Files** (`logs/S8/54-loc-fix.txt`): 1,809 code lines and 150 theorems.
  - `Semantics` 836, `Examples` 402, `Gadget` 301, `ToLayout` 242, `FiniteField` 23.
  - `Examples` grew by the new controls.
- **Builds.**
  - `lake build RecursionFastClean`: green (1 min 52 s after the last edit; 3.4 s warm).
  - Default `lake build`: green and up to date (`logs/S8/51`).
- **BLAKE2s probe**, re-run with the fixed translation: still admissible at class 24, 60 cells
  per row. `ShapeOK` and `Separate` hold under the pair map (compiled `#eval`).
- **Axioms.** `#print axioms` on 29 declarations, including:
  - `toLayout_rel_iff`, `statementPerm_iff`, `toLayout_rel_iff_raw`, `statementRaw_iff`,
    `relK_toLayoutWit`;
  - the new controls.

  All are within `propext`, `Classical.choice` and `Quot.sound`; the two decided `Separate`
  facts use no axiom (`logs/S8/52-axioms-fix.log`).
- **Hygiene.** `check-hygiene.sh` reports OK.
