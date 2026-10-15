# S8 review: the Clean bridge (`FiniteField K`, `toLayout`, `StatementPerm`, `toLayout_rel_iff`) and the ports cap

Adversarial review of Stage 8 as it stands after the orchestrator's decision pass (S8-A9 … S8-A12),
2026-10-15.

**Read.** `CLAUDE.md`; DESIGN §2 and §9; the amendments S1-A1, S1-A3, S1-A4, S1-A11 and
S8-A1 … S8-A12; `docs/stages/S8-RESULT.md`; `docs/upstream/clean-char2-balance.md`.

**Code read in full.**
- `RecursionFast/Clean/{FiniteField,Gadget,ToLayout,Semantics,Examples}.lean` and
  `RecursionFast/Clean.lean`.
- The trusted diff `git diff HEAD -- RecursionFast/Contract/Layout.lean`, `Controls/Layout.lean`,
  `Library/Codec.lean`, `scripts/setup-clean.sh`, `scripts/org-build.sh`, and the `lakefile.toml`
  and `lake-manifest.json` edits.
- Clean `42fe4b26` (`ext/Clean`): `Air/{FlatEnsemble,FlatComponent,Balance}.lean`,
  `Circuit/{Expression,Operations,Channel,Lookup,Basic}.lean` (the channel operations) and
  `Utils/FiniteField.lean`.

**Edits.** Nothing under `RecursionFast/`, `scripts/`, `harness/` or the lakefile was edited.
- **Probes:** `probes/s8/review/P1…P5`.
- **Logs:** `logs/S8-review/` (gitignored).
- **Scratch trees:** `/tmp/s8rev/`.
- **Build:** `lake build RecursionFastClean` is green, 3.8 s warm (`00-build.log`).
  `lake env lean RecursionFast/Controls/Layout.lean` is clean (`01-controls-layout.log`).

## Verdict

**Pass after one major fix.**

**The bridge is correct, and its proof does what it claims.**
- **The theorem holds as stated.** `toLayout_rel_iff` and `statementPerm_iff` are proved in
  both directions, with explicit and computable witness maps (`toCleanWit`, `toLayoutWit`).
- **The hypotheses are inhabited.** `fibK_supported` and `fibK_faithful` inhabit them, and
  `fibK_statement` and `pair_statement` use the theorem.
- **Every constant is clean.** All 626 constants of the `RecursionFast.Clean*` modules depend
  only on `propext`, `Classical.choice` and `Quot.sound`. None depends on `sorryAx`, and
  neither does any Clean constant they reach (P3, an exhaustive audit, not a list).
- **The translation reads only what it should.** A Clean variable at or beyond the component
  width becomes the zero linear form (`xLin`), never the next row or a contract cell.
  - A constant `c` becomes `c · (view cell cols+cols)`, the view's constant `1`, never an empty
    product.
  - Duplicate sparse positions occur (for example, `x + x` merges to `[(x,1),(x,1)]`). Both
    `rowDot` and `Lin.eval` sum them (`rowDot_tag`).
- **The arithmetic is the contract's.** `Field K` through `FiniteField K` is the contract's
  `+ * - 0 1` by `rfl`. A reducing product `x^63 · x = 27` agrees through Clean's
  `Expression.eval` and through the contract's `*` (P1).

**The trusted change is exactly one number and its docstring.**
- `Chip.Admissible`'s `C.ports.length ≤ 2 ^ 5` is the only trusted change.
- `ports_cap` accepts 32 ports and rejects 33.
- `eChip_length` goes from 3000 to 3300. The arithmetic checks: ports ≤ 32 × 20 = 640 words.
- `eLayout_length` keeps `2^(k+8)`, the only bound anything downstream uses.
- No other trusted file is touched (`git diff HEAD --stat`). The `Library/Field.lean` hunk is
  Stage 6b's.

**One major finding.** `StatementPerm` is not "Clean's `Statement` with the balance replaced".
- **The difference.** A channel is identified by its **name**, so an interaction on an
  *unlisted* `RawChannel` that shares a listed channel's name is counted on the listed bus.
- **Proof.** The kernel checks a divergence in both directions, on ensembles where Clean's own
  `Statement` is meaningful (at most one interaction per listed channel). See S8-M1.
- **Contradicting documentation.** The stage's translation table, S8-A5 and the docstrings all
  say such interactions produce "nothing".

**Ten minor findings.**

## Findings

### S8-M1 (major): channel identity by name diverges from Clean's `Statement` in both directions; the docs say it does not

- **Declarations.**
  - `Part.ints` (`ToLayout.lean:152`) keeps `i.channel.name ∈ names`.
  - `OnBus` (`Semantics.lean:70`) and `tableMsgs` (`:81`) also test the name. `BalancedPerm`
    and `StatementPerm` inherit the test.
  - **Docs.** The header table of `ToLayout.lean:16` and `S8-RESULT.md:138` say "interaction
    on an unlisted channel | nothing (Clean balances listed channels only)".
    `S8-RESULT.md:329-330` says "unlisted channels are dropped". S8-A5 says "Interactions on
    unlisted channels produce no port".
- **Problem.** Clean balances `ens.channels` by `RawChannel` equality: `interactionsWith ch`
  filters `i.channel = ch`. The translation and `StatementPerm` instead put every interaction
  whose channel *name* is listed on that name's bus. Concretely:
  - an interaction on an unlisted channel with a listed name is counted, while Clean ignores it;
  - listed channels that share a name are merged, so per-channel balance becomes union
    balance.

  Under the S8-A11 decision, `Supported` no longer requires distinct names. Nothing excludes
  either case, and none of the controls shows it.
- **Probe** (`probes/s8/review/P2Names.lean`, kernel-checked, axioms standard,
  `logs/S8-review/P2.log`).
  - **Setup.** Over `K`, `chA` and `chB` are both named `"c"`, with different guarantees
    (`chA_ne_chB`). Only `chA` is listed.
  - **`divergence : StatementPerm byName ens 1 ∧ ¬ ens.Statement 1`.**
    - The verifier pushes `x` on `chA` and pulls it on `chB`.
    - The translation puts both on bus 0 (`pub_ports`), and `rel` accepts the honest witness.
    - In Clean, `chA` carries one interaction, a push of multiplicity `1`. Its `balanceOf` is
      `1 ≠ 0` in any field, so `Statement` fails for every input.
    - This is a weakening: the bridge accepts what Clean rejects.
  - **`divergence2 : ens2.Statement 1 ∧ ¬ StatementPerm byName ens2 1`.**
    - The verifier only pushes on the unlisted `chB`.
    - Clean balances `chA` trivially: it carries no interaction.
    - `StatementPerm` sees an unmatched send on bus 0.
    - This is a strengthening: an honest Clean witness fails.
  - **The cause.** Neither divergence involves the characteristic-2 length condition. Both
    lists have length `≤ 1 < 2`.
- **Fix.**
  1. **Docs.** Replace the "unlisted channel → nothing" rows and sentences with "an
     interaction whose channel's **name** is not listed → nothing; a channel is its name, so
     an unlisted channel that shares a listed name is on that bus". Do this in
     `ToLayout.lean:16`, `S8-RESULT.md:138` and `:329-330`, and S8-A5.
     - Also make the docstrings of `tableMsgs`, `OnBus` and `BalancedPerm` say "a channel whose
       name is listed" instead of "a listed channel".
     - Make `balancedPerm_byName_iff` say "each channel *name* balances".
  2. **Make the Clean correspondence exact under a stated hypothesis.**
     - Add
       `ChannelsByName ens := (chNames ens).Nodup ∧ ∀ c ∈ ens.allTables, ∀ i ∈ c.rowOperations.interactions, i.channel.name ∈ chNames ens → i.channel ∈ ens.channels`.
       This is not decidable, but it is provable for a concrete ensemble.
     - Prove `balancedPerm_byName_iff_raw`: under it, `BalancedPerm byName w ↔ ∀ ch ∈ ens.channels`,
       the ℕ-multisets sent and received among the interactions with `i.channel = ch` (Clean's
       own filter) are equal.
     - The proof is about 30 lines on top of `balancedPerm_byName_iff`: under `Nodup` and
       membership, `i.channel.name = ch.name ↔ i.channel = ch`.
     - State in `StatementPerm`'s docstring that it is Clean's `Statement` with the ℕ-balance
       exactly when `ChannelsByName` holds.
  3. **Controls.** Adopt P2's `divergence` and `divergence2` as negative controls
     (`name_merge_weakens` and `name_merge_strengthens`). They document the scope.

### S8-m1: in `K`, `readMult` reads `(1 : K) * e` as a receive; a constant `-1` multiplicity is a send (`K`) or silent (`F p`)

- **Declaration.** `readMult` (`ToLayout.lean:51`), its docstring ("Read from the syntax, never
  from the value"), and S8-A3.
- **Problem.** `readMult` matches `mul (const c) e` and compares the **value** `c = -1`.
  - In `K`, `-1 = 1`, so `mul (const 1) e` is `mul (const (-1)) e` definitionally. Clean's
    `pushIf ((1 : K) * en)` (or `(1 : Expression K) * en`) is therefore read as a pull.
  - A multiplicity written as the constant `-1` (`const (-1)`, not through `Neg`) behaves
    differently by field:
    - in `K` it is literally `pushed`'s multiplicity, a send;
    - in `F p` it is a send whose selector evaluates to `-1 ≠ 1`, so it is silent, where Clean
      counts a receive.
  - The S8 docs mention only `pushedIf (-x)` and `emit (-1 * e)` written by hand.
- **Probe.** `P1Arith.lean`, all decided by the kernel:
  - `readMult ((1 : K) * var 0) = (false, var 0)`;
  - `readMult (pushedIf ((1:K) * var 0) _).toRaw.mult = (false, var 0)`;
  - over `F 7` the same expression is a send;
  - `readMult (const (-1) : Expression K) = (true, const 1)`;
  - over `F 7`, `(true, const (-1))`, with a selector value `≠ 1`.
- **Fix.**
  - Reword `readMult`'s docstring, the `ToLayout` header and S8-A3:
    > The pattern `mul (const c) e` with `c = -1` receives with selector `e`. In `K` this
    > includes `c = 1`. Every other multiplicity sends, including the constant `-1`. A
    > receive can be written only through `Neg` (`pull`, `pullIf`).
  - Advise authors over `K` never to scale a push selector by a leading constant.

### S8-m2: stale or inaccurate statements in the RESULT, the amendments and two docstrings

- **`S8-RESULT.md:18`.** It says "Not touched: anything under `RecursionFast/Contract/`", but
  S8-A9 changed `Contract/Layout.lean`.
- **`DESIGN-AMENDMENTS.md:717-718`.** The Stage 8 preamble says "nothing under `Contract/`
  changed", which S8-A9 contradicts.
- **`S8-RESULT.md:27` and `:201`.** They say "`Supported`: distinct channel names". S8-A11
  dropped that.
- **`S8-RESULT.md:329-330`.** This is the same staleness, and it is also wrong (see S8-M1).
- **`ToLayout.lean:9` (header table) and `pubPart`'s docstring (`:253`).** They say "32
  columns" and "(`size PublicIO ≤ 32` cells), zero columns up to 32". The code is
  `max 32 (size PublicIO)` base columns and supports more than 32 public elements (S8-A2).
- **Fix.** Correct each item. The decision-pass section already says it wins, but the headline
  is what readers quote.

### S8-m3: `scripts/setup-clean.sh` does not check the revision of a non-git source or of an existing `ext/Clean`

- **Problem.**
  - In copy mode the revision check runs only if `$src/.git` exists.
  - In the idempotent branch, an `ext/Clean` without `.git` is accepted as is.
  - In both cases the script still prints `ext/Clean at 42fe4b26…`.
  - This repository's own `ext/Clean` was made in copy mode and has no `.git`. The reviewer
    verified separately that it is byte-identical to leanerVM's checkout at `42fe4b26`
    (`diff -rq`).
- **Probe** (`logs/S8-review/10-shell-sims.log`).
  - A copy of Clean with one tampered line in `Air/Balance.lean` is installed and reported as
    "at 42fe4b26".
  - A re-run reports "present".
  - The **clone mode works from a fresh tree.** This was simulated without network by
    cloning a local mirror at the rev. `lake env true` loads the workspace in 23.5 s and the
    manifest is unchanged.
- **Fix.**
  - Pin a content hash of the copied files, for example `scripts/clean-src.sha256` over
    `Clean/**/*.lean`, `Clean.lean` and `lakefile.lean`.
  - Check it after a copy and in the idempotent branch, or refuse a source without `.git`.
  - Print "at REV" only after a check.

### S8-m4: the root's `Clean` require breaks `scripts/harness.sh` with its default `--org`, and root-level `lake` in other scripts

- **Problem.** `harness.sh` defaults `ORG` to this tree, and its fresh-tree manifest copies
  `org`'s package entries verbatim.
  - The `Clean` entry is a path entry, `"dir": "./ext/Clean"`, which then resolves inside the
    fresh tree.
  - Every current caller passes `--org .lake/org` (Clean-free), so the problem is latent.
  - `submissions/baseline/scripts/check.sh` (Stage 7) runs root-level
    `lake build RecursionFastCandidate`. On a fresh clone this now fails without
    `setup-clean.sh`.
- **Probe.** The `mkfresh` manifest transformation, replayed with the default `--org`, fails
  with `error: Clean: package directory not found: /tmp/s8rev/hfresh/./ext/Clean`
  (`10-shell-sims.log`).
- **Fix.** This is for Stage 6b (`scripts/`) and Stage 7.
  - In `harness.sh`'s `mkfresh`, and in `harness/badge-build.sh` for robustness, rewrite path
    entries against `org`:
    `if p["type"] == "path": p["dir"] = os.path.normpath(os.path.join(org, p["dir"]))`.
    Alternatively, drop `Clean` as `org-build.sh` does, or make `--org` mandatory.
  - The baseline's `check.sh` calls `scripts/setup-clean.sh` first.

### S8-m5: the bridge's hypotheses have only positive controls

- **Problem.**
  - `Supported` and `LookupsFaithful` are each shown satisfiable (`fibK_supported`,
    `fibK_faithful`, `pair_faithful`).
  - No control shows that either can fail.
  - No control shows that `Supported` is needed for completeness.
- **Fix.** Add three controls in `Examples.lean`:
  - `¬ Supported ensWide` by `decide`: a component that asserts `var 5 - 1` at width 3.
  - `¬ LookupsFaithful [] FibK.ens`: the lookup is unregistered.
  - The completeness counterexample: a Clean witness with 6-cell rows (`row[5] = 1`) satisfies
    `HoldsPerm` for `ensWide`, but the translated layout reads `0` there and rejects every
    witness.

### S8-m6: no completeness corollary into `relK`

- **Problem.**
  - `holdsPerm_of_relK` gives soundness from the contract's `relK k`.
  - Its converse is missing. The examples rebuild it each time (`fibK_relK`).
  - Admissibility is per instance only: no theorem bounds `t`, `q`, ports or cells by Clean
    quantities (stated in "Not covered" 3).
- **Fix.** Add
  ```lean
  theorem relK_toLayoutWit (hadm : (toLayout tabs ens cm).Admissible k) (hS : Supported ens)
      (hL : LookupsFaithful tabs ens) (h : HoldsPerm cm cw)
      (hk : layoutCells (toLayout tabs ens cm) (toLayoutWit tabs cw) ≤ 2 ^ k) :
      ((toLayout tabs ens cm, pubVec cw.publicInput), toLayoutWit tabs cw) ∈ relK k
  ```
  for an ensemble over `K`, in two lines, so that the bridge has both directions at the
  contract's relation.

### S8-m7: the upstream note understates the vacuity and misattributes one file

- **Problem.**
  - **The vacuity is understated.** Over `K` a balanced interaction list is `[]` or a single
    interaction of multiplicity `0` (`clean_balance_K`, P4). So Clean's `Statement` over `K`
    says that no listed channel carries any message, not merely "at most one interaction".
  - **One file is misattributed.** The note's table lists `Clean/Air/OrderedChannel.lean` among
    the files whose `Fact (ringChar F ≠ 2)` hypotheses would be dropped. It has none. It
    case-splits on `ringChar F = 0` (line 338), which is the length side condition.
  - **Checked otherwise.** The other cited names (`one_ne_neg_one`,
    `guarantees_of_requirements_of_requirements_of_guarantees`,
    `addVm_soundVmChannel_of_soundChannels`, `addVm`) carry the hypothesis as stated. Both
    vacuity theorems the note quotes are kernel-checked.
- **Fix.**
  - State the sharper form.
  - Optionally add P4's `clean_balance_K` next to `clean_balance_vacuous`.
  - Correct the `OrderedChannel` row to "adapt the `ringChar F = 0` case split".

### S8-m8: `ChannelMap` can merge buses silently

- **Problem.**
  - Mixing `none` and `some` can make a `none` channel's default bus (its name's index)
    coincide with a `some` bus. For example, with `"b" ↦ some (0, true)`, `"a"` keeps bus 0
    (P4 `mixed`, decided).
  - A channel mapped `some (b, s)` forces **every** interaction on it to direction `s`, so a
    channel that both pulls and pushes has half of them flipped.
  - Both sides of the bridge use the same `cm`, so the theorem holds. But only
    `balancedPerm_byName_iff` relates a map to a per-channel reading.
- **Fix.**
  - State both effects in `ChannelMap`'s docstring.
  - Optionally add a decidable `ChannelMap.Separate cm names`: no `none` index equals a `some`
    bus, and every `some` channel's interactions are all pulls or all pushes by `readMult`.
  - Prove `BalancedPerm cm` per bus as the union of its channels' traffic.

### S8-m9: no axiom audit of `RecursionFastClean` in CI

- **Problem.**
  - `scripts/AxiomAudit.lean` covers the contract, library, controls and bridge, not
    `RecursionFastClean`.
  - The S8-A12 CI step only builds the library.
  - S8's own audit (`logs/S8/42`) lists 31 declarations by hand.
- **Probe.** P3 audits every constant of the `RecursionFast.Clean*` modules (626): all
  standard, no `sorryAx` (`logs/S8-review/P3.log`, 2 min 22 s).
- **Fix.** Add P3, or an equivalent `axiomaudit`-style scan restricted to
  `RecursionFast.Clean*`, to the S8-A12 CI step.

### S8-m10: hygiene

- **Line length.** 59 lines exceed 100 characters: `Semantics` 37, `ToLayout` 12, `Gadget` 7,
  `Examples` 3. Most are in the `ToLayout` header table and in proofs.
- **Proof length.** `holdsPerm_toCleanWit` is 177 lines and `rel_toLayoutWit` 135 lines. This
  is the golf agent's remit; no statement changes.
- **Orphan instances.** `deriving instance DecidableEq for Variable` and `... for Expression`
  (`ToLayout.lean:35-36`) are global orphan instances on Clean's types. They will clash if
  Clean derives them upstream.
  - **Fix.** Scope them (`local instance`, or `attribute [local instance]` on named
    definitions), or note the clash risk in the header.
- **Checked clean.** `check-hygiene.sh` passes, and there is no `sorry`, `native_decide`,
  `set_option` or `noncomputable` in the bridge.

## `Ensemble.Statement` ↔ `StatementPerm` ↔ `Layout.rel`, clause by clause

Pass B (fidelity to Clean) was done first, from Clean's sources, before reading `Semantics.lean`.

| Clean `Ensemble.Statement ens x` (42fe4b26) | `StatementPerm cm ens x` | `(toLayout tabs ens cm).rel k (pubVec x) w` | Verdict |
|---|---|---|---|
| `∃ witness : EnsembleWitness ens`: `tables`, `data`, `publicInput`, `same_length`, `same_circuits`, `same_data` | the same type | `w : List Table`, `w.length = 1 + #components + #tabs`; the maps `toCleanWit`/`toLayoutWit` | same |
| `witness.publicInput = x`; the verifier table is one row `toElements x` | the same | public chip: `[r = 0] = 1` gives exactly one row; cells `0…31` are the statement; cells `size…base-1` are constrained to `0` | same for `size PublicIO ≤ 32` (`pubVec_injective`); beyond 32 only the first 32 are statement (S8-A2) |
| `Constraints`: every row of every table, the verifier included, satisfies `Operations.ConstraintsHold` = every flattened `assert` evaluates to `0` | the same (`w.Constraints` reused) | the row gadget = `ofExpr` of each assertion (`holds_chip_iff`), padding columns `0`, auxiliary columns equal to their expressions; a variable at or beyond the width reads `0`, as `Environment.fromArray` does | same, given `Supported` for completeness (Clean rows may be wider than the component) |
| … and every flattened lookup satisfies `Contains (env.data name arity) entry` | the same | a receiving port on a `sub` bus, selector the constant `1`; a fixed chip sends the registered rows | same under `LookupsFaithful` (static tables). ProverData tables are not covered (S8-A10a); `StaticLookupChannel` is an `eq` channel (S8-A10b) |
| Guarantees, Requirements, `assumeGuarantees`, `Assumptions`, `Spec` | none | none | same: none is in Clean's `Statement` (`Operations.ConstraintsHold` is assertions and lookups only) |
| `BalancedChannels`: `∀ ch ∈ ens.channels` (a `RawChannel`), `BalancedInteractions (interactionsWith ch)`, filtered by **`RawChannel` equality** over all rows of all tables | `BalancedPerm cm`: `∀ b < cm.nBus`, messages sent = messages received, as `Multiset (List F)`, over interactions whose channel **name** is listed and mapped to `b` | `traffic` per bus, kind `eq` for `b < nBus` | **changed, see the next five rows** |
| — field sum of multiplicities per message | ℕ-multiset | ℕ-multiset | changed on purpose (§9.2, S8-A7) |
| — side condition `length < ringChar F ∨ ringChar F = 0` (counts every interaction, multiplicity 0 included) | dropped | dropped; the cell bound `≤ 2^k` limits rows | changed on purpose. Over `K` the condition makes `Statement` say that no listed channel carries any message (P4) |
| — multiplicity = its **value** (`-1` pull, `1` push, `m` = `m` copies, `0` nothing) | direction from `readMult` syntax (or `cm`); the message counts once iff the selector evaluates to `1`, otherwise silent | port `send` and selector column; `Table.msgs` reads `sel = 1` | changed, documented (S8-A3; DESIGN §2.1(a)). Agrees for `pulled`, `pushed`, `pulledIf b`, `pushedIf b` with `b ∈ {0, 1}`. Differs for counts (`emit m`, LogUp), for non-boolean enables (in `F p` Clean counts them, here they are silent), for `pushedIf (-x)`, and for `(1:K)·e` and `const (-1)` (**S8-m1**) |
| — channel identity: a `RawChannel` | the name | the name (`Part.ints`) | **S8-M1**: unlisted same-name channels are counted, and listed same-name channels are merged; kernel-checked divergence both ways |
| — `ens.channels` as listed | `cm` may join channels into one bus | the same | a generalisation. `byName` with distinct names gives every channel name its own bus (`balancedPerm_byName_iff`); a mixed map can merge silently (**S8-m8**) |
| `ProverData`: witness, arbitrary | the same | not translated; the relation reads none | same, because `LookupsFaithful` quantifies over all data and expressions read no data |
| — | — | `Σ rows · cols ≤ 2^k` | an extra conjunct on the right of `toLayout_rel_iff` (in terms of `toLayoutWit`); `statementPerm_iff` takes `∃ k` |
| — | — | `Admissible k` (in `relK` only) | not bridged; per instance by `decide` (S8 "Not covered" 3; **S8-m6**) |

## Pass A: the specification

- **`toLayout_rel_iff` is non-vacuous.** Its hypotheses are instantiated (`fibK_supported`,
  `fibK_faithful`, `pair_faithful`). Both sides are satisfiable (`fibK_rel`, `fibK_statement`),
  and `rel` is refuted on mutated witnesses (`fibK_wrong_final`, `fibK_mutated`,
  `fibK_lookup_neg`, `fibK_junk_neg`, `pair_byName_neg`).
  - **Gap.** These negatives are witness-level. They show that the translation reads the cells
    and the buses, not that `StatementPerm` is false for some statement. P2's
    `not_statementPerm2` is the first statement-level negative, and it is S8-M1's.
- **Where the hypotheses are used.**
  - The soundness direction needs only `LookupsFaithful`.
  - Completeness also needs `Supported`, which is genuinely necessary (S8-m5 gives the
    counterexample shape).
  - `hpub : size PublicIO ≤ 32` is needed only for injectivity in `statementPerm_iff`.
- **The `∃ k` in `statementPerm_iff`** is a size class with no admissibility. That is correct
  for `rel`. The contract-level corollary is one-directional (`holdsPerm_of_relK`; S8-m6).
- **The degree claim of S8-A4 is proved** (`length_ofExpr_le`). `gadgetOf` has
  `D = max 1 (max product length)` and `Q · D` matrices, and absent products give empty
  (zero) rows (`prod_factor`). That `D ≤ 8` follows from `degreeBound ≤ 8` is a remark, not
  a theorem. Admission is decided per instance.
- **`FiniteField K`** has `val = bits.toNat`, `fromNat = BitVec.ofNat 64`, `size = 2^64`. This
  is the bit-pattern embedding Clean documents for binary fields. `Field K` is the library's
  `K.instField`, whose data is the contract's operations (P1, by `rfl`).
- **`#synth DecidableEq K`** gives the contract's `instDecidableEqK`, not Clean's
  `propext ▸` instance, so `decide +kernel` through `toLayout` reduces.

## Pass B: fidelity to Clean

Pass B was done independently, from Clean's sources. Its results are in the clause table above.

- **Identical:** the witness type, `Constraints` (assertions and lookups, subcircuits flattened
  through `Operations.constraints`/`lookups`), the verifier row and the data.
- **Changed on purpose and documented:** the ℕ-multiset in place of the field sum, the dropped
  length condition, and the selector reading of multiplicities.
- **Changed without documentation:**
  - the channel identity (S8-M1);
  - the `K`-specific readings of `(1:K)·e` and `const (-1)` (S8-m1).
- **Guarantees and Requirements** are not part of Clean's `Statement`, so nothing is lost by
  omitting them. Their role is in Clean's soundness theory, which S8 does not transport
  ("Not covered" 6), correctly. Over `K` that theory is vacuous anyway: `Statement` holds only
  without messages (P4), and `clean_push_requirement_vacuous`.
- **Direction by constructor:**
  - `pushed`: `const 1` → send, selector `1`.
  - `pulled`: `(-1)·1` → receive, selector `1`.
  - `pushedIf e` → send, selector `e`, **unless** `e = c·e'` with `c = -1`, which in `K`
    includes `c = 1` (S8-m1).
  - `pulledIf e`: `(-1)·e` → receive, selector `e`.
  - `emit m` → send, selector `m` (a count is read as a selector: documented).
  - A raw `AbstractInteraction` → by the same pattern. A `const (-1)` multiplicity is a send
    (S8-m1).
- **Booleanity of selectors.** The translation neither adds nor assumes it. A non-boolean
  selector is silent on both sides, as DESIGN §2.1(a) prescribes, so the bridge is exact.
  - **Where it differs from Clean.** In `F p`, Clean counts `e` copies. A Clean circuit that
    leaves an enable unconstrained therefore has different witnesses under the two semantics.
    This is inherent and documented.
- **leanerVM's BLAKE2s table under the hypotheses.**
  - The S8 report does not mention the hypotheses. P5, run in the S8 probe package with
    compiled evaluation, finds `Supported` true and 0 lookups, so `LookupsFaithful []` holds
    trivially.
  - The interaction names are the six listed channels, so the S8-M1 hazard does not arise
    there.
  - "What remains is the BF64 → K transport and the compression" therefore stands. It is still
    not kernel-checked.

## The trusted change (S8-A9)

- **The diff is exactly one number and its docstring.** In `Contract/Layout.lean`,
  `C.ports.length ≤ 2 ^ 4` became `2 ^ 5`, and the docstring now reads "at most `2^5` ports".
  The code line count is unchanged.
- **The §2.2 reasoning still holds.** A port serialises to `4 + |msg| ≤ 20` words. Per chip
  that is `32 × 20 = 640` words (`eChip_length`: 3000 → 3300). With at most 256 chips the
  ports add at most 163,840 words, against an index bound of `2^(k+8) ≥ 2^28`
  (`eLayout_length`, unchanged).
- **Nothing downstream needed the old cap.** `Library/Extractor.lean` and `Controls/Toy.lean`
  use only `eLayout_length`. The trusted `Extractor.lean` serialisation has no cap constant.
- **The boundary control moved.** `ports_cap` accepts 32 and rejects 33, and no other control
  mentions the cap.
- **Builds.** The S8 logs show the default build, the organiser build and `axiomaudit` green
  after the change (`logs/S8/40`, `41`, `44`). `Controls/Layout.lean` compiles here.
- **No other trusted change.** No other `Contract/` or `Vendor/` file is in
  `git diff HEAD --stat`.

## Setup, isolation, organiser package

- **Isolation.** `RecursionFastClean` and `Clean` are imported by nothing in `Contract/`,
  `Library/`, `Controls/`, `scripts/`, `harness/` or the challenges (grep). Their only
  importers are the bridge's own files and the probes.
- **`org-build.sh`.** Its transformation, replayed into a scratch directory, yields a lakefile
  and manifest with 0 mentions of Clean. It syncs only `Contract`, `Vendor`, `Library`,
  `Controls` and `Bridge`.
- **Manifest and gitignore.** The manifest entry is a path entry to `./ext/Clean`, and
  `.gitignore` has `ext/`.
- **`ext/Clean` matches the pin.** It is byte-identical to leanerVM's checkout at `42fe4b26`
  (`Clean/`, `Clean.lean`, `lakefile.lean`).
- **Fresh clone (clone mode).** It works offline from a mirror. The manifest is untouched, and
  `lake env true` succeeds in 23.5 s. Copy mode is not revision-checked (S8-m3).

## Lean4 review summary (`lean4:review`, scope = `RecursionFast/Clean/*`, batch; Layer 2 advisory, `repository_kind = other-lean`)

- **Build:** `lake build RecursionFastClean` ✓ (warm 3.8 s; only Clean's two deprecation
  warnings).
- **Sorry audit:** 0.
- **Axioms:** all 626 constants standard (P3).
- **Style:** 59 lines over 100 characters, two long proofs, orphan derived instances
  (S8-m10).
- **Advisory, mathlib-style:**
  - Three generic helpers live in the bridge's namespace: `sum_flatMap'`, `le_foldr_max` and
    `mem_list_sum`. A quick search found only the `Finset`-indexed `Finset.mem_sum` and
    `List.foldr_max_of_ne_nil`, not exact equivalents. They can stay; a golf pass may look
    again.
  - `Part` is a structure with a proof field (`width_le`), which is appropriate.

## Probes

| Probe | What it shows | Log |
|---|---|---|
| `probes/s8/review/P1Arith.lean` | `fmul/fadd/fneg/0/1` through `FiniteField K` = the contract's, by `rfl`; `x^63·x = 27` through `Expression.eval`, `fmul` and the contract's `*`; `readMult` over `K`: `(1:K)·e` is a receive and `const (-1)` a send; over `F 7`, `(1)·e` is a send and `const (-1)` silent; `#synth DecidableEq K = instDecidableEqK` | `logs/S8-review/P1.log` |
| `probes/s8/review/P2Names.lean` | **S8-M1**: `chA_ne_chB`, `pub_ports`, `rel_ok`, `statementPerm_one`, `not_statement`, `divergence`, `statement2`, `not_statementPerm2`, `divergence2` (axioms standard) | `logs/S8-review/P2.log` |
| `probes/s8/review/P3Axioms.lean` | the axioms of all 626 constants of the `RecursionFast.Clean*` modules: standard, no `sorryAx` | `logs/S8-review/P3.log` |
| `probes/s8/review/P4Vacuity.lean` | `clean_balance_K` (a balanced list over `K` is `[]` or `[i]` with `i.mult = 0`); `mixed` (a `none` bus coinciding with a `some` bus) | `logs/S8-review/P4.log` |
| `probes/s8/review/P5Blake2sSupported.lean` (run from `probes/s8/blake2s`) | leanerVM's BLAKE2s table: `OpsWithin` true, 0 lookups, interaction names = the listed names | `logs/S8-review/P5.log` |
| shell, `/tmp/s8rev/*` | fresh clone (clone mode, offline mirror) loads; a tampered copy is accepted (S8-m3); `harness.sh` with the default `--org` fails on `./ext/Clean` (S8-m4); `org-build.sh`'s transformation is Clean-free | `logs/S8-review/10-shell-sims.log` |

Each Lean probe runs with `lake env lean probes/s8/review/<P>.lean` from the repository root,
about 8 s each (P3: 2 min 22 s), except P5, which runs from `probes/s8/blake2s`.

## Notes for other stages (not S8 findings)

- **Orchestrator.** Fold S8-A9 into DESIGN §2.2 (the "ports per chip" row) and §2.3, which
  still say `2^4`.
- **Stage 6b.**
  - `harness/check-chain.py:201` still checks `len(C.ports) <= 2 ** 4`, and
    `harness/CHAIN-LAYOUT.md:97` says "a chip has at most `2^4` ports".
  - `scripts/olean-manifest.sha256` must be regenerated (S8-A12).
  - The S8-A12 CI step is not yet in `scripts/ci.sh`.
  - The lakefile comment on `RecursionFastSmoke` says `org-build.sh` drops it and the smoke
    executables, but `org-build.sh`'s `drop` set does not contain them. The replayed organiser
    lakefile keeps `RecursionFastSmoke`, `smoke-verify` and `smoke-index`.
- **Stage 7.** `submissions/baseline/scripts/check.sh` needs `scripts/setup-clean.sh` on a
  fresh clone (S8-m4).
