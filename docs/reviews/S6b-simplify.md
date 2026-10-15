# S6b simplify pass: the harness code

This is the golf pass of Stage 6b, run on 2026-10-15 by one agent with the `simplify` recipe. Four
read-only review agents each took one angle (reuse, simplification, efficiency, altitude), and the
pass merged their findings and applied the ones that preserve behaviour.

Nothing is committed. The pass did not touch `RecursionFast/`, `harness/gen-chain-layout.py`,
`harness/check-chain.py`, `submissions/` or `docs/DESIGN*.md`. Verification aids and logs are in
`logs/S6b-simplify/`, which is gitignored: `before/` holds the pre-pass copies.

## Headline

- **CI: OK in 9 min 47 s** (587 s; `logs/S6b-simplify/ci-run-new2.log`).
  - Before this pass it took 25 min 52 s (1,552 s; `logs/S6b/ci-run-5.log`).
  - Every check still runs. Every step log is identical up to timings and temporary paths.
- **Gate:** all 20 invocations give byte-identical full output with the old and the new `gate`
  binaries. They cover every gate run of CI step 8, plus `Forge` without `--allowed-imports`, the
  usage error and a malformed `--closure` (`probes-before/` against `probes-final/`).
  - The S7 probes that still elaborate are also identical: irforge, SpoofNs, WfRec and the cpass
    registration (`s7-before/` against `s7-final/`).
  - `ForgeGate.lean` and `EpsGate.lean` in `probes/s7/` no longer elaborate, and neither does
    `Baseline.lean` (section 1 of `run.sh`). This predates the pass: since S7-A5, `Declared` has 4
    fields. Their S6b ports are covered by CI step 8.
- **Runner:** the 10 runs of CI step 10 were repeated with the old and the new
  `run-benchmark.py`, using the same secrets and the same executables. The results JSON is
  identical once timings, memory, dates and temporary paths are removed. This includes key order.
  - Files: `runner-before/*.norm.json` against `runner-new1/`.

## CI time, per step

| step | before (s) | after (s) |
|---|---:|---:|
| 1 vendor, hygiene | 2 | 3 |
| 2 organiser build | 27 | 38 (the gate, the harness library and linkcheck rebuilt after the edits; one `lake build` less: −4 s warm) |
| 3 manifest, allowlists | 12 | 5 (manifest hashing 11.0 → 3.6 s) |
| 4 axiom audit, loc | 6 | 7 |
| 5 ‖ 6 (concurrent) | 122 + 94 = 216 | **121** (5: 121; 6 render + stubs: 25; 6 layout check: 69) |
| 7 ‖ 8 ‖ 9 ‖ 10's builds (concurrent) | 591 + 379 + 110 + ≈ 76 = ≈ 1,156 | **284** (critical path 7-toy; see below) |
| 10 timed benchmark (alone) + 9 runner rejections | ≈ 110 | 114 |
| 11 Clean | 12 | 11 |
| 12 manifest re-check | 11 | 4 |
| **total** | **1,552** | **587** |

Phase B job wall times:

| step | job | wall (s) |
|---|---|---:|
| 7 | toy (comparator 194 s inside) | 284 |
| 7 | toy `--bench` | 218 |
| 7 | negative toy | 93 |
| 8 | A4 | 127 |
| 8 | v2, then Clean | 241 |
| 8 | S7 | 80 |
| 9 | cmpproj | 54 |
| 9 | gateproj | 28 |
| 9 | bindproj | 51 |
| 10 | builds | 94 |

Resources during the run: at least 45.9 GB of memory stayed available, and the load average
peaked at 23 on 32 cores (`mem-new2.log`). The smoke benchmark ran alone. `S_leaf` 0.1748 s,
`S_wrap` 0.1764 s and `S_rec` 0.1746 s are within the 3-run noise of §6 of the RESULT.

## Per file

### `scripts/Gate.lean`: 535 → 588 lines (code 356 → 355, `scripts/loc.py`)

**Rule structure.** Each rule is now a named, documented function. `main` calls them in the
order of the `REJECT` lines: 5, 1–2, 3, 6, 8, 7, 4 with 9. A new header paragraph says so.

| rule | function | what it checks |
|---|---|---|
| 5 | `classify` | unchanged |
| 1 | `rule1` | banned constant, non-standard axiom |
| 2 | `rule2` | `unsafe`, `opaque`, `partial` |
| 1, 2 | `rules12` | runs `rule1` and `rule2` constant by constant over `closure`, and collects the axioms; the interleaved message order of `HygieneBypass` is kept |
| 3 | `rule3` | one local `pinnedNote` replaces the three "note if pinned, else reject" copies; it produces the same note texts |
| 6 | `rule6` | |
| 7 | `rule7` | |
| 8 | `rule8` | prints `gate: badge-root-module` |
| 4 | `rule4` | the `MetaM` set-up around the unchanged `checkExec` |

The rule functions read `GateCtx`, which holds `env`, `trusted`, `pinned`, `allowed` and `front`,
plus the helpers `untrusted` and `modules`.

**One graph walk.** `reach roots succ` returns the nodes in depth-first, first-visit order. It
replaces three hand-written worklist loops:
- `closure` (rules 1 and 2);
- rule 8's import walk;
- `frontendRefs` (rule 9), which is now a pure function of the `Environment`.

Because the visit order is unchanged, the `take 3` lists in the rule 8 and rule 9 messages are
unchanged. Three shared helpers replace the copies of the same logic: `usedConsts` (type and value
constants), `isTheorem` and `moduleImports`.

**Unchanged:**
- every verdict message;
- every `gate: rule 4:`, `gate: note:` and `gate: badge-root-module` line;
- the REJECT order;
- the CLI;
- `checkExec`, `compileAux`, `reduceProjs`, `ctorField?`, `classify` and the manifest reader.

### `harness/run-benchmark.py`: 607 → 615

- **`Runner.stage(name, files, layout)`** creates a fresh step directory with its inputs.
  - The index steps use it.
- **`Runner.prove(name, mode, layout, files, budget, what)`** runs the prover: the exit-status and
  `proof.bin` check, the read, and the cleanup. It keeps the `Reject` text that CI greps ("wrote no
  proof.bin").
  - The leaf steps and the node steps use it.
- **`Runner.run_verify(name, vkc, x, tape, budget, what)`** stages and runs `VERIFY`.
  - The DoS tapes use it.
  - `Runner.verify` uses it and adds the cap check and the acceptance check ("does not verify").
- **`step_record`** produces the six measurement keys of a leaf record or a node record, in the
  same order.
- **`chain_stmt`** uses `digest_to_slot`.

Not touched:
- `Runner.run`: the timed region, the sandbox and the `ru_maxrss` measurement. S6b-M1's fix
  belongs there, and every new helper goes through it.
- The board logic, the results schema and `load_config`.

One small difference: after a rejected verify, the step directory is now removed straight away
instead of at the end of the evaluation. This does not apply with `--keep`, and it is not
observable in the results.

Kept on purpose:
- `p.returncode = …`, because Popen bookkeeping needs it for a process reaped by `os.wait4`.
- The `log` parameter of `Runner`, because `measure-noise.py` passes it.

### `scripts/harness.sh`: 267 → 214

- **`mkfresh`.** Its 47-line Python heredoc is now `harness/mk-tree.py`.
  - For production the output is byte-identical: the same `lakefile.toml`, the same
    `lake-manifest.json`, and the same error messages for a module-root clash and for a badge-root
    clash. This was tested against the old heredoc.
- **`badge_mains DIR MODULE`.** Both stage 1 and stage 3a use it. Stage 3a now always regenerates
  the mains from `${BMOD:-$SOL_MOD}`.
  - The old special case regenerated them only when `BMOD` differed. The files are byte-identical
    whenever the module is the same, and nothing builds the mains before stage 3a.
- **`jget FILE KEY`** replaces `cfg` and the inline reader for the rejection reason.
- **Removed: the v0.3 option `--badge CMD`** and its "stage 3". Nothing calls it: not ci.sh, the
  tests, the README or the docs.
- **Found while doing this: `mkfresh` returned the wrong status.**
  - `mkfresh` is called as `mkfresh … || reject`, so `set -e` is off inside it.
  - It used to end with `cp config`, which returned 0 even after a module-root clash. The run was
    then rejected later, at "comparator, exit 1", because the tree had no lakefile.
  - The generator is now its last command, so the rejection reason is "fresh tree (module names)".
    The verdict was REJECT before and is REJECT now.
- **The A6-G0 order is untouched.**

### `harness/mk-tree.py` (new, 45 lines) and `harness/badge-build.sh` (72 → 39)

- **`mk-tree.py ORG TREE NAME [CHALLENGE_MODULE]`** is the single tree generator.
  - The module-root freshness check runs only when a challenge is given, which is production's
    case.
- **`badge-build.sh`** now uses it.
  - Its manifest is byte-identical to before.
  - Its lakefile lists the two `[[lean_exe]]` blocks in sorted order (index, then verify).
  - The smoke test in CI step 10 therefore exercises production's generator.
- **`harness/README.md`** gains a row for `mk-tree.py`.

### `scripts/ci.sh`: 319 → 358

**Concurrency.** `job NAME CMD…` and `join NAME…`, together with a `titled` wrapper, run CI in
phases:

| phase | jobs |
|---|---|
| A (after step 4) | step 5; step 6 render + stubs; step 6 layout check |
| B | step 7's three harness runs; step 8 as A4, v2 then Clean, and S7; step 9's three regressions; step 10's two executable builds |
| after both | step 10's timed benchmark, run alone; its rejections; steps 11 and 12 |

- Outputs are replayed in step order, and each job reports its own wall time.
- `trap` waits for any running job before it removes `$T`.
- The organiser-only steps 2–6 still finish before any code that resembles a solution runs, as the
  header's A6-G0 paragraph requires. Each harness run keeps its own order.
- The Clean probes run after GateV2 in the same job, because `GClean.Core` imports `GateV2`. The
  first CI run, with Clean as a separate job, failed exactly there.

**De-duplication:**
- `gate_rejects LOG PATTERN ARGS…` replaces five copies of "run the gate, expect REJECT, grep".
- `olean` replaces the probe compiles.
- `GA` holds the gate options they share.
- `regress NAME` runs one pipeline regression.
- One loop covers the two list-staleness checks.
- `mkcfg` uses `dict.update`.

Every echo text is unchanged. The step-8 lines in the CI log now come in the order A4, v2, Clean,
S7; before, they came A4, v2, S7, Clean. The `gate-*.log` files are byte-identical.

**Found while doing this:**
- `check-chain.py` appends to its log, so step 5 printed the results of the last five runs. CI now
  truncates the log first.
- In the Clean positive, `grep A && grep B` left the first grep non-binding under `set -e`. Both
  greps now bind. Both lines are present, so the verdict is unchanged.

### `scripts/olean-manifest.py`: 126 → 127

- `hash_all` now runs `sha256sum -z` in parallel batches of 256, as the gate does. Before, it
  hashed with hashlib in threads, which ran on about 5 cores here because this CPU has no SHA
  extensions.
- Each check takes 3.6 s instead of 11.0 s. CI runs it in steps 3 and 12 and two to four times in
  each harness run.
- `gen` reproduces the committed manifest byte for byte, and a manifest with one hash changed fails
  (`changed core/Init.olean`).

### `scripts/org-build.sh`: 75 → 75

- The organiser was built twice. The second build, `> /dev/null`, existed only for its exit
  status; it is a 4.2 s no-op.
- It is now built once. The output is filtered from a variable and the status is checked
  explicitly. The duplicated "manifest out of date" warning is gone.

### `harness/lean/RecursionFastHarness/Twin.lean`: 128 → 131 (code 79 → 79)

- Two docstrings said the twin uses "the gate's `reduceProjs`". It has its own: `ctorApp?` with
  structure info and an arity check, where the gate's `ctorField?` has neither. The docstrings now
  say so, and say that the kernel's `rfl` in the main module is what binds the twin.

### `scripts/run-comparator.sh`: 12 lines, deleted (unstaged)

- It was a v0.3 leftover that nothing references, and it no longer worked under v2: it passed
  `--computable RecursionFast.Challenge.protocol`, which does not exist, so the gate would reject
  the positive toy.
- CI step 7 does its job. `git checkout scripts/run-comparator.sh` restores it.

## Declined, and why

1. **Gate rule 4's `Fin`-family branch (b)**, flagged by the altitude review.
   - Removing it would tighten rule 4. A `shape` with no code as a whole would then be rejected,
     and stage 3a, which compiles `shape` whole through the twin, needs exactly that.
   - That is a change of behaviour, so it is left for the review and fix pass. It is a candidate
     minor finding: today the gate can PASS what stage 3a then fails to build.
2. **One projection reduction for the gate and the twin, or `ctorFields` → `getStructureFields`.**
   - The gate imports Lean core only and loads no imported extension state beyond `pureExts`.
   - Structure info comes from an extension. Taking on that risk in trusted code would save about
     10 lines.
3. **The copies of the claim schema:**
   - `dummy-claim.py`'s placeholder regex and its chip and entry counts;
   - `test-render.sh`'s `layout_stats`;
   - `FIRST_MSG` in both `toy-solution.py` and `dummy-claim.py`.

   They have not diverged, and the brief says to unify only if they have. Any drift fails CI
   step 6 loudly with "key mismatch". The toy's words are checked by the kernel's `rfl`; the
   dummy's are filler.
4. **The manifest key format, parsed three times** (`Gate.readManifest`, `olean-manifest.py`,
   `harness.sh shadow`). The three are in three languages. Loading `olean-manifest.py` by path from
   `shadow` would save no lines.
5. **A sourced `tests/pipeline/lib.sh`.** It would hold three one-line helpers; a new sourced file
   for those is not simpler.
6. **Marginal tidy-ups:**
   - a field helper in LayoutJson;
   - a dispatch dict or emitter cache in `render-challenge.py`, which has one layout placeholder;
   - `load_config`'s key tuples;
   - running org-build's two `gate --closure` loads concurrently (≈ 3 s).
7. **Running steps 5–6 concurrently with 7–10.** The efficiency review estimated CI at about
   8 min this way. It would break ci.sh's rule that organiser-only steps run first, for about
   2 min.
8. **Splitting step 5.** `check-chain` runs single-threaded for about 102 s and is phase A's
   critical path. Splitting would save about 15 s, and `check-chain.py` is Stage 6a's.
9. **A cache of hashes in the gate or the manifest.** It would weaken trust by content hash
   (A6-G2).
10. **Merging the toy run with the toy `--bench` run.** That would drop the toy's
    `HARNESS: ACCEPT` check.

## Notes for the fix pass

- S6b-M1 (the sandbox is optional) concerns `Runner.run` and `load_config`. This pass left both
  unchanged, and `stage`, `prove` and `run_verify` all go through `Runner.run`.
- In ci.sh, a probe that imports another probe must run in the same job as that probe, after it.
- `probes/s7/{Baseline,ForgeGate,EpsGate}.lean` are stale since S7-A5. Their S6b ports are the
  regressions that run in CI.
