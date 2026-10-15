# S6b RESULT: the harness (gate, challenges, badge executables, benchmark runner, CI)

Stage 6b builds DESIGN §3.3, §6.3–§6.5, §7.4 and §11 step 7. One agent implemented it on
2026-10-15, with the addendum of the S7 and S8 reviews (S7-M1, S7-M2, the S8 CI items) folded in.
Nothing is committed. The amendments are `S6b-A1 … S6b-A14` in `docs/DESIGN-AMENDMENTS.md`.

## Headline

- **CI** (`scripts/ci.sh`, 12 steps): **CI OK in 23 min 48 s** (1,428 s; 28 min user) on this machine, target ≤ 1 h. Breakdown in §7
  (`logs/S6b/ci-run-4.log`, step logs in `logs/S6b/ci/`).
- **Gate rule 4 (v2).** Only the badge-path fields must have compiled code (S6b-A1). Probes: 4
  positives pass (`ε := errorCap`, a noncomputable prover, a noncomputable fuel split, a board-R
  submission); 6 negatives are each rejected at exactly their field (`P.IDX`, `P.VK`, `P.verify`,
  `P.extractor.img`, `entry.decode`, `entry.C`).
- **S7-M1 (executed code ≠ proved code).** Rules 3 (`cpass`, `computed_field`), 6 (imports only
  within the organiser's import closure, 10,820 modules) and 7 (no definition uses the compiler's
  or the environment's API) are new. The S7 forgery is rejected (rule 6); the `@[cpass]` installer
  by rules 3, 6 and 7; the forgery with every allowed import does not elaborate. The residual
  (raw memory-level forgery) and the sound fix (kernel-regenerated badge code, 2–3 days) are
  S6b-A2/A3: **decision needed**.
- **Badge executables.** `verify` and `index` are built against the submission in the gate tree,
  sandboxed, from a template whose kernel-checked `rfl` theorems say the executable's `NARG` and
  `index` are the submission's (S6b-A4). On `cmpToy` with the S3 reference tapes: `verify`
  0.07 s (accepts `tape2`, the Python reference's tape byte for byte; rejects a flipped bit),
  `index` 0.10 s (digest `0f4c678b…`, `digest_kat`). Both are dominated by process start-up.
- **Finding (S6b-A5, fixed).** Every executable importing `Library/Field.lean` ran out of memory
  at start-up (a computable `Fintype K` is a closed term enumerating `2^64` elements). The two
  instances are now `noncomputable`; `harness-linkcheck` guards against a recurrence.
- **Benchmark runner** (`harness/run-benchmark.py`). End to end on `cmpToy` with the Python prover
  (64 leaves, 32 wrap and 31 node steps, root, 3 runs, 100 DoS tapes): ACCEPT in 98 s;
  `S_leaf` 0.167 s, `S_wrap` 0.168 s, `S_rec` 0.168 s, DoS max 0.17 s (prover ≈ 0.06 s, `verify`
  ≈ 0.105 s per step, sandbox included). Its rejections are CI-tested: a flipped `digestC`, a
  `digestL` of `L_chain(16)`, a bad proof, a timeout, no proof, the board-L cap, a class below 24;
  and board separation (board L rejected, R and W accepted).
- **Noise** (10 repeats, this VM, not a reference machine): `verify` median 0.108 s (min 0.099,
  max 0.123; 23 % spread), the Python prover 0.060 s (0.055–0.069; 23 %), sandboxed; without the
  sandbox 0.078 s and 0.037 s. Medians of medians move by up to 5.9 % between three evaluations,
  above the 3 % record margin on this shared VM with 0.17 s steps (O-6: re-measure on the
  reference SKU with realistic steps).
- **Decisions needed:** S6b-A3 (kernel-regenerated badge code), S6b-A9 (the leaf prover reads `s`),
  S6b-A11 (pin Clean, or Clean-free circuits), S6b-A13 (prebuild Mathlib's objects), O-6 (the
  reference SKU must have carry-less multiply).

## 1. Files

New (code lines by `scripts/loc.py` for Lean, `wc -l` for the rest):

| file | lines | what |
|---|---|---|
| `RecursionFast/Challenge/L.lean.in`, `R.lean.in` | 8 + 13 code | the board-L and board-R challenge stubs (S6b-A6) |
| `harness/lean/RecursionFastHarness/Driver.lean` | 43 code | `verifyMain`, `indexMain`, key/statement parsing |
| `harness/lean/RecursionFastHarness/Twin.lean` | 79 code | `harness_twin`: the executable twin (S6b-A4) |
| `harness/lean/RecursionFastHarness/LayoutJson.lean` | 113 code | layout JSON → `Layout K`, the renderer's checks |
| `harness/lean/Main.lean.in`, `harness/badge-main.py` | 9 code + 22 | the executables' main module and its generator |
| `harness/lean/LinkCheck.lean` | 7 code | `harness-linkcheck` (object files, start-up) |
| `harness/badge-build.sh` | 72 | the gate tree's stage 3a without comparator and gate |
| `harness/run-benchmark.py` | 612 | the benchmark runner: `run`, `secrets`, `selftest`, `record` |
| `harness/measure-noise.py` | 58 | repeated timed runs through the runner's timer and sandbox |
| `harness/smoke/` | 11 code + 85 | `RecursionFastSmoke` (NOT SECURE `cmpToy`, `keyed`), `SmokeVerify.lean`, `SmokeIndex.lean`, `toy_prover.py` |
| `harness/reference-machine.md` | — | §6.4 as the organiser's checklist; first noise measurement |
| `scripts/toy-solution.py`, `audit/` | 45 | the v2 toy comparator pair (board L, `toy20`) and its configs |
| `scripts/import-allowlist.txt` | 10,820 | gate rule 6's allowed imports (generated, checked by CI) |
| `scripts/olean-manifest.sha256` | 35,092 entries | regenerated from a clean organiser build |
| `probes/s6b/gate/` | 58 code (`GateV2`) | rule-4 probes; the S7-M1 regressions `Forge`, `Cpass`, `ForgeNoLean`; the A4 probes ported (`a4/`) |
| `probes/s6b/layout/` | — | the reader = renderer cross-check (7 layouts + a negative) |
| `probes/s6b/pipeline/`, `tests/pipeline/` | — | v0.3's cmpproj, gateproj, bindproj regressions, ported |
| `probes/s6b/AxiomAuditClean.lean` | — | axiom audit of `RecursionFast.Clean*` (739 declarations at the last run) |

Changed: `scripts/Gate.lean` (rules 3, 4, 6, 7, `--closure`; 247 → 297 code lines),
`scripts/render-challenge.py` (placeholders `hash`, `digest`, `layout`; strict JSON),
`scripts/test-render.sh` (54 malformed claims), `scripts/dummy-claim.py`, `scripts/harness.sh`
(stages 3a/3b, `--org` required, `--allowed-imports`), `scripts/ci.sh` (rewritten),
`scripts/org-build.sh` (harness driver, linkcheck, allowlist), `scripts/bwrap-landrun.sh`
(`--hide`), `harness/render-layout.py` (`layout_lean` factored out; `ChainData.lean` renders
byte-identically), `harness/check-chain.py` and `harness/CHAIN-LAYOUT.md` (ports cap `2^5`),
`harness/README.md`, `RecursionFast/Library/Field.lean` (S6b-A5), `lakefile.toml` (appended:
`RecursionFastHarness`, `harness-linkcheck`, `RecursionFastSmoke`, `smoke-verify`, `smoke-index`).

Side effect: building `harness-linkcheck` writes the object files of the organiser closure
(≈ 2,000 `.o`, Mathlib's among them) into the shared packages directory's build trees; they are
build outputs, outside the olean manifest's scope.

Untouched: `RecursionFast/Clean/`, `submissions/`, the contract (its `Certificate.lean` change is
Stage 7's, S7-A5), Stage 8's lakefile blocks.

## 2. The gate

- **Rule 4** (S6b-A1). `badgeFields` as in S6b-A1. Mechanics unchanged from v0.3: the
  environment is loaded without running any imported code, trust is by `.olean` hash, and a
  field without code as a whole is unfolded to its constructor and each badge-path field compiled
  as an auxiliary definition in the gate's process. Probe log: `logs/S6b/ci/gate-v2.log`.
- **Rules 3, 6, 7** (S6b-A2). Results on the S7 probes (`logs/S6b/ci/gate-s7.log`):

  | probe | result |
  |---|---|
  | `Forge` (S7's `ForgeGate`: `run_meta` overwrites `dec`'s emitted code) | REJECT, rule 6: `module Forge imports Lean` |
  | `Forge`, gate without `--allowed-imports` | PASS (rule 7 sees no declaration: `run_meta` leaves none) |
  | `Cpass` (`@[cpass]` installer) | REJECT: rule 3 `@[cpass] on noopInstaller`, rule 6, rule 7 |
  | `ForgeNoLean` (the forgery importing `Mathlib` and every organiser root instead of `Lean`) | does not elaborate: `Unknown identifier impureExt.getState` |
  | the v2 toy, `GateV2` positives, the baseline's imports | PASS (rules 6 and 7 hold for the library and controls) |

  - **What was measured.** The forgery changes the C that `lean -c` emits (from the LCNF
    `impureExt`), not the stored IR: `IR.findEnvDecl S7Forge.dec` still calls `toyDecide`, while
    `l_S7Forge_dec` in the `.c` calls `acceptAll`. Mathlib's whole closure (10,744 modules)
    imports neither `Lean` nor `Lean.Compiler.LCNF.PhaseExt`; it does import
    `Lean.Compiler.IR.CompilerM` and `Lean.Compiler.LCNF.Basic`.
  - **Residual** (in the gate's docstring and S6b-A2's trust statement): forgery through raw
    extension access (`persistentEnvExtensionsRef` + `unsafeCast` with re-declared types) or of
    the stored IR signatures. S6b-A3 is the sound fix; it is not implemented (estimate 2–3 days).
- **The A4 probes**, ported to v2 (`Image` without `harts`; `SkipKernel` with an in-file
  unchecked tactic instead of the dropped `Library.Tactic`): `SpoofCert`, `GateBypass`,
  `UnboundImage` (implemented_by), `HygieneBypass` (sorry, native decide, opaque, partial) rejected;
  `SkipKernel` passes the gate and is rejected by `leanchecker`, as in v0.3.

## 3. Challenges and the renderer

- L and R stubs as in S6b-A6 (with Stage 7's `Declared.img`, S7-A5). Both elaborate with a dummy
  claim; R also with `L_chain(16)` as `C` (7.8 s). The rendered literal needs
  `Mathlib.Data.Fin.VecNotation` (`![…]`), which `R.lean.in` imports.
- Renderer tests (`scripts/test-render.sh`): 3 well-formed claims accepted; 54 malformed ones
  rejected (scalars, hash menu, digests, duplicate keys, floats, NaN, image keys and sizes, 8 path
  attacks, 20 layout mutations: schema, unknown or missing keys, `row ≥ cons`, `col ≥ 2·cols+3`,
  `S ≥ t`, `|M| ≠ t`, `|c| ≠ q`, K format, booleans, bus kinds, table kinds, counts); a layout
  whose names carry `-/ … /-` renders without them; a line placeholder inside a line is rejected.
- Reader = renderer (`probes/s6b/layout/check.sh`): equal `Layout.words` on all 6 example layouts
  (787,730–792,851 words with the `add8` table, 1,490 with the trimmed ones) and the dummy; a
  rendered literal with one matrix value changed is detected.

## 4. Badge executables

- `verify VKC STMT TAPE` and `index LAYOUT.json VKC_OUT` (`harness/README.md`). Built in the gate
  tree at stage 3a, sandboxed (37 s, mostly Lake's workspace load and the link of a 142 MB
  executable), after which the 2 bound artifacts of the toy are checked unchanged.
- Smoke (`cmpToy`, arity 2, built both in this tree and through `badge-build.sh`):

  | run | result | wall | peak |
  |---|---|---|---|
  | `index` on any layout | key `vkc2`, digest `0f4c678b…229556d3` (= `digest_kat`) | 0.10 s | 79 MB |
  | `verify` on `tape2` (the Python reference's honest tape of `x0`) | ACCEPT, exit 0 | 0.07 s | 78 MB |
  | `verify`, bit 0 of byte 40 flipped | REJECT, exit 1 | 0.07 s | 78 MB |
  | `verify`, a 41-byte key | exit 2 | — | — |
  | `index` of `keyed` on `L_chain(16)` / `L_chain(1024)` | `e14eb11c…` / `8e0b780b…` | 0.48 / 0.63 s | 131 MB |
  | the toy's gate-tree `verify` on a random tape | REJECT, exit 1 | 0.08 s | 75 MB |

- Start-up of an executable importing the whole organiser library: 0.07 s, 79 MB
  (`harness-linkcheck`).

## 5. The benchmark runner

- §6.3 as specified, with S6b-A8 (classes, boards), S6b-A9 (interface), S6b-A12 (measurement).
  `selftest`: the statement functions equal the kernel-checked `xN`, `xR`, `xT` (`nodeStmt_kat`,
  `treeKat`, `rootOK_xT`), reject an odd count and a wrong depth; the chain statement equals
  `gen-chain-layout.py`'s for n = 1, 4; the record rule.
- Smoke run (`logs/S6b/ci/bench-smoke.json`): per-step medians over 3 runs: leaves prover 0.061 s,
  verify 0.106 s; wrap 0.061 / 0.106 s; nodes 0.061 / 0.104 s; root verify 0.10 s; indexing 0.1 s
  per layout; whole evaluation 98 s (≈ 0.17 s per process pair plus ≈ 0.09 s bookkeeping).

## 6. Reference machine and noise

`harness/reference-machine.md` holds the per-season checklist (SKU with carry-less multiply,
frequency policy, memory cgroup, storage, OS, glibc, Lean, gcc/clang, Rust, Python, bubblewrap,
THP/ASLR/swap, isolation), the timed-region definition, the record rule (`is_record`: at most
0.97 × the standing record) and the re-run policy, and the first measurement:

| process (10 repetitions) | median | min | max | spread |
|---|---|---|---|---|
| `verify`, sandboxed | 0.108 s | 0.099 s | 0.123 s | 23 % |
| `verify`, no sandbox | 0.078 s | 0.074 s | 0.084 s | 13 % |
| Python prover, sandboxed | 0.060 s | 0.055 s | 0.069 s | 23 % |
| Python prover, no sandbox | 0.037 s | 0.032 s | 0.041 s | 25 % |

Three smoke evaluations: `S_leaf` 0.1695 / 0.1674 / 0.1719 s (2.7 %), `S_wrap` 0.1638 / 0.1682 /
0.1735 s (5.9 %), `S_rec` 0.1709 / 0.1679 / 0.1710 s (1.8 %). This VM exposes neither
`pclmulqdq` nor `gfni`.

## 7. CI

| step | what | time |
|---|---|---:|
| 1 | vendored Rv64 byte-identical, hygiene lint | 3 s |
| 2 | organiser build (warm; cold ≈ 5 min, plus ≈ 1.5 min once for the linkcheck's object files) | 19 s |
| 3 | olean manifest (35,092 files), import allowlist current | 11 s |
| 4 | axiom audit (organiser), contract line count (669 code lines) | 7 s |
| 5 | BLAKE2s vs hashlib (8,432 cases), `check-chain.py` at n = 16 (0 survivors of 244 mutations, 8 mutants), runner self-test | 121 s |
| 6 | 54 malformed claims rejected; L, R, Rchain stubs elaborate; reader = renderer on 7 layouts + negative | 93 s |
| 7 | toy harness: comparator (Lean kernel + nanoda) 182 s, gate, badge build ≈ 40 s; `--bench` plumbing (REJECT by the 5 s indexing budget) ≈ 150 s; negative toy (comparator 115 s) | 589 s |
| 8 | gate probes: A4 ports, v2 rule 4 (4 positives, 6 negatives), S7-M1 (Forge, Cpass, ForgeNoLean) | 268 s |
| 9 | pipeline regressions cmpproj, gateproj, bindproj | 111 s |
| 10 | smoke: 2 sandboxed badge builds (≈ 37 s each), the full benchmark run (100 s), 9 runner rejections/separation checks | 184 s |
| 11 | Clean: setup + `lake build RecursionFastClean` (warm), axiom audit of 739 `RecursionFast.Clean*` declarations | 11 s |
| 12 | manifest re-check | 11 s |

Where the time goes: three comparator runs in step 7 (≈ 7 min) and the gate's environment loads
in step 8 (≈ 15 s each, 14 runs). The final smoke evaluation: `S_leaf` 0.1726 s, `S_wrap`
0.1753 s, `S_rec` 0.1740 s, DoS max 0.168 s (`logs/S6b/ci/bench-smoke.json`). The default
`lake build` stays green.

## 8. Deviations from the design and the brief

1. **Badge-path fields** include `n`, `shape`, `vkLen`, `idxShape` (S6b-A1).
2. **The smoke protocol is not a `Submission`** (S6b-A10): no `sorry`.
3. **The executables run the twin**, not `S.P` directly (S6b-A4), with kernel-checked equality.
4. **`Library/Field.lean` changed** (S6b-A5), outside this stage's files, to make any executable
   start.
5. **The leaf prover reads `s`**, not the tables, by default (S6b-A9; proposal).
6. **S7-M1 option (c) not implemented** (S6b-A3); (a) and (b) are.
7. **Badge-path code outside the organiser's import closure** needs prebuilt objects (S6b-A13).

## 9. Open questions for the orchestrator

1. S6b-A3: adopt kernel-regenerated badge code (Stage 6c), or accept the residual of S6b-A2.
2. S6b-A9: `s` as the leaf prover's witness.
3. S6b-A11: pin Clean in the manifest and the allowlist, or Clean-free board-R circuits.
4. S6b-A13: prebuild all of Mathlib's object files on the reference machine.
5. O-6: the reference SKU (carry-less multiply), toolchain pins, and the noise on it.
6. A board R run with `tree.leaves = 2` has no level-2 step (`S_rec` undefined) but is accepted;
   only test configurations use it.

## 10. Review addendum (S7 and S8 reviews, folded into this stage)

| item | done | where |
|---|---|---|
| S7-M1 (a): rule 3 scans `cpass` and every compiler attribute | `cpass`, `computed_field` added; the docstring enumerates Lean 4.34's attributes with an effect on compiled code and the allowed ones | `scripts/Gate.lean`, S6b-A2 |
| S7-M1 (b): no reach into the compiler; exact allowed imports | rule 6 (imports within `scripts/import-allowlist.txt`: Mathlib, contract, library, controls, own modules) and rule 7 (no definition uses the compiler/environment API) | S6b-A2 |
| S7-M1 (c): kernel-regenerated badge code | not implemented; design, obstacles (linked initialisers, `brecOn`, inductives, manual link) and estimate (2–3 days) | S6b-A3 |
| S7-M1: the probes as CI regressions | `probes/s6b/gate/{Forge,Cpass,ForgeNoLean}.lean`, CI step 8 (copies of `probes/s7/`, updated to `Declared.img`) | CI step 8 |
| S7-M1: trust statement for DESIGN §8 | in S6b-A2 | `docs/DESIGN-AMENDMENTS.md` |
| S7-M2: leaf board `{2^8, 2^10}` at class 24, `2^12` only at `k ≥ 26`, early class rejection, separate boards | runner config `k`, `classes`; per-board verdicts; CI checks a class below 24 and board separation | `harness/run-benchmark.py`, S6b-A8 |
| S7-M2: the baseline prover README | the interface is S6b-A9 (mode last; `vkc.bin`, `stmt.bin`, `secret.hex`, `layout.json`; node inputs) | S6b-A9 |
| S8: `setup-clean.sh && lake build RecursionFastClean` + axiom audit of `RecursionFast.Clean*` | CI step 11 (11 s warm) | `probes/s6b/AxiomAuditClean.lean` |
| S8: regenerate the manifest | `scripts/olean-manifest.sha256` from the organiser build after the Stage 6b/7/8 changes (35,092 entries; CI steps 3 and 12 pass) | |
| S8: `harness.sh` default `--org` | `--org` is now required | `scripts/harness.sh`, S6b-A14 |
| S8: `check-chain.py:201`, `CHAIN-LAYOUT.md` ports cap | `2 ** 5`; the CHAIN-LAYOUT paragraph says the two-row split is no longer forced | |
| S8: the lakefile comments match `org-build.sh`'s drop set | `RecursionFastSmoke`, `smoke-verify`, `smoke-index` say "dropped by org-build.sh" | `lakefile.toml` |
| found on the way | Clean registers `[init]` entries, so the gate rejects any submission importing it until Clean is pinned | S6b-A11 |

## Decision pass

Applied on 2026-10-15 (amendments `S6b-A15 … S6b-A19`); no commit; `docs/DESIGN.md` untouched.

1. **S6b-A3 → O-12, deferred** (S6b-A15): the open-item text is in the amendments; rules 3, 6, 7,
   8 and S6b-A2's trust statement are the current guarantee (`scripts/Gate.lean`'s docstring says
   so).
2. **S6b-A9 → the leaf prover reads `s`** (S6b-A16): `harness/run-benchmark.py` gives the leaf
   step `layout.json`, `vkc.bin`, `stmt.bin`, `secret.hex` and no witness file (the
   `"witness": "full"` option is gone); witness generation happens inside the timed region.
   `harness/README.md`, "Prover interface", is the reference; the baseline README should follow it.
3. **S6b-A11 → Clean for circuit proofs, never on the badge path** (S6b-A17).
   - **Finding.** Clean's closure (4,708 modules) contains `Lean` and
     `Lean.Compiler.LCNF.PhaseExt`; the S7 forgery elaborates through `import RecursionFast.Clean`
     and its emitted `dec` calls `acceptAll` (`probes/s6b/gate/ForgeClean.lean`). Listing Clean's
     closure in `import-allowlist.txt` would have reopened S7-M1 for every submission, so only
     Clean's own 39 modules and the 6 bridge modules are allowed direct imports
     (`scripts/import-frontend.txt`), and two rules keep them off the badge path.
   - **Rule 8** (`--badge-root`): the executables import only the badge root's module (L:
     `submission`; R: the new `leaf`), whose closure must stay compiler-free; the harness builds
     the mains from the module the gate prints. **Rule 9**: no badge-path field calls Clean code.
     The R stub has `leaf` and `submission.toSubmission = leaf`.
   - **Hash-pinned.** The organiser package builds `Clean` and `RecursionFastClean`; the manifest
     has 130 `packages/Clean/` entries (35,222 in all); Clean's `[init]` entries are reported, not
     rejected.
   - **Probes** (CI step 8, `logs/S6b/ci/gate-clean.log`): circuit proofs importing Clean, `leaf`
     in a Clean-free module: PASS (badge root module `GClean.Core`); `decode` calling
     `FiniteField.val`: REJECT (rule 9, `[RecursionFast.K.instFiniteField, FiniteField.val]`); a
     badge root declared in a Clean-importing module: REJECT (rule 8, 560 modules outside the
     closure); `ForgeClean` as a badge root: REJECT (rule 8).
4. **S6b-A13 → prebuild all of Mathlib's objects** (S6b-A18): `(cd ORG && lake build
   mathlib/Mathlib:static)`, measured 3 min 35 s wall and 29 min CPU here for the ≈ 5,000 objects
   the organiser build had not made (298 MB archive, 974 MB of objects); documented in
   `harness/reference-machine.md` §2.
5. **O-6** (S6b-A19): `harness/reference-machine.md` requires carry-less multiply (`pclmulqdq`;
   Zbc on RISC-V) and keeps this machine's noise figures (§5) as the placeholder.

CI after the decision pass: **CI OK in 25 min 52 s** (1,552 s; `logs/S6b/ci-run-5.log`): +2 min against the previous run, from step 8's Clean probes (379 s, was 268 s) and the organiser build of Clean (step 2: 27 s warm). The toy harness reports `gate: badge-root-module ToySolution`; the default `lake build` is unaffected.

## Fix pass (the S6b review, `docs/reviews/S6b-review.md`)

The amendments are S6b-A20 … S6b-A26 (`docs/DESIGN-AMENDMENTS.md`, "Stage 6b fix pass"). Nothing
is committed. **One file outside this stage's area was edited:** `submissions/baseline/prover/README.md`
(S6b-m4), as the fix-pass instruction allowed.

| finding | fix | CI regression (quoted from `logs/S6b/ci-run-8.log`) |
|---|---|---|
| **S6b-M1** the runner's sandbox is optional | `run` fails closed: it rejects without an executable `sandbox` and a working `systemd-run --user --scope -p MemoryMax=… -p OOMPolicy=continue`; `harness.sh` stage 3b sets `sandbox` to its own landrun (S6b-A21) | "runner rejects no-sandbox: no sandbox: the config's "sandbox" must name scripts/bwrap-landrun.sh (got None); the runner does not run unsandboxed steps (S6b-M1)" |
| **S6b-M2** `layouts.C` unpinned; **m2** `k`; **m5** `arity` | `--bench` requires `--claim` and `--stub`. The harness re-renders the stub with its own copy of the claim and requires the challenge to be that rendering byte for byte. It then writes `k`, `cfg = {"hash"}`, the claim's digests and `layouts.C` from the claim. The runner's `cfg` takes only `hash` (S6b-A22). | "harness rejects a claim that does not render the challenge (S6b-M2): HARNESS: REJECT (the challenge is not the rendering of the stub with the claim)"; "runner rejects layout-mismatch: board R: declared digestC 'e14eb11c…' differs from the indexer's 2fd15909… (S5-A13)" |
| **S6b-M3** badge code forgeable through Mathlib's `Lean` | The source rule `scripts/source-rule.py` runs in each fresh tree before the build. Gate rule 6t makes rule 6 transitive. The probes are `ForgeRaw.lean`/`UseRaw.lean`: Mathlib-only imports, `run_meta` and `persistentEnvExtensionsRef` + `unsafeCast`. The trust statement now says O-12 is the sound fix (S6b-A20). | "harness rejects ForgeRaw by the source rule before any build (S6b-M3): 19: open Lean 29: run_meta 30: persistentEnvExtensionsRef.get 33: unsafe 33: unsafeCast"; "S6b-M3 ForgeRaw: forges its importer's code (useDec = msg == msg); the gate PASSES it (rules 1-9 cannot see a run_meta); only the source rule rejects it"; "source rule: 52 rejected forms reported, each on its line; the allowed forms pass" |
| **S6b-m1** the memory cap is per process | Each step runs in its own cgroup: `MemoryMax`, `MemorySwapMax=0`, `OOMPolicy=continue`. An organiser shell outside the sandbox records `memory.peak`, `oom_kill` and the wall time. Any `oom_kill` rejects (S6b-A23). | "runner rejects memory-cap: run 0 leaf 0 (n = 16): killed at the memory cap of 150000 KB (cgroup MemoryMax, 1 oom_kill, exit 137)" (a 300 MB prover under a 150 MB cap) |
| **S6b-m3** the whole filesystem is readable | `bwrap-landrun.sh --minimal-root` makes readable only `/usr`, `/etc`, a fresh `/tmp`, the executables' directories, the prover's argv files and `sandbox_ro` (S6b-A24) | "runner: a step cannot read the repository (minimal sandbox root, S6b-m3); the run is accepted" (a prover that exits 7 if it can read `CLAUDE.md`) |
| **S6b-m4** the baseline prover README is stale | Its Interface section states the S6b-A9/A16 interface (S6b-A25) | (documentation) |
| rule 4's `Fin`-family branch (simplify note) | Documented, behaviour kept: such a shape fails at stage 3a, one stage later, and is never accepted (S6b-A26) | (CI steps 7, 10: every shape in the repository passes both) |

Findings made during the fix pass:

1. **systemd stops the scope on an OOM kill.** CI run 6 failed: "no measurement from the step's
   cgroup (exit -15)". Under the scope's default `OOMPolicy=stop`, the kernel's OOM kill makes systemd
   stop the whole scope, so the organiser shell receives SIGTERM before it writes anything.
   Reproduced by hand: exit 143 under the default; exit 137 and `oom_kill 1` with
   `OOMPolicy=continue`. Fix: pass `-p OOMPolicy=continue` (the preflight checks it too) and reject
   on the cgroup's `oom_kill` count, whatever the exit code.
2. **The first source rule rejected `#[…]` and `#v[…]`.** It reported 26 false findings in
   `RecursionFast/Clean/`, which uses Clean's `#v[…]` throughout. Fixed: the two literals are
   allowed, as is a `#` not followed by a letter. Mathlib's `#s` is rejected; write `s.card`.
3. **Keywords the first source rule missed.** A sweep of the keywords of Lean v4.34.1 and
   Mathlib's package closure found code-running syntax the first list missed: Qq's `by_elabq`
   (a term) and `run_tacq`, and Mathlib's `run_conv`. These are now rejected, together with every
   word starting `run_`, `import Qq`/`open Qq`, `open _root_.Lean…`, and the simproc commands (rule 7
   rejects those too).
4. **Fixture test for the source rule.** `tests/source-rule/check.sh` (CI step 1) has one fixture
   line per rejected form (52). It checks that each is reported on its own line and nowhere else,
   and that a file of allowed forms has no finding. The check has a negative control: with one
   marker removed, it fails. RecursionFast/Clean (5 files), the baseline (8 files), the toy, GateV2
   and GClean have no findings.
5. **`measure-noise.py` under the minimal root.** A relative `--sandbox` path failed (exit 127),
   and the prover's script was not readable (exit 2). It now resolves the path and passes the
   prover's whole argv.

The cost of the sandbox and the cgroup was re-measured (`logs/S6b/noise-*-fixpass.json`, 10
repetitions, `harness/reference-machine.md` §5):

- `verify`, sandboxed: median 0.156 s, against 0.108 s before the fix pass.
- `verify`, unsandboxed: 0.084 s.
- The Python prover, sandboxed: 0.095 s, against 0.060 s.

So the sandbox and the cgroup add about 0.07 s per process; it was 0.03 s. The smoke benchmark's
`S_leaf`/`S_wrap`/`S_rec` are 0.267/0.262/0.268 s (`logs/S6b/ci/bench-smoke.json`), against
0.167 s before the fix pass.

CI after the fix pass: **CI OK in 11 min 47 s** (707 s; `logs/S6b/ci-run-8.log`; run 7, without
the fixture step, took 11 min 48 s). That is 14 min less than the decision pass's 25 min 52 s,
mostly from the simplify pass's concurrent phases. The default `lake build` is green (2,490 jobs).

## S9 fix pass (the S9 reviews' harness items)

Sources: `docs/reviews/S9-definitions.md`, `S9-incentives.md` and `S9-feasibility.md`. The
amendments are S9-A30 … S9-A44 in `docs/DESIGN-AMENDMENTS.md` ("Stage 9 harness fix pass").
Nothing is committed. Other agents edited `Contract/`, `Library/` and `Bridge/` at the same time;
I touched none of those. The only Lean I changed is the KAT `xNK` with its theorem
(`Controls/RecursionData.lean`, `Controls/Recursion.lean`) and the harness driver
(`harness/lean/`).

| finding | fix | CI evidence (`logs/S9/ci-harness-1.log`) |
|---|---|---|
| **S9D-M1** the source rule's lexer diverges from Lean's | `scripts/source-rule.py` has two nets. Net 1 is a Lean lexer (raw strings only for `r#…"`, every string read both plainly and as an interpolation, nested comments, character literals) that **fails closed** on anything open at the end of the file and on a string whose end depends on interpolation. Net 2 is a raw word scan. The keywords are exact (Library names such as `run_mono` stay usable). A keyword sweep over the closure's token table runs in CI. Trust statement corrected (S9-A30). | "source rule: 95 rejected forms reported exactly (bad/: by each net alone; …), 4 forgeries (S9 bypasses, ForgeRaw) caught by each net alone; the allowed forms pass"; "sweep: 418 keyword tokens: 159 rejected by the source rule, 259 reviewed, 0 unreviewed"; "harness rejects ForgeRawR by the source rule before any build: 25: open Lean 35: run_meta 36: persistentEnvExtensionsRef.get 39: unsafe 39: unsafeCast" |
| **S9F-M1** `RecursionFast/Bridge/` breaks clones | `org-build.sh` makes a missing source directory an empty one (a library's `globs` needs it; deleting it failed, measured). The directory is now tracked through the ArkLib port (S9-A4). | the fresh clone, below |
| **S9F-M2** the manifest is machine state | `olean-manifest.py gen --closure` covers exactly the trusted closure (allowlist plus the whole frontend closure; `check` scoped to the manifest's modules). Regenerated: 34,512 entries, down from 35,222; exactly the reviewer's 710 out-of-closure files are gone. CI step 3 regenerates it and requires equality. | "olean manifest = the trusted closure: 34512 files of the import allowlist and the frontend closure (S9F-M2)" |
| `harness.sh` comparator default | `scripts/tools.env` holds one default, shared with `ci.sh`, with pins and build commands. Without a built comparator the harness stops with a message naming `COMPARATOR_HOME` (CLAUDE.md text: S9-A43). | the fresh clone's baseline check, below |
| **S9I-M1** board L is won by recomputing the chain | L (and W) are `"ranked": false`; R is the only ranked board. | "result: board R ranked, … L, W unranked" |
| **S9I-M2** level 2 decides the `S_rec` median | `S_rec` = max over the level groups 2, 3, 4–6 of the median step time; per-level medians are published. | "S_rec = max of the level groups {'2': 0.2659…, '3': 0.2667…, '4+': 0.2631…} = 0.2667 s" |
| **S9I-M3** the record rule does not separate noise | `record` only screens (result files; same season and hardware id; different entries). `compare` confirms in one session: shared fresh instances, ABBA interleaving, 5 pairs, median ratio ≤ 0.97. `compare --calibrate` gives σ and the pairs needed; the sybil limit is in reference-machine.md §4. | "compare: faster challenger: RECORD: median ratio 0.454…"; "slower challenger: NOT A RECORD: median ratio 2.138…"; "--calibrate (self-pairs): CALIBRATED: … sigma 0.047…, pairs needed 35"; "record refuses: … the same entry …; … differ in config_sha256" |
| **S9I-m3** no wrong proof is ever verified | Canaries for 8 proofs per kind and run: a byte appended, a byte removed, a statement bit flipped, the other key. DoS tapes also go under the recursion key. | "225 canaries rejected; DoS {'leaf key': 50, 'recursion key': 50}"; "runner rejects accept-all: … the verifier ACCEPTED a canary (one byte appended; S9I-m3)" |
| **S9I-m4** secrets from a file | The runner draws the secrets from `os.urandom` per evaluation; `--secrets` is refused. | "harness refuses --secrets (S9I-m4)" |
| **S9I-m5** a result does not say what it was measured under | `config_sha256`, `hardware_id`, `machine` (with `has_clmul`), `entry` (hashes of `verify`, `index`, the prover's argv and files, the claim, `C`'s layout) and `entry_id`. | the result's checks (`entry a68b…`) |
| **S9D-m2** the selftest is blind to a `d0`/`d1` swap | Kernel KAT `nodeStmt_kat_keys` with two keys (`xNK`). The selftest checks it and that a swap differs. | "selftest: nodeStmt_kat_keys (xNK …): OK", "a d0/d1 swap is caught: OK"; a swapped `node_stmt` fails the selftest, while the S6b selftest passed it (by hand) |
| **S9D-m4** the recursion key comes from a second reader | The harness renders the claim's `C` with the challenge renderer into `harness-index` (`--certified-c`); the runner indexes it (`--certified-C`, `index_C = certified`). | "runner (index_C = certified, S9D-m4): the recursion key is the certified C's (e14eb11c… = the layout file's), whatever layouts.C says (here chain-n1)" |
| **S9F-M5** caps that cannot be met together | The per-step caps are kept; the whole-evaluation cap is derived from them (`budget` in the result; 73 h at the defaults). `budgets.eval_s` is refused. S9F-M4: the 1 h indexing cap stays. | "derived budget 207682 s" (the CI smoke configuration) |

Findings made during the fix pass:

1. **Prefixes were too broad.** The first S9 lexer rejected every `run_…` word. The organiser's
   Library has `run_mono`, `run_length` and `run_firstMsgImage…` (the baseline cites them in
   docstrings). The keywords are now exact words, checked against the closure's token table.
2. **More code-running keywords.** The sweep found and banned `test_extern`, `compile_inductive%`,
   `compile_def%`, `leading_parser`/`trailing_parser`, `elab_stx_quot`, `grind_propagator`,
   `set_library_suggestions` (it defines a `meta def` run by `grind`), Mathlib's `sudo` and
   `idbg`. The rest of the closure's 418 keywords are reviewed in
   `tests/source-rule/reviewed-tokens.txt`. The token table does not hold scoped or non-reserved
   keywords (`by_elabq`, `run_tacq`, `run_tac`), so those come from grepping the syntax
   declarations: a residual.
3. **Fail-closed costs.** Rejected are: a string inside `{…}` of an interpolation (also a legitimate
   nested `s!`), an unbalanced `{` in a plain string, Mathlib's `#s`, and a rejected word in a
   comment. Clean's `#v[…]` and `#[…]` are fine. The baseline (8 files) and the toy have no
   finding. `RecursionFast/Clean/Examples.lean` (organiser code, never scanned) has one comment
   word.
4. **`compare` identity and order.** Entry identity first ignored the prover's argv: two configs
   differing only in `--spin` were "the same entry", which a dev-clone CI run caught. Runs are now
   interleaved ABBA. Self-pairs of the smoke protocol here give σ ≈ 4.7–8 % per pair, so a 3 %
   margin would need 35–110 pairs on this shared VM with 0.27 s steps. The calibration procedure
   is doing its job; O-6 must calibrate on the reference SKU with realistic steps.
5. **The old manifest broke clones.** In a dev clone of HEAD (S6b state), `olean-manifest.py check`
   fails on the committed manifest: "missing packages/Clean/Clean/Gadgets/Addition8/Theorems…, FAIL
   (12 differences in 35222 entries)", the reviewer's S9F-M2 observation. The closure manifest
   regenerated there differs from this tree's only in the 5 `Contract` files that the contract
   cleanup changed.

Timings:

- Main CI: **CI OK in 15 min 0 s** (900 s; `logs/S9/ci-harness-1.log`). That is +3 min 13 s over
  the S6b fix pass's 11 min 47 s: step 10 adds canaries, three `compare` sessions and the
  certified-C runs (from 4 min to 7 min 16 s); step 6 adds the sweep (21 s, concurrent).
- Dev-clone CI (HEAD plus only my changes): 12 min 51 s, failing only at the `compare` identity
  bug since fixed.
- Default `lake build`: green in the main tree and in the clones.

**Fresh clone** (S9F; the reviewer's procedure, `logs/S9/fresh/`, driver `logs/S9/fresh/fresh-clone.sh`):
`git clone` of HEAD plus this working tree's changes and untracked files (55 paths, 10:21). Then
`scripts/setup-clean.sh <local ext/Clean>` (offline) and the packages symlink. No environment
override: `COMPARATOR_HOME` and `COMPARATOR_NANODA` were unset and came from `scripts/tools.env`.
**No workaround.**

| step | result | wall (CPU) |
|---|---|---|
| default `lake build`, cold | OK, 2,490 jobs | 5 min 03 s (695 s user), peak 9.1 GB |
| `lake build` again | OK | 4 s |
| `scripts/ci.sh` | **CI OK** (1,304 s by CI's clock) | 21 min 44 s (4,394 s user) |
| ↳ step 2, organiser build | OK, cold, Clean's cone included | 5 min 26 s |
| ↳ step 3, manifest | OK: 34,512 files match; equals the closure | 8 s |
| ↳ step 10, timed benchmark and rejections | OK | 7 min 14 s |
| ↳ step 11, Clean frontend | OK, cold in the clone's root tree | 1 min 59 s |
| `HARNESS=1 ORG=… MANIFEST=scripts/olean-manifest.sha256 submissions/baseline/scripts/check.sh` | **CHECK OK**, HARNESS: ACCEPT | 5 min 54 s; harness 268 s (comparator 195 s; gate: 3,639 modules, 3,596 trusted and 29 pinned by hash, PASS) |

Before this pass the same procedure failed at CI step 2 (Bridge), then at step 3 (12 Clean
files), and the baseline check failed on `COMPARATOR_HOME`.
