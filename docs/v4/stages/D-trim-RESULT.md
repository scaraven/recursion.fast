# Stage D-trim (v4, SROM): cutting the fat — RESULT

Status (2026-10-26): **done, not yet reviewed.** The user's decisions V4-A9 (`docs/v4/BRIEF.md`
§5b), items 1–11, implemented on the branch `v4/trim-fat` (worktree
`/home/devops/Verified-zkEVM/recursion.fast-v4-trim`, from `v4/srom-rules` at `01a25b0`),
uncommitted. Everything below ran on the development VM (32 vCPU, QEMU, 62 GB); nothing ran on
GitHub. Logs are under `logs/trim/` (gitignored).

**In one paragraph.** Every evaluation job now ends within 30 minutes with its caps nested inside
(§2), the organiser's environment is built and cached per core commit by a `setup` job that never
sees the entry, and the benchmark is two parallel jobs of one run each. Liveness, the inner proofs,
the samples, the non-malleability canaries and the medians are gone; the organiser's own checks
moved to the core CI. The certificate job builds the entry once, and the comparator, the gate and
the badge read that build (item 9 landed, §5). The contract changed in two numbers:
`errorCap = 2^-120` and `completenessCap = 2^-40`, still 355 code lines. The build, the axiom
audit, every test of `ci.yml` and the end-to-end smoke pass (§4).

## 1. What was built

| File | What changed, and why |
|---|---|
| `RecursionFast/Contract/Security.lean` | `errorCap` `2^-128 → 2^-120` (item 10), `completenessCap` `2^-128 → 2^-40` (item 8); the header's arithmetic (chargeable events from 216 bits, `2^-24` at `2^96` queries, `2^-56` at `2^64`) and the two reasons |
| `RecursionFast/Contract/Certificate.lean` | the `cap` docstring: `ε ≤ 2^-120`, `δ ≤ 2^-40` |
| `RecursionFast/Controls/Completeness.lean` | `grind128_complete`/`grind127_not_complete` re-instanced as `grind40_complete`/`grind39_not_complete` |
| `RecursionFast/Controls/Potential.lean` | the negatives re-instanced for `2^-120` (§3) |
| `scripts/speed/Extract.lean` (new), `scripts/speed/lakefile.toml` | the core CI's test of the compiled extractor interpreter on the library's witness-sending entry (item 4) |
| `harness/season.toml`, `harness/smoke.toml` | new caps, `[certificate]`, `[canaries]`, `M = 256`, DoS 100, no repeats, samples or liveness |
| `harness/rfh/bench.py` | one tree run (root only) and one stream run; statement canaries on the root and the first 2 leaf and node stream outputs; the stream's `stream_s` a hard deadline over requests and checks; DoS fails on time and crashes only, accepts recorded; score from single runs |
| `harness/rfh/checks.py` | per-entry canaries are the statement canaries only; `liveness` gone; `BadgeError` says `timeout`, `crash` or `slow`; chain-checker timeout 120 s |
| `harness/rfh/prover.py` | a stream request takes the stream's deadline |
| `harness/rfh/service.py` | no logging mode |
| `harness/run-benchmark.py`, `harness/aggregate.py` | parts `calibrate,tree,dos` and `calibrate,stream`; no repeats; single-run score |
| `harness/evaluate.py` | the one build before the comparator, the binding by unchanged artifacts, per-step caps from `[certificate]`, no liveness badge, `PART_S` = 28 min, organiser commands 300 s; a missing comparator is a harness ERROR |
| `harness/badge/Liveness.lean.in` (deleted), `harness/badge/Common.lean.in` | no liveness badge, no log parser |
| `harness/org-setup.sh` | step timeouts summing to 1,020 s |
| `harness/ci/build-kernels.sh` | keeps a checkout at its pin; `--env-only` for the certificate job |
| `harness/lean-tools/Gate.lean` | comments only: no badge runs `P` or `ext` any more (rule 4 unchanged, §7) |
| `harness/toy-prover/toy.c` | comment only (its inner proofs are ignored); `prover.s` unchanged |
| `service/src/main.rs`, `service/src/lib.rs`, `service/PROTOCOL.md` | the `--log` liveness mode removed (item 4: nothing uses it) |
| `.github/workflows/evaluate.yml` | `setup` job and per-commit caches; every job ≤ 30 min; two benchmark jobs; no repeats |
| `.github/workflows/ci.yml` | every job ≤ 30 min with nested step timeouts; the extractor test; the organiser's canaries (`accprobe`) |
| `harness/ci-template/evaluate-entry.yml` | job limits; the `split` description |
| `tests/harness/canaries.py` (new) | the organiser's canaries, core CI only (item 5b) |
| `tests/harness/accprobe/run.py` | asserts: the file accepted, all 7 organiser canaries rejected, on a `2^16`-query trace |
| `tests/harness/smoke.py` | single runs; statement-canary counts; the organiser's canaries on the ws root and a stream leaf |
| `tests/harness/test_aggregate.py`, `test_dos.py`, `test_tv.py` | the two-part plan and single-run score; DoS fails on time and crashes only; the new `Bench.verify` |
| `tests/harness/mock_badge/liveness` (deleted), `tests/service/test_service.py` | liveness and the log test gone |
| `docs/DESIGN-v4-srom.md` | §0, §1.4, §2.1–2.8, §3.1 (setup job; the separation principle), §3.2, §3.4 (steps; the nesting arithmetic), §3.5, §3.6 (parameters; the tail at `M = 256`), §3.7, §4.3, **§4.4 What each rule is for**, §5, §6.1–6.3, §7 |
| `docs/v4/BRIEF.md` | §5b, amendment V4-A9, items 1–11 |
| `docs/v4/CHECKS.md`, `README.md`, `docs/README.md`, `CLAUDE.md`, `harness/PROVER.md` | where they stated what changed |

`harness/FORMAT.md` is unchanged: nothing in it states the inner proofs, the samples or the
removed checks.

## 2. The limits (as amended by the fix pass, §9)

| Limit | Old | New |
|---|---|---|
| GitHub job | certificate, benchmark 360 min; ci `lean`, `smoke` 300, `harness` 120, `service` 60; attest 30; template jobs none | every job 30 min; `plan`, `attest` and the template's `select`, `report` 10 |
| entry Lean build | 3,600 s (`--timeout`, shared) | `build_s` 600 s |
| comparator (exports and kernel) | 3,600 s | `kernel_s` 600 s |
| gate | 3,600 s | `gate_s` 120 s |
| badge build | 3,600 s | `badge_s` 180 s |
| organiser command in `evaluate.py` | 3,600 s | 300 s |
| benchmark part (`evaluate.py bench`) | 24 h | `PART_S` 1,680 s (28 min) |
| prover build, prover setup | 3,600 s, 3,600 s | 300 s, 300 s |
| tree run | 3,600 s | 600 s |
| stream request (`step_s`; also the wait for `ready`) | 600 s | 60 s |
| the stream | 14,400 s, tested at each link's start | 960 s of wall time (900 s for the entry, 60 s for the organiser's overhead inside it), a deadline over every request, check and canary |
| one `acc` check (`verify_s`) | 60 s | 10 s; a badge batch `verify_s · n + 30 s` |
| DoS column | 1,800 s; 10 × `T_V` per input | 180 s; 10 × `T_V` per input |
| chain checker run, service throughput probe | 3,600 s, 600 s | 120 s, 60 s |
| `org-setup.sh` steps | 7,200 + 1,800 + 1,800 + 1,800 + 7,200 + 1,800 s; outer 14,400 s | 300 + 60 + 90 + 90 + 540 = 1,080 s for steps 1–4 (outer 1,080 s, `setup`; the service is `setup-tools`'), + 120 s for the service in `ci.yml` (outer 540 s) |
| `lake exe cache get`; `build-kernels.sh` (inner) | 3,600 s; 5,400 s (evaluation), 3,600 s (ci); inner 600 + 600 s, nanoda 900 s | 240 s (setup), 300 s (ci); outer 240 s (540 s with nanoda); inner 120 + 60 s, nanoda 300 s |

**Nesting per job** (season 1; design §3.4 has the table):

- **setup** (no entry code): on a cold miss, an earlier commit's cache, `lake exe cache get`
  ≤ 240 s, `org-setup.sh` steps 1–4 ≤ 1,080 s, the save and its check: 22 min of timeouts and
  about 3 min of transfers (**estimate**), about 25 of 30 min. **Measured** on a runner (CI run
  39966237935, the package tree cached): `cache get` 39 s, `org-setup.sh` 237 s
  (`logs/trim/ci-39966237935-lean.log`); cold (CI run 39935079265, before CompPoly and
  `Mathlib.Tactic` joined): 139 s and 270 s, of which the objects 191 s
  (`logs/trim/ci-39935079265-lean.log`); the `Mathlib.Tactic` objects 221 s on 4 cores of the
  development VM (`logs/trim-fix/objects-mathlib-tactic-4cores.log`). On a hit it does nothing.
- **setup-tools** (no entry code): the comparator ≤ 240 s (14 s **measured**), the service ≤ 120 s,
  two small saves: about 6 min.
- **certificate**: build 600 + kernel 600 + gate 120 + badge 180 = 1,500 s (25 min) capped by the
  entry; fixed steps about 3 min, itemised in design §3.4 (runner setup 8 s, elan 1 s and the
  toolchain 29 s **measured**; two manifest checks at 15.5 s each warm on 4 cores **measured**,
  allowed 40 s cold; the two restores about 45 s, **estimate**): 28 of 30 min.
- **benchmark, tree**: prover build 300 + setup 300 + tree 600 + root check ≤ 150 (up to three
  badge runs of `2 · verify_s + 30` s) + its canary ≤ 40 + DoS 180 = 1,570 s (26.2 min); the
  organiser's steps under 30 s: 26.7 min inside `PART_S` = 28 min, inside 30.
- **benchmark, stream**: prover build 300 + setup 300 + the stream 960 = 1,560 s (26 min); the
  organiser's steps under 30 s: 26.5 min inside 28, inside 30.
- **`ci.yml`**: step timeouts sum to 26 min (`lean`), 22 (`service`), 23 (`harness`), 26 (`smoke`)
  against measured jobs of 7.5, 1.6, 1.4 and 9.3 min (`logs/trim-fix/yaml-parse.log` sums them).

The binding: each cap's breach is the entry's REJECT with the cap named (a kernel over its cap is
"unchecked", PROVISIONAL, Q12); the organiser's steps are outside the caps and a breach of the job
by them is an ERROR, as before.

## 3. The contract and the controls

**Contract diff, in words.** Two values: `errorCap := (2 : ℝ≥0)⁻¹ ^ 120` (was `^ 128`) and
`completenessCap := (2 : ℝ≥0)⁻¹ ^ 40` (was `^ 128`); their docstrings; `Certificate.cap`'s
docstring; the `Security.lean` header (which says v4 changed exactly these two values, the guard's
arithmetic at the new cap, and the two reasons). No definition's shape changed. **Trusted lines:
355 → 355** (`scripts/loc.py`, `logs/trim/loc.log`; budget 500). Library 1,856 code lines and 233
theorems, Controls 2,089 and 309, both unchanged in count (2,082 after the golf).

**Controls touched** (each keeps a positive and a negative; no statement of a theorem about a
definition changed, only instances tied to the cap's exponent):

| Definition | Positive | Negative | Change |
|---|---|---|---|
| `completenessCap` | `grind40_complete` (40 nonces fail with probability exactly `2^-40`) | `grind39_not_complete` | was `grind128_complete`, `grind127_not_complete`; the instance is the cap's exponent |
| `errorCap` (potential vs boolean) | `twoLucky_ks`, `collision_ks`, `v24_ks` (unchanged: `2^-192`, `2^-160`, `2^-96` ≤ or vs the cap) | `twoLucky_no_bool_kstate` (`2^-120 < 2^-96`), `collision_no_bool_kstate` (a log of `2^136 + 1` distinct answers, was `2^128 + 1`), `v24_no_bool_kstate` (`2^72 + 1` answers with distinct prefixes, still under the guard `2^96`, leave more than `2^136` bad answers; was `2^64 + 1` and `2^128`) | at `2^-120` the cap allows `2^136` bad answers per query, so the counting arguments need longer logs; each still shows what it showed |
| `errorCap` elsewhere | `Backdoor.bounded` (`1 ≤ 2^-120 · 2^256`), `error_one_no_certificate`, `errorCap_lt_one` | — | proofs unchanged, re-checked |

The Potential header's v3 remarks (the first guard `2^64`, F1's "borderline at `2^-128`") are now
marked as v3's figures, not recomputed. The baseline declares `ε = 2^-129`, within the new cap.

## 4. Checks run

| Check | Outcome | Log |
|---|---|---|
| `timeout 1800 lake build` | green, 1,264 jobs, no warning; after the cap change 48.8 s (incremental); the final build, against the shared packages under a read-only bind, 16.6 s (a comment in `Potential.lean` changed last) | `logs/trim/lake-build-errorcap.log`, `lake-build-final.log` (first build: `lake-build.log`) |
| line budget (`scripts/loc.py`, as CI) | 355 ≤ 500 | `logs/trim/loc.log` |
| axiom audit (`axiomaudit`, as CI) | PASS, 4.7 s | `logs/trim/axiom-audit.log` |
| hygiene, source-rule fixtures, token sweep | OK | `logs/trim/hygiene.log`, `token-sweep.log` |
| gate fixtures | OK, 52.6 s (a first run failed on the manifest generated before the cap change; `org-setup.sh` regenerates it, as CI does) | `logs/trim/gate-fixtures.log` |
| Lean signer against the service | 0 failures, 55.3 s | `logs/trim/test_lean_signer.log` |
| extractor interpreter (`extract`) | 4 cases, 0 failures, 0.13 s; built in 9.1 s | `logs/trim/extract-run.log`, `extract-build.log` |
| `acc` probe and the organiser's canaries | file accepted 5×, 128–138 ms; all 7 canaries rejected; 36.6 s | `logs/trim/accprobe.log` |
| service: build, `cargo test`, `test_service.py` | OK; 90 checks, 16.4 s | `logs/trim/service-build.log`, `service-cargo-test.log`, `test_service.log` |
| `test_sandbox.py` | 45 checks, 20.8 s | `logs/trim/test_sandbox.log` |
| `test_tv.py`, `test_aggregate.py`, `test_dos.py` | 6, 12, 6 checks | `logs/trim/test_tv.log`, `test_aggregate.log`, `test_dos.log` |
| `smoke.py --mock` | 10 checks, 30.2 s | `logs/trim/smoke-mock.log` |
| `smoke.py --org` (end to end, as CI's `smoke` job) | **16 checks, 4 min 30 s**, after every change but the last comment edit (earlier runs 4 min 46 s and 5 min 19 s) | `logs/trim/smoke-e2e.log` |
| `org-setup.sh` | 44–63 s | `logs/trim/org-setup.log` |
| certificate job, witness-sending entry, before and after item 9 | 2 min 2 s → 1 min 33 s (build 25 s, comparator 34 s) | `logs/trim/cert-ws-before.log`, `cert-ws-after.log` |
| `py_compile` of every touched Python file; `bash -n` | OK | `logs/trim/py-compile.log` |
| workflows | parsed (PyYAML), every job ≤ 30 min, step timeouts summed; `actionlint` is not installed | `logs/trim/yaml-parse.log` |

**How the smoke ran here.** `org-setup.sh` and the badge build write compiled objects into the
package tree; with `.lake/packages` on the shared `pkgs-local` they fail read-only (shown under a
read-only bind: EROFS, nothing written). So `org-setup.sh`, the smoke and the cap measurements ran
against a private copy, `.lake/pkgs-trim` (9.2 GB, `cp -a` of `pkgs-local`), with `.lake/packages`
pointing at it; the symlink was then restored to `pkgs-local`, and the final `lake build`, the
speed executables and the axiom audit re-ran against it under a read-only bind, writing nothing
there. Leftovers to delete (gitignored): `.lake/pkgs-trim` (9.2 GB) and `.lake/pkgs-overlay`
(33 MB, the read-only probe).

## 5. Item 9: one Lean build — landed

**The binding to keep**: the badge executes code compiled from exactly the modules the kernel
checked. The comparator (`d03acab`) runs `lake build Challenge`, exports, `lake build Solution`,
exports, and replays the exports in the kernel; its builds run in the sandbox shim with only the
tree's `.lake` writable, and nothing writes the tree after its last build. The old harness then
built the same targets again in a fresh tree and required every artifact (`.olean`, `.ir`, `.c`)
to be byte-identical; the gate and the badge used that second tree.

**Why one build keeps it.** The `.c` and `.ir` the badge compiles come from the same `lean`
processes that wrote the `.olean` files; that is the trust both schemes rest on (the source rule
excludes elaboration-time code), and a deterministic tampering would be reproduced by the rebuild
anyway, so the second build only checked determinism, which one build does not need. Now:
1. `evaluate.py` builds `+Challenge +Solution` once, in the sandbox, `.lake` the only writable path
   (`build_s`), and hashes the artifacts;
2. the comparator runs on that tree; its own `lake build` finds both targets up to date
   (`Replayed Challenge`, no `Built` line for `Solution`: `logs/trim/smoke-cert-comparator-lean.log`,
   the smoke's run; the build itself `logs/trim/smoke-cert-build.log`), exports and replays them;
3. the artifacts must be unchanged after the comparator, so the gate and the badge read exactly
   what the exports were made from; a change is a REJECT;
4. the badge build must change no entry artifact and add no entry module (as before).
No new trust: lake's up-to-date check is not relied on, since the hashes are compared. **Measured**
on the witness-sending entry: 2 min 2 s → 1 min 33 s; the baseline's rebuild was 173 s
(submissions repository, `v4/flock-baseline`, `docs/v4/flock-baseline/stages/F4-final-harness-RESULT.md`).

## 6. The separation audit (the coordinator's requirement)

| Step (where) | Subject | Outcome |
|---|---|---|
| `lake exe cache get`, `org-setup.sh` (`evaluate.yml` certificate job) | environment | **stays**, moved to the `setup` job, cached per core commit (it also builds the organiser's controls, importable by entries, and the test tools `axiomaudit`/`tokensweep`, never run in an evaluation) |
| `build-kernels.sh` (certificate job) | environment | **stays**, moved to `setup`, cached; `--env-only` in the certificate job |
| `cargo build` of the service (benchmark jobs) | environment | **stays**, moved to `setup`, cached (`rf-svc-…`) |
| `lscpu`, runner setup, the machine and toolchain record | environment, record | **stays** |
| render, source rule, module-root check, the build, comparator, gate, badge build, binding checks (`evaluate.py`) | the entry | **stays** |
| olean-manifest checks (`evaluate.py`) | the environment the entry builds against | **stays**, 2 per evaluation since the fix pass (was 4): before the build, and after the badge build, which covers every step in between |
| the byte-identical second build (`evaluate.py`) | the entry's binding | **dropped** (item 9) |
| the badge's claim-fuel check (`evaluate.py`) | duplicate of the renderer's | **dropped** with the liveness badge |
| liveness: the logging service, `ext` on the compiled interpreter (`bench.py`, badge `liveness`) | organiser code (the interpreter), the entry's extractor | **dropped**; the interpreter test **moved to `ci.yml`** (`extract`) |
| canaries `file±1`, `trace-answer`, `trace-query`, `trace-extra`, `sig-ots`, `sig-idx` (`checks.py`) | organiser code (parser, `traceDigest`, `SigOk`) | **moved to `ci.yml`**: `accprobe` (all 7, a `2^16`-query trace) and the smoke (the 5 that apply to an empty trace, on the ws root and a stream leaf) |
| canaries `pi±1` | non-malleability | **dropped** |
| canaries `stmt-bit`, `swapped-child` | the entry | **stays**, 2 proofs per kind |
| 16 inner samples, inner proofs read | the entry | **dropped** (item 7) |
| `T_triv,best` (chain checker; its root compared with the runner's) | environment, the cap | **stays** |
| service throughput calibration (`rf-bench`) | informational | **stays**: about 5 s per job, published beside the score (V4-A5) |
| tree run, root check, stream run, output checks, `T_V` re-measure, DoS, score | the entry | **stays** |
| the service's `--log` mode | organiser feature for liveness | **dropped** |
| `run-benchmark.py`'s "no calibration with `T_V` enforced" guard | harness configuration | **stays** (a guard, not a test) |

## 7. Deviations from the brief, and why

1. **The stream cap is a hard deadline**: `stream_s` now bounds every request, check and canary
   from the first request (the old test ran only at each link's start), so a stream cannot outrun
   its job. A request's `ready` wait keeps `step_s` as its own cap, as before.
2. **`PART_S` = 28 min** wraps each benchmark part as the outer bound of the organiser's own steps;
   a badge batch is allowed `verify_s` per check plus 30 s (was 60 s).
3. **`ci.yml` jobs are 30 min too**, with nested step timeouts (the brief's "every GitHub job").
4. **Smoke caps** shrank to fit (tree 120 s, stream 300 s, request 60 s, build and setup 300 s,
   `verify_s` 10 s, DoS 180 s); the smoke's DoS stays at 64 inputs and `M = 4`.
5. **The toy prover still writes inner proofs**; they are ignored. Regenerating the committed
   assembly would change 2,164 lines for nothing.
6. **A missing comparator is an ERROR**, not a REJECT whose text said "harness error".
7. **The service lost its logging mode** (−26 Rust code lines), since nothing uses it; the
   trusted runtime is **3,800 → 3,670 code lines** by stage B's groups and rule, after the golf and
   the fix pass (3,675 at the stage's commit; `logs/trim/loc-runtime-before.log`,
   `logs/trim-fix/loc-runtime-after.log`, the script `logs/trim-fix/loc_runtime.py`; the design's
   old 3,559 predates stage B's final fix pass).
8. **Gate rule 4 unchanged**: it still requires `P` and `ext` compiled although no badge runs them
   (comments corrected); relaxing it is the user's (§8).
9. **The certificate caps live in the season file** (`[certificate]`), read by `evaluate.py cert
   --season`, so the rule is stated where the others are.

## 8. Open questions for the user

1. **The 30-minute certificate job binds entries**: the build and the kernel get 10 min each on a
   4-vCPU runner. The baseline took 147 s to build and about 144 s in the kernel on the 32-vCPU VM;
   on 4 vCPUs neither is measured. The alternative is a larger runner for the certificate job
   (nanoda would then fit too).
2. **Caches in the submissions repository**: one `rf-org-…` cache per core commit holds the package
   tree (several GB) under GitHub's 10 GB per repository; eviction, and the first evaluation's cold
   `setup` job (about 26 min worst case), are unmeasured.
3. **Gate rule 4**: relax to `V` alone, now that no badge runs `P` or `ext`?
4. **The service throughput calibration**: kept (about 5 s per job, informational); drop it?
5. **The crafted-input DoS column** (FB-5): the follow-up the random column stands in for.
6. **The stream's tail** at `M = 256`: at most about 9.4% of the merges escape (`c ≈ 25` at
   `R = 10`).
7. **Nothing of this has run on GitHub**: the `setup` job, `lookup-only` and `restore-keys`, the
   `env` context in cache keys, the two benchmark jobs and the attestation; `actionlint` was not
   available here.
8. Unchanged and still open: `T_V` on compiled Lean against binary fields (Q11), the second
   kernel (Q5), FB-10.

## 9. Fix pass (review `docs/v4/reviews/D-trim-review.md`, golf `docs/v4/stages/D-trim-GOLF.md`)

On top of `fcb1d5b`, uncommitted. The review found no major finding and six minors; every one is
fixed. Logs are under `logs/trim-fix/`.

| Finding | Disposition |
|---|---|
| **m-1** the badge cap also compiles organiser objects | **Fixed.** `org-setup.sh` step 4 now also precompiles the objects of `Mathlib.Tactic`'s closure (`RF_BADGE_OBJECTS`, default `Mathlib.Tactic`; the core CI sets it empty, since its badges import only the organiser's closure). The precompiled set is the closures of `RecursionFast`, the CompPoly roots and `Mathlib.Tactic`: 4,716 modules, 2,825 of Mathlib's 8,530. **Measured**: 1,063 more objects in 221 s on 4 cores of the development VM (`objects-mathlib-tactic-4cores.log`). The witness-sending entry with `import Mathlib.Tactic` added then certifies with a badge build of about 19 s that compiles 5 objects (`cert-ws-mathlib-tactic.log`). The residual rule (about 860 further modules fit `badge_s` at 4.8 objects/s; `import Mathlib` does not) is stated in `PROVER.md` §6 and design §3.6 and §6.2. Step 4's timeout went from 360 to 540 s |
| **m-2** organiser timeout as REJECT; fixed steps unitemised | **Fixed.** A `TimeoutExpired` (only organiser commands raise it) is now `error` with the command and its limit. A failed pre-build manifest check is now a harness ERROR (no entry code has run). The manifest is checked twice, not three times: before the build and after the badge build, which covers every step in between (the gate itself re-verifies every trusted module's hash). The certificate job's fixed steps are itemised in design §3.4: runner setup 8 s, elan 1 s and the toolchain 29 s **measured**; two manifest checks at 15.5 s each on 4 cores warm **measured** (`manifest-check-time.log`), allowed 40 s cold; the restores about 45 s **estimate**, scaled from the measured 35 s for 2.7 GB. Total about 3 min against 25 min of entry caps: 28 of 30 min, and 29 at twice the restore estimate. Not yet measured on a runner (open, §8 item 7) |
| **m-3** the nesting table not the code's | **Fixed.** Root check ≤ 150 s, so the tree job's entry caps total 1,570 s (26.2 min) inside `PART_S` = 1,680 s. The setup job is split so that a cold miss nests: `setup` runs `lake exe cache get` (240 s) and `org-setup.sh` steps 1–4 (1,080 s), 22 min of timeouts plus about 3 min of transfers. The comparator and the service moved to a parallel `setup-tools` job (`RF_ORG_SERVICE=0` in `setup`), about 6 min |
| **m-4** cache provenance | **Fixed.** (a) Design §2.7 item 9 names the cache store and its three facts. (b) `cert.json` and the result record `environment` (the core commit and the hashes of `manifest.sha256` and `allowlist.txt`), carried by `evaluate.py bench` and `aggregate.py`, checked in the smoke. (c) A `plan` job resolves `core_ref` to its commit; every job checks out that SHA and the caches are keyed on it (`rf-org-SHA`, `rf-kernels-lean|nanoda-SHA`, `rf-svc-SHA`); `RF_HARNESS_COMMIT` is the SHA. (d) Each save is followed by a `lookup-only` restore with `fail-on-cache-miss`, so a failed upload fails its setup job with an `::error::` reason. A cache missing in the certificate or benchmark job writes a `cert.json` or part result with status `error` and the reason, so the evaluation ends as an attested ERROR, not a missing part |
| **m-5** `stream_s` charges organiser overhead; budget unstated | **Kept wall time and added the measured overhead to the cap**: `stream_s` = 960 s, of which 60 s allow for the organiser's work inside it. **Measured** about 30 s: a request's sandbox start, staging, kill and read ≤ 50 ms × 513; a badge batch's start ≤ 0.2 s × about 20 (`stream-overhead.log`). The implied per-link budget, about 3.1 s per link with every check at `T_V` ≈ 178 ms, is stated in design §3.6 and `PROVER.md` §3. Charging only the entry's time would need a separate wall bound for the job anyway |
| **m-6** stale text | **Fixed**: BRIEF V4-7, V4-11, V4-12 annotated as design §6.1 is; "75 s" gone from design §3.4 and §2 here; `test_dos.py`'s stub uses the season's numbers (`verify_s` 10, `total_s` 180, 100 inputs); the blank lines after `HarnessError` removed |

**The golf record's items for the fix step.**
- Runtime count: **3,670 code lines** (service 948, runner 1,023, sandbox 233, badge 88, proof-side
  order 456, tools 697, CI scripts 64, calibration 161; `loc-runtime-after.log`). Design §0 and §5
  and §7 above are corrected; Controls 2,082 code lines, 309 theorems.
- `build-kernels.sh`: inner `timeout 120` (comparator) + `60` (lean4export), nanoda `300`, inside
  the callers' outer 240 s (540 s with nanoda). `setup-tools`' service build is `timeout 120`, as
  `org-setup.sh`'s.
- `test_lean_signer` in `ci.yml`: `timeout 120` (55 s here, 44 s on the runner).
- Golf suggestion 1 applied: the three `by_contra hno` in `Controls/Potential.lean` are
  `refine Classical.byContradiction fun hno => ?_`; statements unchanged; build and audit green.
- Golf suggestion 2 applied: `rfh/files.py` `write_atomic`, `rfh/signed.py` `Signed.sig_bytes` and
  `Bench.calibrate`'s unused `starts` removed.
- Golf suggestion 3 not applied, as asked. The `plan` job now also resolves the core commit (m-4)
  and runs first, but it is not merged into `setup`. The golf's `ci.yml` change (`smoke` needs only
  `harness`) is kept.

**`ci.yml` after the fix pass.** `org-setup.sh` 540 s (with `RF_BADGE_OBJECTS=`),
`build-kernels.sh` 240 s, the e2e smoke 480 s, the signer test 120 s. The step sums are 26, 22, 23
and 26 min (`yaml-parse.log`).

**Checks** (all pass; `logs/trim-fix/`):

| Check | Outcome | Log |
|---|---|---|
| `lake build` | green, 1,264 jobs, no warning; again against the shared `pkgs-local` under a read-only bind, nothing written there | `lake-build.log`, `lake-build-final.log` |
| axiom audit; `loc.py` | PASS; 355 ≤ 500 | `axiom-audit.log`, `axiom-audit-final.log`, `loc.log` |
| hygiene, source-rule fixtures, token sweep, gate fixtures | OK | `hygiene.log`, `token-sweep.log`, `gate-fixtures.log` |
| `org-setup.sh` with the `Mathlib.Tactic` objects (warm) | 47 s | `org-setup.log` |
| service builds, `cargo test`, `test_service.py` (90), `measure.sh 4` | OK | `service-build.log`, `service-cargo-test.log`, `test_service.log`, `service-measure.log` |
| Lean signer (55 s), `extract` (4 cases), `accprobe` (12 answers, all 7 canaries rejected), chain checker | OK | `test_lean_signer.log`, `extract-run.log`, `accprobe.log`, `chaincheck.log` |
| assembly; `test_sandbox.py` (45), `test_tv.py` (6), `test_aggregate.py` (12), `test_dos.py` (6) | OK | `asm.log`, `test_sandbox.log`, `test_tv.log`, `test_aggregate.log`, `test_dos.log` |
| `smoke.py --mock` | 10 checks, 26.6 s | `smoke-mock.log` |
| `smoke.py --org` (on the private package copy, as before) | **16 checks, 4 min 21 s**; `environment` recorded in `cert.json` and the result; two manifest checks | `smoke-e2e.log`, `smoke-cert-comparator-lean.log` |
| a certificate of the witness-sending entry importing `Mathlib.Tactic` | ok; build 29.5 s, comparator 38.2 s, badge about 19 s (5 objects) | `cert-ws-mathlib-tactic.log` |
| `py_compile`, `bash -n` | OK | `py-compile.log` |
| workflows (PyYAML; job limits; step-timeout sums) | parsed; every job ≤ 30 min | `yaml-parse.log` |

**Still open** (beyond §8):
- The new workflow structure (`plan` → `setup` and `setup-tools` → certificate → benchmark) has not
  run on GitHub. Neither has its signalled-ERROR paths, nor its cache sizes: `rf-org` now also
  holds the objects, 3,135 of them in 195 MB uncompressed here (`*.c.o.export` in the package
  copy, the `Mathlib.Tactic` ones included), beside a package tree whose cache is 2.7 GB
  compressed.
- The certificate job's restore time and cold manifest checks on a runner, which bound the 2-minute
  margin.
- Whether `Mathlib.Tactic` is the right precompiled set. A larger one costs the setup job's
  budget: about 5,700 more Mathlib objects would not fit it.
