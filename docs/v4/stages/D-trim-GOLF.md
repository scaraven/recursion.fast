# Stage D-trim (v4, SROM): golf

Status (2026-10-26): **done, uncommitted** in the worktree
`/home/devops/Verified-zkEVM/recursion.fast-v4-trim` (branch `v4/trim-fat`, on `93587a9`). Scope:
what stage D-trim touched (`git diff 01a25b0 93587a9`). No statement, definition, rule, cap,
timeout or number changed; no check was removed. Everything ran on the development VM (32 vCPU);
logs are under `logs/golf-trim/` (gitignored).

## 1. What changed

| File | Change | Why |
|---|---|---|
| `RecursionFast/Controls/Potential.lean` | `collision_no_bool_kstate`, `v24_no_bool_kstate`: the step `2^-120 · 2^256 = 2^136` is `h.trans_eq (by norm_num)` in place of a named `have`, `refine h.trans (le_of_eq ?_)` and `apply NNReal.coe_injective; push_cast; norm_num`; `lt_of_le_of_lt hL _` is `hL.trans_lt _` | −6 lines, no detour through `ℝ`, no naked `;` |
| `RecursionFast/Controls/Completeness.lean` | `grind39_not_complete`: `(hc c w h).not_gt` applied to the rewritten strict inequality, in place of `have`, `rw … at`, `absurd`, `not_le.mpr` | −1 line, direct |
| `scripts/speed/Extract.lean` | `same` inlined as `(decodeWit o).map encodeF == e.map encodeF` (the same truth table: two witnesses compare by encoding, two `none` agree, a mixed pair does not); the `let ok ← match …; return ok` wrapper removed; `leaf`, `node` inlined; `rs.count false`; `encodeF` opened; the 110-character line wrapped | 62 → 56 lines; output byte-identical (§3) |
| `service/src/lib.rs` | `push_item` deleted: no caller in the crate, the binaries or the tests before or after the stage (the trace digest hashes the items in place); the stage had only edited its comment, which named the removed liveness log | −5 trusted Rust code lines |
| `service/src/main.rs` | the module comment the log removal left broken mid-sentence, reflowed | comment only |
| `tests/harness/accprobe/run.py` | `ok or (len(w) == 2 and w[1].isdigit())` is `len(w) == 2 and w[1].isdigit()` (`ok` implies it) | same output |
| `tests/harness/test_aggregate.py` | `part()` builds its dict once, without the `"tree": [], "stream": []` initialisers it overwrote | same parts |
| `.github/workflows/ci.yml` | `smoke` needs `harness` only, not `lean`: it builds the organiser itself and uses nothing of the `lean` job | the critical path, §2 |
| `docs/DESIGN-v4-srom.md` §3.1 | the sentence listing the organiser checks that run in `ci.yml` puts its list in parentheses, so the list of subjects no longer reads as part of the sentence | same words and ids |

Nothing else in the harness was worth cutting: the stage's Python (`bench.py`, `checks.py`,
`prover.py`, `service.py`, `evaluate.py`, `aggregate.py`, `run-benchmark.py`) has no unused import,
function or `Params` field left by the removals (checked by an AST scan and `git grep`), and its
remaining repetition (the three `timeout` → REJECT branches of `evaluate.py`, the two "rebuild if
not at the pin" blocks of `build-kernels.sh`) would cost as many lines to factor as it saves.

## 2. Numbers, before → after

| Quantity | Before (`93587a9`) | After | Log |
|---|---|---|---|
| `Potential.lean` elaboration, `lake env lean`, 3 runs (imports about 2.6 s) | 6.23–6.26 s | 6.21–6.47 s (noise) | `module-time-before.log`, `module-time-after.log` |
| `Completeness.lean`, same | 5.12–5.27 s | 4.99–5.23 s (noise) | same |
| `scripts/speed/Extract.lean`, same | 4.71–4.83 s | 4.63–5.09 s (noise) | same |
| the golfed declarations (profiler, sum of its categories) | `collision_no_bool_kstate` 29.6 ms, `v24_no_bool_kstate` 28.7 ms, `grind39_not_complete` 14.8 ms | 18.9, 23.4, 11.4 ms | `decl-profile.log` |
| `lake build` of the two modules (incremental) | 4.0 s and 3.6 s (`logs/trim/lake-build-final.log`) | 4.5 s and 3.5 s | `lake-build.log` |
| Controls code lines (`scripts/loc.py`), theorems | 2,089, 309 | 2,082, 309 | — |
| trusted runtime code lines (the stage's script, stage B's groups) | **3,675** | **3,670** (service 953 → 948) | `loc-runtime-before.log`, `loc-runtime-after.log`, `loc_runtime.py` |
| contract code lines | 355 | 355 | `loc.log` |
| `smoke.py --org` wall time | 4 min 30 s (`logs/trim/smoke-e2e.log`) | 4 min 27 s (no path it runs changed; noise) | `smoke-e2e.log` |
| core CI critical path | `lean` 7.4 min then `smoke` 9.2 min: 16 min 45 s, **measured** (CI run 39966237935) | `harness` (1.4 min) then `smoke`, beside `lean`: about 10.7 min (**estimate**); every job's own wall time unchanged | — |

The trusted runtime at `93587a9` counts 3,675, not the 3,677 that the RESULT (§7 item 7), the
design's §0 and §5 state: the stage's `loc-runtime-after.log` was taken before its last edits
(proof-side order 452 there, 450 at the commit). See §5.

## 3. Checks (all pass)

| Check | Outcome | Log |
|---|---|---|
| `timeout 1800 lake build` | green, 1,264 jobs, no warning; again against the shared `pkgs-local` after restoring the link (nothing written there: no file newer than the switch) | `lake-build.log`, `lake-build-final.log` |
| line budget, as `ci.yml` | 355 ≤ 500 | `loc.log` |
| axiom audit, as `ci.yml` | PASS, 4.4 s; again against `pkgs-local` | `axiom-audit.log`, `axiom-audit-final.log` |
| `org-setup.sh` (regenerates the manifest) | 58 s | `org-setup.log` |
| hygiene, source-rule fixtures, token sweep | OK | `hygiene.log`, `token-sweep.log` |
| gate fixtures | OK, 52.6 s | `gate-fixtures.log` |
| Lean signer against the service | 0 failures, 53.6 s | `test_lean_signer.log` |
| `extract` (built in 7.5 s) | 4 cases, 0 failures; output identical to `logs/trim/extract-run.log`; seeds 1 and 99 too | `extract-build.log`, `extract-run.log` |
| `accprobe` and the organiser's canaries | file accepted 5×, all 7 canaries rejected, 35.5 s | `accprobe.log` |
| chain checker step, as `ci.yml` | 3 runs `ok` | `chaincheck.log` |
| service: builds, `cargo test`, `test_service.py` (90 checks), `measure.sh 4` | OK | `service-build.log`, `service-test-keys-build.log`, `service-cargo-test.log`, `test_service.log`, `service-measure.log` |
| assembly assembles; `test_sandbox.py` (45), `test_tv.py` (6), `test_aggregate.py` (12), `test_dos.py` (6) | OK | `asm.log`, `test_sandbox.log`, `test_tv.log`, `test_aggregate.log`, `test_dos.log` |
| `smoke.py --mock` | 10 checks, 0 failures, 26.8 s | `smoke-mock.log` |
| `smoke.py --org` (as the implementer ran it: `.lake/packages` on the private copy `.lake/pkgs-trim`, `scripts/tools.env` sourced, `timeout 540`) | 16 checks, 0 failures, 4 min 27 s | `smoke-e2e.log` |
| `py_compile` of the 14 Python files the stage touched; `bash -n` of every CI and test shell script | OK | `py-compile.log` |
| workflows parsed (PyYAML); job limits and step-timeout sums unchanged (`ci.yml` 26, 22, 23, 26 min) | OK | `yaml-parse.log` |

`.lake/packages` points at `pkgs-local` again. The private copy `.lake/pkgs-trim` (9.2 GB) and
`.lake/pkgs-overlay` are still there to delete (RESULT §4).

## 4. Suggestions not applied

1. **Elaboration of `Potential.lean`, outside the stage's declarations.** Three `by_contra hno`
   on existentials over `Digest` (`exists_lucky`, `collision_no_bound`, `v24_no_bound`) spend
   0.26–0.42 s each searching for a `Decidable` instance that cannot be found (the bad set is an
   arbitrary `Prop`). `refine Classical.byContradiction fun hno => ?_` skips the search: 5.9–6.15 s
   instead of 6.2–6.3 s for the module (**measured**, a scratch copy; the same axioms;
   `decidable-profile.log`). Not applied: not touched by the stage.
2. **Dead trusted-runtime code older than the stage**: `rfh/files.py` `write_atomic` (5 code lines)
   and `rfh/signed.py` `Signed.sig_bytes` (2) have no caller anywhere; `Bench.calibrate` takes
   `starts` and never reads it.
3. **`evaluate.yml`: fold the `plan` job into `setup`** (both run no entry code and check out the
   same commit): one runner fewer per evaluation, about 15 YAML lines, no wall-time change (`plan`
   runs beside `setup`). Not applied: it rewires `benchmark` and `attest` and the header's account
   of the plan, and nothing of `evaluate.yml` has run on GitHub yet.
4. **Timeout nesting in `build-kernels.sh`**: its inner `timeout 600` (each `lake build`) and
   `timeout 900` (nanoda) are longer than the outer bounds the workflows give the script
   (`timeout 300` in `setup`, `timeout 120` in `ci.yml`), so the inner caps never bind. Likewise
   the `setup` job's fallback `timeout 600 cargo build` against `org-setup.sh`'s 120 s for the
   same build. Numbers are the stage's; for the fix step.
5. **The signer test's cap**: `test_lean_signer.py` took 53.6 s here and 44 s on the runner (CI run
   39966237935) against its new `timeout 60`.

## 5. Numbers in other documents, if this golf is taken

Not changed here (the golf changes no number in a document). The design's §0 and §5 and RESULT §3,
§7 item 7 state: trusted runtime 3,677 (3,675 at `93587a9`; 3,670 after this golf, the service
948), Controls 2,089 code lines (2,082 after; theorems 309 unchanged).
