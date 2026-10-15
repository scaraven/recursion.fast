# S6b review: the harness (gate, challenges, badge executables, benchmark runner, CI, docs)

Adversarial review of Stage 6b, 2026-10-15. The reviewer read `CLAUDE.md`, `docs/DESIGN.md`
§3.2–§3.3, §6, §7.4, §8, `docs/DESIGN-AMENDMENTS.md` (S6b-A1 … S6b-A19, incl. the decision pass;
S6b-A3/O-12 deferred), `docs/stages/S6b-RESULT.md`, `docs/reviews/S7-review.md` (S7-M1, S7-M2),
and then in full: `scripts/Gate.lean` (rules 1–9), `scripts/{harness.sh, ci.sh, org-build.sh,
olean-manifest.py, render-challenge.py, bwrap-landrun.sh, import-allowlist.txt}`,
`RecursionFast/Challenge/{L,R}.lean.in`, `harness/lean/{Main.lean.in, RecursionFastHarness/*,
LinkCheck.lean}`, `harness/{run-benchmark.py, render-layout.py, badge-main.py, README.md,
reference-machine.md}`, `submissions/baseline/prover/README.md`, the CI step bodies, and the v0.3
standard (`A6-G0` harness order, `A7-M3` build binding) in `contract-v03`'s reviews. Nothing under
`scripts/`, `harness/`, `RecursionFast/` was edited. Probes: `probes/s6b/review/`.

## Verdict

**The gate, the renderer, the twin binding, the CI order and the manifest are sound. The benchmark
runner has one hole that voids its isolation and one that unpins what it scores; the S7-M1 residual
is real on the badge path and is correctly deferred (O-12).** S7-M1 and S7-M2 fixes check out.

Majors:
- **S6b-M1** the runner's sandbox is optional and silently defaults to off; `harness.sh` does not force it.
- **S6b-M2** the recursion board is scored against `layouts.C`, which is pinned only to the submitter's own uncertified `claim.digestC`, not to the certified `entry.C`.
- **S6b-M3** (confirmed, orchestrator-deferred as O-12) emitted badge code can still be forged via raw compiler-state access reachable from the badge-root module through Mathlib's transitive `Lean` closure.

Minors: S6b-m1 … S6b-m5 below.

---

## What was verified sound (no finding)

- **The twin binding (S6b-A4).** `harness_twin` (`Twin.lean`) rebuilds `Protocol.mk` from the
  submission's own `n/shape/vkLen/VK/idxShape/IDX/verify` field terms (after definitional
  `reduceProjs`), and `Main.lean.in` kernel-checks `NARG cfg' P' = NARG S.cfg S.P` and
  `index cfg' P' = index S.cfg S.P` by `rfl` at badge-build time. Proof-irrelevance makes the
  copied proof fields harmless. With the A7-M3 build binding (gate-tree build byte-identical to the
  comparator's, `harness.sh` stage 2) and rule 8, the thing timed is the thing proved, *up to the
  compiler* (the M3 gap).
- **Gate rules 1–9.** Trust by `.olean` content hash (never name); rule 3 enumerates the 4.34
  code-affecting attributes (`implemented_by/extern/export/init/builtin_init/csimp/cpass/
  computed_field`) and allows only the behaviour-preserving steering ones; rule 6 restricts *direct*
  imports to the allowlist + frontend; rule 7 rejects any *definition* touching the compiler/env
  API; rule 8 keeps the badge-root module's transitive closure compiler-free; rule 9 keeps Clean
  code off the badge-path fields. Rule 4 unfolds to the constructor and checks only `badgeFields`.
  The CI probes (`GateV2`, `Forge/Cpass/ForgeNoLean`, `GClean*`, `ForgeClean`, the A4 ports) each
  reject at the right rule.
- **Renderer (`render-challenge.py` + `render-layout.py`).** The emitter writes only numerals and
  constructors: K elements re-validated to 16 hex by `kx`, matrix `(row,col,v)` bounded
  (`row<cons`, `col<2·cols+3`), `S<t`, bus kinds restricted to `.sub/.eq`; `check_layout` strips
  every informational string and names chips by index, so the `-/ … /-` comment-escape is closed;
  `strict_json` bans floats/NaN/dup-keys; `confined` rejects abs/`..`/symlink paths with a
  realpath-containment check. The `{{layout}}`/`{{image}}`/`{{digest}}` literals cannot carry a
  term.
- **CI order & manifest (A6-G0).** org-build (2) → manifest check (3) run before any solution-like
  code; the production harness (7) is the first such step and uses fresh trees; manifest re-checked
  (12). Clean is a pinned path package: 130 `packages/Clean/` entries in the manifest, read from
  `ext/Clean` by `olean-manifest.py`'s path-package branch; the gate pins Clean and *reports* its
  `[init]`/`csimp` entries. `harness-linkcheck` guards organiser start-up cost (the `Fintype K`
  OOM, S6b-A5). Clean is built twice (org tree at step 2, repo tree at step 11) and the comparator
  runs 3× in step 7 — expected, not duplicated work on the same tree.

---

## Majors

### S6b-M1 (major): the benchmark runner's sandbox is optional and off by default

`harness/run-benchmark.py` `DEFAULTS["sandbox"] = None` (line 80); `load_config` neither requires
nor defaults it (lines 476–494); `Runner.run` applies `--hide` for the secrets file and the run
directory, the bwrap wrapper, `--unshare-net` and `--unshare-pid` **only inside `if sb:`**
(lines 169–181). With `sandbox` unset or `null`, every leaf/node/DoS/index step runs with **no
isolation at all**: the secrets file and the whole run directory are readable, the network is open,
there is no PID namespace (so a double-forked daemon survives the step and can precompute for later
steps, defeating "fresh process per step, no persistent state"), step directories are not isolated
from one another, and peak memory is `os.wait4`'s `ru_maxrss` of the direct child only.

The production path does not close this: `scripts/harness.sh` stage 3b builds the benchmark config
from the organiser's `--bench FILE` **verbatim**, injecting only `cfg["verify"]`/`cfg["index"]`
(the stage-3b heredoc), and never sets `sandbox` — although its banner prints "every step
sandboxed". So isolation depends entirely on the organiser remembering to put
`"sandbox": "scripts/bwrap-landrun.sh"` in the bench file, with no check; `harness/README.md`
documents `"sandbox": ... | null` as if `null` were a normal option.

Probe: `probes/s6b/review/sandbox-default.py` — a board-L config omitting the key yields
`cfg["sandbox"] = None`, and `Runner.run`'s `if sb:` is false.

Fix: (a) in `cmd_run`/`load_config`, refuse to `run` (not `selftest`) unless `sandbox` names an
executable the runner can exec — fail closed; and (b) in `harness.sh` stage 3b, set
`cfg["sandbox"] = $LANDRUN` the same way it injects `verify`/`index`, so the production harness
forces its own sandbox regardless of the bench file. Update the README to stop presenting `null` as
an ordinary choice.

### S6b-M2 (major): the recursion board is scored against an unpinned `layouts.C`

On board R the recursion key is `vkC = index(layouts.C)` (`run-benchmark.py` line 327), and every
node/wrap/root step is proved and verified under that key. `layouts.C` comes from the bench config.
The only check tying it to anything is line 329: `claim["digestC"] == H(index(layouts.C))` — i.e.
it is tied to the **submitter's own `claim.digestC`, which the design explicitly leaves
uncertified** (§3.3: "the key digests are declared, not certified"). Nothing ties `layouts.C` to
the certified `submission.entry.C` (the literal `C` the R stub renders and `CertificateR` +
`submission.entry.C = C` pin), and nothing checks `H(index(rendered C)) == claim.digestC`.
`harness.sh` builds the bench config from `--bench FILE` verbatim and never consults the
certificate, the claim JSON used for rendering, or the rendered challenge.

Consequence: the scoreboard's headline `S_rec` (and `S_wrap`) can be measured on a C_V — and under
a key — different from the certified one. The `sound`/`complete`/`live` guarantees are statements
about `submission.entry.C`; if the measured key is `index` of a different layout, those guarantees
do not cover the timed runs. This is organiser-misconfiguration territory today, but it is exactly
the "scoreboard value not pinned by the certificate" the review brief asks to flag, and there is no
script or check preventing it. (`digestL` is fine: line 329 ties it to the organiser-generated
`L_chain(tree.n)`, not to a submitter value.)

Probe: `probes/s6b/review/pinning.sh` — shows stage 3b derives only `verify`/`index`.

Fix: the harness should supply `layouts.C` (and the `claim`) from the **same** claim JSON that
rendered the R challenge, not from an independent organiser file; and the runner should index the
*rendered* `C` and reject unless `H(index(rendered C)) == claim.digestC`. Better still, have the
badge `index` executable expose `index cfg P entry.C` directly (it is a badge-path field, rule 4),
so the recursion key is derived from the certified constant rather than from any JSON.

### S6b-M3 (major; confirmed, orchestrator-deferred as O-12): badge code is forgeable via Mathlib's transitive `Lean`

S7-M1's forgery (an elaboration-time `run_meta` overwrites a definition's emitted code, leaving the
kernel term intact) needs a handle on the compiler's code-emission state. Rules 6 forbids *direct*
imports of `Lean`/`Lean.Compiler.*`, and rule 7 only sees *definitions*; a `run_meta` is neither.
The `ForgeNoLean` probe shows the specific `impureExt`/`saveImpureDeclCore` route is dead because
`Lean.Compiler.LCNF.PhaseExt` is not in Mathlib's closure. **But the deeper route the trust
statement itself names — `Lean.persistentEnvExtensionsRef` + `unsafeCast` with re-declared types —
is reachable:** `persistentEnvExtensionsRef` lives in `Lean.Environment`, which every Mathlib
module imports transitively, so its full name resolves inside a `run_meta` in a module that imports
only Mathlib (allowed by rule 6). That module can be the **badge root** `leaf` itself (importing
Mathlib does not trip rule 8, which only excludes Clean/compiler-API-via-allowlist, and Mathlib is
*in* the allowlist). The twin then links `leaf`'s forged object code into `verify`/`index`, and the
`rfl` theorems pass on the untouched kernel terms. So the residual is on the badge path, not merely
theoretical.

This is accurately characterised and explicitly deferred by the orchestrator (S6b-A15 → O-12,
"recommended before launch"; S6b-A2's trust statement admits it). The review's contribution is only
to confirm it reaches the badge path through the allowlist, and that no probe exercises the
raw-extension route (the CI only tests the import-`Lean` and import-`Clean` variants). Recommend a
`probes/s6b/gate/ForgeRaw.lean` that forges via `persistentEnvExtensionsRef`+`unsafeCast` under
Mathlib-only imports as a regression marker, and that **O-12 (kernel-regenerated badge code, S6b-A3)
ship before any ranked board opens** — rules 3/6/7/8/9 are not a sound substitute, only a raise of
the bar.

---

## Minors

- **S6b-m1 (memory cap is per-process, not per-tree).** Peak memory is GNU `time -f %M` =
  `ru_maxrss` of time's single child (`run-benchmark.py` lines 180, 203–211), or `os.wait4`'s
  without a sandbox; neither sums a forked process tree, so a multi-process prover evades `mem_kb =
  48 GB`. S6b-A12 defers this to "production cgroup". Recommend the runner itself enforce a
  `memory.max` (bwrap `--cgroup`, or `systemd-run --scope -p MemoryMax=`) rather than leave it to a
  future production step; it is the only thing bounding memory.
- **S6b-m2 (`k` not pinned to `Declared.k`).** The class the runner uses for board gating is the
  bench-config `k` (lines 266–282), never cross-checked against the certificate's `Declared.k`. A
  wrong `k` silently changes which leaf-board sizes run or are skipped (board-L scope) and whether a
  class-24 entry is rejected up front. Have `harness.sh` derive/verify `k` from `Declared.k`.
- **S6b-m3 (whole-filesystem read).** `bwrap-landrun.sh` binds `--ro-bind / /` (landrun `--ro /`
  semantics), so an untrusted prover reads the entire reference machine except the two `--hide`
  paths — other submissions, standing records, organiser material if co-located. Keep only the
  current submission on the box, or narrow the read set. Hardening.
- **S6b-m4 (baseline prover README stale vs S6b-A9/A16).** `submissions/baseline/prover/README.md`
  defers the interface to `harness/README.md` ("Stage 6b is finalising it, so it is not restated
  here") and does not state the decided interface (leaf prover reads `secret.hex`, builds the
  witness inside the timed region, no witness file; mode is the last argument). Flagged for the
  orchestrator to reconcile, as S6b-A16 anticipates.
- **S6b-m5 (config `cfg.arity` unused).** The runner never reads `cfg["cfg"]["arity"]`; the real
  arity is the submission's. A wrong config arity is silently ignored. `cfg.hash`, by contrast, is
  pinned by the index self-check (line 313), which ties the config hash to the submission's own
  `cfg.hash`. Cosmetic; drop the field or note it as informational. (Observation.)

---

## Trust statement (S6b-A2) × what actually enforces it

| Clause of the S6b-A2 trust statement | Enforced by | Holds? |
|---|---|---|
| executed verifier/indexer = code the compiler emitted for the submission | twin terms + `rfl` in `Main.lean.in`; A7-M3 build binding; rule 8 badge-root | yes, *up to the compiler* (S6b-M3) |
| no attribute substitutes/changes compiled code | Gate rule 3 (8 attributes; pinned deps reported) | yes |
| submission imports nothing the organiser libraries do not | Gate rule 6 (direct imports ⊆ allowlist ∪ frontend) | yes for **direct** imports; transitive `Lean` via Mathlib is the M3 gap |
| compiler code-emission state (`PhaseExt`) out of reach | rule 6 + "not in Mathlib's closure" (ForgeNoLean probe) | yes for `PhaseExt`/`impureExt` |
| no definition uses the compiler/environment API | Gate rule 7 (prefixes + consts, theorems exempt) | yes for **definitions**; blind to `run_meta` |
| badge path never links a compiler-reaching module | Gate rule 8 (`--badge-root` closure) | yes vs Clean; does **not** exclude Mathlib, which carries the API constants (M3) |
| badge-path field never calls frontend (Clean) code | Gate rule 9 (`frontendRefs`) | yes |
| **Not excluded:** forgery via raw extension access | — (nothing) | residual, O-12 (S6b-M3) |

## Scoreboard-visible values × where pinned

| Value (in `result["scores"]`) | Pinned by | Gap |
|---|---|---|
| `verify` wall (all boards) | submission's `NARG` via twin `rfl` + A7-M3 + rule 8 | S6b-M3 (emitted code) |
| `S_leaf` key `index(L_chain(n))` | organiser `gen-chain-layout.py` + submission's `index` | layout fidelity tested not proved (§7.2, by design) |
| `S_rec`/`S_wrap` key `vkC = index(layouts.C)` | only `claim.digestC` (uncertified, submitter-declared) | **S6b-M2** — not tied to certified `entry.C` |
| `digestL` | organiser `L_chain(tree.n)` (line 329) | sound |
| `cfg.hash` | index self-check (line 313) ties config↔submission | sound |
| `cfg.arity` | nothing (submission governs) | S6b-m5 (unused) |
| class `k` (gating) | bench config | **S6b-m2** — not tied to `Declared.k` |
| node/root statements | runner's `node_stmt`/`tree_root`, KAT-checked vs `treeKat`/`rootOK_xT` (selftest) | re-implementation (§6.3, by design) |
| `tape_L` proof-size cap (board L) | runner (line 358), all leaf tapes incl. tree chains | sound (S7-A3/S7-M2 item 3) |
| secrets | `os.urandom` per eval, hidden | **only when a sandbox is set** (S6b-M1) |
| memory | GNU `time %M` / `wait4` of one child | **S6b-m1** per-process |

## Probes

- `probes/s6b/review/sandbox-default.py` — `load_config` defaults `sandbox` to `None`; `Runner.run`
  skips all isolation (S6b-M1).
- `probes/s6b/review/pinning.sh` — `harness.sh` stage 3b derives only `verify`/`index` into the
  bench config; `k`, `cfg`, `layouts.C`, `claim.*` pass through unchecked (S6b-M1, S6b-M2).
- Recommended (not built here): `probes/s6b/gate/ForgeRaw.lean` — S7-M1 via
  `persistentEnvExtensionsRef`+`unsafeCast` under Mathlib-only imports, as the regression marker for
  O-12 (S6b-M3).
