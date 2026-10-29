# Stage D-trim (V4-A9): adversarial review

Reviewed: commit `93587a9` on `v4/trim-fat` (base `01a25b0`), in the read-only worktree
`recursion.fast-v4-trim-review`. Record under review: `docs/v4/stages/D-trim-RESULT.md`; decisions:
`docs/v4/BRIEF.md` §5b (V4-A9); design: `docs/DESIGN-v4-srom.md`. The user's eleven decisions are
not reviewed; their implementation is.

What I ran (logs and the scratch build under the session scratchpad, nothing written in either
worktree except this file): a copy of the commit built against the shared package tree
(`lake build`: 1,264 jobs, no warnings, exit 0); `#print axioms` of every re-instanced control
(`propext`, `Classical.choice`, `Quot.sound` only) and `#check` of their statements; `scripts/loc.py`
on the Contract (355 code lines); `scripts/check-hygiene.sh` (OK); `py_compile` of every Python file
(OK); measurements of the organiser-side costs the new caps now enclose (below). The pinned
comparator's source (`CambridgePQ/.../tools/comparator`, read-only) and the implementer's logs
(`recursion.fast-v4-trim/logs/trim/`, read-only) were read where a claim depended on them.

## Pass A: specification (Lean)

Nothing to report. The contract changed in two values only (`errorCap := 2⁻¹ ^ 120`,
`completenessCap := 2⁻¹ ^ 40`, `Security.lean:108-109, 154-155`); no definition's shape and no
theorem about a definition changed; the docstrings say what, not how. The re-instanced controls are
non-vacuous at the new values and prove what their docstrings say:

- `grind40_complete` / `grind39_not_complete` (`Completeness.lean:133-143`): 40 nonces fail with
  probability exactly `2^-40 ≤ cap`; 39 nonces (`2^-39`) are not complete, for any relation with a
  witness (the hypothesis `R c w` is inhabited by the Library's entries).
- `collision_no_bool_kstate` (`Potential.lean:369`): `K = 2^136` with `2K < 2^256`; the cap allows
  `2^256 · 2^-120 = 2^136` bad answers per query, so the log of `2^136 + 1` distinct answers is
  exactly what the argument needs.
- `v24_no_bool_kstate` (`Potential.lean:616`): `K = 2^72`, `M = 2^136`: `(2^72 + 1) · 2^64 =
  2^136 + 2^64 > 2^136` and `2^72 + 1 < logCap = 2^96`, so the negative still lives inside the guard.
- `twoLucky_no_bool_kstate` (`2^-120 < 2^-96`), `Backdoor.bounded` (`1 ≤ 2^-120 · 2^256`),
  `errorCap_lt_one`, `error_one_no_certificate`: unchanged proofs, re-checked by the build.

The derived numbers were recomputed and agree everywhere I looked: chargeable events from `216`
bits (`2^96 · 2^-216 = 2^-120`, birthday `2^108`), `2^-24` at `2^96` queries, `2^-56` at `2^64`,
`2^-90` at `2^30`, `2^-145` for `2^15` digests per query, `640 · 2^-40 ≈ 2^-30.7`,
`40 ln 2 ≈ 28` (`Security.lean` header, design §2.4, §4.4, §1.4, `Certificate.lean:106-108`,
`docs/v4/CHECKS.md` C3/C8). No in-force document or source still states `2^-128` as a cap; every
remaining `2^-128` is labelled as v3's.

## Pass B: fidelity (code against the decisions and the documents)

The decisions are implemented as stated, with the exceptions listed as findings. In particular:

**Item 9, one build (attacked as asked).** Sound. The binding rests on `evaluate.py:218-225`
(the build, sandboxed, only the tree's `.lake` writable), `:307-311` (every `.olean`, `.olean.server`,
`.olean.private`, `.ir`, `.c` byte-identical after the comparator), `:339-342` (unchanged after the
badge build, no entry module added). What the badge executes is `leanc` output of the hashed `.c`
(plus cross-module IR from the hashed `.ir`), linked in the badge build where no entry code runs;
the `.o` files are derived after the hash from hashed inputs and are correctly outside the set. The
comparator's `lake build` (its `safeLakeBuild`, with only the tree's `.lake` writable under the
shim) can only re-elaborate the same sources: a different output is a REJECT, the same output is
the same binding. Lake's up-to-date decision is not trusted. I could not construct a lakefile trick
(the lakefile and manifest are the harness's, `mkfresh`), a build-time execution (the source rule),
a module outside `Solution`'s closure (never built, never linked), or a write between hash and badge
build (the gate's sandbox has nothing writable; the badge build is hashed afterwards). The
`HarnessError` test at `:272` still works: the comparator itself prints `Building Solution`
(`Main.lean`, `safeLakeBuild`), as the implementer's smoke log shows (`smoke-cert-comparator-lean.log`
lines 1, 7), so a comparator failure before the solution is still ERROR and a kernel rejection is
still PROVISIONAL.

**Item 2, caches.** No job but `setup` saves; `setup` never fetches the entry; keys are immutable
once saved; the certificate and benchmark jobs only restore. A sandboxed entry cannot reach the
cache. See m-4 for what the design should say and two robustness gaps.

**Items 4, 5, 7 (DoS, root-only tree, separation).** As decided. "Crash" is `exit ≠ 0` or missing
answers of the badge process (`checks.py:92-94`), named with the input being checked; accepts are
recorded (`bench.py:380-382`); nothing in the design relies on non-malleability. The root is
checked against the harness's own `treeRoot` under the run's `vk` (`run-benchmark.py:107`,
`bench.py:258`); starts are fresh per job and per evaluation, `setup` runs before they exist, and
the sandbox of every run is killed, so no proof or state crosses runs. The moved canaries are
asserted in core CI: `accprobe/run.py:99-120` exits 1 unless the file is accepted five times and all
seven mutations are rejected (on a `2^16`-query trace), and `smoke.py:111-132, 216-221` fails the
smoke on any wrong answer on the honest root and a stream leaf. An accepted mutated DoS input lets
nothing through that either goal needs.

**Item 8, the stream.** No statistic assumes repeats (`bench.py:327-332`, `aggregate.py:209`,
`score`). The deadline is set after the stream's service starts (`bench.py:281, 290`) and cleared
before it stops (`:325`), so the service's lifetime is not charged; see m-5 for what is.

## Findings

No major finding. Six minor findings, in priority order.

### m-1. The badge cap (180 s) also pays for compiling the organiser's objects, and no document says so

`harness/evaluate.py:373-382`, `harness/org-setup.sh` step 4, `harness/season.toml:15`,
`harness/PROVER.md`, design §3.4/§3.6.

An executable links the compiled object of every module in `Solution`'s import closure. The
organiser precompiles only the closure of `RecursionFast` and the two CompPoly roots; the shared
package tree holds **2,883 objects (`*.c.o.noexport`) for 8,548 Mathlib `.c` files**, none for
CompPoly before `org-setup`. Every other module an entry imports, for its proofs as much as for `V`,
is compiled by `leanc` inside `badge_s`.

Measured here (`leanc -c -O3`, pinned to 4 cores, 160 random non-precompiled Mathlib objects):
16.3 s, about **1,760 objects per 180 s** on this VM's cores (a runner's are slower); single files
run 0.3 s (`Algebra/Group/Defs.c`) to 4.9 s (`Tactic/Linarith/Frontend.c`). The baseline's own
record (`F4-final-harness-RESULT.md:71`): "badge build 74 s (986 objects compiled)" on 32 vCPU
before CompPoly's objects were prebuilt, 16 s after. So an entry whose closure adds about a
thousand modules beyond the organiser's is near the cap on a runner, and `import Mathlib`
(5,665 objects, about 580 s here) is a certain REJECT "the badge did not build within badge_s",
for compiling organiser code. The RESULT's Q1 and design §6.2 item 2 name the build and kernel caps
as the ones binding entries and omit this one, and PROVER.md does not tell an entrant what the
badge build compiles.

Fix: state the rule where the caps are stated (PROVER.md §1 or §5, design §3.6): the badge build
compiles the objects of every module in `Solution`'s closure outside the organiser's precompiled
set (`RecursionFast` and the CompPoly roots), at about N objects per minute on the runner, within
`badge_s`. Cheap mitigation for the user to decide: add `Mathlib.Tactic` (and whatever else
entrants plausibly import for proofs) to the `nop` executable's imports in `org-setup.sh` step 4,
so the objects are built once per core commit in the setup job and cached; precompiling all of
Mathlib (about 15 min on 4 cores here) would not fit the setup job.

### m-2. The certificate job's fixed steps are unmeasured and under-itemised, and an organiser timeout is recorded as the entry's REJECT

`.github/workflows/evaluate.yml:153-202`, `harness/evaluate.py:57, 164-166, 353-355`, design §3.4
table ("about 2.5 min, estimate"), RESULT §2.

The entry's caps sum to 1,500 s (25 min); the job's margin is 5 min for everything else. The
estimate names "the cache restore (35–38 s, measured)" for `.lake/packages` in the core CI, but the
cache is now `core/.lake` whole plus `lean-tools/.lake` plus the kernels; and it does not itemise
the three olean-manifest checks, each of which hashes **7.58 GB over 34,374 files** (measured on the
implementer's manifest; cold after a restore, warm afterwards), nor the toolchain download
(`lean --version`, `timeout 300`), nor `runner-setup.sh`'s `apt-get`. My estimate for a runner is
3–4 min; nothing on the 25 + 5 split has been measured. If the fixed steps exceed 5 min, an entry
that uses its caps (which a hostile one can do on purpose: a build that ends at 599 s, a kernel run
that ends at 599 s) ends the job at 30 min as a kill, the ERROR that V4-A9 item 1 forbids. Not
confirmed on a runner (nothing has run there); confirmed: the scope and the arithmetic.

Separately and confirmed: `TIMEOUT` went from 3,600 to 300 s for the organiser's own commands
(render, source rule, manifest check, `lake env printenv`), and `evaluate.py:353-355` records a
`subprocess.TimeoutExpired` from them as `status = "reject"` with the reason `timeout: python3`.
That is an organiser fault attributed to the entry.

Fix: (a) measure the certificate job's fixed steps on a runner before the rule binds, and put the
measured numbers in §3.4; (b) `except subprocess.TimeoutExpired` → `status = "error"` (it can only
come from an organiser command: every entry step returns `"timeout"` instead of raising); (c) if the
margin is short, hash less: the gate re-verifies the hash of every module it trusts, so the
manifest check after the comparator could go, or the scope could be the modules `Solution` imports.

### m-3. The nesting table's arithmetic is not the code's

Design §3.4 table, RESULT §2 ("root check ≤ 75 s (three badge runs of 2 checks of ≤ 10 s)"),
`harness/rfh/bench.py:147-156, 171-180, 188-196`, `.github/workflows/evaluate.yml:78-151`.

Each badge batch is allowed `verify_s · (n + warm) + 30` s: the root check is one batch of 50 s plus
up to two re-measures of 50 s (`checker_runs = 3`), and its canary 40 s, so the tree job's
entry-capped timeouts sum to `300 + 300 + 600 + 150 + 40 + 180 = 1,570 s` (26.2 min), not 1,495 s,
leaving 110 s of `PART_S` (1,680 s) for the organiser's steps. Those are small (measured here: the
instance's digests 2.2 s on 4 workers, three chain-checker runs of about 1.8 s, the service probes
about 5 s, three service lifetimes), so the conclusion stands, but the table should be derived from
the code. The setup job's own timeouts (`240 + 1,020 + 300 = 1,560 s`) plus elan, the restore and a
multi-GB save do not nest inside its 30 min on a cold miss; no entry runs there, so the outcome is
an organiser ERROR that is re-run, which the table should say (or the setup job gets a larger
limit, which the user's rule about jobs that run entries does not forbid).

### m-4. The organiser environment's provenance now rests on the cache store; say so, bind it, and close two gaps

`.github/workflows/evaluate.yml:72-75, 91-99, 113-122, 137-151, 171-179`, design §2.7 item 9, §3.1.

(a) The olean-manifest check cannot detect a poisoned cache: the manifest is inside it. What the
certificate job trusts is that the cache under `rf-org-…-<core_ref>` was saved by the `setup` job
(keys are immutable, only `setup` saves, and `restore-keys: rf-org-lean-` trusts the most recent
cache with that prefix in the submissions repository's default-branch scope). The trust statement
(§2.7 item 9, "the trusted machine") should name the cache store and these three facts. (b) Nothing
in the attested result names the environment: record `sha256(manifest.sha256)` (and the allowlist's)
in `cert.json`, so a record is bound to the environment it was checked against. (c) The key binds
the *string* `inputs.core_ref`, not the checked-out commit: a branch or tag ref reuses an older
commit's tree under a newer harness (`fail-on-cache-miss` never fires); bind the key to
`git -C core rev-parse HEAD` (or `hashFiles` of the core tree). (d) `actions/cache/save` reports a
failed upload as a warning, so a run can have a green `setup` and a certificate job that fails on
`fail-on-cache-miss` with no signal; verify the save in `setup` (a `lookup-only` restore after it).
None of (a)–(d) is reachable by a pull-request author: a `pull_request_target` run executes the
base's workflow, and a fork's or a `pull_request`-scoped cache is not visible to the base scope.

### m-5. `stream_s` charges the organiser's overhead to the entry, and the implied per-link budget is stated nowhere

`harness/rfh/bench.py:290, 336-347`, `harness/rfh/prover.py:196, 224`, `harness/PROVER.md` §3,
design §3.6.

From the first request, the deadline covers the spawn of every request's sandbox up to its `ready`
line (measured here: 74 ms per sandbox, `× 513 = 38 s`), every badge process start (17 batches plus
re-measures), and the checks themselves (decided). At the season shape with `T_V ≈ 178 ms`, the
timed proving must fit in about `900 − 38 − 17 · (0.2 + 32 · 0.178) ≈ 750 s`, i.e. **about 2.9 s per
link**; an honest entry above that is REJECTed, not scored at `S = T_tree + K · t_link`. PROVER.md
says only "a link that would end after it fails the run". Fix: state the implied budget (and that
organiser overhead is inside it) in PROVER.md §3 and design §3.6; or keep the spawn-to-`ready` wait
under `step_s` alone and start charging at `go`, which is what the clock does.

### m-6. Stale or inconsistent text, and hygiene

- `docs/v4/BRIEF.md:83, 87, 88`: the V4-7, V4-11, V4-12 rows still say "root, samples, canaries",
  `M = 512`, "root, samples". §5b overrides them, but the design's §6.1 row for V4-11 was annotated
  "(256 since V4-A9)" and these were not; annotate them the same way.
- Design §3.4 and RESULT §2: "root check ≤ 75 s" (m-3).
- `tests/harness/test_dos.py:159, 165`: the stub still says "a check took 61.0 s, above verify_s"
  with `verify_s=60`, `dos_total_s=300`; harmless, but the file documents the new rule with the old
  numbers.
- `harness/evaluate.py:66-70`: three blank lines after `HarnessError`.

## Observations (not findings)

- The per-entry `file±1`/`trace-*`/`sig-*` canaries were also a weak detector for a badge template
  subverted through the entry's environment (the template is elaborated with `Solution` imported;
  the source rule allows `notation`, O-12's residual, trust statement item 5). That detection is
  gone; the guard is the source rule alone, as the trust statement already says.
- Under the `prlimit` fallback (no systemd user manager), a comparator run killed at `kernel_s`
  leaves `lean`/`bwrap` orphans running into the gate and badge steps (`kill_unit` is a no-op);
  `runner-setup.sh` makes this the non-default path on runners. Pre-existing.
- `dos_inputs` materialises all 100 inputs in memory (up to 75 copies of the root file); bounded in
  practice by what passes `T_V` (a few MB), so harmless; generate lazily if the DoS column grows.
- `badge_sha256` is recorded in `cert.json` and again by `run-benchmark.py`, never compared;
  the artifact is GitHub's. Pre-existing.
- The RESULT's claims I could check hold: trusted lines 355; the runtime's 3,677 and the service's
  953 match `loc-runtime-after.log`; `CHECKS.md`'s old "963" was the stale number.

## Pass C: hygiene

The Lean hard rules hold (axioms, no `sorry`/`native_decide`, no code-changing attributes, no
`unsafe`/`partial`/`opaque`; `check-hygiene.sh` OK). No dead code found from the removals: the
`log` mode is gone from the service, `Service` and PROTOCOL; `Liveness.lean.in`, `parseLog`, the
mock `liveness` and the `--tree-repeats`/`--stream-repeats` options are gone with their callers;
`statistics` and `random` in `bench.py` are still used. Comment density and idiom match the
surrounding files. Residue is listed in m-6.

## Verdict

**Accept with the minors fixed.** The two attacked mechanisms, the one-build binding (item 9) and the
cache-isolated setup job, are sound as implemented; the contract change and its controls are
correct and non-vacuous; the separation of pipelines is complete and the moved checks are asserted
in core CI. What must change before the 30-minute rule binds entries: the certificate job's fixed
steps measured on a runner and organiser timeouts classified as ERROR (m-2); the badge cap's subject
stated to entrants, with a decision on precompiling more of Mathlib (m-1); the nesting table derived
from the code (m-3); the cache named in the trust statement, bound into the result, keyed to the
commit, and its save verified (m-4); the stream's implied per-link budget stated (m-5); the stale
rows (m-6).
