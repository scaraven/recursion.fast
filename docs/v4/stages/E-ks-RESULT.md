# Stage E-ks (v4, SROM): textbook knowledge soundness — RESULT

Status (2026-10-27): **done, not yet reviewed.** The user's decision V4-A10 (`docs/v4/BRIEF.md`
§5c) implemented on the branch `v4/ks-standard` (worktree
`/home/devops/Verified-zkEVM/recursion.fast-v4-ks`, from `v4/trim-fat` at `15dac52`), uncommitted.
Everything below ran on the development VM; nothing ran on GitHub. Logs are under `logs/ks/`
(gitignored).

**In one paragraph.** The contract now states **textbook single-output knowledge soundness** in
the random-oracle model: every adversary, a query program asking at most `Q` queries and outputting
a statement and a proof, run and then followed by the verifier against one lazily sampled random
oracle, makes the verifier accept on the final query log while the extractor, given the statement,
the proof and that log, returns no witness, with probability at most `(Q + qV)·ε`, for
`Q + qV ≤ logCap`. v3's potential (`KState`, same name, same laws) is an untrusted library tool,
and `KState.ks` turns one into `KS`; every entry and control that went through a knowledge state
migrates through it. `failProb` left the contract too: `CompleteWithError` is stated through the
same `prob`, provably the same statement. The tree's composition is now a **kernel theorem with
probabilities** (`Compose.compose_prob`): the walk on the run's log ends in an escape with
probability at most `(2^(r+1) − 1)·(Q + qV)·ε`, a union bound over the extraction tree's members.
Trusted lines **355 → 350**. The build, the axiom audit, every test `ci.yml` runs and the
end-to-end smoke pass; the witness-sending entry certifies under the new contract and ACCEPTs.

## 1. What was built

| File | What changed |
|---|---|
| `RecursionFast/Contract/Security.lean` | `prob` (the lazy-sampling probability, from `Library/PaperTheorem.lean`); `KS` the textbook statement; `CompleteWithError` through `prob`; `KState` and `failProb` removed; the header rewritten (what `KS` says, the adversary, why `qV` is charged, why `logCap`, what it does not exclude, the potential as a library route) |
| `RecursionFast/Contract/Oracle.lean`, `Contract.lean` | header comments only |
| `RecursionFast/Library/Security.lean` | `KState` moved here, unchanged, with its docstrings; header (why a potential, why the guard) |
| `RecursionFast/Library/Prob.lean` (new) | the calculus of `prob`: `expect`, `ind`, `prob_eq_expect`, monotonicity (also along an invariant of the log), `expect_sum`, the union bound `prob_exists_le`, `expect_bind`/`prob_bind`, `prob_bind_of_runLog`, `withLog` (a program that keeps its own log) with `expect_withLog`, `queries_withLog_le`; `avg_le`, `avg_const`, `prob_le_one`, `prob_eq_zero` |
| `RecursionFast/Library/KS.lean` (new) | `Wins`, `KS.bound`, **`KS.select`** (KS against an adversary that outputs any function of its own log), **`KS.union`**, `KS.of_extracts`, `KS.mono`, `accept_wins`, `not_ks_of_accept`, `small_of_caps`, `acceptAll_ks_iff` |
| `RecursionFast/Library/PaperTheorem.lean` | `pot_le`, `prob_le_pot`, `paper` generalised from the syntactic `DepthLE` to the functional query bounds (`bound_found`, `bound_fresh`, `bound_zero`); `prob_potential_ge_one`; **the bridge `KState.ks`**; `DepthLE` and the local `prob` removed |
| `RecursionFast/Library/Oracle.lean` | `queries_bind`, `bind_assoc`; `Consistent`, `exists_consistent`, `consistent_append` moved here from `Completeness.lean`; `consistent_append_self` |
| `RecursionFast/Library/Completeness.lean` | `failProb` (v3's definition, moved here), `failProb_eq_prob`, **`completeWithError_iff`** (the contract's `CompleteWithError` is v3's statement word for word) |
| `RecursionFast/Library/Compose.lean` | the walk without a knowledge state: a fourth outcome, the **escape**; `InTree` with paths; `follow`, `Escape`, `Outcome.Escaped`; `Escape.wins`, `escape_prob_le`, `paths`, `card_paths`, **`compose_prob`**; the meter's lossless form `compose_of_kstate`, `Escape.not_of_kstate`; `extract_escape` |
| `RecursionFast/Library/WitnessSending.lean`, `SigTrust.lean` | through the bridge; `SigTrust`: the adversary that holds `sk` and the `KS` statements (§4) |
| `RecursionFast/Library/Trace.lean`, `Library.lean`, `RecursionFast.lean`, `Controls.lean` | header comments and imports |
| `RecursionFast/Controls/Security.lean` | direct controls of the textbook `KS` (§4); the potential's controls kept as library facts |
| `RecursionFast/Controls/Certificate.lean`, `Backdoor.lean`, `Potential.lean`, `Completeness.lean`, `Compose.lean` | re-proved or migrated (§4); `prob`'s controls; the composition's controls |
| `docs/DESIGN-v4-srom.md` | status, §0 (summary, the status table, the v3/v4 table), §1.4, §2.1, §2.2, §2.4, §2.7 items 2 and 4, §2.8, §4.4, §5, §6.1 (V4-A10), §6.2, §7 |
| `docs/v4/BRIEF.md` | §5c, amendment V4-A10; §2 and V4-1 annotated |
| `docs/v4/CHECKS.md`, `README.md`, `docs/README.md`, `CLAUDE.md` | where they describe the security definition or the trusted line count |

No Python, Rust, workflow or harness file changed.

## 2. The contract

**The new `KS`**, as it stands in `Contract/Security.lean`:

```lean
noncomputable def prob {α : Type} (B : α → Log → Prop) : OProg α → Log → ℝ≥0
  | .ret x, L => by classical exact if B x L then 1 else 0
  | .query q k, L =>
    match L.find? fun e => e.1 = q with
    | some e => prob B (k e.2) L
    | none => (2 ^ 256)⁻¹ * ∑ a : Digest, prob B (k a) (L ++ [(q, a)])

def KS (R : Digest → Wit → Prop) (V : Digest → Proof → OProg Bool)
    (E : Digest → Proof → Log → Option Wit) (ε : ℝ≥0) (qV : ℕ) : Prop :=
  (∀ H c π, ((V c π).queries H).length ≤ qV) ∧
  ∀ (A : OProg (Digest × Proof)) (Q : ℕ), (∀ H, (A.queries H).length ≤ Q) → Q + qV ≤ logCap →
    prob (fun x L => (V x.1 x.2).runLog L = some true ∧ ¬ ∃ w, E x.1 x.2 L = some w ∧ R x.1 w)
      (A.bind fun x => (V x.1 x.2).bind fun _ => .ret x) [] ≤ (Q + qV) * ε

def CompleteWithError (R : Digest → Wit → Prop) (P : Digest → Wit → OProg Proof)
    (V : Digest → Proof → OProg Bool) (δ : ℝ≥0) : Prop :=
  ∀ c w, R c w → prob (fun b _ => b = false) ((P c w).bind (V c)) [] ≤ δ
```

It is the starting design of the brief, unchanged. `(Q + qV) * ε` elaborates as
`(↑Q + ↑qV) * ε` in `ℝ≥0`. The adversary's budget is functional, like `qV`: workable, since a
lazily sampled run agrees with some oracle function (`Library/PaperTheorem.lean`, `bound_found`,
`bound_fresh`; `Library/Prob.lean`, `queries_withLog_le`), so `DepthLE` was not needed.

**The diff in words.** Removed: `KState` (the structure, its four fields and their docstrings),
`failProb`, the old `KS` (`Nonempty KState ∧` the query bound). Added: `prob` and the new `KS`
(the query bound is now the **first** conjunct, the bound the second). `CompleteWithError`'s body
reads `prob (fun b _ => b = false)` where it read `failProb`; `Library/Completeness.lean`'s
`completeWithError_iff` proves it the same statement. `logCap`'s docstring now says what it bounds
(the adversary's and the verifier's queries together). `Certificate.lean` is unchanged:
`secure : ∀ vk, KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV`, `errorCap = 2^-120`, `logCap = 2^96`,
`Computes`, the caps. **Trusted lines** (`scripts/loc.py`, as CI runs it): `Security.lean`
33 → 28, the contract **355 → 350** of 500 (`logs/ks/loc-before.log`, `logs/ks/loc.log`).

**One property to know** (stated in the header, with a control): for `qV > logCap` no adversary
satisfies `Q + qV ≤ logCap`, so `KS` is vacuous there (`Controls/Security.lean`,
`acceptAll_ks_above_logCap`); `Certificate`'s `qV ≤ 2^16` excludes it. The old `KS` was not
vacuous there (its potential did not depend on `qV`). See open question 3.

## 3. The bridge

```lean
theorem RecursionFast.KState.ks {R : Digest → Wit → Prop} {V : Digest → Proof → OProg Bool}
    {E : Digest → Proof → Log → Option Wit} {ε : ℝ≥0} {qV : ℕ} (k : KState R V E ε)
    (hq : ∀ H c π, ((V c π).queries H).length ≤ qV) : KS R V E ε qV
```

In `Library/PaperTheorem.lean`; no extra hypothesis. The game `A.bind (V …).bind ret` asks at most
`Q + qV` queries under every oracle function (`OProg.queries_bind`), and the generalised `paper`
bounds it by `(Q + qV)·ε`. An entry migrates `⟨⟨k⟩, hq⟩` to `k.ks hq` (or `KState.ks k hq` when
`k`'s type must come from the expected type, as in `Controls/Security.lean`, `rejectAll_ks`).

**For the baseline's migration** (`spartan-srom`, submissions repository): besides `⟨⟨k⟩, hq⟩ ↦
k.ks hq`, any use of `h.1` / `h.2` on a `KS` swaps (the query bound is now `h.1`);
`PaperTheorem.prob` is the contract's `RecursionFast.prob`; `PaperTheorem.DepthLE` is gone and
`PaperTheorem.paper` takes `∀ H, (G.queries H).length ≤ n`; `PaperTheorem.avg_le`, `N_pos`,
`prob_le_one` are `RecursionFast.avg_le`, `N_pos`, `prob_le_one` (`Library/Prob.lean`); `Consistent`
is in `Library/Oracle.lean`; `failProb` is a library definition (`completeWithError_iff` converts a
`failProb` bound); `Compose.walk` and `compose` take the log first and no knowledge state.

## 4. The controls

**New, direct against `KS`** (`Controls/Security.lean`; each negative exhibits its adversary):

| Control | Kind | What it shows |
|---|---|---|
| `acceptAll_wins`, `acceptAll_not_ks` | negative | for the empty relation the adversary `ret (0, ∅)`, no query, wins with probability exactly 1, so the accept-all verifier is knowledge-sound at no error, whatever the extractor |
| `acceptAll_not_ks_none` | negative | nor for `Rel acc` with the extractor that returns nothing, at any `qV ≤ logCap`, `qV·ε < 1` |
| `queryThenAccept_wins`, `queryThenAccept_ks_ge_one` | negative | a verifier that asks one query and accepts: the adversary that asks nothing wins with probability 1, so `qV = 1` needs `ε ≥ 1` (the verifier's queries are charged) |
| `queryThenAccept_ks_one` | positive | it is knowledge-sound at `ε = 1`: the error fails, not the definition |
| `oneQuery_not_KS` | negative | the query conjunct (now `h.1`) |
| `acceptAll_ks_above_logCap` | what it does not say | `KS` is vacuous for `qV > logCap` |
| `prob_askGood` (`Controls/Completeness.lean`) | positive, `prob` | a fresh answer is uniform: exactly `1/2` |
| `prob_askTwice` (`Controls/Completeness.lean`) | negative, `prob` | a repeated query is the table's answer: probability `0`, where re-sampling would give `1 − 2^-256` |
| `twoLucky_ks_exact` (`Controls/Potential.lean`) | positive | `twoLucky` is knowledge-sound at its own error `2^-192`, through its potential |

**Library facts with the same purpose** (`Library/KS.lean`, `Library/SigTrust.lean`):
`acceptAll_ks_iff` (the `KS` twin of `acceptAll_kstate_iff`), `not_ks_of_accept`, `accept_wins`;
`SigTrust.adversary` (asks nothing, outputs `c` with `sk`'s signature of `c`), `adversary_wins`
(probability 1 unless `E` opens it), `sigTrust_ks_extracts`, `sigTrust_not_ks_none`,
`sigTrust_ks_iff`.

**Re-proved against the new `KS`** (statements unchanged):
- `Controls/Certificate.lean`: `sigTrust_no_certificate` (the certificate's `∀ vk` reaches
  `Signer.pk sk`, the adversary holding `sk` wins with probability 1, above `qV·ε < 1`, which the
  caps give: `small_of_caps`), `sigTrust_certificate_opens`, `acceptAll_no_certificate`;
  `big_secure` (through the bridge); `choice_certificate` holds with its proof unchanged.
- `Controls/Backdoor.lean`: `certified` (still certified in the model), through the bridge.
- `Controls/Potential.lean`: `twoLucky_ks`, `collision_ks`, `v24_ks`, through the bridge.
- `Controls/Security.lean`: `ws_ks` (through `WitnessSending.ks`, itself through the bridge),
  `rejectAll_ks`, `rejectAll_not_complete` (through `completeWithError_iff`).
- `Controls/Completeness.lean`: `grind40_complete`, `grind39_not_complete`, `fixed_complete_half`,
  `fixed_not_complete` (through `completeWithError_iff`; their `failProb` computations unchanged).
- `Library/SigTrust.lean`: `sigTrust_ks_of_unsignable` (the twin), through the bridge.

**Moved, as library facts about `KState`** (statements unchanged): `acceptAll_kstate_iff`,
`no_kstate_of_empty`, `KState.ofBool`, `KState.zero`, `KState.mono`, `step_of_hits`,
`KState.final_unguarded`, `KState.step_unstopped`, `KState.one_le_of_jump`
(`Library/Security.lean`); `sigTrust_kstate_iff`, `sigTrust_extracts`, `sigTrust_no_kstate_none`
(`Library/SigTrust.lean`); in `Controls/Security.lean` `queryThenAccept_ge_one`, `ks1`,
`mono_control`, `acceptAll_no_kstate_empty`, `acceptAll_no_kstate_none`, `jumpAll_ge_one`,
`badAll_not_capped` and the boolean form; all of `Controls/Potential.lean`'s negatives.

**Composition controls** (`Controls/Compose.lean`): kept and adapted `walk_one_leaf`,
`walk_two_leaves`, `forgery_trivial`, `compose_exists_free`; new `ws_compose_prob` (positive: the
witness-sending walk escapes with probability 0, against every adversary under every key),
`noExt_not_ks`, `noExt_walk_escaped`, `noExt_escape_prob` (negative: with an extractor that returns
nothing, the walk on an honest one-leaf tree escapes at the root, so `compose_prob`'s event is
certain; only the hypothesis `KS` bounds it).

Counts (`scripts/loc.py`): Library 1,856 → 2,281 code lines, 233 → 285 theorems; Controls
2,082 → 2,165 code lines, 309 → 322 theorems (`logs/ks/loc-library-controls.log`, the controls
recounted after `prob`'s two controls).

## 5. Composition: what is kernel and what is paper

**Kernel** (`Library/Compose.lean`, on the exact contract text):

```lean
theorem RecursionFast.Compose.compose_prob (hks : KS (Rel (S.acc vk)) (S.V vk) S.E ε qV)
    (n : ℕ) (hn : n ≤ chainCap) (r : ℕ) (hs : List Digest) (hr : hs.length = 2 ^ r)
    (A : OProg Signed) {Q : ℕ} (hA : ∀ H, (A.queries H).length ≤ Q) (hQ : Q + qV ≤ logCap) :
    prob (fun p L => ∃ hacc : S.acc vk (treeRoot (hs.map fun h => leafStmt h n)) p = true,
      (walk L n hn r hs hr p hacc).Escaped) A [] ≤ (2 ^ (r + 1) - 1 : ℕ) * ((Q + qV) * ε)
```

For an adversary asking at most `Q` queries and outputting the root signed proof, the probability
over one lazily sampled random oracle that `acc` accepts the root and the walk on the final log
returns none of the leaf starts, a collision, or a forgery in the extraction tree is at most
`N·(Q + qV)·ε` with `N = 2^(r+1) − 1`. The pieces: the walk (no knowledge state needed; its fourth
outcome is the escape), `Escape.wins` (on a functional log an escape is a win of `KS`'s game at that
member), `KS.select` (the adversary that runs `A` keeping its log, `withLog`, and outputs the member
at a path asks at most `Q` queries, and `V` run after it on an accepted member asks nothing fresh),
`KS.union` and `escape_prob_le` (the union bound over any finite set of paths), `card_paths`
(`2^(r+1) − 1` paths of length at most `r`). The bound is `N·(Q + qV)·ε`, **not**
`N·(Q + d·qV)·ε`: no member's adversary runs an inner verifier, since `E` reads the log.

`compose_prob` is stated on the walk's output, not on `compose`'s disjunction: that leaf starts
*exist* is free whenever the harness drew them, so the event "accepted and no starts exist" would
be empty for every honest tree; the content is that `walk` computes them (RA-M1).

Also kernel: `compose_of_kstate`, the meter's lossless form (a knowledge state and one functional
log within `logCap` below potential 1: no member escapes, the walk returns the first three
outcomes), and `PaperTheorem.prob_potential_ge_one` (the potential reaches 1 with probability at
most `n·ε` for a game of `n` queries), so an entry with a potential keeps the one-event bound
`(Q + qV)·ε` for the tree; joining the two (a lazily sampled log is functional and within
`logCap`) is a paper step, not a stated theorem.

**Paper**: the passage from the lazily sampled oracle to a random function and to randomised
adversaries; the reading of the forgery outcome as an EUF-CMA forgery or a trace-digest collision;
the PRF hybrid; and the walk over the **stream's** shape (the kernel walk is the balanced tree's, as
before; the union bound `escape_prob_le` is kernel for any finite set of paths, so for the comb's
513).

**Numbers** (recomputed). The season tree's extraction tree has `2^7 − 1 = 127` members; the
stream's final output (`M = 256`) `257 + 256 = 513`, depth 256. At `Q ≈ 2^30`, `ε = 2^-120`,
`qV ≤ 2^16`: `513 · 2^30 · 2^-120 ≈ 2^-81.0` for the stream's output, `127 · 2^30 · 2^-120 ≈
2^-83.0` for the tree's root, against `2^30 · 2^-120 = 2^-90` with the potential's lossless
composition (**estimate**; the design's §2.4).

The documents say exactly this: design §2.4 (the table), §2.7 item 4, §2.8, §0, BRIEF V4-A10.

## 6. Checks

Final pass on the final tree, every step under its `ci.yml` timeout (`logs/ks/final-summary.log`,
each step's log `logs/ks/final-<step>.log`; the script, kept outside the repository, is
`/tmp/claude-1000/-home-devops-Verified-zkEVM-recursion-fast/deb0fda2-5afe-4ae8-816d-bf1a4a32e03f/scratchpad/ks-final/run.sh`):

| Step | Outcome | Duration (`final-summary.log`) |
|---|---|---|
| `timeout 1800 lake build` | green, 1,266 jobs, no warning | 40.3 s (incremental) |
| line budget (`loc.py`) | 350 ≤ 500 | 0.1 s |
| axiom audit | PASS | 4.7 s |
| hygiene, source-rule fixtures | OK | 5.7 s |
| `org-setup.sh` (`RF_BADGE_OBJECTS=`) | OK | 58.9 s |
| token sweep | 0 unreviewed | 17.8 s |
| gate fixtures | OK | 54.3 s |
| `signer`, `extract` build; Lean signer against the service | OK; 0 failures | 5.7 s; 55.7 s |
| `extract` | 4 cases, 0 failures | 0.3 s |
| `acc` probe, organiser's canaries | 0 failures | 43.8 s |
| `smoke.py --mock` | 10 checks, 0 failures | 28.0 s |
| `smoke.py --org` | **16 checks, 0 failures**; the witness-sending entry certified (Lean kernel) and ACCEPTed | 265.6 s (4 min 26 s) |
| after restoring the symlink: `lake build`, axiom audit against the shared `pkgs-local` | green, PASS; 0 files written there | 2.3 s, 4.6 s |

The service's and the harness's own tests (Rust and Python, untouched by this stage) ran in the first
pass below.

First pass, during the stage (same commands; logs under `logs/ks/`):

| Check | Outcome | Duration, log |
|---|---|---|
| baseline `lake build` of `15dac52` in this worktree | green, 1,264 jobs | 1 min 29 s cold for the project's modules, `lake-build-baseline.log` |
| `timeout 1800 lake build` | green, 1,266 jobs, no warning | 11.8 s incremental, `lake-build.log` |
| axiom audit (`axiomaudit`, as CI) | PASS, every declaration within `propext`, `Classical.choice`, `Quot.sound` (the new `Prob`, `KS` included) | 4.6 s, `axiom-audit.log` |
| line budget (`loc.py`, as CI) | 350 ≤ 500 | `loc.log` (before: `loc-before.log`, 355) |
| hygiene, source-rule fixtures | OK | `hygiene.log` |
| service: build, test-keys build, `cargo test` | OK | 47.9 s, `service-build-test.log` |
| `test_service.py` | 90 checks, 0 failures | 16.8 s, `test_service.log` |
| `test_sandbox.py`, `test_tv.py`, `test_aggregate.py`, `test_dos.py` | 45, 6, 12, 6 checks, 0 failures | 21.3 s, 0.2 s, 1.7 s, 0.2 s; `test_*.log` |
| `smoke.py --mock` | 10 checks, 0 failures | 27.3 s, `smoke-mock.log` |
| `org-setup.sh` (`RF_BADGE_OBJECTS=`, as CI) | OK | 86 s, `org-setup.log` |
| token sweep | 411 tokens, 0 unreviewed (the note "Word reprove" is pre-existing) | `token-sweep.log` |
| gate fixtures | OK (ws, backdoor, comppoly PASS) | 59.3 s, `gate-fixtures.log` |
| Lean signer against the service | 0 failures | 64.7 s, `test_lean_signer.log` |
| compiled extractor interpreter (`extract`) | 4 cases, 0 failures | 0.36 s, `extract.log` |
| `acc` probe and the organiser's canaries | 0 failures, all 7 canaries rejected | 40.6 s, `accprobe.log` |
| chain checker | 3 runs ok | `chaincheck.log` |
| `build-kernels.sh` (comparator `d03acab`, lean4export) into the scratchpad | OK | 25.4 s, `build-kernels.log` |
| `smoke.py --org` (end to end, as CI's `smoke` job) | **16 checks, 0 failures**: the witness-sending entry certified with the Lean kernel under the new contract, ACCEPT with the compiled `accF` badge | 4 min 51 s, `smoke-e2e.log` |
| `py_compile` | no Python touched | — |

**How the smoke ran here** (as in stage D-trim): `org-setup.sh` and the badge build write compiled
objects into the package tree, so they ran against a private copy, `.lake/pkgs-ks` (9.2 GB,
`cp -a` of `pkgs-local`, 20.3 s, `pkgs-copy.log`), with `.lake/packages` pointing at it; the
symlink was then restored to `/home/devops/Verified-zkEVM/recursion.fast-v4/.lake/pkgs-local`
and the build and the audit re-ran against it, writing nothing there (`final-summary.log`). The
comparator was built from its pin into the scratchpad rather than taken from the read-only
`CambridgePQ` tree. **Leftover to delete** (gitignored): `.lake/pkgs-ks` (9.2 GB), kept for the fix
pass's re-run of the smoke.

## 7. Deviations from the brief, and why

1. **`compose_prob` is stated on the walk's output** (`Outcome.Escaped`), not on `compose`'s
   disjunction: the existence of leaf starts is free for honest trees (§5), so a bound on "no
   starts exist" would say nothing.
2. **The bound is `N·(Q + qV)·ε`**, sharper than the target `N·(Q + d·qV)·ε`: the per-member
   adversary needs no verifier run (`E` reads the log), and the one `V` run in its game asks nothing
   fresh on an accepted member.
3. **The walk changed shape**: it needs no knowledge state, no functional log and no length bound,
   takes the log explicitly, and has a fourth outcome, the escape; `InTree` carries the member's
   path (the union bound's index); `compose_exists` has four disjuncts. The old KState walk is kept
   as a corollary (`compose_of_kstate`), not as a separate walk.
4. **`failProb` left the contract** (the brief allowed it): 6 lines saved, and
   `completeWithError_iff` proves the statement unchanged.
5. **`paper` was generalised and `DepthLE` removed** (nothing else used it).
6. **New library modules** `Prob.lean` (the calculus of `prob`) and `KS.lean`; `Consistent` moved to
   `Library/Oracle.lean`; `avg_le`, `N_pos`, `prob_le_one` left the `PaperTheorem` namespace.
7. **Controls for `prob`** (`prob_askGood`, `prob_askTwice`): `prob` is a new trusted definition.

## 8. Open questions

1. **What "the whole run" bounds.** The bound is per composed output: 127 members for the tree's
   root, 513 for the stream's final output. A claim about every stream output at once, by the same
   union bound taken over every output's extraction tree, would count about
   `Σ_{i ≤ 256} (2i + 1) ≈ 2^16` members, about `2^-74` at `2^30` queries (**estimate**); the
   documents quote the per-output figures.
2. **The stream's walk** (a comb of depth 256) is paper; the union bound is kernel for its 513
   paths. A kernel walk over the stream's shape is a library follow-up with no trusted change.
3. **`KS` is vacuous for `qV > logCap`**, excluded only by `Certificate`'s `qV ≤ 2^16`. Adding
   `qV ≤ logCap` as a conjunct of `KS` would make the definition non-vacuous by itself, at one
   trusted line; not done, since the certificate's cap already forces it.
4. **The baseline's migration** (§3 lists the API changes): the `KS` conjuncts swap order; an entry
   that destructures `KS` must follow.
5. Unchanged and still open: everything in `D-trim-RESULT.md` §8 and design §6.2.
