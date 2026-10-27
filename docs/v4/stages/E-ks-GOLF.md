# Stage E-ks (v4, SROM): golf

Status (2026-10-27): **done, uncommitted** in the worktree
`/home/devops/Verified-zkEVM/recursion.fast-v4-ks` (branch `v4/ks-standard`, on `a283ff8`). Scope:
what stage E-ks touched (`git diff 15dac52 a283ff8`). No statement, definition, docstring meaning,
rule, cap or number changed; no theorem was removed or renamed (`KState.ks` and every name the
baseline's migration uses stay); two library lemmas were added. Everything ran on the development
VM (32 vCPU); logs are under `logs/golf-ks/` (gitignored).

## 1. What changed

**Shared lemmas.** Two small lemmas replace arguments that were repeated:

- `Library/Prob.lean`, **`ind_le`**: the indicator is at most every `y` with `B x L → 1 ≤ y`. It
  replaces the `by_cases` on the event in `ind_le_ind`, `ind_le_one`, `prob_exists_le`,
  `KS.select` and `prob_le_pot`'s leaf.
- `Library/PaperTheorem.lean`, **`prob_le_of_pot`**: an event that forces the potential to `1` at
  the leaves within `logCap` has probability at most `n · ε` (`prob_le_pot`, `pot_le`,
  `k.empty`). `paper` and `prob_potential_ge_one` repeated that calc; each is now one line
  through it. The module header mentions it.

| File | Change | Why |
|---|---|---|
| `Contract/Security.lean` (**trusted**) | `prob`: `\| .query q k, L => match … with` on one line (it was two) | −1 trusted code line; the same syntax tree: `#print prob` and `prob.match_1` under `pp.all` are byte-identical before and after |
| `Library/Prob.lean` | `avg_const` first, then `avg_le` as one term through it (was two calcs, 9 lines); `ind_le` (above), `ind_le_ind` and `ind_le_one` one line each; `expect_bind_of_runLog` through `Option.bind_eq_some_iff` (no case split on the lookup, no `simp … at`); `prob_exists_le` through `ind_le`; `expect`, `withLog`: the `match` layout of `prob` | −15 code lines |
| `Library/KS.lean` | `KS.select`: the query bound by `rw` (no `simp only` with six lemmas), the win case through `ind_le` and `dsimp only [OProg.bind]` (no `show`, no negative branch); `KS.union`, `not_ks_of_accept`, `small_of_caps` in term mode (`small_of_caps`: `by norm_num [errorCap]` for `2^16 · 2^-120 < 1`, `by decide` for `2^16 ≤ logCap`) | −10 |
| `Library/PaperTheorem.lean` | `bound_found`, `bound_fresh`, `bound_zero` in term mode (`Nat.le_of_succ_le_succ`, `Nat.not_succ_le_zero`; no `omega`, no `simpa`); `pot_le`: the average of a sum through `avg_const` (was eight rewrites and a `congr`), two single-use `have`s inlined; `prob_le_pot`: the leaf by `ind_le`, the stopped branch by `prob_le_one` before `prob` is unfolded (no `split`); `prob_le_of_pot` (above); `KState.ks` in term mode (`Nat.add_le_add (hA H) (hq H _ _)` by definitional unfolding, `Nat.cast_add` in place of two `simpa`) | −20 |
| `Library/Compose.lean` | `walkFrom_leaf`: `unfold walkFrom` then one `simp only` with `extract_of_E` (was a four-way `split` with three dead branches and a `Sum.getLeft?` injectivity argument, 13 lines); `InTree.follow_eq`: `simp only` with its lemmas; `compose_prob`: the card rewritten in the goal, no intermediate `hb`; `functional_append`: `decide_eq_true` in place of a `simpa`; `escape_prob_le`: `fun _ _ _ => functional_append` | −12 |
| `Library/Completeness.lean` | `failProb_bind_false` from `prob_bind` and `expect_const` (was its own induction); `failProb`: the `match` layout | −5 |
| `Library/Oracle.lean` | `consistent_append_self` through `Option.or_eq_some_iff` (no case split on the prefix's lookup, no `by_cases` on `ByteArray` equality, no `simp at`) | −1 |
| `Controls/Compose.lean` | `noExt_walk_escaped`: `unfold walk walkFrom`, `rw` with `extract_escape`, `trivial` (was a four-way `split`); `walk_two_leaves`: the outer step by `rw` with `extract_of_E` and `dite_eq_left_of_eq_true` (was a four-way `split` and a `Wit.node.inj` argument), the trace-in-log arguments `nofun` (the traces are empty) in place of six `by simp [leafSigned]`, the impossible inner outcomes by `nofun` in place of `by simp [Outcome.starts?]`, and the six of them closed in their known order (three for the first walk, three for the second) instead of `first`, which tried the first walk's lemma on the second walk's three cases and failed each time; `fresh_answer` (in the file, older than the stage): `refine by_contra fun h => ?_` in place of `by_contra h`, which searched for a `Decidable` instance it could not find | −18; the module 2.61 → 1.71 s (§2) |
| `Controls/Security.lean` | `queryThenAccept_ks_ge_one` in one `simpa` (no `have`, `rw … at`); `queryThenAccept_ks_one`: the query bound `le_rfl` | −3 |
| `Controls/Certificate.lean` | `big_complete` through `completeWithError_iff.mpr`, so the leaf case is the v3 line (no `failProb_eq_prob` detour) | −1 |
| `Controls/Potential.lean` | `twoLucky_ks_exact`, `twoLucky_ks`, `collision_ks`, `v24_ks`: the verifier's query bound `le_rfl` (each verifier asks two fixed queries) in place of `by simp [·, OProg.queries]` | same lines, four `simp` calls fewer |
| `docs/v4/BRIEF.md` §2 | the model paragraph said "textbook since V4-A10" twice and broke a sentence mid-line; one sentence now: the model is v3's but for V4-A10, `KS` is the textbook statement, the potential a library route | same claims and ids, −1 line |

`big_secure` (`Controls/Certificate.lean`) and `sigTrust_ks_of_unsignable` (`Library/SigTrust.lean`)
are shorter through `KS.of_extracts` than through the bridge; not changed, since RESULT §4 records
them as proved through the bridge (§4 item 3). Nothing else in `SigTrust.lean`,
`WitnessSending.lean`, `Library/Security.lean`, `Controls/Backdoor.lean` or
`Controls/Completeness.lean` was worth changing: the stage's edits there are one-line bridge calls,
moves and new controls already in term mode. The design and RESULT are dense but not wordier than
the text around them; not changed.

## 2. Numbers, before → after

**Elaboration**, per module: the profiler's total minus `import`, minimum of 3 runs, HEAD's copy of
the file and the golfed file run alternately against the same (current) imports
(`logs/golf-ks/elab-ab.log`, the script `ab.py` in the scratchpad's `golf-ks/`). Modules this golf
did not change move by up to ±0.09 s: that is the noise.

| Module | `a283ff8` | golf | Δ |
|---|---:|---:|---:|
| `Contract/Security.lean` | 0.57 s | 0.58 s | +0.01 |
| `Library/Oracle.lean` | 0.64 | 0.68 | +0.04 |
| `Library/Prob.lean` | 2.09 | 1.96 | −0.13 |
| `Library/KS.lean` | 0.92 | 0.89 | −0.03 |
| `Library/PaperTheorem.lean` | 2.15 | 1.61 | **−0.54** |
| `Library/Completeness.lean` | 0.80 | 0.68 | −0.12 |
| `Library/Compose.lean` | 5.27 | 4.78 | **−0.49** |
| `Library/Security.lean` (unchanged) | 1.95 | 2.01 | +0.06 |
| `Library/SigTrust.lean` (unchanged) | 0.72 | 0.70 | −0.02 |
| `Library/WitnessSending.lean` (unchanged) | 4.01 | 3.92 | −0.09 |
| `Controls/Security.lean` | 1.69 | 1.66 | −0.04 |
| `Controls/Certificate.lean` | 2.27 | 2.24 | −0.03 |
| `Controls/Backdoor.lean` (unchanged) | 1.70 | 1.66 | −0.05 |
| `Controls/Potential.lean` | 5.07 | 5.12 | +0.05 |
| `Controls/Completeness.lean` (unchanged) | 2.49 | 2.45 | −0.04 |
| `Controls/Compose.lean` | 2.61 | 1.71 | **−0.90** |
| **the 16 modules** | **34.96** | **32.63** | **−2.33** |

The declarations behind it (`-Dprofiler.threshold=20`, `decl-profile-before.log`,
`decl-profile-after.log`): `walk_two_leaves` 0.73 → 0.10 s; `fresh_answer` 0.30 s → below 0.02 s;
`InTree.follow_eq` 0.29 → 0.05 s; `KState.ks` 0.14 s → below 0.02 s; `pot_le`
0.17 → 0.13 s; `noExt_walk_escaped` 0.10 → 0.02 s. `walkFrom_leaf` stays at 0.92 s (was 0.95):
it is the first `unfold walkFrom`, which generates `walkFrom`'s equation lemmas (§4 item 2).

**Lines** (`scripts/loc.py`):

| Quantity | `a283ff8` | golf | Log |
|---|---:|---:|---|
| contract code lines (as `ci.yml`) | 350 | **349** (`Security.lean` 28 → 27) | `loc-before.log`, `final-loc.log` |
| Library code lines, theorems | 2,281, 285 | 2,218, 287 | `loc-library-controls-before.log`, `loc-library-after.log` |
| Controls code lines, theorems | 2,165, 322 | 2,143, 322 | same, `loc-controls-after.log` |

Per file (code lines): Library `Prob` 158 → 143, `KS` 70 → 60, `PaperTheorem` 124 → 104,
`Compose` 322 → 310, `Completeness` 57 → 52, `Oracle` 63 → 62; Controls `Compose` 134 → 116,
`Security` 138 → 135, `Certificate` 140 → 139.

**Build and smoke**: `timeout 1800 lake build` after the edits, 37.8 s incremental (the RESULT's
final pass: 40.3 s); `smoke.py --org` **253.7 s** (4 min 14 s) against the RESULT's 265.6 s
(4 min 26 s), no path it runs changed beyond the library's elaboration: noise
(`final-summary.log`).

## 3. Checks (all pass)

One pass on the final tree, each step under its `ci.yml` timeout, by the implementer's script
extended with the service and harness tests and the chain checker (`final-summary.log`, each step
`final-<step>.log`; the script is `golf-ks/run/run.sh` in the scratchpad).

| Step | Outcome | Duration |
|---|---|---|
| `timeout 1800 lake build` | green, 1,266 jobs, no warning | 37.8 s |
| line budget (`loc.py`, as `ci.yml`) | 349 ≤ 500 | 0.1 s |
| axiom audit | PASS (every declaration within `propext`, `Classical.choice`, `Quot.sound`) | 4.8 s |
| hygiene, source-rule fixtures | OK | 4.9 s |
| `org-setup.sh` (`RF_BADGE_OBJECTS=`) | OK | 74.7 s |
| token sweep | 411 tokens, 0 unreviewed (the note "Word reprove" is pre-existing) | 12.8 s |
| gate fixtures | OK | 52.8 s |
| `signer`, `extract` build; Lean signer against the service | OK; 0 failures | 5.2 s; 54.3 s |
| `extract` | 4 cases, 0 failures | 0.3 s |
| `acc` probe, organiser's canaries | 0 failures | 36.3 s |
| chain checker | 3 runs `ok` | 8.6 s |
| service build, `cargo test` | OK (4 tests) | 0.3 s (cached) |
| `test_service.py`, `test_sandbox.py`, `test_tv.py`, `test_aggregate.py`, `test_dos.py` | 0 failures each | 16.3, 20.8, 0.2, 1.6, 0.2 s |
| `smoke.py --mock` | 10 checks, 0 failures | 26.8 s |
| `smoke.py --org` | **16 checks, 0 failures**; the witness-sending entry certified (Lean kernel) and ACCEPTed with the compiled `accF` badge | 253.7 s |
| after restoring the link: `lake build`, axiom audit against the shared `pkgs-local` | green, PASS | 2.2 s, 4.7 s |

**How the smoke ran** (as in the RESULT, §6): `.lake/packages` pointed at the private copy
`.lake/pkgs-ks` for the steps from `org-setup.sh` on, with the comparator the implementer built
into the scratchpad (`logs/ks/kernels.env`); then the link was restored to
`/home/devops/Verified-zkEVM/recursion.fast-v4/.lake/pkgs-local` and the build and the audit
re-ran there. No file in the shared tree is newer than the golf's start
(`final-pkgs-local-written.txt`, empty). `.lake/pkgs-ks` (9.2 GB) is still there, for the fix pass.

**Statements**: every declaration header in the changed Lean files is the same text as at
`a283ff8` (a scripted comparison of the text before `:=`, its three heuristic mismatches checked by
hand: match-style proofs); the only new declarations are `ind_le` and `prob_le_of_pot`.

## 4. Suggestions not applied

1. **Numbers in other documents, if this golf is taken** (this golf changes no number in a
   document): the contract is **349** code lines, `Contract/Security.lean` **27**. The design
   states 350 in §0 ("Trusted code: 350 Lean lines"), §2.7 item 2 ("10 files, 350 code lines")
   and the §5 table (`Security.lean` 28, **total** 350; "355 before V4-A10" stays). The RESULT's
   summary paragraph, §2 and §6 quote 350 for the stage's own commit, which stays true of
   `a283ff8`. Library and
   Controls line counts (RESULT §4: 2,281 and 2,165) become 2,218 and 2,143.
2. **`walkFrom`'s equation lemmas cost 0.6 s** at the first `unfold` (in `walkFrom_leaf`), from its
   overlapping patterns on `(r, hs)`; a definition that matched on `r` alone and on `hs` inside
   might generate cheaper ones (untested). Not applied: it changes a definition.
3. **`big_secure` and `sigTrust_ks_of_unsignable` through `KS.of_extracts`** rather than
   `KState.zero` and the bridge: one line shorter and more direct, and `SigTrust.lean` would no
   longer import `PaperTheorem` (checked: both compile). Not applied: RESULT §4 records both as
   proved through the bridge. `rejectAll_ks` likewise (no line saved).
4. **`acc_false` (`Controls/Certificate.lean`, older than the stage) spends 1.0 s** synthesising
   `Decidable` instances inside `simp [Sbig, Vbig, OProg.runSeq, …]`, the slowest declaration of
   the touched controls. Not applied: not the stage's.
5. A shared `KS.of_total` (the reverse direction of `acceptAll_ks_iff` and `sigTrust_ks_iff`, an
   extractor that returns a chosen witness) would cost more lines than it saves.
