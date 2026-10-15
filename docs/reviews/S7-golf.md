# S7 golf: the baseline submission (Stage 7)

The golf agent wrote this on 2026-10-15. Nothing is committed.

**What changed.** Proofs only, in two of the four files.

- **Edited.** `submissions/baseline/RecursionFastCandidate/Protocol.lean` and `Compiled.lean`.
- **Unchanged.** No statement, type, data field, docstring or module comment changed. No declaration
  was renamed, reordered, split, merged, added or removed. No import was added.
- **Proof fields of definitions.** Two of the edited proofs are proof fields inside a `def`:
  `trivExtractor.fuel_le` and `trivKSF.next`. Every data field (`img`, `fuel`, `toFun`, all of
  `P_triv`) is byte-identical; only proof terms differ.
- **Not touched.** `Submission.lean` and `audit/BaselineSolution.lean` (see Declined).
  `RecursionFast/`, `scripts/`, `harness/` and `README.md` were not touched either.
- **Records.**
  - Originals: `logs/S7-golf/orig/` (`Protocol.lean` `bc469495…`, `Compiled.lean` `e5b5aed5…`).
  - Golfed copies: `logs/S7-golf/{Protocol,Compiled}.lean.after`.
  - Diffs: `logs/S7-golf/{Protocol,Compiled}.diff`.

**Checks.**

- **Build.** `lake build RecursionFastCandidate` was green after each file, with no warnings:
  - after `Protocol`: 19.5 s (`build-after-protocol.log`; it rebuilds all 4 modules);
  - after `Compiled`: 15.4 s (`build-after-compiled.log`).
- **LSP.** No diagnostics on either file.
- **The solution.** `audit/BaselineSolution.lean` still elaborates against the golfed candidate
  (`lake env lean -o`, `solution-after.log`), so `certified` is still `⟨⟨⟨rfl, rfl⟩⟩, rfl⟩`.
- **Axioms** (`logs/S7-golf/axioms-after.log`).
  - All 20 declarations use a subset of `propext`, `Classical.choice` and `Quot.sound`.
  - The 11 checked by `scripts/Axioms.lean` have the same sets as in `logs/S7/axioms.log`.
  - `triv_noChal` uses no axioms at all.
  - There is no `sorry`, no `native_decide` and no `Lean.ofReduceBool`.
- **Hygiene.** `submissions/baseline/scripts/check-hygiene.sh` reports OK (`hygiene-after.log`).

## Summary

| | before | after |
|---|---:|---:|
| `loc.py` code lines: `Protocol` / `Compiled` / `Submission` / root / solution | 120 / 63 / 14 / 3 / 16 | **111 / 53** / 14 / 3 / 16 |
| total code lines (`loc-before.log`, `loc-after.log`) | **216** | **197** (−19, −8.8 %) |
| theorems | 19 | 19 |
| `/usr/bin/time lake env lean Protocol.lean`, mean of 3 interleaved runs | 6.68 s | 6.52 s |
| the same, `Compiled.lean` | 6.46 s | 6.45 s |
| elaboration excluding import (profiler, mean of 3): `Protocol` | 1.81 s | 1.75 s |
| the same, `Compiled` | 1.24 s | 1.31 s (+0.07 s, about 1 % of the file's wall time) |
| peak RSS (either file) | 2.65 GB | 2.65 GB |

- **Logs.** `logs/S7-golf/time-after-interleaved.log` and `profile-nonimport-after.log`. The original
  copies and the golfed files ran alternately on the same machine.
- **Where the time goes.** Import is 3.6–3.7 s of each file's 6.5 s. Elaboration is below 0.4 s per
  file. Both files are within the ±10 % budget.
- **`Submission.lean` and the solution** are unchanged: 5.97 s and 6.48 s after, against 6.12–6.26 s
  and 6.15 s before (noise).

## Changes, by declaration

### `Protocol.lean` (120 → 111)

| declaration | before | after | lines |
|---|---|---|---:|
| `trivExtractor` (`fuel_le` only) | `le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) …)`, a 102-character line | `Nat.pow_le_pow_right two_pos (Nat.le_add_left 3 (2 * k + 13))`. The detour through `le_trans` is not needed, because `2 ^ 3` and `8 + (0 + 0)` are defeq. The `show` stays, since it states the fuel sum. | 0 |
| `trivExtractor_fuel_tight` | `⟨by decide +kernel, by decide +kernel⟩` | `by decide +kernel` (one decision of the conjunction; the kernel work is the same) | 0 |
| `triv_accepts_iff` | `simp […, leaf_zero]` then `exact congrArg _ (leaf_zero (k + 10) (tr 0))` | `simp […, leaf_zero, leaf_zero (k + 10) (tr 0)]`. The general `leaf_zero` does not fire on `tr 0`, whose type is `(trivShape k 0).Ty`, not syntactically `OVal`, so simp gets the instance explicitly. | −1 |
| `triv_noChal` | `by have := c.2; simp [trivShape, Round.isMsg] at this` | `nomatch c.2`: a term with no axioms, and the naked `;` is gone | −1 |
| `trivKSF` (`next` only) | 12 lines: destructure `m`, then `s`; prove the message's tables satisfy `relK` through `e` and `h0`; then `show`, `rw`, `exact` | 5 lines: `rintro ⟨m, _⟩ ⟨L, x⟩ tr msg w h`, `obtain rfl : m = 0`, `h' := Transcript.concat_last tr msg ▸ h`, `exact (triv_extractMid …).symm ▸ h'` | −7 |

### `Compiled.lean` (63 → 53)

| declaration | before | after | lines |
|---|---|---|---:|
| `triv_uncapped_length` | a 5-line `simp only` of 22 lemmas, mostly generic `List`/`Nat` lemmas, then `simp [pathOf, triv_depth, …]` | one `simp` with only the definitions to unfold and the domain facts: `uncapped, trivVerify, record, FullTranscript.oracles, trivShape, Round.oracles, OShape.leaves, Round.tapeBytes, OShape.plain, pathOf, triv_depth, K.bytes_length, Oracle.leaf_length`. `erw [List.length_ofFn]` and `ring` are unchanged. | −3 |
| `triv_prove_none` | 9 lines: `cases hu : uncapped …` with `none`/`some` arms, two `simp only … at h`, `exact` | 2 lines: `obtain ⟨t, hu, ht⟩ := Option.map_eq_some_iff.mp (triv_uncapped_length …)` and `rw [prove_eq_uncapped, hu, Option.bind_some, ht, ite_eq_right (triv_tape_gt_cap k hk).not_ge]`. It reads as the argument itself: the uncapped tape is `some t` of length `5 · 2^(k+11)`, which is over the cap, so the `if` gives `none`. `ite_eq_right` is the non-deprecated name of `if_neg`. | −7 |

## Declined

| item | why |
|---|---|
| `triv_secure.complete`: inline `h28` into the `pWit_eWit` argument (−1, tested) | `h28 : 2 ^ k < 2 ^ 64` names the bound the argument needs. Inlining makes the `rw` harder to read and saves one line. |
| `triv_accepts_iff`: drop `obtain ⟨L, x⟩ := s` and pass `s.1 s.2` (−1, tested) | It relies on structure eta, and `L`, `x` read better in a worked example. |
| `triv_depth`: `simp [Cfg.depth, Nat.eq_zero_or_pos]` (−1, tested) | It is 2.5× slower (44 ms against 18 ms) and moves from `simp only` to a broad `simp` to save one line. The term `Nat.div_eq_zero_iff.mpr (by omega)` fails, because `omega` does not reduce `⟨m, m⟩.logLen`. |
| `triv_extractMid`: drop `h12`, discharging `2^(k+10) ≤ 2^(k+12)` with `simp [Round.words, trivShape, witCap, Nat.pow_le_pow_right]` (tested) | The side condition then needs its own line, so nothing is saved. |
| `triv_extractMid`: `rw [Transcript.concat_last]` for `e`, `← List.map_ofFn` for the `show … from` (tested) | Both rewrites fail. `concat_last` wants `Fin.last ↑m`, not `Fin.last 0`, and `List.ofFn (K.bits ∘ msg)` does not match the lambda form. |
| `trivDecide_iff`: inline `hN` (tested) | `List.forall_mem_map.mpr` needs `hN`'s type ascription to elaborate. |
| `trivDecide_iff`: merge the two simp calls | Order matters: `relBelow_iff hN` must fire before `Layout.normal` unfolds. |
| `triv_tape_gt_cap`, `triv_narg`: remove the existing `unfold tapeCap …; omega` | Splitting the `;` costs a line, and every alternative tried was no shorter or less clear. |
| `prove_eq_uncapped` (`split <;> simp_all`), `takeN_short`, `triv_no_entry` | Already minimal. In `triv_no_entry`, `x'` → `_` is cosmetic only. |
| `trivExtractor.fuel_le` with `omega` instead of `Nat.le_add_left 3 (2 * k + 13)` | In the section, `omega` captures `hk`, which changes the type of `trivExtractor` (tested: it becomes `20 ≤ k ∧ k ≤ 28 → ExtractorImage k 1`). `show 8 ≤ …` instead of `8 + (0 + 0) ≤ …` times out in `whnf`. |
| `P_triv` proof fields (`n_le`, `vkLen_le`, `shape_ok`) | Already one token each. The data fields are out of scope. |
| `Submission.lean` | No proof is longer than `⟨⟨rfl, rfl⟩⟩` or `by decide`. |
| `audit/BaselineSolution.lean` | It is generated by `scripts/make-solution.py`, which writes the proof `⟨⟨⟨rfl, rfl⟩⟩, rfl⟩`, already minimal. A hand edit would drift from the generator. |

## For the fix pass

- **Stale line counts.** `submissions/baseline/README.md:255` and S7-RESULT (Headline "216 code
  lines", §Files table) still give 216 / 120 / 63. They are now **197 / 111 / 53**. The theorem
  count, 19, is unchanged.
- **Stale baseline log.** `logs/S7/loc.log` should be regenerated with `scripts/loc.py`.
