# S8 golf: `RecursionFast/Clean/*.lean` (Stage 8)

The golf agent wrote this on 2026-10-15. Nothing is committed.

**What changed.** Proofs only, in `Clean/Semantics.lean`, `Clean/Gadget.lean`,
`Clean/ToLayout.lean` and `Clean/Examples.lean`.
- **Unchanged.** No statement, type, definition body, docstring or module comment changed. No
  declaration was added, removed, renamed, reordered, split or merged; no import changed.
  `Clean/FiniteField.lean` and the root `Clean.lean` are byte-identical (nothing in them is a
  theorem proof worth touching; see Declined).
- **One proof comment removed**: `-- the fixed chips carry their tables` in `rel_toLayoutWit`,
  whose `have hfixt` is now inlined into its only use.
- **Not touched:** `Contract/`, `Controls/Layout.lean`, `Library/Codec.lean`, the lakefile,
  `scripts/`, `harness/`, `submissions/`, and every `decide +kernel` control.
- **Records** (`logs/S8-golf/`): the originals `orig/*.lean` (SHA-256 `b561dd6d…` Semantics,
  `d0256d91…` Gadget, `998c825d…` ToLayout, `0343031f…` Examples), the diffs `*.diff`, the
  timings `time-final.log`, `time-final-examples.log`, `time-examples-interleaved.log`, the
  profiles `prof-{before,after}-Semantics.log`, the axiom audit `axioms-after.log` (from
  `scratch/Axioms.lean`), line counts `loc-{before,after}.txt`.

**Checks.**
- **Build.** `lake build RecursionFastClean` was green after each file was installed
  (Semantics, Gadget, ToLayout, Examples, in that order; 2,370 jobs). It prints no warning from
  our modules (only Clean's own two deprecations in `Gadgets/Conditional.lean`).
- **LSP.** No diagnostics on any of the five files, not even a linter warning.
- **Axioms** (`axioms-after.log`). All 210 theorems of the five modules (the 121 written ones
  plus Lean's generated equation, `congr_simp` and injectivity lemmas) use a subset of
  `propext`, `Classical.choice`, `Quot.sound`. `#print axioms toLayout_rel_iff`:
  `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide`, `admit`.
- **Hygiene.** `scripts/check-hygiene.sh`: OK.
- **Line length.** No added line exceeds 100 characters. The five files had 59 longer lines
  (up to 136 characters) and now have 52. One of them grew by 2 characters (`simp only` →
  `simpa only`) and was reflowed; no other line was reflowed.

## Summary

Code lines are `python3 scripts/loc.py` (`loc-before.txt`, `loc-after.txt`). Times are
`/usr/bin/time lake env lean <file>`, original and golfed interleaved on the same machine
(load average 4.4–5.9) against the same (golfed) imports; each includes the ≈ 7 s import.
For `Examples.lean` the bracketed pair is an earlier interleaved round against the original
`Semantics` (`time-examples-interleaved.log`).

| File | Code before → after | Theorems | Time before (s) | Time after (s) | Peak RSS |
|---|---:|---:|---|---|---|
| `Semantics.lean` | **881 → 778** (−103) | 48 | 17.22, 17.06, 16.85 | **12.75, 12.43, 12.23** (−27 %) | 3.42 → 3.37 GB |
| `Gadget.lean` | **346 → 301** (−45) | 27 | 6.53, 6.28, 6.14 | 6.06, 5.99, 6.10 (same) | 1.91 → 1.90 GB |
| `ToLayout.lean` | **249 → 234** (−15) | 18 | 8.77, 8.84, 8.95 | 8.85, 8.69, 8.72 (same) | 3.29 → 3.29 GB |
| `Examples.lean` | **186 → 180** (−6) | 24 | 67.72, 65.91 (64.78, 66.50) | 65.41, 65.60 (64.61, 67.34) (same) | 3.94 → 3.94 GB |
| `FiniteField.lean` | 23 → 23 | 4 | — | — | — |
| `Clean.lean` (root) | 5 → 5 | 0 | — | — | — |
| **Total** | **1,690 → 1,521** (−169, −10 %) | 121 | | | |

(The brief's 1,561 is the count before the decision pass; the tree had 1,690 when this golf
started, as in `S8-RESULT.md` "After the pass".)

## Where `Semantics.lean`'s time went, and the two fixes

Per-declaration profile (`-Dtrace.profiler=true -DElab.async=false`, threshold 100 ms;
`prof-before-Semantics.log`, `prof-after-Semantics.log`):

| Declaration | Before | After |
|---|---:|---:|
| `holdsPerm_toCleanWit` | 7.52 s | **2.24–2.27 s** |
| `rel_toLayoutWit` | 6.21 s | **1.26–1.32 s** |
| `Part.portMsgs_chan` | 0.46 s | 0.26 s |
| every other declaration | ≤ 0.55 s | within ± 40 ms |

1. **`tabs[j]` with `j : Fin tabs.length` inside a proof's `have`.** Each occurrence runs
   `get_elem_tactic` to find the bound, and in these large contexts each run takes 0.26–0.43 s.
   `hfixt` (4 occurrences: 1.15 s in `holdsPerm_toCleanWit`, 1.5 s in `rel_toLayoutWit`),
   `hmem` (1) and `hmemz` (2, 0.86 s) paid it.
   - **Fix:** write the bound, `(tabs[j]'j.2)`. It is the same term (the same `getElem` with a
     different proof of the same `Prop`), so every later `rw`/`simp` matches as before.
   - In `rel_toLayoutWit` `hfixt` is gone altogether: it had one use, and inlined as the
     argument of `tabs_sum_look` it takes its type from that lemma's (already elaborated)
     statement.
2. **`congr 1` / `congr 2` on sums of `Part.tableOf …` products.** `congr` tries to close each
   new goal by `rfl`; here every such attempt unfolds `tableOf`, `rows`, `*` and fails slowly.
   The "cells" branch of `holdsPerm_toCleanWit` took 3.96 s, 3.5 s of it in two `congr 1`;
   `hW`'s `congr 2` in `rel_toLayoutWit` took 1.7 s.
   - **Fix:** say which congruence: `refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) …` and
     `congrArg (T0 :: · ++ wt) (List.map_congr_left …)`.

## Changes, by declaration

### `Semantics.lean` (881 → 778)

- `coe_flatMap_eq_sum`, `mem_list_sum`, `zip_map_zip`: the `induction … with` alternatives
  become `induction … <;> simp [*, …]` (one line each).
- `coe_filter_map_eq_sum`: the two `by_cases` branches become `by_cases h : p a <;> simp [h, ← ih]`.
- `Part.portMsgs_chan`: `hI` ends `exact and_comm` instead of `unfold OnBus; tauto`; the final
  8-line `congr`/`filter_congr`/`tauto` chain is `simp only [List.filter_filter, Bool.decide_and,
  Bool.and_comm]`.
- `Part.portMsgs_look`: `have := swap_filter …; simp only … at this; exact this.symm` → `simpa
  using (swap_filter …).symm`.
- `portMsgs_tab`: the two nested `List.ext_getElem` blocks are one `refine` and two `simp`s; the
  negative branch (a 5-line `have` about the singleton filter) is `simp [eq_comm (a := b), h]`.
- `map_getD_range`, `trunc_of_size`: term mode, `List.ext_getElem … fun _ _ h => by simp [h]`
  (resp. `Array.ext`).
- `sum_zip_ofFn`, `toCleanWit_tables`: `apply …; intro …` → `exact`/`refine … fun … =>`.
- `tabs_sum_look`: the two `ite_eq_right` subproofs lose their `rintro`/`rw` steps (one is a
  term, the other `refine` + `exact`).
- `holdsPerm_toCleanWit` (fix 1 and 2 above, and):
  - `hfl`, a restatement of `hL`, is removed; its uses take `hL` directly (as
    `rel_toLayoutWit` already did).
  - `hrows0`, `hfixt`: no intermediate `have`/`obtain`.
  - `hlook`: the bound and the table come from `List.getElem?_eq_some_iff.mp htj` (was a
    `by_contra` plus a `simpa`, 3 lines); `hsent`'s `h0` (6 lines) is a `List.map_congr_left`
    in the `rw` plus `simp [hj]`; the end is `rwa [Lookup.Contains, hfaith, Vector.toList_map]`.
  - Clean's constraints: `refine (table_constraints_iff _).mpr fun r hr => ?_`; `hgr` inlined.
  - The ℕ-balance: `replace hb` and `← hnames` dropped (`simp [toLayout, hb]`), `rwa`.
- `Part.env_tableOf`: `simp [env, trunc, tableOf]` (was 6 lines).
- `part_look`: `rw [canonLooks, …] at hm`; `obtain rfl := of_decide_eq_true hlj`; the table
  via `List.getElem?_eq_some_iff`; `heq`/`show`/`rw` → `(List.map_congr_left …).symm ▸ hc`.
- `rel_toLayoutWit` (fix 1 and 2 above, and): `hfl0`, `hflc` inlined (one use each); the fixed
  tables case is `rcases … <;> cases ht'` (the two impossible cases and the table equation are
  all `Option` constructor equations); `have hmem …; obtain … := hmem` → `obtain … : … := by`.
- `tableMsgs_byName`: the `constructor`/`rintro`/`subst` block is one anonymous-constructor
  term; `unfold OnBus` dropped (the `show` already unfolds it).
- `balancedPerm_byName_iff`: `have := …; simp only … at this; exact this` → `simpa only … using`
  (twice).
- `statementPerm_iff`: term mode (3 lines instead of 7).

### `Gadget.lean` (346 → 301)

- `eval_of_constVal?`, `degreeBound_of_constVal?`, `one_le_degreeBound`: the identical `add` and
  `mul` alternatives share one right-hand side (`| add a b ha hb | mul a b ha hb => …`).
- `eval_ofExpr`, `length_ofExpr_le`: the two identical last cases are one `all_goals` block.
- `sum_ofFn_dite`: the inner `have` is `List.ext_getElem … fun i _ _ => by simp [List.getElem_append]`.
- `Lin.eval_smul`: one `simp only` (`List.sum_map_mul_left`), no induction, no `ring`.
- `prodEval_scaleProd`: `cases p <;> simp […]`.
- `SOP.eval_merge`: `hsplit` is Mathlib's `List.sum_map_filter_add_sum_map_filter_not`
  (with `Bool.beq_eq_decide_eq`), replacing an induction with `split_ifs <;> simp_all <;> ring`
  (the declaration went from 0.35 s to 0.11 s); `unfold; dsimp only` → `simp only [SOP.merge]`.
- `length_merge_le`: `simp only [SOP.merge] at hp`.
- `eval_lin_part`: `simp only …; exact ih` → `simpa only … using ih`.
- `lt_mul_of_lt`: the 3-step `calc` (with `ring`) is a term:
  `Nat.lt_of_lt_of_le (Nat.add_lt_add_left hl _) (Nat.succ_mul k D ▸ Nat.mul_le_mul_right D hk)`.
- `rowDot_tag`: `split_ifs with h <;> simp […, h]`.
- `le_foldr_max`: `rcases List.mem_cons.mp h with rfl | h`.
- `prod_factor`: `hlen` is `simp [hP p (List.getElem_mem hk)]`.
- `holds_gadgetOf`: the final `constructor` is one `refine ⟨…, …⟩`.

### `ToLayout.lean` (249 → 234)

- `eval_trunc`: shared `add`/`mul` alternative.
- `Part.eval_firstLin`: one `simp` with `show ¬ … < P.cols names by omega` (was two `have`s and
  two `simp only`s).
- `Part.holds_chip_iff`: the padding branch is one `simp`; the one-row branch is
  `cases P.oneRow <;> simp […, add_neg_eq_zero]` (was 7 lines).
- `Part.cell_colOf`: `simpa only … using h ⟨_, List.idxOf_lt_length_of_mem hmem⟩`.

### `Examples.lean` (186 → 180)

- `fibK_faithful`: the reverse direction is `obtain rfl | rfl : a = 0 ∨ a = 1 := by simpa […]
  using h` then `exacts [⟨0, rfl⟩, ⟨1, rfl⟩]` (was 7 lines).
- `pair_faithful`: `rcases hc with rfl | rfl <;> simp […] at hl`.

## Declined

1. **`idxOf_eq_iff`** is `List.idxOf_inj ha` (Mathlib), one line instead of five, but then `hb`
   is unused and the linter warns. Dropping `hb` changes the statement, so it is left to the
   implementer (its only caller, `tableMsgs_byName`, would pass one argument fewer).
2. **Proof fields inside definitions** (definition bodies, out of scope):
   `K.instFiniteField.val_injective`/`val_fromNat`, `Bits.contains_iff` (likely 2 lines shorter
   with `exacts [⟨0, rfl⟩, ⟨1, rfl⟩]`, as in `fibK_faithful`; not tried), the
   `soundness`/`completeness` fields of `step`, `verifier`, `stepP`, `verifierP`,
   `ens`/`ensP.verifier_length_zero`, `cleanTable.uniform_width`, `toCleanWit.same_*`,
   `wit`/`witP.same_circuits`.
3. **`tabs[j]` in statements** (`tabChips`, `traffic_split`, `tabs_sum_chan`, `tabs_sum_look`,
   `cells_split`): each statement pays `get_elem_tactic` once at elaboration (`tabs_sum_look`'s
   header: 0.66 s). `(tabs[j]'j.2)` is the same term, but it is statement text; not touched.
4. **`rel_toLayoutWit`, public chip:** `split_ifs with h1 h2 <;> simp [h1]` then `omega` saves 3
   lines but costs 0.14 s and replaces three explicit cases by a `simp` that leaves one goal for
   `omega`.
5. **`Part.auxOK_tableOf`:** `simp [tableOf, h1, h2]` for `simp only …` + `rw …` saves 1 line
   by moving up the tactic ladder.
6. **Tried, failed, kept:** one `simp` for `holds_chip_iff`'s auxiliary branch (`SOP.eval`
   unfolds before `SOP.eval_merge` can fire); a term for `prod_factor`'s inner `List.ext_getElem`;
   `rcases` through `List.mem_map` in `rel_toLayoutWit` (needs `List.mem_map.mp`); `omega`
   on `r < (P0.chip …, T0).2.rows` (the projection is not reduced, so `rw [hrows0] at hr` stays).
7. **The `decide +kernel` controls** (`fibK_*`, `pair_*`; almost all of `Examples.lean`'s
   ≈ 58 s past the import, per `S8-RESULT.md`) are untouched. Whether S6a-golf's `K`-product
   rewrite (`mul_fast`) would speed them up was not measured.

## Notes for the implementer

- **`(tabs[j]'j.2)`** in a proof-internal statement is the cheap spelling; plain `tabs[j]` with
  `j : Fin tabs.length` costs 0.3–0.4 s per occurrence in the big bridge contexts. If the
  statements in item 3 are ever edited anyway, the same spelling saves ≈ 0.1–0.7 s each.
- **Avoid bare `congr n`** on goals whose sides are sums of `Part.tableOf` cells; name the
  congruence (`congrArg₂ (· + ·)`), as above.
- **`hfixt` is still stated in `holdsPerm_toCleanWit`**, because it has two uses (`hsent` and the
  cells branch).
- **The `S8-RESULT.md` file table** (code lines per file) is now out of date: Semantics 778,
  Gadget 301, ToLayout 234, Examples 180, total 1,521; theorems unchanged (121). The
  Semantics build time drops by about 4.5 s.
- **Process.** Each file was golfed on a scratch copy under `logs/S8-golf/scratch/` (not in the
  `RecursionFast.Clean.*` glob), checked by LSP and `lake env lean`, then copied over the
  original after checking that the original was still byte-identical to `orig/`.
