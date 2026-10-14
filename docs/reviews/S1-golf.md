# S1 golf: the layout relation, `Protocol` over `Layout`, library bridges, controls (Stage 1)

The golf agent wrote this on 2026-10-14. Nothing is committed.

**What changed:** proofs only, in seven files. No statement, type, definition body, docstring,
module comment, declaration name or declaration order changed; no declaration was added, split or
merged; no import was added or removed. In the trusted files the only edit is layout: each of the
two `Decidable` instances in `Contract/Layout.lean` is now on one line, with the same term
`inferInstanceAs (Decidable (_ ∧ _))`.

**Checks after the golf** (logs under `logs/S1/golf-*`):
- `lake build` (default targets) and `lake build RecursionFastBridge gate axiomaudit` are green,
  with no warnings. They were re-run after every file.
- `lake env .lake/build/bin/axiomaudit` reports **PASS**. `scripts/check-hygiene.sh` reports OK.
- **Statements are unchanged, checked mechanically.** I built the original sources in a separate
  copy of the tree and dumped every constant of `RecursionFast.{Contract,Library,Controls}` from
  both environments: the type of every theorem and the type and value of every definition and
  instance. The two dumps agree (`logs/S1/golf-types.diff`). The only differences are
  auto-generated equation lemmas, which are now generated in another module:
  - `unsat.eq_1` moved from `Controls.Layout` to `Controls.Negative`;
  - `Codec.decGadget.eq_1`, `Codec.decMat.eq_1`, `Codec.decS.eq_1` and `r1csGadget.eq_1` are new;
  - a private `msgs_trim._simp_1_1` is gone.

  This is why the audit's per-module counts moved: `Codec` 89 → 92, `Controls.Layout` 46 → 45,
  `R1CS` 25 → 26 and `Negative` 25 → 26.
- **Axioms are unchanged.** `#print axioms` for the 39 declarations listed in
  `logs/S1/axioms.log` gives byte-identical output (`logs/S1/golf-axioms.log`). This includes the
  `[propext, Quot.sound]` and `[propext]` ones that the RESULT quotes.
- The reviewer's probes `probes/s1/*.lean` (nine files) all still compile against the golfed tree.

## Summary per file

Code lines are from `scripts/loc.py` (`logs/S1/golf-loc.log`).

Elaboration time is the wall time of `lake env lean <file>`, in seconds. Each file was run five
times, original and golfed interleaved, and the median is reported (`logs/S1/golf-time.log`). The
original was built in a separate copy of the tree with the original sources, so each side imports
its own `.olean`s. Between 2.5 s and 4 s of every figure is import.

| File | Code before → after | Elaboration before → after |
|---|---:|---|
| `Library/Layout.lean` | **179 → 146** | 5.80 → 5.82 (+0.3 %) |
| `Library/R1CS.lean` | **119 → 104** | 5.57 → 5.55 (−0.2 %) |
| `Library/Codec.lean` | **360 → 340** | **11.55 → 8.17 (−29 %)** |
| `Library/Field.lean` | 161 → 161 (declined) | unchanged |
| `Library/Challenges.lean` | 33 → 33 (declined) | unchanged |
| `Controls/Layout.lean` | **108 → 103** | 11.66 → 11.58 (−0.7 %) |
| `Controls/Toy.lean` | **86 → 74** | 5.43 → 5.42 (−0.1 %) |
| `Controls/Negative.lean` | **98 → 85** | 6.85 → 6.66 (−2.8 %) |
| `Contract/Layout.lean` (TRUSTED) | **77 → 75** | 4.99 → 4.95 (−0.9 %) |
| `Contract/Protocol.lean` (TRUSTED) | 30 → 30 (no proofs) | unchanged |
| **Total** | **1251 → 1151 (−100, −8 %)** | no file slower beyond noise |

- **Trusted contract:** 253 → 251 code lines (`python3 scripts/loc.py RecursionFast/Contract.lean RecursionFast/Contract/*.lean`).
- **Codec speed-up.** The only real speed-up is in `Codec`. Two bare `congr 1` calls spent 4.9 s and 1.1 s trying to close their
  subgoals by `rfl` at default transparency. Details are under `Library/Codec.lean`.

## Changes, by declaration

### `Library/Layout.lean` (179 → 146)

| Declaration | Change |
|---|---|
| `rowDot_eq` | **`cons` case.** The `hsplit` proof is one `simp only` (now including `List.filter_cons`) and `Finset.sum_congr rfl fun c _ => by split_ifs <;> simp_all`. It replaces `refine` / `congr 1` / `simp only` / `split_ifs`. The final two-bullet `by_cases` is `by_cases h : e.1 = r <;> simp [h, Finset.sum_ite_eq]`. (−4) |
| `traffic_eq_zero` | One `simp only [traffic, List.sum_eq_zero_iff, List.forall_mem_map, List.mem_filter, and_imp, beq_iff_eq, Bool.and_eq_true]` and one `exact`. It replaces two rounds of `List.sum_eq_zero` / `List.mem_map` destructuring. (−3) |
| `relBelow_iff` | **Inner `hb`.** It uses `if hbN : b < N then hb b hbN else ?_` and closes the other case with `simp only [traffic_eq_zero …, balanced_zero]`. The side fact `p.bus ≠ b` is the term `((h C hC p hp).trans_le (not_lt.mp hbN)).ne`, not a `have … omega`. (−4) |
| `msgs_trim` | The `filter_congr` side goal and the `map_congr` are each one `simp`. The intermediate `have` is gone. (−1) |
| `traffic_trim` | Nested `congrArg _ (List.map_congr_left …)` replaces `congr 1; refine; simp only [Function.comp]; congr 1; refine; exact`. (−4) |
| `rel_trim_iff` | **Opening.** `simp only [Layout.rel, traffic_trim hL]` replaces the `hlen` helper, `unfold` and `simp only`.<br>**Size clause.** It is closed by `Iff.rfl` inside the `refine`.<br>**Fixed-table clause.** One term.<br>**Public-chip clause.** It was a 14-line `cases hp : w[L.pub]?` with three helper `have`s. It is now a case split on `L.pub < L.chips.length`: in range, one `simp +contextual` with `hc : ∀ i : Fin 32, ↑i < L.chips[L.pub].cols`; out of range, `simp [hp, hw]`. (−13) |
| `rel_normal_iff` | **Buses `≥ N`.** The same `traffic_eq_zero` term as `relBelow_iff`.<br>**Opening.** `simp only [Layout.rel, htr, hbus]` replaces `unfold` plus `simp only`. (−3) |
| `Layout.Admissible.readsOwn` | **Public-chip half.** `Option.mem_unique hC' hC ▸ h32` replaces `rw [Option.mem_def] at …` and `Option.some.inj`. (−1) |

**Declined:**
- `view_trim`: I found a 3-line `simp +contextual` proof, but it no longer uses the section
  variable `[DecidableEq F]`. The unused-section-variable linter then requires adding it to the
  `omit`, which changes the type of the (private) lemma. I kept the original proof.
- Not touched, already minimal: `spToMat`, `Gadget.holds_iff`, `view_castAdd`, `balanced_zero`,
  the `Balanced` and `relBelow` `Decidable` instances, `zip_map_zip`, `Admissible.bus_lt`, and all
  definitions.

### `Library/R1CS.lean` (119 → 104)

| Declaration | Change |
|---|---|
| `r1csGadget_holds_iff` | One `simp only` that unfolds `r1csGadget` and ends with `one_mul, mul_one, neg_one_mul, add_zero, ← sub_eq_add_neg, sub_eq_zero`. It replaces `rw` / `delta` / `dsimp` / `refine forall_congr'` / `simp only` and `constructor <;> intro h <;> linear_combination h` (two `ring` calls gone). (−4) |
| `holds_r1csChip_iff` | Term mode: `(r1csGadget_holds_iff A B C _).trans (iff_of_eq (congrArg _ (funext fun c => view_castAdd …)))`. (−1) |
| `rel_r1csLayout_iff` | **Case split on `t`** (`[]`, `[T]`, two or more tables).<br>**Wrong lengths.** `iff_of_false` on the length clause.<br>**`[T]`.** Two `simp only` sets and `exact and_left_comm`. (−7)<br>**Speed.** A 5-line variant with plain `simp [...]` cost +0.5 s (+9 % of the file). I replaced its two `simp`s by the `simp only` sets that `simp?` reported, so the file is now no slower than before. |
| `rel_r1csWit_iff` | `hx` is `simpa [rowOf] using congrFun hrow (Fin.castAdd n i)`, without the intermediate `have`. (−1) |
| `R1CS_of_rel` | `hz`: `exact Fin.addCases (fun i => by simpa …) (fun j => by simp …) c`. It replaces two bullets and a `rw [Fin.append_right]`, which `simp` does by itself. (−2) |

**Declined:**
- `rowDot_sparseOf`: no `simp` variant closed it.
- Not touched, already minimal: `rowDot_eq_sum`, `R1CS_iff_layout` and the definitions.

**Note:** `import Mathlib.Tactic.LinearCombination` is now unused in this file. I left it in place,
because no import may change in this pass.

### `Library/Codec.lean` (360 → 340; 11.55 s → 8.17 s)

| Declaration | Change |
|---|---|
| `decLayout_idxOracle` | **Speed.** `congr 1` → `with_reducible congr 1`: **4.9 s → negligible**. The bare `congr` tried to close goals such as `toNat (rd k (idxOracle k L) 0 7 1 0 0) = L.pub` by `rfl` at default transparency, unfolding the oracle arithmetic. The three subgoals and their proofs are unchanged.<br>**`hpub`.** It is `(List.getElem?_eq_some_iff.mp hC0).1`, not a 4-line `by_contra`.<br>**`hk`.** It is no longer destructured; `hk.1` and `hk` are passed directly.<br>**`pub` bullet.** It is `rw [g7 1 _]` and `exact toNat_ofNat _`; the `if 1 = 0` reduces by unification. (−5) |
| `decChip_idxOracle` | **Speed.** The same `congr 1` → `with_reducible congr 1` on the chip equality: **1.1 s → negligible**.<br>**`hh`.** Five `· omega` bullets → `any_goals omega`.<br>**Fixed-table argument.** `(fun t ht => hfR t ht)` → `hfR`. (−4) |
| `decGadget_eq` | `cases g`, `simp only [decGadget, Gadget.mk.injEq, true_and, heq_eq_eq]`, `exact ⟨funext hM, funext hS, funext hc⟩`. It replaces `obtain` / `show` / `congr 1` and three bullets. (−3) |
| `decMat_eq` | `rw [decMat, hn]`. The two bounds are terms `l[e.1].1.isLt.trans hb.1` and `l[e.1].2.1.isLt.trans hb.2.1`, not `have`s plus `omega`. (−3) |
| `decS_eq` | The same, with `l[p.1].isLt.trans hb.1`. (−2) |
| `decPort_eq` | **Message list.** `(List.getElem_ofFn hc1).trans (h4 c hc2)` inside the anonymous constructor replaces `simp only` plus `exact`. (−1) |
| `trim_decWit_wOracle` | `hk` is not destructured, and `hsize` is inlined. (−2) |

**Declined:**
- `pk_lt`: a shorter `calc` needs `linarith`, which is not imported here.
- `chip_bounds`: the one-line form of its `fixedCells` step exceeds 100 columns.
- The `e0`–`e6` block of `decChip_idxOracle`: `simp only [decChip, hh, hdr]` cannot rewrite
  `cols` under the dependent `Gadget K (cols + cols)`, and `rw [hh …]` plus `dsimp only [hdr]`
  leaves unreduced `match`es. The explicit `e`-lemmas plus `rw` are what make the dependent
  rewrite work.
- Not touched: `pk_div`, `pk_mod`, `toNat_ofNat`, `get_idxOracle`, `get_wOracle`,
  `K_zero_ne_one`, `filterMap_ofFn`, `decFixed_eq`, `rd_idxOracle_chip`, and all definitions.

### `Library/Field.lean`, `Library/Challenges.lean`: declined

Both are carried over byte-identical from v0.3 (RESULT deviation 7; the reviewer checked this with
`diff`). Keeping them verbatim keeps that check trivial.

Small golfs are possible, for example:
- `toExt_zero/one/neg/sub/add` → `Ext.ext fun i => by fin_cases i <;> rfl`;
- `ofK`'s `map_add'`/`map_mul'` → `by simp`.

They should be done in v0.3 first, if at all.

### `Controls/Layout.lean` (108 → 103)

| Declaration | Change |
|---|---|
| `r1cs_bool_iff` | `forall_const` added to the `simp only` set, which drops the final `exact ⟨fun h => h 0, fun h _ => h⟩`. (−1) |
| `noPub_neg` | `exact absurd (List.getElem?_eq_some_iff.mp hT).1 (by omega)` replaces `rw … at hT; simp at hT`. The axioms are still `[propext, Quot.sound]`. (−1) |
| `unsatGadget_not_holds` | Term: `fun h => by simpa [unsatGadget] using h ⟨0, Nat.one_pos⟩`. (−2) |
| `unsat_neg` | The witness's membership in the zip is `List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨rfl, hT⟩)`. This replaces the detour through `w = [T']` and `T' = T`. (−1) |

**Declined:**
- Every control closed by `decide +kernel` (`twoChip_*`, `lookup_*`, `fib_*`, `stmt_neg`,
  `emptyPub_neg`, `unsat_admissible`, `cells_neg`, `cols_neg`, `pubCols_neg`, `entries_neg`,
  `fixedCells_neg`). Each is already one line, and the kernel check is the cost: the profiler
  gives 5.1 s of type checking out of the file's 11.6 s (4 s is import).
- `r1cs_pos`, `r1cs_neg`, `r1cs_iff` and `twoChip_noPub` are already terms.
- `boolM_mulVec` is already one line.

### `Controls/Toy.lean` (86 → 74)

| Declaration | Change |
|---|---|
| `toyVerify_iff` | `hN := List.forall_mem_map.mpr hL.bus_lt` replaces `intro` / `obtain` / `exact`. (−2) |
| `toyKSF` (`next`) | `obtain ⟨m, hm⟩ := m; obtain rfl : m = 0 := Subsingleton.elim _ _; simpa using h`. (−1) |
| `toyKSF` (`full`) | `simpa using (toy_accepts_iff k hk s tr).mp hV`: `simp` decides `Fin.last 1 ≠ 0` itself, so the `have` and `simp only [h1, dite_false]` go. (−2) |
| `toy_secure` (`complete`) | `refine ⟨(toy_accepts_iff …).mpr ⟨hL, ?_⟩, Set.mem_univ _⟩`, a `show` of the decoded witness, and one `exact` chaining `rel_trim_iff`, `trim_decWit_wOracle` and `rel_trim_iff`. It replaces the `htr` rewrite, the `hw` helper and four `refine`/`rw` steps. (−7) |

**Declined:**
- `toy_noChal`: the term form exceeds 100 columns.
- Not touched, already minimal: `toy_accepts_iff`, `toy20_secure`, and the definitions.

### `Controls/Negative.lean` (98 → 85)

| Declaration | Change |
|---|---|
| `triv_relK` | **Gadget clause.** `by simp [triv, Gadget.holds, freeGadget]` (a `Fin 0` quantifier).<br>**Bus clause.** `fun b => by simp [traffic, triv, balanced_zero]`.<br>This replaces two 3-line bullets. (−4) |
| `rejectAll_not_complete` | `fun h => by simpa using (h _ _ (triv_relK k hk) _).1`. (−2) |
| `rejectAll_not_secure` | One `simpa`. `5 ≤ k` is the term `(by norm_num : 5 ≤ 20).trans P.k_range.1`, not `by have := …; omega`. (−2) |
| `acceptAllChal_err_ge_one` | **`hall`.** An anonymous constructor.<br>**Last step.** `le_of_mul_le_mul_right ((one_mul _).trans_le hc) hpos` replaces a 3-line `have`. (−5) |

**Declined (already short):**
- `unsat_admissible_of`, `unsat_not_relK`, `acceptAll_no_KSF`, `acceptAllKSF`;
- `acceptAllChal_rbr_one`, `acceptAllChal_complete`, `errorCap_lt_one`, `acceptAllChal_not_secure`.

### `Contract/Layout.lean` (TRUSTED, 77 → 75), `Contract/Protocol.lean` (TRUSTED, 30 → 30)

- **`Contract/Layout.lean`.** The two `Decidable` instances (`Chip.Admissible`,
  `Layout.Admissible k`) each fit on one line: 85 and 99 columns. The term and the docstrings are
  unchanged, and the instance values are identical in the type dump.
- **`Contract/Protocol.lean`** has no proofs, so there is nothing to touch.
- I touched no other trusted line.

## Definition notes for the implementer (not applied)

The trusted definitions are already tight. I found nothing that is clearly simpler with the same
meaning. Four observations:

1. **`view`** could be written as
   `Fin.addCases (fun c => T.cell r c) (fun c => T.cell ((r + 1) % T.rows) c)`. That would make
   `view_castAdd` a `simp` lemma (`Fin.addCases_left`) and remove the `i - C.cols` arithmetic from
   the library. However, the `if i.val < C.cols` form is easier to read in a trusted file, and
   `view_trim` would still need `(r + 1) % T.rows < T.rows`. **Not recommended.**
2. **`1 ≤ C.cols` vs `0 < C.cols`.** `Chip.Admissible` uses `1 ≤ C.cols` and `Layout.ReadsOwn`
   (library) uses `0 < C.cols`. They are definitionally equal in ℕ, and `Admissible.readsOwn` uses
   that. Writing `0 < C.cols` in `Chip.Admissible` would make the two read the same. This is
   cosmetic.
3. **`congr` on oracle goals is a performance trap.** Any later proof whose goal mentions
   `idxOracle`, `wOracle` or `toNat (rd …)` (for example the stage-8 baseline) should avoid a bare
   `congr`/`congr 1`. Its closing `rfl` attempt unfolds the oracle arithmetic: it took 4.9 s here,
   and `with_reducible congr 1` fixed it.
4. **`Library/R1CS.lean`'s `LinearCombination` import** is now unused. It can be dropped when
   imports are next touched.

## How the work was done

- **Isolation.** Each file was golfed in a scratch copy under `/tmp`, checked with
  `lake env lean`, timed against the original, and only then copied into the tree.
- **Drift check.** Before each copy, a content-hash check confirmed that the target file had not
  changed since my last write, so no concurrent edit was overwritten.
- **Concurrent Stage-2 files.** The Stage-2 files that appeared during the run (`Contract/Hash/`,
  `Library/Blake2s.lean`, `Controls/Blake2s.lean`, `probes/s2/`) were not touched. They are outside
  the totals above. The default build globs (`RecursionFast.Library.*`, `RecursionFast.Controls.*`)
  already build them, and they were green at each of my builds.
