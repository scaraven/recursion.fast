# S4 golf: the bounded extractor (Stage 4)

The golf agent wrote this on 2026-10-14. Nothing is committed.

**What changed:** proofs only, in `RecursionFast/Library/Extractor.lean` and
`RecursionFast/Controls/Extractor.lean`. No statement, type, definition, docstring, module comment
or declaration order changed; no declaration was added, removed, renamed, split or merged; no
import was added. The trusted `Contract/Machine.lean` and `Contract/Extractor.lean` are
byte-identical (SHA-256 `f8f7c27d…` and `140b244a…`, `logs/S4-golf/baseline.sha256`,
`logs/S4-golf/after.sha256`). The originals are kept as `logs/S4-golf/*.lean.orig`; the diffs are
`logs/S4-golf/library.diff` and `logs/S4-golf/controls.diff`.

**Checks after the golf:**
- `lake build RecursionFast.Library.Extractor RecursionFast.Controls.Extractor` is green after each
  file, and the default `lake build` is green (2480 jobs, `logs/S4-golf/build.log`).
- `lake exe axiomaudit` reports **PASS** (`logs/S4-golf/axiomaudit.log`). See the note on the
  declaration count below.
- `scripts/check-hygiene.sh` reports OK: no `sorry`, `native_decide` or new axiom.
- LSP diagnostics on both files are empty (no warnings).
- `probes/s4/ProtocolSwap.lean` still compiles (checked with `lake env lean`; not edited).

## Summary per file

| File | Code lines (`loc.py`) before → after | Total lines | Elaboration (`/usr/bin/time lake env lean`) before → after | Peak RSS |
|---|---:|---:|---|---:|
| `Contract/Machine.lean` (TRUSTED) | 109 → 109 | 198 → 198 | unchanged | — |
| `Contract/Extractor.lean` (TRUSTED) | 63 → 63 | 148 → 148 | unchanged | — |
| `Library/Extractor.lean` | **423 → 360** | 569 → 506 | **8.21–8.51 s → 6.60–6.62 s** (−22 %) | 2.06 GB → 2.01 GB |
| `Controls/Extractor.lean` | **329 → 311** | 495 → 477 | 10.95–11.38 s → 10.54–11.47 s (same) | 2.84 GB → 2.85 GB |

`logs/S4-golf/loc-before.log`, `loc-after.log`.

### How the timing was measured

- **Whole files** (the ±10 % rule). The original and the golfed file were timed interleaved,
  three rounds, on a shared machine with load average about 1.5–2 (`logs/S4-golf/time-final.log`).
  Both Controls files import the same (golfed) Library olean, so the Controls row measures the
  Controls proofs only. The pre-golf baseline with the old Library olean is
  `logs/S4-golf/time-before.log` (Library 8.87–9.18 s, Controls 11.46–12.10 s).
- **Per declaration.** `lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=20
  -DElab.async=false`, minimum over three runs (`logs/S4-golf/prof.py`,
  `prof-library.log`, `prof-controls.log`). The run-to-run noise is up to about ±60 ms: the
  unchanged `decide +kernel` controls move by that much. Every changed declaration is no slower
  beyond that noise. Contested variants were measured in isolation in a bench file
  (`logs/S4-golf/scratch/Bench*.lean`, five rounds where it mattered).
- **Totals.** Summed over the declarations above 20 ms, the Library goes from 8.51 s to 5.16 s
  and Controls from 7.97 s to 7.93 s.

## Changes, by declaration: `Library/Extractor.lean`

| Declaration | Before | After | Kind | ms before → after |
|---|---|---|---|---|
| `extractMid_eq_of_run`, `extractMid_eq_nil_of_run`, `extractOut_eq_of_run`, `extractOut_eq_nil_of_run` | `by rw [extractMid_eq]; exact E.call_of_run k h ho` (2 lines each) | the term `E.call_of_run k h ho` (or `E.call_of_run_none k h`). The `_eq` lemmas are `rfl`, so the refinement lemmas are `call_of_run*` up to unfolding. | directness | ~32 → ~32 |
| `getReg_setReg` | `cases r <;> cases r' <;> rfl` (1024 goals, 1 line) | `obtain rfl \| h := eq_or_ne r' r`. The equal case is `cases r' <;> rfl` (32 goals). The other is `rw [ite_eq_right …, MachineState.getReg_setReg_ne …]` (vendored lemma). | **performance, +2 lines** (see note) | **1950 → 75** |
| `getMem_initState_tape` | `have` + `simp only` + `rw` + `congr 1; omega` (5 lines) | one `rw` chain ending in `Nat.add_sub_cancel_left`, `Nat.mul_div_cancel_left` (3 lines) | structural | 152 → 52 |
| `execute_mono` | `induction` with two `split at h <;> simp_all` rounds (7 lines) | `fun_induction execute img f s <;> simp_all [execute, Nat.add_right_comm _ 1 d]` | structural | 228 → 165 |
| `ordinaryStep_ld` | `simp only [ordinaryStep, memAccess]`; `rw [ite_eq_left (by simp only [h]; rfl)]; rfl` | `simp only [ordinaryStep, memAccess, h]`; `rfl` | removes a nested `by` | 285 → 261 |
| `ordinaryStep_sd` | the same pattern, with six Bool lemmas (3 lines) | `simp only [ordinaryStep, memAccess, h, ht]`; `rfl` (2 lines) | the Bool lemmas are not needed | < 30 |
| `readWords_eq` | `induction` + `rw` + `simp only` + `refine` + two `congr` + `toNat` arithmetic (9 lines) | `induction n generalizing base <;> simp [*, List.range_succ_eq_map, Nat.mul_succ, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_comm 8#64]` (2 lines) | structural | 220 → 43 |
| `foldl_add_eq` | 3-line `induction … with` | `induction l generalizing a <;> simp [*, Nat.add_assoc]` | structural | < 20 |
| `flatMap_pair_getD` | 15 lines (index arithmetic, `getElem?_append_right`, two `simpa`) | 6 lines: both `cons` cases hold by unfolding (`exact ⟨rfl, rfl⟩`, `exact ih i (Nat.lt_of_succ_lt_succ hi)`); `nil` is `nomatch hi` | directness | **699 → 43** |
| `drop_sum_flatten` (private, kept) | 10-line induction | `rw [List.map_take, List.drop_sum_flatten]`. The Mathlib lemma is already imported transitively, so no new import. | library lemma | 41 → < 20 |
| `frame_drop` | `List.drop_append`, `drop_eq_nil_of_le`, an `omega` `show` (7 lines) | `rw [frame_eq, frameStart, ← List.drop_drop, List.drop_left' (by rw [List.length_cons, dir_length]; omega), drop_sum_flatten]` (2 lines) | structural | 230 → 40 |
| `frameStart_add_le` | hand-proved split of the sum (7 lines) | `List.sum_take_add_sum_drop`, then `rw`, then `omega` (4 lines) | library lemma | 70 → 61 |
| `unframe_frame` | local `toNat_toWord` by `simp [toWord]; omega` (2 lines) | `fun _ => Nat.mod_eq_of_lt`, which holds by unfolding (1 line) | directness | 153 → 131 |
| `length_readWords` | `rw [readWords_eq]; simp` | `simp [readWords_eq]` | syntax | < 20 |
| `pLayout_words` | `have : K.mk ∘ K.bits = id`, then two `rw` (3 lines) | the `show … from rfl` inside the `rw`, then `exact` (2 lines) | syntax | < 20 |
| `pMany_pK_eq` | `succ` case: `cases l with`, two identical `simp` arms (4 lines) | `cases l <;> simp [pMany, pK, ih, List.ofFn_succ]` | structural | 175 → 166 |
| `decTables_map_bits` | 29 lines: `nil` case as `simp only` + `refine` + `simp`; `cons` case as `by_cases` with `h'` copies, an `e` lemma and four `ite_eq_*` rewrites | 18 lines: `nil` is one `simpa … using ih []`; `cons` is `congrArg₂ _ (congrArg (Table.mk _) (funext₂ fun r i => ite_congr rfl (fun h => ?_) fun _ => rfl)) (ih _)`, then `hq` and one `rw` | structural | 264 → 219 |
| `run_firstMsgImage` | helper `ha`: `rw` + `simp only [BitVec.toNat_ofNat]` + `omega` | `BitVec.toNat_ofNat` moved into the `rw` (−1 line) | syntax | 1289 → 1177 (noise) |
| `toNat_toWord` (private) | `by simp [toWord]; omega` | `Nat.mod_eq_of_lt h` | directness | < 20 |
| `firstMsg_extractMid` | `hf` by `le_trans (by norm_num) (Nat.pow_le_pow_right …)` (2 lines), then `obtain ⟨f, hf'⟩`, `rw [hf']` | `hf` by `(Nat.le_add_left 8 (2 * k + 8)).trans Nat.lt_two_pow_self.le` (1 line); `run_mono (f := 0 + 8) ?_ hf` inside the `refine` | structural, −2 lines | 100 → 85 |

## Changes, by declaration: `Controls/Extractor.lean`

| Declaration | Before | After | Kind | ms before → after |
|---|---|---|---|---|
| `spin_run` | `intro f` + `induction f with` + `intro s hs` + a `have hf` for the fetch (11 lines) | `intro f s hs`; `induction f generalizing s`; the fetch fact inline as `execute_step (i := .base (.JAL .x0 0)) _ ((fetch_eq 0 (by decide) hs).trans rfl) rfl` (8 lines) | structural | 47 → 49 (noise) |
| `run_long` | `rw [readOut, readWords_eq]` + two `simp only` (11 lemmas) + `simp` (6 lines) | `simp [readOut, readWords_eq, getMem_initState, hd, BitVec.toNat_shiftLeft]`, which reaches the same goal (checked with `lean_goal`). `h1`: the bound inlined into the `rw` (−1 line). | structural | 534 → 520 |
| `long_extractMid` | `rw [ExtractorImage.extractMid_eq]` before the `refine` | dropped: `call_of_long` unifies with `extractMid` by unfolding | directness | 123 → 119 |
| `brute_iter` | first bullet `simp only [s4, execInstrBr, pc_setPC, p3]` + `simp [CODE_BASE, …]` | `simp [s4, execInstrBr, p3, CODE_BASE, RiscvZkvm.Rv64.signExtend21]` (`pc_setPC` is already `@[simp]`) | syntax | 293 → 286 |
| `brute_loop` | `zero` case `obtain rfl : f = 0 := by omega` on a hanging line, then `rfl` (2 lines) | `obtain rfl := Nat.le_zero.mp hf; rfl` (1 line) | directness | 139 → 120 |
| `brute_prologue` | helper `hal`: `rw` + `simp only [BitVec.toNat_ofNat]` + `omega` | `BitVec.toNat_ofNat` moved into the `rw` (−1 line) | syntax | 588 → 588 |
| `bruteTarget_tape` | `hl`, `hs2` (two `simp [secs]`) feeding `hst` by `rw … ; ring`; `h5`; two `rw` lines | `hst` by `simp [frameStart, secs]; omega`; `frame_getD_start` inline; one `rw` (−3 lines, two fewer `simp [secs]` calls) | structural | **1353 → 1203** |
| `brute_extractMid_nil` | `have e := bruteTarget_tape …` + `rw [show … from e]` (4 lines) | `rw [bruteTarget_tape m s _ w (by …)]` (1 line) | directness | 110 → 104 |

## Declined (tried, measured or failed)

- **`execute_step`.** `split <;> simp_all [ordinaryStep]` would save 3 lines, but it is 2.2× slower
  (386 → 855 ms). Kept.
- **`extractorFuel_eq`.** `:= extractorFuel.eq_1 k` would save 1 line, but generating the equation
  lemma costs about 120 ms against < 20 ms for `unfold extractorFuel; rfl`. Kept.
- **`run_firstMsgImage_frame`.** Typed `have h7 : (frame secs).getD 7 0 = _ := …` in place of the
  `simp only [show 1 + 2 * 3 = 7 …] at h7 h8` line saves 1 line, but in isolation it is
  182 → 207 ms over five rounds. Reverted.
- **`bruteTarget_tape`, `haddr`.** Merging `rw [BitVec.toNat_add, BitVec.toNat_shiftLeft]` and
  `simp only [toWord, BitVec.toNat_ofNat, TAPE_BASE]` into one `simp only` fails with
  `(kernel) deep recursion detected`. A variant without `let secs` (defeq length arguments)
  failed the same way. Kept.
- **`copy_extract_relK`.** The `have this` on `decTables [32] trivWords` was not shortened:
  - `simp [decTables, trivWords]` expands `List.replicate 32` and stalls on the cell function;
  - `convert triv_relK 20 _` is blocked by the dependent `Mid` type;
  - `List.getD_replicate_default_eq` does not exist under that name.
- **`toy_extractMid`.** `rw [Transcript.concat_last tr msg]` without the typed `e` fails: the
  motive mismatches `Fin.last ↑0` against `Fin.last 0`. Replacing `rw [… decTables_map_bits]; rfl`
  by `exact decTables_map_bits _ _` saves no line. Kept unchanged.
- **`call_of_run`, `call_of_long`.** `rw [call, h, if_pos ho]` fails: `rw` does not reduce the
  `match` on `some o`, and `[]` must be read at type `Mid n j`. `unfold call; rw [h]` →
  `rw [call, h]` saves no line. Kept.
- **`fetch_eq`.** `simp [fetch, this, CODE_BASE]` fails because `CODE_BASE` unfolds before
  `this` fires. Kept.
- **`decTables_map_bits`, `hq`.** loogle and leanfinder found no lemma
  `a < n → b < c → a * c + b < n * c`, so the 3-line derivation stays.
- **`frame_dir`.** Only reformatting would save lines. `Nat.add_comm 1` would first rewrite the
  `1 + 2 * secs.length` inside the directory, so the `show … by ring` stays.
- **`layout_roundTrip`.** Dropping `List.append_nil` would make the kernel evaluate
  `triv.words ++ []` (over 256 words). Kept.
- **Symbolic execution** (`run_firstMsgImage`, `brute_prologue`, `brute_iter`, `run_long`).
  - The per-step `rw [execute_step …]` then `simp` structure stays. Merging steps would need the
    pc side goals discharged through unsimplified states.
  - `brute_iter`'s `p3` merged into one `simp` would put a 102-character line on the `have` line.
  - `brute_iter`'s final `interval_cases f` block stays: a `<;>` combinator would need `rw` to
    fail gracefully on `f = 0`.
- **`decide +kernel` controls** (`copy_run`, `copy_steps`, `copy_run0`, `wzbc_run`, `tape_*`,
  `halt_*`, `ecall_trap`, `spin_run_100`, `tape_roundTrip`, `brute_cost`): untouched, as
  instructed, including their two-line `:= by` / `decide +kernel` layout.

## Notes

1. **`getReg_setReg` grows by 2 lines.** This is the one change that lengthens a proof. The
   1024-goal `cases` was 22 % of the Library's elaboration (1.95 s), and the new proof takes
   75 ms. Perf ranks above length in the golf order. It uses the vendored
   `MachineState.getReg_setReg_ne`; the Library is untrusted, so the contract's closure (S4
   RESULT: 205 vendored declarations, 0 theorems) is unaffected.
2. **Axiom-audit count.** `fun_induction` in `execute_mono` generates
   `RecursionFast.execute.induct_unfolding` and `execute.match_N.congr_eq_*` in
   `Library/Extractor.lean`.
   - The audit's count for `RecursionFast.Library.Extractor` therefore goes from 91 to 99, all
     PASS.
   - The fix pass should quote the new number in the RESULT.
   - The eight new names are `execute.induct_unfolding` and seven `execute.match_N.congr_eq_*`.
     They sit in the `RecursionFast.execute` namespace but in the untrusted module. The module
     already held other generated lemmas about `execute` before the golf (`execute.eq_1`,
     `execute.eq_def`, the match splitters, from `simp only [execute]` and `split`).
   - If the orchestrator prefers a stable count, restore the 7-line `induction` proof. It is
     about 60 ms slower; see `library.diff`.
3. **Safety of term-mode refinement lemmas.** The four refinement lemmas are now plain
   applications of `call_of_run`/`call_of_run_none`. They depend on `toExtractor`'s fields
   unfolding to `E.call …` by `rfl`, the same fact `extractMid_eq`/`extractOut_eq` already
   state. A change to `toExtractor` breaks both places alike.
4. **`run_long` simp.** The merged `simp` sees `List.replicate (2 ^ sh.toNat) 0` with `sh`
   symbolic. The S4 RESULT's warning (never let `simp` see `(List.replicate (2^33) _).length`)
   is respected: `long_extractMid` still uses `rw [List.length_replicate]`.

## Trusted files (`Contract/Machine.lean`, `Contract/Extractor.lean`): no edits

Neither file has an instance or `Decidable` proof. The only proof term is `eqIn := rfl` in
`toExtractor`, which is already minimal. Simplification ideas for the implementer follow. They are
**not applied**, because they change definition bodies.

### `Machine.lean`

1. **`execute`.** The inner `match ordinaryStep s i with | some s' => execute img fuel s' |
   none => none` is `(ordinaryStep s i).bind (execute img fuel)`.
   - It saves 2 code lines, and structural recursion on `fuel` still applies.
   - The Library's `execute_step` (`simp only [execute, hf]; split …`) would need a re-proof.
     `execute_mono`'s `fun_induction` one-liner should survive.
2. **`initState.regs`.** `fun r => match r with | .x2 => … | _ => 0` can be written as
   `fun | .x2 => … | _ => 0`. That saves characters, not lines.
3. **`unpack`.** It has no user in v2 yet. It is there for the Stage 6/7 renderer, which decodes
   the image literal. If Stage 6 decodes outside Lean, it can leave the trusted base.
4. **`memAccess` and `ordinaryStep`.** These are best left verbatim from v0.3. Factoring the
   repeated `s.getReg r + signExtend12 o`, or the shared `.word`/`.wordShift` tail, saves at most
   one line and loses the provenance claim.

### `Extractor.lean` (63 code lines; target 60)

1. **`call`.** As `((run E.img t (extractorFuel k)).filter (·.length ≤ witCap k)).elim []
   (decMid L j)` it is −2 lines; the RESULT declined this for readability. The Library's
   `call_of_run*` would become `simp [call, h, ho]`-style proofs.
2. **`toExtractor`.** `extractMid` spells the round words `Round.words _ (tr i)`, while
   `extractOut` spells them `(sh i).words (tr i)`. A single spelling would make the two calls
   read alike (no line change); the Library's `midTape`/`outTape` mirror the difference.
3. **`imageCap`.** It could be inlined into `img_le` (−1 code line), but S4-A2 names it. Not
   recommended.
