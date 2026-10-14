# S3 golf: the compiled argument (Stage 3)

The golf agent wrote this on 2026-10-14. Nothing is committed.

**What changed:** proofs only, in `RecursionFast/Library/Compile.lean` and
`RecursionFast/Controls/Compile.lean`. No statement, type, definition, docstring, module comment,
import or declaration order changed. The other three Stage 3 files are byte-identical to the
baseline (`logs/S3-golf/baseline.sha256`): the trusted `Contract/Compile.lean`,
`Controls/CompileFS.lean` and `Controls/CompileToy.lean`.

**Checks after the golf:**
- `lake build RecursionFast.Library.Compile RecursionFast.Controls.Compile
  RecursionFast.Controls.CompileFS RecursionFast.Controls.CompileToy` is green, with no warnings
  (`logs/S3-golf/build-s3-targets.log`). `Library.Compile` builds in 5.3 s and `Controls.Compile`
  in 55–56 s. The full `lake build` was not run: the concurrent Stage 4 files break it.
- **Statements are unchanged, checked mechanically.** All 277 constants of the five Stage 3
  modules were dumped with their pretty-printed types, before the golf (from the original oleans)
  and after the rebuild. The two dumps are identical (`logs/S3-golf/types-{before,after}.txt`).
  This also shows that no declaration was added or removed.
- **Axioms.** No theorem gains an axiom (`logs/S3-golf/axioms-lib-{orig,new}.txt`,
  `axioms-touched.log`). Five theorems lose `Classical.choice`: `wordOfBytes_bytes`,
  `K.ofBytes_bytes`, `kList_flatMap`, `readOpening_honest` and `roundViews_tapeBytes`. The headline
  theorems keep `[propext, Classical.choice, Quot.sound]`: `narg_complete*`, `prove_isSome`,
  `narg_local`, `runs`, `honest_accepted` and `oversize`.
- `scripts/check-hygiene.sh` reports OK. LSP diagnostics on `Library/Compile.lean` are empty.
- No `sorry`, `native_decide` or new axiom; no new `<;>` on goals that need different tactics.

## Summary per file

The times are from `/usr/bin/time lake env lean <file>`, original and golfed run **interleaved**
on the same imports. The machine had load ≈ 2 and a Stage 4 agent was running.

| File | Code lines (`loc.py`) | Total lines | Wall time before → after | User CPU before → after | Peak RSS |
|---|---:|---:|---|---|---:|
| `Library/Compile.lean` | **511 → 439** | 658 → 586 | **11.4–11.7 s → 7.1–7.2 s** | 14.2–14.6 s → 9.4–10.0 s | 2.67 → 2.63 GB |
| `Controls/Compile.lean` | 27 → 29 | 48 → 50 | **71.7–73.2 s → 58.1–62.0 s** | 66.8–68.3 s → 54.1–58.0 s | 8.13 GB, unchanged |
| `Controls/CompileFS.lean` | 12 → 12 | 29 → 29 | unchanged (byte-identical; S3 baseline 56 s) | | |
| `Controls/CompileToy.lean` | 91 → 91 | 174 → 174 | unchanged (byte-identical; S3 baseline 9.8 s) | | |
| `Contract/Compile.lean` (TRUSTED) | 159 → 159 | 334 → 334 | unchanged (byte-identical) | | |

Where the logs are:
- library, three rounds each: `logs/S3-golf/time-lib-final.log`;
- controls, two rounds each: `logs/S3-golf/time-controls-compile-final.log`;
- an earlier round of the controls, at 58.6–59.0 s against 72.9–73.3 s:
  `logs/S3-golf/time-controls-compile.log`.

**Where the time went.**
- **Library.** `wordOfBytes_bytes` (64 `interval_cases` branches) took ≈ 4.5 s of the library's
  ≈ 8 s past the imports. It now takes ≈ 0.25 s (isolated profile,
  `logs/S3-golf/iso-word.log`: `simp` 3.4 s → 0.12 s, type class 0.73 s → 0.05 s).
- **Controls.** `oversize` spent **10.3 s of kernel time** in `have : 0 < tape2.length := by
  decide +kernel`, which decodes the `hex` string (`logs/S3-golf/iso/Ctl3.lean`). The new proof
  needs no evaluation (see below).

## Changes, by declaration

### `Library/Compile.lean`

Lines are code lines per declaration (`logs/S3-golf/decl-lines.log`, from
`logs/S3-golf/decl_lines.py`). The net change is −72.

| Declaration | Lines | What changed | Kind |
|---|---:|---|---|
| `wordOfBytes_bytes` | 8 → 12 | 64-way `interval_cases i <;> simp` replaced by a byte-step invariant `step : (y >>> (s+8)) <<< 8 ||| ((y >>> s).setWidth 8).setWidth 64 = y >>> s` (bitwise: two `simp`s). The leading `0` becomes `a.bits >>> 64` (`BitVec.ushiftRight_eq_zero`); then `simp only [step]` and `exact step a.bits 0` | **perf**: +4 lines, −4.5 s, no `Classical.choice` |
| `kList_go` (private) | 9 → 8 | `rw … at *` + `simp only … at h ⊢` + `rw …; simp` → `simp only [K.bytes_eq, List.append_nil] at h` + `simp [K.bytes_eq, kList.go, h, ih]` | structural |
| `node_length` | 4 → 2 | case split with inner `split` → `cases h <;> simp [..., apply_ite List.length]` | structural |
| `climb_honest` (private) | 25 → 24 | zero case `intro h hh; simp only [Nat.add_zero] at hh; subst hh` → `rintro h (rfl : h = _)` | syntax |
| `climb_pathOf` | 5 → 4 | `have h := …; simpa … using h` → `simpa … using climb_honest …` (`lt_of_lt_of_le` → `hl.trans_le`) | directness |
| `flatMap_bytes_length` | 4 → 2 | induction + `simp; ring` → `simp [K.bytes_length, mul_comm]` | structural |
| `readOpening_honest` | 24 → 22 | `obtain … := List.mem_map.mp hlev` (no `simp at`); `List.length_eraseIdx_of_lt` instead of `length_eraseIdx` + `if` reduction; `fun lev hl t => hlev lev hl t` → `hlev` | directness |
| `leaf_of_plain` | 9 → 7 | two `simp only … at; subst` pairs and the `List.ext_getElem` step → `obtain rfl : lf = len`, `obtain rfl : l = 0`, one `simp` | structural |
| `runQ_record` | 26 → 19 | `done`: `cases h; rfl`. `query`: `rcases hj`, then one `simp only [record, hj, Option.ite_none_right_eq_some, Option.map_eq_some_iff] at h` and `obtain ⟨hl, op', hrec, rfl⟩` replace the `by_cases hl`/`swap` and three `simp`s. `hpl` is `Bool.and_elim_right hp`. The root branch's two `simp`s are merged | structural |
| `fsPrefixes_zero` | 3 → 2 | `simp [fsPrefixes]` → `rfl` | directness |
| `fsPrefixes_msg`, `fsPrefixes_chal` | same | `simp only [fsPrefixes, Fin.induction_succ, h]; rfl` → term `(Fin.induction_succ _ _ _).trans (dite_eq_left h)` (resp. `dite_eq_right (Bool.ne_true_of_eq_false h)`) | directness |
| `fsTranscript_eq` | 17 → 15 | `have hpre (m : Fin (P.n + 1))` (no `intro`). The zero case is `exact funext fun i => i.elim0` (no `rw`). The branches use `rw [dite_eq_left h, …]` and `rw [dite_eq_right h, …]` + `exact congrArg (Transcript.concat _) (fsTranscript_chal … h').symm`, instead of `simp only [h]`, `dsimp`, `rfl` and two `by simpa using h` | directness |
| `pass_chain` | 26 → 24 | per branch: `rw [pass, …]; dsimp only` → `simp only [pass, …]`; `congr 2; apply Array.toList_inj.mp; simp […]` → `simp […]` | structural |
| `ofFn_eq_map_range` (private) | 4 → 3 | term `List.ext_getElem (by simp) fun i h1 _ => by simp [show i < n by simpa using h1]` | directness |
| `msgLen_tapeBytes` | 6 → 4 | `by_cases` with two `simp only`s and `exact node_length` → one `simp only [..., apply_ite List.length, ..., node_length]` | structural |
| `pass_honest` | 35 → 25 | `hσ0` and `hσ1` are now terms `dite_eq_left (Nat.lt_succ_of_lt hi)` and `dite_eq_left (Nat.succ_lt_succ hi)`, replacing `simp only [σ, show … by omega]; rfl`. Further: the `e1`/`e2` haves and the rewrites of `this` → `rw [ofFn_eq_map_range …]` on the goal; `hσ` is the term `congrArg Prod.snd (fsPrefixes_zero …)`; then `simpa [hσ] using this` | structural |
| `chals_honest` | 7 → 5 | `have hc := c.2` inlined; the two `simp`s merged | syntax |
| `views_honest` | 10 → 8 | `refine congrArg List.ofFn (funext fun i => roundViews_tapeBytes cfg _ _ _ fun hm => ?_)` + `simp [fsEntry, hm]` replaces the 2-line `simp only` and the `exact` | structural |
| `narg_complete` | 28 → 19 | Four simplifications. (1) `heval` by one `simpa only [Protocol.specVerifier, Option.ite_none_right_eq_some, and_true] using hacc`, not `split at hacc`. (2) `obtain ⟨hcap, ⟨⟩⟩ := Option.ite_none_right_eq_some.mp ht`, not `split_ifs` + `cases`. (3) `hvs` by `rintro (_ \| j) o hj <;> simp_all [os]` (two identical branches before). (4) `hrun` inlined | structural |
| `narg_complete_of_perfect` | 6 → 4 | tactic `refine`/`have`/`rwa` → term `narg_complete … (fsTranscript_eq cfg P L x w ▸ (hP (L, x) w hrel _).1)` | directness |
| `record_isSome` | 17 → 12 | three `simp only … at h` and the explicit 3-line witness (a copy of `record`'s body) → `ih _ (by simpa only […] using h)` + `simp only [record, …, Option.some.injEq, exists_eq']` | structural |
| `prove_isSome` | 17 → 14 | `split at h` with an absurd branch → `simp only [Protocol.specVerifier, Option.ite_none_right_eq_some, and_true] at h` | structural |
| `runQ_local` | 48 → 32 | Nesting is replaced by early exits. `rcases … with _ \| v` and `_ \| o'` have one-line absurd bullets. `hj : o'.shape = v.shape` is derived once. Each `if l < … then … else none = some b` is split by `Option.ite_none_right_eq_some`, with no `by_cases` and no dead branch. `View.shape` is folded into the final `simp only` | structural |
| `narg_local` | 14 → 13 | `refine ⟨h.1, ?_⟩`; `fun os hc => runQ_local … (by simpa using h) os hc` → `runQ_local … (eq_of_beq h.2)` | directness |

### `Controls/Compile.lean`

| Declaration | Lines | What changed | Kind |
|---|---:|---|---|
| `honest_accepted` | 2 → 2 | `by rw [index_eq]; exact runs.1` → `index_eq ▸ runs.1` | directness |
| `oversize` | 5 → 7 | `have : 0 < tape2.length := by decide +kernel; omega` → `Nat.lt_add_of_pos_left (List.length_pos_of_ne_nil fun h => ?_)`. Non-emptiness comes from `runs.1` through `narg_local`: the pass reads a 32-byte root, so `pass … [] #[] = some _` is absurd (`cases hp`) | **perf**: +2 lines, −10.3 s kernel, −1.3 GB in isolation |

`runs`, `fsRuns` and `index_eq` are single `decide +kernel` calls and were not touched, as
instructed. The hash-sharing grouping is unchanged.

## Declined

- **`fsTranscript_eq` with `cases h : (P.shape j).isMsg`.** `generalize` fails because the
  dependent `⟨j, h⟩ : MessageIdx` blocks it. Kept `by_cases`.
- **`runQ_record` tail as `split` / `unfold viewOf at hv; split at hv` + `simp_all`.** The
  non-plain branch is left unsolved: simp normalises `j != 0` and `!(j == 0)` differently. Kept
  the two `have hv'`.
- **`climb_honest`: inlining `hr` into `insert_eraseIdx`.** The index must then be spelled out, so
  nothing is saved.
- **`readOpening_honest`: `Nat.zero_lt_of_lt cfg.two_le_arity` instead of `have hA` + `omega`.**
  The line goes past 100 characters, and there is no line saving.
- **`leaf_of_plain` with `simpa [OShape.leaves] using hl` on one line.** It pulls in
  `Classical.choice`. The 2-line `simpa only` keeps the axioms as before.
- **`oversize` with `nomatch hp`.** It creates an auxiliary declaration `oversize.match_1_1`.
  `cases hp` creates none, and the declaration set stays identical.
- **`narg_complete` final `rw [NARG, …]; dsimp only; rw […]; rfl` → `simp only`/`simp`.** It is
  rw → simp for one line, a move up the ladder.
- **`runQ_local`: inlining `hmem` into `hleaf`.** It saves one line but loses a meaningful name.
- **`leaves_le_pow_depth`.** `cases hf : List.find? _ _` cannot use placeholders, and `getD` is
  not a `match` for `split`. Unchanged.
- **`kList_go` as a single `simp`.** `simp` cannot use `K.ofBytes_bytes` (stated with
  `++ r`) against the expanded byte list. It keeps the `have`.
- **Line width.** Every line is ≤ 100 characters (the project style, as in the original file).
  The skill's 80-character guideline was applied only to new single terms.

## Notes for the implementer (fix pass)

1. **`hex` decoding is a large, hidden kernel cost in the controls.**
   - **Measured** (`logs/S3-golf/iso/Hex.lean`):
     - `tape2.length = 152` by `decide +kernel` takes **11.2 s**;
     - `tape2 = tape2L` takes 11 s;
     - the same 152 bytes written as a `List UInt8` literal take under 0.1 s.
     The cause is the kernel's UTF-8 decoding of the `String`.
   - **Where it applies.** The kernel caches results only within one declaration, so:
     - `runs` decodes `tape2` once (≈ 11 s of its ≈ 57 s);
     - `fsRuns` decodes `tape2` and `cheatTape` (≈ 22 s of ≈ 50 s);
     - `index_eq` decodes the 32-byte root of `vkc2`.
   - **Suggestion** (a definition change in `CompileToy.lean`, which is off limits to the golf):
     write `tape2`, `cheatTape` and `vkc2.2` as byte-list literals. Keep the hex strings only in
     compiled-code `#guard`s (`hex "…" = tape2`), so the Python cross-check stays visible.
   - **Expected effect.** About −11 s on `Controls/Compile.lean`, about −20 s on `CompileFS.lean`
     and about −2 s on `index_eq`, with no loss of what the controls show.
   - The same applies to Stage 5's controls.
2. **Unused import.** `Library/Compile.lean` no longer uses `interval_cases`, so
   `import Mathlib.Tactic.IntervalCases` can be dropped. The golf leaves headers alone.
3. **The S3 RESULT's claim about `oversize`.** It says `oversize` is checked "by the general lemma
   `narg_oversize`, no evaluation". That was not true before: it decoded `tape2` in the kernel for
   10 s. It is true now. The `Controls/Compile.lean` header comment, which I did not edit, now
   matches.
4. **`record` and `viewOf` state the plain test in different forms:** `j != 0 && …` against
   `!idx && …` with `idx := (j == 0)`.
   - The mismatch is why `runQ_record` needs two `simp_all`s and a `by_cases` on the `bne` form.
   - If `viewOf` is ever revised, using the same `bne` form (or one shared predicate `isPlainAt j o`
     in `Contract/Compile.lean`) would let `runQ_record` close by `split` + `simp`.
   - This would change `runQ_record`'s statement, so it is not a golf.
5. **`Cfg.depth` (trusted, definition idea, not applied).** Every menu arity is `2^a` with
   `a ∈ {1, 2, 3, 4}`, so the depth is `⌈(logLen − logLeaf) / a⌉ = (d + a − 1) / a`.
   - This closed form removes the `find?` over ≤ 39 candidates on every query (S3 RESULT open
     question 5).
   - Its cost: `leaves_le_pow_depth` needs a new short proof (`2^d ≤ (2^a)^⌈d/a⌉`).
   - `Contract/Compile.lean` has no `Decidable` or instance proofs (only
     `deriving DecidableEq, Repr`), so it has nothing to golf.
6. **`CompileToy.lean` proofs inside definition bodies (cosmetic, not touched).** These are:
   - `cmpToy.shape_ok`'s `| 1 => fun b hb => by simp at hb; omega`;
   - `cfg2`/`cfg4`'s `by decide` (could be `Or.inl rfl` and `Or.inr (Or.inl rfl)`);
   - the `⟨0, by decide⟩` and `absurd h (by decide)` in `cmpVerify`/`cmpNext`.

   None affects the kernel runs.

## Logs (`logs/S3-golf/`)

- `baseline.sha256`, `after.sha256`;
- `*.orig.lean`, the five original files;
- `loc-before.log`, `loc-after.log`;
- `time-lib-final.log`, `time-controls-compile{,-final}.log`, `iso-word.log`;
- `types-before.txt`, `types-after.txt`;
- `axioms-lib-orig.txt`, `axioms-lib-new.txt`, `axioms-touched.log`;
- `build-s3-targets.log`;
- `iso/`, the isolation experiments: `Word*.lean`, `Ctl*.lean`, `Hex.lean`, `Leaf.lean`.
