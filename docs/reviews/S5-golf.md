# S5 golf: recursion and the certificate types (Stage 5)

The golf agent wrote this on 2026-10-15. Nothing is committed.

**What changed:** proofs only, in `Library/Recursion.lean`, `Controls/Recursion.lean`,
`Controls/RecursionNode.lean` and `Controls/Certificate.lean`. No statement, type, definition,
docstring, module comment, import or declaration order changed; no declaration was added, removed,
renamed, split or merged. The hash-heavy kernel facts (`x1Runs`, `nodeStmt_kat`, `rootRuns`,
`nodeRuns`, `completeRuns`, `digestToSlot_kat`) and the way they are shared are untouched.
`Controls/RecursionData.lean` is not touched. The trusted `Contract/Recursion.lean` and
`Contract/Certificate.lean` are byte-identical (SHA-256 `159b78b3…`, `017103fd…`,
`logs/S5/golf/trusted.sha256`). The originals are kept as `logs/S5/golf/*.lean.orig`, the diffs as
`logs/S5/golf/*.diff`.

**Checks after the golf:**
- `lake build RecursionFast.Library.Recursion RecursionFast.Controls.Recursion
  RecursionFast.Controls.RecursionNode RecursionFast.Controls.Certificate` is green after the
  library (`logs/S5/golf/build-after-library.log`), after the controls (`build-after-controls.log`)
  and at the end (`build-final.log`; kernel files 60 s and 83 s, in parallel).
- LSP diagnostics on the four files are empty (no errors, no warnings, no deprecations).
- `#print axioms` on the 21 changed declarations and `keys_of_root`
  (`logs/S5/golf/axioms-after.log`): 15 use
  `[propext, Classical.choice, Quot.sound]`, 6 use `[propext, Quot.sound]` and `takeN_short` uses
  none. No new axioms, `sorry` or `native_decide`.
- `scripts/check-hygiene.sh`: OK (`logs/S5/golf/hygiene-after.log`).
- No line over 100 characters was introduced.

## Summary per file

| File | Code lines (`loc.py`) before → after | Total lines | Elaboration (`/usr/bin/time lake env lean`), original → golfed | Peak RSS |
|---|---:|---:|---|---:|
| `Contract/Recursion.lean` (TRUSTED) | 45 → 45 | 130 → 130 | unchanged | — |
| `Contract/Certificate.lean` (TRUSTED) | 23 → 23 | 75 → 75 | unchanged | — |
| `Library/Recursion.lean` | **149 → 139** | 254 → 244 | 13.3–14.2 s → 12.9–13.5 s (same) | 2.72 GB → 2.71 GB |
| `Controls/Recursion.lean` | **60 → 54** | 147 → 141 | 59.0–61.5 s → 60.2–63.4 s (median +2 %) | 5.56 GB → 5.56 GB |
| `Controls/RecursionNode.lean` | **37 → 30** | 81 → 74 | 84.4–88.2 s → 85.3–88.5 s (median +4 %) | 6.95 GB → 6.95 GB |
| `Controls/Certificate.lean` | **37 → 32** | 76 → 71 | 5.95–6.12 s → 6.04–6.16 s (same) | 2.61 GB → 2.61 GB |
| **Total (6 files)** | **351 → 323** | 763 → 735 | | |

`logs/S5/golf/loc-before.log`, `loc-after.log`.

### How the timing was measured

- **Whole files** (the ±10 % rule). Baseline before any edit: `logs/S5/golf/time-before-*.log`.
  Then the original and the golfed file were timed interleaved on a shared machine (load average
  1.3–2.8): 2 rounds for `Controls/RecursionNode.lean` and 4 for the other three files
  (`logs/S5/golf/time-final.log`, `time-interleaved.log`, `time-after-*.log`). The originals
  (`/tmp` copies) were elaborated against the same golfed library olean. Every golfed file is
  within ±10 % of its original. The spread comes from the unchanged `decide +kernel` runs: in the
  profiles below, `x1Runs` takes 26.5–27.0 s, `nodeRuns` 31.6–31.9 s and `completeRuns` 45.4–46.9 s
  from run to run, in both versions.
- **Per declaration.** `lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=5|10
  -DElab.async=false` on the original and the golfed file (`logs/S5/golf/prof-*.log`). Every
  changed declaration takes no longer than before, up to a few ms of noise. Every changed
  declaration in the two kernel files takes ≤ 60 ms.

## Changes, by declaration

### `Library/Recursion.lean` (149 → 139 code lines)

| Declaration | Before | After | Kind | ms before → after |
|---|---|---|---|---|
| `Stmt.ofSlots_slot` | `funext`, `simp only`, `congr 1; ext; simp; omega` (4 lines, naked `;`) | the term `funext fun i => congrArg x (Fin.ext (Nat.div_add_mod i 4))` | directness | 71 → < 10 |
| `Stmt.eq_ofSlots_iff` | `mpr` through `Stmt.ext_slot` and a 2-line `by rw` | `fun h => by rw [← funext h, Stmt.ofSlots_slot]` (one line) | structural | < 10 |
| `K.ofBytes_bytes'` | `by simpa using K.ofBytes_bytes a []` | the term `List.append_nil a.bytes ▸ K.ofBytes_bytes a []` | directness (no `simp`) | < 10 |
| `K.ofBytes_cons8` | `by simp [K.ofBytes, wordOfBytes]` | `rfl` (`List.take 8` reduces on an 8-cons list) | directness | 54 → < 10 |
| `nodeStmt_slot` | `simp only [nodeStmt, Stmt.slot_ofSlots]`; `refine ⟨rfl, rfl, rfl, …⟩`; `fin_cases i <;> first \| exact absurd hi (by decide) \| rfl` (3 lines) | the term `⟨Stmt.slot_ofSlots _ 0, …, fun \| ⟨_ + 3, _⟩, _ => Stmt.slot_ofSlots _ _⟩`: the slots `≥ 3` are the match's wildcard case, and the impossible `i < 3` cases are discharged by the match compiler (2 lines) | directness, performance | 147 → 69 |
| `eq_nodeStmt_iff` | `obtain`, `refine`, `fin_cases i`, three bullets and `all_goals` with two `by decide` each (7 lines) | `obtain`, then one `exact` whose `mpr` is `Stmt.ext_slot fun \| ⟨0, _⟩ => … \| ⟨1, _⟩ => … \| ⟨2, _⟩ => … \| ⟨_ + 3, _⟩ => …`, with `Nat.le_add_left` for `3 ≤ n + 3` (4 lines) | structural, performance | 88 → 44 |
| `aggOK_leaves` | `by simpa only [child] using h₁` (and `h₂`) | `h₁`, `h₂`: a leaf `child` is `NARG … vkL …` by definition (3 → 2 lines) | directness | < 10 |
| `aggOK_nodes` | simp set with `(nodeStmt_slot cfg _ _ _ _).1, (nodeStmt_slot cfg _ _ _ _).2.1` (2 lines) | `nodeStmt_slot` (simp splits the conjunction) (1 line) | syntax | 34 → 37 (noise) |

### `Controls/Recursion.lean` (60 → 54 code lines)

| Declaration | Before | After | Kind |
|---|---|---|---|
| `aggOK_two_leaves` | `rw [← nodeStmt_kat]`; `exact aggOK_leaves …` | `nodeStmt_kat ▸ aggOK_leaves …` (term) | directness |
| `wrong_d1` | `rw [← Bool.not_eq_true]; intro h`, a typed `have` over 2 lines, `rw … at`, `exact absurd` (5 lines) | `Bool.eq_false_iff.mpr fun h => absurd ((… .mp h).2.1.trans digestToSlot_kat) (by decide)` (2 lines). `Eq.trans` unfolds `nwN.vkL` to `vkc2`, which the typed `have` did by hand | structural |
| `nonzero_d3` | `rw [← Bool.not_eq_true]; intro h` + `exact absurd …` | `Bool.eq_false_iff.mpr fun h => absurd …` (same 2 lines, removes the naked `;`) | syntax |
| `rootOK_xN` | `rw [← nodeStmt_kat, ← index_eq]; exact rootOK_nodeStmt …` (naked `;`) | `nodeStmt_kat ▸ index_eq ▸ rootOK_nodeStmt …` (term) | directness |
| `cbad_not_sound` | `have`, `rw … at`, `simp only … at`, `exact Bool.false_ne_true` (4 lines) | `simpa only [decodeBad_bad, aggOK, child, x1Runs.2.2, Bool.and_false, Bool.false_eq_true] using h xN wBad (cbad_rel _ _)` (2 lines; same simp level as before) | structural |

The changed declarations take ≤ 19 ms before and ≤ 11 ms after
(`prof-Recursion-{orig,new}-5ms.log`).

### `Controls/RecursionNode.lean` (37 → 30 code lines)

| Declaration | Before | After | Kind | ms before → after |
|---|---|---|---|---|
| `aggOK_node_child` | `refine … ⟨vkc2_root, vkc2_root, ?_, ?_⟩`, a bullet with two `have`s, `rw … at`, `change`, `exact (child_iff …).mpr ⟨…, fun h => absurd h (by decide)⟩`, a bullet `exact runs.1` (9 lines) | `refine … ⟨vkc2_root, vkc2_root, ?_, runs.1⟩`; the same `change`; `simp only [child, Bool.and_eq_true, decide_eq_true_eq, nodeStmt_slot, digestToSlot_kat, nodeRuns.2, and_true]`; `decide` on the two key slots (6 lines). The `decide` decides the same two literal slot equalities as the two old `by decide`s; the aggregate statement is never evaluated | structural | 58 → 56 |
| `node_child_d0`, `node_child_d1` | `rw [← Bool.not_eq_true]; intro h`, two `have`s, `rw … at`, `exact absurd` (5 lines each) | `Bool.eq_false_iff.mpr fun h => by`, one `have`, `exact absurd (h0.trans ((nodeStmt_slot ..).1.trans digestToSlot_kat)) (by decide)` (3 lines each) | structural | 16 → 13, 18 → 14 |

### `Controls/Certificate.lean` (37 → 32 code lines)

| Declaration | Before | After | Kind |
|---|---|---|---|
| `takeN_short` | `(by simp at h; omega)` | `(Nat.lt_of_succ_lt_succ h)` (`(c :: t).length` is `t.length + 1` by definition) | directness |
| `toy_narg` | `have hs : … := takeN_short _ _ _ (lt_of_le_of_lt ht (by decide))` + `simp [… , hs]` (3 lines) | `simp [NARG, toy, toyShape, pass, takeN_short (msgLen ⟨30, 30⟩) t [] (ht.trans_lt (by decide))]` (1 line) | structural |
| `toy_vacuous_fields`, `toy_no_entry` | `absurd h (by rw [toy_aggOK]; decide)` | `Bool.ne_true_of_eq_false (toy_aggOK x' nw)` (term; the undeprecated name) | directness |
| `toy_no_submissionR` | `by obtain ⟨⟨P, cfg, _⟩, e⟩ := S; subst hP hc; exact toy_no_entry e` (4 lines) | `toy_no_entry (hP ▸ hc ▸ S.entry)` (on the statement's last line) | directness |

## Declined

- **`K.bytes_ofBytes`** (`Library/Recursion.lean`). It takes 7.4–7.6 s, more than half of the file.
  The 8 × 8 `interval_cases i <;> simp` bit cases are brute force. Three single-`simp`
  replacements with `hi`, `i < 64` and an `omega` discharger leave all or 7 of the 8 byte goals
  open (shifted indices `8k + i - 8 - …`). A faster proof needs a new route: `toNat` arithmetic
  with `omega`, or a byte lemma `setWidth 8 ((w <<< 8 ||| c.setWidth 64) >>> 8k)`. That is a
  rewrite, not a golf. Left for the implementer.
- **`bytes_digestToSlot`** (2.3–2.5 s). `simp?` gives a 24-lemma `simp only` (4 lines instead of
  1). It measured 2.54 s, no faster, so I reverted it.
- **`Stmt.slot_ofSlots`.** Term forms (`congrArg₂ s (Fin.ext (by simp; omega)) …`) work only with
  a naked `;` or a longer `show`. `omega` cannot see through `Fin.val ⟨4 * i + j, _⟩ / 4`. Kept the
  3-line `funext`/`simp only`/`congr 2 <;> omega`.
- **`eq_nodeStmt_iff` as `fin_cases i <;> simp [e0, e1, e2, e3, nodeStmt_slot]`** (3 lines). I
  tried it first: 88 → 222 ms, and up the tactic ladder. I replaced it with the pattern-matching
  term (4 lines, 44 ms).
- **`aggOK_leaves` / `aggOK_nodes` with `(aggOK_nodeStmt_iff cfg P _).mpr`.** Unifying the node
  witness from `nodeStmt cfg ?nw.vkC …` hits a deterministic whnf timeout (200000 heartbeats). The
  explicit witness stays.
- **`aggOK_node_child` without `change`** (`simp only [nwR, …]`). After unfolding `nwR`, the
  `Decidable` instances still mention `nwR.x₁`, so `decide_eq_true_eq` and `nodeStmt_slot` do not
  fire, and the closing `decide` reaches `maxRecDepth` evaluating the aggregate statement. The
  `change` stays.
- **`cbad_rel`** as `refine ⟨rfl, ?_, ?_, fun b => ?_, ⟨…⟩, ?_⟩ <;> simp [union of the four simp
  sets]`. It compiles and saves 1 line. But it runs `<;>` over four different goals and loses the
  information of which lemmas close which conjunct. Fails the minimum-value filter.
- **`decodeBad_good`, `decodeBad_bad`** (`simp only […]; decide +kernel`, an existing naked `;`).
  Splitting them adds a line each. A `congrArg (NodeWitness.mk …)` term is longer.
- **`rootOK_nodeStmt` as `by simp [rootOK, nodeStmt_slot]`.** Up the ladder for a 1-line win.
- **`digestToSlot_inj` (`fun h => h ▸ rfl` → `congrArg _`), `keys_of_root`, `h20`
  (`⟨le_rfl, by decide⟩` → `by decide`), `K.bytes_ofBytes`'s `refine ⟨?_, …⟩` → `and_intros`.**
  These are 0-line cosmetic changes, so I skipped them.
- **The kernel facts and their sharing** (`x1Runs`, `nodeStmt_kat`, `rootRuns`, `nodeRuns`,
  `completeRuns`), as instructed.

## Trusted files: notes for the implementer

- `Contract/Recursion.lean` and `Contract/Certificate.lean` contain **no instance proofs and no
  theorems**. The only proof terms are the `by omega` bounds inside the bodies of `Stmt.slot` and
  `Stmt.ofSlots` (definitions, off limits). `Tag`'s `DecidableEq` is derived. Nothing was golfed.
- I have no shortening to propose for the trusted files. The definitions are already
  near-minimal: `aggOK` is a single `&&` chain, and `child` and `rootOK` are a few lines each.
  - `Stmt.ofSlots` could use Mathlib's `Fin.divNat`/`Fin.modNat`, but only through a cast
    `Fin 32 = Fin (8 * 4)`. That would be longer and less transparent.
- **Out of my scope, flagged:** line 15 of `Controls/Recursion.lean` (module docstring) is 127
  characters. It was edited during the S5-A8 decision pass. Docstrings are off limits for golf.
- **Hotspot:** `K.bytes_ofBytes` (Declined above) is the cost of `Library/Recursion.lean`.
- **API:** the four `… = false` controls (`wrong_d1`, `nonzero_d3`, `node_child_d0`,
  `node_child_d1`) now use `Bool.eq_false_iff.mpr fun h => …`. The certificate controls use
  `Bool.ne_true_of_eq_false`; the root-namespace `ne_true_of_eq_false` is deprecated in v4.34.1.
