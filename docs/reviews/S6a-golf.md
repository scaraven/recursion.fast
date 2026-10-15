# S6a golf: `Controls/Chain.lean` (Stage 6a)

The golf agent wrote this on 2026-10-15. Nothing is committed.

**What changed.** The edits are in `RecursionFast/Controls/Chain.lean` only, and almost all of them
are proofs.
- **Unchanged.** No statement, type, definition body, docstring or module comment changed. No
  declaration was renamed, reordered, split, merged or removed.
- **Added.** One theorem, `mul_fast`, with a docstring. It is an equation of `Mul K` instances, used
  as a rewrite.
- **New import.** `RecursionFast.Library.Field` (untrusted; `Controls/Layout.lean` already imports
  it). It supplies `zero_mul`, `mul_one`, … for `K`.
- **Not touched.** `ChainData.lean` (rendered), `harness/`, and every trusted file.
- **Records.** The original is `logs/S6a-golf/Chain.lean.orig` (SHA-256 `f8bf7039…`), the golfed
  copy `Chain.lean.after`, and the diff `logs/S6a-golf/Chain.diff`.

**Checks.**
- **Target build.** `lake build RecursionFast.Controls.Chain` was green after each of the three
  hunks: 73 s, then 50 s, then 16 s (2,089 jobs once `Library.Field` is imported).
- **LSP.** No diagnostics on the file, not even a warning.
- **Axioms** (`logs/S6a-golf/axioms-after.log`). All 20 theorems use a subset of `propext`,
  `Classical.choice` and `Quot.sound`. There is no `sorry`, no `native_decide` and no
  `Lean.ofReduceBool`.
- **Hygiene.** `scripts/check-hygiene.sh` reports OK.
- **Default `lake build`.** `Controls.Chain` builds. The only failures are
  `RecursionFast.Controls.Recursion` and `RecursionFast.Controls.RecursionNode`, which are Stage 5's
  files and are being edited concurrently. They do not import `Chain`.

## Summary

| | before | after |
|---|---:|---:|
| `loc.py`: total / blank / comment / code / theorems | 195 / 36 / 62 / 97 / 19 | 204 / 37 / 68 / 99 / 20 |
| `/usr/bin/time lake env lean RecursionFast/Controls/Chain.lean` | **127.5 s** | **18.3–18.9 s** (3 runs, `after-time.log`) |
| interleaved, 2 rounds, same machine and load (`logs/S6a-golf/time-interleaved.log`) | 128.3 s, 128.7 s | 18.9 s, 18.0 s (**×6.9 faster**) |
| peak RSS | 3.80 GB | 3.03 GB |
| kernel type checking (profiler, sum) | 121 s | 11.7 s |
| `import` | 2.7 s | 3.9 s (+1.2 s: `Library.Field` pulls in CompPoly's `BF64`) |

- **Lines.** The code grows by 2 lines. `mul_fast` adds 3 code lines and its import 1; the
  negatives and `LGF_rel` lose 2 net. The comment lines are the 4-line docstring of `mul_fast` and
  two proof comments.
- **Time.** As the brief asked, time came first. Every changed declaration is faster.

## Where the 128 s went (profile before)

Measured with `lake env lean -Dprofiler=true`, per declaration, using `#eval` markers in a scratch
copy (`logs/S6a-golf/before-per-decl.log`, `after-per-decl.log`, generated from
`scratch/ChainProf.lean`, `scratch/ChainAfterProf.lean`; whole file: `before-profile.log`). The
ranges are over the runs. Kernel type checking
was 121 s of the 127.5 s. Import was 2.7 s and elaboration plus tactics about 0.4 s. Nothing ran in
parallel: the sum of the type-checking times equals the wall time.

| declaration | kernel time before | what the kernel evaluates | after |
|---|---:|---|---:|
| `LG0_rel` | 22.1–23.4 s | the whole `relBelow`; the G chip's 2 rows are 18.6 s, the PUBG row ≈ 4 s | **4.56 s** |
| `LG79_rel` | 22.1–23.6 s | the same | **4.57–4.71 s** |
| `LG0_neg_sum` | 22.1–22.7 s | all gadgets (they hold), then bus 0 | **0.10 s** |
| `LG0_neg_out` | 22.6–23.3 s | all gadgets (they hold), then bus 5 | **0.04 s** |
| `LGF_rel` | 22.6 s in 10 aux lemmas: PUBG gadget 5.3 s, G gadget 17.2 s, the rest ≤ 0.3 s | the gadgets of chips 0, 1 again | **0.62 s** in 8 aux lemmas |
| `LG0_neg_byte` | 7.8–8.5 s | the PUBG row, then G row 0 up to the failing constraint | **0.43–0.49 s** |
| `Lchain_admissible` | 0.55 s | the admissibility of 25 chips | 0.57 s (unchanged) |
| `LG0_trim` | 0.49 s | 24 + 24 table rows against `add8` | 0.46 s (unchanged) |
| the rest (`*_admissible`, `*_not_admissible_23`, `*_mix`) | < 0.13 s each | | unchanged |

**The cost is `K` products.**
- **Per product.** The kernel spends 32–53 ms on every `K` product (bench
  `logs/S6a-golf/scratch/exp3.lean`, 100 products per theorem). It is a 64-step `Fin.foldl` plus two folds
  of 64 steps each. The factors make no difference: by `0x10000` it is 3.2 s per 100, by a dense
  word 4.7 s.
- **Not the recursion scheme.** The loop's well-founded recursion is not the bottleneck. The same
  product with `List.finRange 64` instead of `Fin.foldl` (equal by `Fin.foldl_eq_finRange_foldl`)
  takes 3.6 s per 100, no faster.
- **What a G row costs.** One row has about 316 products, most with a factor `0` or `1`:
  - the gate matrix `M0` and the coefficient `c = 1`;
  - the `S` product `(M0·z)(M1·z)`, where `M0·z ∈ {0, 1}`;
  - the many zero cells.

## Changes, by declaration

Three hunks, each building green before the next.

| declaration | before | after | kind | kernel time before → after |
|---|---|---|---|---|
| `LG0_neg_sum` | `rw [← relBelow_iff …]; decide +kernel` (the whole relation) | `fun h => absurd (h.2.2.2.1 0) (by decide +kernel)`: only bus 0's clause is decided, i.e. the add lookups the docstring names | structured, 2 → 2 lines | 22.6 s → 0.10 s |
| `LG0_neg_out` | the same | `fun h => absurd (h.2.2.2.1 5) (by decide +kernel)`, with the comment `bus 5 is GOUT` | structured, 2 → 2 | 22.7 s → 0.04 s |
| `LG0_neg_byte` | the same | `fun h => absurd (h.2.2.1 _ (List.getElem_mem (n := 1) _) 0 _ ⟨8, _⟩) (by decide +kernel)`: only constraint 8 (`in_A`, `harness/CHAIN-LAYOUT.md` §4) of G row 0 is evaluated, the constraint the docstring names | structured, 2 → 3 (+1 comment) | 7.9 s → 0.45 s |
| `LGF_rel`, gadget clause | `revert r; decide +kernel` for chips 0, 1 and 3 | chips 0 and 1 are `LG0_rel.2.2.1 _ (mem) r hr`, because `LGF_chip0/1` and `LGF_wit[0/1]` are, by unfolding, `LG0`'s (the same reason as `harness_G`). Chip 3 (`NIB`) has 0 constraints, like chip 2, so `all_goals exact fun i => i.elim0`. The proof comment is updated. | reuse, 4 → 3 lines | 22.5 s → 0 s |
| `LGF_rel`, fixed clause | chips 0, 1: `absurd ht (by rw [show LGF_chip0.fixed = none from rfl]; exact Option.not_mem_none _)`; chip 2: `have h2`, `rw [h2, Option.mem_def, Option.some.injEq] at ht`, `subst ht` | chips 0, 1: `absurd ht (Option.not_mem_none _)` (by unfolding); chip 2: `obtain rfl := Option.some.inj (Option.mem_def.1 ht)`, the pattern chip 3 already used | syntax, −3 lines | < 0.1 s |
| `mul_fast` (new theorem) | — | `K.instMul = ⟨fun a b => if a = 0 ∨ b = 0 then 0 else if a = 1 then b else if b = 1 then a else a * b⟩`, by `congrArg Mul.mk (funext₂ fun a b => show a * b = _ by split_ifs <;> simp_all)` (field lemmas from `Library.Field`) | helper for the next row | elaboration 0.15 s |
| `LG0_rel`, `LG79_rel` | `rw [← relBelow_iff (N := 8) (by decide)]; decide +kernel` | `rw [← relBelow_iff (N := 8) (by decide), mul_fast]; decide +kernel`. `relBelow`'s `Decidable` instance is generic in `[Mul F]`, so the kernel evaluates the same relation with the short-cut product. The statement is unchanged: `rw` rewrites the instance argument only. | performance, same lines | 22.7 s → 4.56 s, 22.6 s → 4.6 s |

**What still costs time** (after: 11.7 s kernel in total).
- **`LG0_rel`, `LG79_rel`** (9.1 s). These are the about 55 products per G row by the constants
  `X^8, X^16, X^24, X^4, X^12, …, 1 + X^32` with non-zero byte cells.
- **`Lchain_admissible` and `LG0_trim`** (1 s).

## Declined

1. **A fully fast `K` product** (one helper that is provably `K.mul`, used by `mul_fast`).
   - **The gain.** A `Nat`-level carry-less product with early exit takes 2 ms instead of 32 ms for
     the sparse constants of the G chip (`scratch/exp3.lean`, `nat a=const`: 0.20 s per 100). That would
     bring `LG0_rel`/`LG79_rel` to under 1 s each and the file to about 10 s.
   - **Why not here.** Proving it equal to `K.clmul`/`K.reduce` for all inputs takes about 30–60
     lines of bit-level lemmas, or CompPoly's `toPoly_*`. That is library work, not golf, and it is
     the same item as S6a-RESULT open question 4 (O-9).
   - **Recommendation.** If the orchestrator wants it, `mul_fast` and its fuller version belong in
     `Library/` (e.g. next to `relBelow_iff`), where `Controls/Layout.lean` and later controls can
     use them.
2. **Removing the now-unused local instance** `Decidable (g.holds z)`, lines 42–44.
   - After the `LGF_rel` change no proof uses it: a scratch copy without it compiles.
   - It is a declaration with a docstring, so removing it is not a proof edit. **Recommendation:**
     the implementer drops it.
3. **Updating stale prose.** The rules forbid this edit, so it is left to the implementer:
   - **Module comment.** It says "the kernel evaluates one G row in about 10 s". With `mul_fast` a
     G row takes ≈ 1.8 s: the 2-row G gadget took 3.59 s in isolation, `logs/S6a-golf/scratch/exp2.lean`.
     S6a-RESULT's extrapolation "a full compression ≈ 27 min" becomes roughly 5–6 min (160 G rows
     at ≈ 1.8 s; the 21 S and `FINAL` rows were not measured).
   - **S6a-RESULT §4.** Its table quotes `decide +kernel` and 8–23 s for the negatives and `LGF_rel`,
     and "128 s, 3.8 GB" for the build. These are now the numbers above.
   - **`LGF_rel`'s docstring.** It still reads correctly, since chips 0 and 1 are "by the kernel"
     through `LG0_rel`.
4. **`Elab.async` parallelism.** The theorems are independent, but the kernel checks ran serially.
   Forcing parallel elaboration with an option is a harness setting, not a proof golf.
5. **`mem_list_sum` via Mathlib.** There is no list analogue of `Multiset.mem_sum`
   (loogle: none). A `Multiset.join` detour would not be shorter.
6. **`add8_sub`'s `rw [← he]; exact …` as `he ▸ …`.** It saves one line but is fragile; the policy
   allows a 1-line saving only when it is zero-risk.
7. **Merging the two `absurd ht (Option.not_mem_none _)` bullets** (`iterate 2`). It saves one line
   and makes the proof less clear.
8. **`Lchain_admissible`, `*_not_admissible_23`, `LG0_admissible`, `*_mix`, `LG0_trim`.** They are
   already under 0.6 s each. There is no structured proof that is shorter or faster.

## Robustness notes

- **`LGF_rel` and `LG0`'s data.** `LGF_rel` now depends on `LG0`'s chips 0, 1 and witness tables 0,
  1 being `LGF`'s by unfolding.
  - **Today.** This holds: the rendered text is identical apart from the names, and `harness_G`
    already relies on it for chip 1.
  - **If the generator ever diverges them.** `LGF_rel` fails to build. It cannot pass silently.
- **The negatives and their docstrings.** The negatives now prove exactly the clause their
  docstrings name: `in_A` for `LG0_neg_byte`, bus 0 for `LG0_neg_sum`, `GOUT` for `LG0_neg_out`.
  - **The statements are unchanged** (`¬ rel`).
  - **"Only".** The claim "only the lookup fails" was not proved before either. The Python log
    covers it (`logs/S6a/lean-negatives-python.log`).
