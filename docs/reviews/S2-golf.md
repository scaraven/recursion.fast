# S2 golf: BLAKE2s (Stage 2)

The golf agent wrote this on 2026-10-14. Nothing is committed.

**What changed:** proofs only, in `RecursionFast/Controls/Blake2s.lean`. No statement, type,
definition, docstring, module comment or declaration order changed. The trusted
`Contract/Hash/Blake2s.lean` is byte-identical: its SHA-256 `9783228d…` is unchanged
(`logs/S2-golf/baseline.sha256`).

**Checks after the golf:**
- `lake build` (default targets) is green: 2092 jobs, no warnings (`logs/S2-golf/build.log`).
- `scripts/check-hygiene.sh` reports OK.
- LSP diagnostics are empty.
- `#print axioms` on every touched declaration gives `[propext, Quot.sound]`, the same as before
  (`logs/S2-golf/axioms.log`).

## Summary per file

| File | Code lines (`loc.py`) before → after | Total lines | Elaboration (`/usr/bin/time lake env lean`) before → after | Peak RSS |
|---|---:|---:|---|---:|
| `Contract/Hash/Blake2s.lean` (TRUSTED) | 67 → 67 | 131 → 131 | unchanged (6.7 s wall) | 0.85 GB |
| `Controls/Blake2s.lean` | **55 → 51** | 142 → 138 | **34.13–34.40 s → 33.71–33.98 s** | 1.07 GB → 1.07 GB |

### How the timing was measured

- The original file was kept as `logs/S2-golf/Blake2s.controls.orig.lean`.
- I timed the original and the golfed file **interleaved**, three rounds, on a shared machine with
  load average about 2 (`logs/S2-golf/timing2.log`, `time2-*.log`):

  | Round | Original | Golfed |
  |---|---:|---:|
  | 1 | 34.16 s | 33.71 s |
  | 2 | 34.40 s | 33.98 s |
  | 3 | 34.13 s | 33.80 s |

- The golfed file is never slower. The 0.3–0.4 s gap is mostly noise: the seven KATs, at about
  1.5–5.8 s of kernel time each, dominate the file.
- The changed proofs were also profiled in isolation, which measures them below that noise
  (method and numbers under `rotr_eq_rotateRight` below).

## Changes, by declaration (`Controls/Blake2s.lean`)

| Declaration | Before | After | Kind |
|---|---|---|---|
| `iv_spec` | `:= by` and a line `decide +kernel` | `:= by decide +kernel` on the statement line (100 characters) | layout, −1 line |
| `rotr_eq_rotateRight` | `rcases Nat.eq_zero_or_pos n with rfl \| h0`, two bulleted `simp`s, the second with `Nat.mod_eq_of_lt (show 32 - n < 32 by omega)` (5 lines) | `cases n <;> simp [rotr, BitVec.rotateRight, BitVec.rotateRightAux, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (Nat.sub_lt_succ 31 _)]` (2 lines) | structural, −3 lines; `omega` replaced by the term `Nat.sub_lt_succ 31 _ : 31 - k < 31 + 1` |
| `lastNode_kat` | `:= by` and a line `decide +kernel` | `:= by decide +kernel` on the last statement line | layout, −1 line |
| `blake2s_length` | `simp [blake2s, List.length_flatMap, List.map_const']` | `simp [blake2s, List.map_const']` | redundant simp argument removed: `List.length_flatMap` is already `@[simp]` |
| `blake2s256_length` | `by simp [blake2s256, blake2s_length]` | term `blake2s_length [] 32 msg` (`min 32 32` reduces to `32` by `rfl`) | directness: `simp` → term |

### `rotr_eq_rotateRight`: how the form was chosen

**Why `cases n`.** The `n = 0` case cannot be avoided:
- `rotr x 0` shifts left by `32 % 32 = 0`, giving `x ||| x`;
- `BitVec.rotateRight` shifts by `32`, giving `x ||| 0`.

`cases n` keeps both branches under one tactic.

**Method.** Each variant was written 20 times into one file and profiled with
`-DElab.async=false` and `set_option profiler true`. The figure is the sum of elaboration, tactic
execution, `simp`, type checking and typeclass inference over the 20 copies.

**Results** (`logs/S2-golf/iso-rotr-summary.log`):

| Variant | ms per 20 proofs | Same-round original | Verdict |
|---|---|---|---|
| Original | 1006–1210 | — | baseline |
| `cases n <;> simp (disch := omega) [rotr, BitVec.rotateRight_def, Nat.mod_eq_of_lt]` | 1377–1589 | 1006–1114 | **declined**: 25–40 % slower |
| `cases n <;> simp [rotr, BitVec.rotateRight_def, Nat.mod_eq_of_lt, hn, X]`, with `X` = `Nat.sub_lt_succ`, `Nat.lt_succ_iff` or `Nat.lt_add_one_iff` | 1258–1699 | 1006–1114 | **declined**: slower |
| **Adopted** (instantiated rewrites, original unfolding lemmas) | 1004–1141 | 1107–1210 | no slower in any round |

The `omega` variant is the shortest (1 line after `apply`). The slowdown comes from rewrites
that `simp` must discharge one at a time, against the original's instantiated ones; this is about
+25 ms per proof.

### The length theorems

The length theorems, with the same method (`logs/S2-golf/iso-len-summary.log`), take 745–782 ms
after against 758–849 ms before, per 20 pairs.

## Declined, and why

- **The KATs, the negative controls, `hex_pos` and `sigma_perm` (`decide +kernel`).** Left
  unchanged, because I found no strictly faster closed form.
  - **What I measured:** the obvious alternative is a kernel-only `Eq.refl`, v0.3's `kernel_rfl`.
    It was defined in a scratch file only (`logs/S2-golf/katforms.lean`, `katforms.log`).
  - **Results:**

    | Proof | `decide +kernel` | `kernel_rfl` |
    |---|---:|---:|
    | `abc` | 2.55 s | 2.25 s |
    | `keyed_65` | 5.79 s | 5.79 s |

  - **Why not adopt it:** it needs `import Lean` and a new tactic definition (a new declaration,
    out of scope for a proof golf). `import Lean` doubles peak RSS (2.16 GB against 1.07 GB) for
    at most about 0.3 s per KAT.
  - `rfl` and plain `decide` exceed the recursion depth (S2-RESULT), and raising `maxRecDepth` is
    forbidden by the hygiene check.
- **The statement-side cost of `hex` in the KATs (≈ 0.2 s each, S2-RESULT deviation 4).** Writing
  the digests as byte lists would change the statements, so this was not touched.
- **One-line `rotr_eq_rotateRight` without the `apply`** (`cases n <;> simp (disch := omega)
  [← UInt32.toBitVec_inj, …]`). It is 104 characters long, over the 100-column style. It was not
  timed on its own, but it uses the same `omega` discharger as the variant measured slower above.
- **`blake2s256_length` on one line.** It would be 104 characters, so it keeps the two-line term
  form.

## Trusted file (`Contract/Hash/Blake2s.lean`)

It contains **no `theorem`, `lemma` or `instance`**: only definitions, all off limits. There is
nothing to golf and nothing that belongs in `Controls/`.

## Notes for the implementer

1. **`docs/stages/S2-RESULT.md`, table "Files".** `Controls/Blake2s.lean` is now **51** code lines
   and **138** in total (was 55 and 142).
2. **`docs/stages/S2-RESULT.md`, table "Controls and what each shows".**
   - `blake2s256_length` is now a term proof (`blake2s_length [] 32 msg`), not `simp`.
   - `rotr_eq_rotateRight` is still closed by `simp`, now in one `cases n <;> simp` call without
     `omega`.
   - The headline sentence "the structural facts by `decide +kernel` or `simp`" is still true.
3. **Line numbers in the reviewer's findings** for `Controls/Blake2s.lean` may be off by −1 to −5
   after line 73.
4. **Scratch files.** Everything I measured is under `logs/S2-golf/` (gitignored): the scratch
   Lean files, profiles, timings, the diff (`controls.diff`) and the original copy. None of it is a
   module of the build.
