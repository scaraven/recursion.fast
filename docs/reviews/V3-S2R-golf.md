# V3-S2R golf report

The golf pass ran after the fix pass, on the tree as it stood then: the stage's modules plus the
fix pass's `Controls/LogScan.lean` and the ported certificate controls. It changed no statement:
every existing declaration keeps its signature, and the pass adds two helper lemmas. Logs:
`logs/s2r/golf/` (gitignored). The pre-golf copies are `logs/s2r/golf/before/`, and the
per-module timer is `logs/s2r/golf/time.sh` (`lake env lean <file>` with prebuilt imports).

## Line counts (`scripts/loc.py`, code lines)

| File | Before | After |
|---|---:|---:|
| `Library/Machine.lean` | 109 | 113 (+ `getD_toArray`) |
| `Library/WitnessSending.lean` | 237 | 235 |
| `Controls/LogScan.lean` | 309 | 298 |
| `Library/Completeness.lean`, `Controls/Machine`, `Extractor`, `Completeness`, `WitnessSending`, `Certificate`, `Relation`, `Security`, `Backdoor` | 836 | 836 (unchanged) |
| **Total of the twelve modules** | **1561** | **1552** |

The trusted contract was not golfed. Its 292 lines are the fix pass's, and shortening definitions
there would change trusted text that the review has read.

## Per-module times (seconds, development VM; `logs/s2r/golf/time-before.log`, `time-after.log`)

| Module | Before | After |
|---|---:|---:|
| `Controls/Relation` | 50.2 | 50.5 |
| `Controls/LogScan` | 8.6 | 8.6 |
| `Controls/WitnessSending` | 8.6 | 8.5 |
| `Controls/Certificate` | 7.3 | 7.1 |
| `Controls/Backdoor` | 6.9 | 7.1 |
| `Library/WitnessSending` | 6.7 | 7.1 |
| `Controls/Extractor` | 6.1 | 6.0 |
| `Controls/Completeness` | 6.1 | 5.7 |
| `Controls/Machine`, `Library/Machine`, `Library/Completeness`, `Controls/Security` | 5.0–5.4 | 5.0–5.4 |

The import floor is about 2.5 s per module. The differences are within run-to-run noise: the pass
saved lines, not time.

## What changed

- `getD_toArray` (new, `Library/Machine.lean`): the tape read as an array is the list read. It
  replaces three local copies of the same `have`: `ext_run` in `Library/WitnessSending.lean`, and
  `scan_loop` and `scan_computes` in `Controls/LogScan.lean`.
- `st_n_ne` (new, `Controls/LogScan.lean`): the loop's entry test. It replaces the duplicated
  `have h5` in `iter_next` and `iter_found`.
- `ceilw`: the two `by_cases` branches, which ran the same `simp only; omega`, are one `split_ifs`
  with the identical tactic on both goals.

## Declined, and why

- **`Controls/Relation` (50 s)**: the time is the kernel evaluating BLAKE2s known answers
  (`decide +kernel`, about 2.5 s per compression). They are controls against `hashlib`, and
  shortening them would change what they check.
- **`iter_next`'s `e1`/`e2`/`e3`**: these could be folded into one `simp` with
  `← BitVec.ofNat_add`. The attempt did not elaborate cleanly, and the named equations read better.
- **`head_exec`'s `toNat_toWord` list**: shorter forms push the address arithmetic into a broad
  `simp` with `omega` side goals, which goes up the complexity ladder for a one- or two-line saving.
- **`Controls/Completeness.sum_bad`**: a shorter proof through an `Equiv` sum lemma was not found
  quickly, and the current proof is explicit.
- **`Library/WitnessSending` `check_*`, `Controls/Certificate`, `Backdoor`**: already direct; no
  win found by the pattern scan (`lean4-skills-find-golfable`, no hits) or by reading.
- **The contract**: not golfed (above).

Saturation: 3 of 5 attempts succeeded; the remaining candidates were marginal or went up the
ladder.

## Verification

- `lake build` of every target is green after the golf.
- `scripts/ci.sh` passes (`logs/s2r/fix/ci-final.log`), with the axiom audit PASS.
- The pre-golf and post-golf declaration headers differ only by the two added lemmas
  (`diff` against `logs/s2r/golf/before/`).
