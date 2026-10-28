# Stage F-ivc: adversarial review of the implementation (commit `80330cb`)

Reviewer: a Fable subagent, 2026-10-28, with the `adversarial-review` and `lean4:review` skills. Read-only review of
`git diff 8ad98e9 80330cb` against BRIEF §5d, design §3.4–§3.6, the draft's §11 and `F-ivc-rules-review.md`. Four
probes ran on copies of harness modules (`tree_bytes`, `rmtree`, `aggregate.rank`, `bwrap --dev`), marked
**measured**; the line count came from `scripts/loc.py` on a `git archive` of the commit. Recorded by the orchestrator
from the reviewer's report; the fix pass answers each finding in `F-ivc-RESULT.md`.

## Majors

**M-1. `/work` on the host's shared `/dev/shm` lets the prover make the runner's own writes fail: an uncaught
`OSError`, a harness ERROR, a free re-roll (reopens rules-review M-1).** `rfh/bench.py:128-135` places request and
staging directories on `/dev/shm` (half of RAM, **measured** 31.4 of 62.8 GiB here; about 8 GB on a 16 GB runner,
estimate), under the prover's 11 GB cgroup. The prover can fill it during its untimed start-up, or in a previous step,
and defeat cleanup with a mode-000 subdirectory (`bench.py:300-304` chmods only the top directory and `rmtree`s with
`ignore_errors`; **measured**, the subtree survives). The runner's staging writes (`prover.py:239-242`) and `vk.hex`
(`bench.py:293-294`) are outside any `except OSError`, so the run becomes ERROR, which `--rank` ignores. Inode
exhaustion has the same effect. R-M1 asked for a tmpfs sized inside the cgroup. Fix: any exception while an entry
process is alive is the entry's failure (default, not an allow-list); a per-request size bound (or a before/after
disk check that REJECTs a prover leaving it fuller); robust cleanup.

**M-2. `setup_cap` is bypassed by a sparse file or a mode-000 directory, and `tree_sha256` then runs unbounded.**
`prover.py:318-329` sums `st_blocks·512` under `os.walk` with `onerror=None`: a 1 TiB sparse file plus 1 MiB under a
000 directory counts 0 (**measured**). Then `run-benchmark.py:85`'s `tree_sha256` reads the whole tree without a byte
cap or timeout (about 1,000 s at 1 GB/s, estimate) → `PART_S` → ERROR; or hidden real data fills the disk and the
runner's later writes fail. Fix: count `max(st_size, st_blocks·512)`; walk with `onerror` raising (→ unbounded →
REJECT); make the tree readable before measuring; bound `tree_sha256` by `setup_cap` bytes and a timeout.

**M-3. A `PART_S` overrun is reachable by the entry and yields ERROR.** `evaluate.py:422` runs the part under
`timeout=PART_S` and nothing catches `TimeoutExpired`; the workflow writes `benchmark: error`. The capped steps sum to
1,500 s of 1,680, but work that starts before the stream cap and ends after it is outside the 960 s: a check batch's
two badge passes (each `left + 30`, so 60 s; `bench.py:339`), the canaries (`verify_s·(items + 1) + 30`, `bench.py:192`),
the closing calibration sample. The entry steers every term (a slow build, a sleeping setup, stalls to the stream cap, a
`V` that takes 9.9 s on a flagged π). Fix: a part timeout after the prover's build started is the entry's REJECT; after
truncation skip the canaries and the closing sample and bound the last batch by one 30 s badge run; make the nesting
hold at the real worst case.

**M-4. The provisional ranking still discards a disliked run for free.** (a) `aggregate.py:110-125` counts a REJECT
as `inf`, but a truncated (not comparable) ACCEPT adds nothing to `vals` while occupying a slot of the last three
(**measured**: runs [5.0, trunc, trunc, 1.0] rank at 1.0); stalling to the cap is cheaper than a REJECT. (b) Grouping by
binary hash: a binary with one evaluation ranks on it (**measured**), and a `nop` per submission gives a fresh hash, so
"median of the last three" binds nothing. Fix: a truncated or not-comparable run counts as `inf`; rank a hash only with
at least three evaluations, or group by the entry (source tree or pull request) instead of the binary.

## Minors

- m-1. R-M1 is an allow-list: `sb.track()` failing (a prover `_exit`ing at once can race `pidfd_open`), `kill_tree` not
  dead in 30 s, the stage and `vk.hex` writes, `exit_code()` returning `None` treated as success
  (`prover.py:212-213, 270-271, 276-278`) are still ERROR or wrong. Fix as M-1.
- m-2. Residual load on `c_P` and `T_triv`: a slower sample helps the entry (kernel compaction, freeing tmpfs pages,
  thermal state within the 1 s idle gap). Fix: a longer gap, samples as medians of short runs, publish per-sample
  variance; measure (D10).
- m-3. `calib_ref_ns` is a placeholder (400 ms); flag results `c_P_provisional` until measured.
- m-4. The hostile-clock tests pass under the old clock order too (the kill is fast either way); only the `eof` path
  discriminates. Fix: expose the stop time and have the late writer stamp `CLOCK_MONOTONIC` every 1 ms; assert the last
  stamp in `proof.bin` ≤ the stop time.
- m-5. A badge crash after the cap becomes truncation (`bench.py:343-348`); only a timeout should.
- m-6. Prover stderr reaches the public PR comment as Markdown (`Bench.diag`; `run-benchmark.py:92`;
  `evaluate-entry.yml:117` neutralises only `@`): reduce to printable ASCII in a code span.
- m-7. Stale trusted docstring: `Contract/Certificate.lean:17` ("the root, the samples, the canaries, the stream").
- m-8. Design §3.6 says a batch ends within 30 s of the cap; the code allows 60 s (see M-3).
- m-9. The signature index tells a step `i < 64` that it is not last; harmless under the cubic mean (0.1–0.3 %,
  estimate); state it in PROVER.md.
- m-10. `draws.py` rounds through a float; say that the realised integers are what is published.

## Checked and found right

**Lean.** `acc` is tight and non-vacuous (positive `deep_accepted`, `deep7_over_old_cap`, `acc_query_at_cap`; negative
`acc_over_word`, `deep_accepted_but_unwritable`, `acc_rejects_all_certified`; `accF_eq`). D1 is forced: a bound inside
an entry's own `V` fails completeness on the node of two children just under it, and no bound leaves `Rel` holding
children no 64-bit word encodes. D2 is sound: `KS` is unchanged, and `decodeWit_children_size` / `child_in_domain`
close the domain under extraction, with `ws_output_beyond_domain` showing it tight; `Library/Compose.lean` never used
`proofCap`. The disposition of R-M4 is D2, documented. `outCap`'s arithmetic rechecked. No stale `proofCap` in code.
349 contract lines. Controls in both directions for every changed definition.

**Harness.** Draws from `secrets` only, exact distributions; the clock stops when the namespace init's pidfd is
readable after `cgroup.kill` (the kernel makes init wait for every process), `kill_unit` after; staging invisible to the
prover (fresh `/dev/shm` inside bwrap, **measured**); R-M2 as specified; checks and calibration never overlap an entry
process; best-of-2 `V_i`; the score as §4; truncation flagged; DoS on π_M with `SystemRandom`; `calib` built and hashed
before entry code; `ready_s`; bounded stdout; `read_output` safe; `stream.jsonl` escaped; CI runs every new test.

## Verdict

Not ready as the closure of R-M1: the Lean side is correct and well controlled, and the measurement core is as
specified, but R-M1 is implemented as two caught exceptions rather than the default rule, and M-1 to M-4 leave
zero-cost ways to turn a disliked run into an uncounted ERROR or an unscored truncation. All four are small, local
fixes.
