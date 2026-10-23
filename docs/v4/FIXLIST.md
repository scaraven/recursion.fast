# v4 orchestrator's fix queue

Items found outside the formal reviews (CI runs, the baseline team, cross-reading), queued for the
next pass of the stage that owns them. Each item is closed with the commit that fixes it.

| # | Owner | Item | Source | Status |
|---|---|---|---|---|
| Q1 | B | `Service.stop()` closes stdin then calls `communicate()`: `ValueError: flush of closed file` on Python 3.12 (the runner's); fails the service and sandbox CI jobs | CI run 39935079265 | fixed in golf GB |
| Q2 | B | `harness/org-setup.sh` default ROOTS lack CompPoly's `BF64.Ext3`, `BF64.Bytes` closure (v3 precedent `09668b5`): an entry using CompPoly's field is rejected by gate rule 3 (its `@[csimp]` lemma) and CI does not prebuild it | baseline team (F) | B fix pass |
| Q3 | D | design text: baseline "will be PROVISIONAL" (it is certified: `spartan-srom`); one 13 GB cgroup vs B's 11 GB + 2 GB; "mean leaf time" vs `bench.py`'s Σ(M+1 leaves)/M; README/CLAUDE.md still say the submissions repository pins `15e4ae5` | baseline team (F) | doc pass |
| Q4 | D | design/AGENTS: a `Submission` must be computable for the badge to compile (a noncomputable `ε : ℝ≥0` literal fails; write it as a cast from `ℚ≥0`); compiled `ByteArray.data` copies the array (a v3-style parser became quadratic: 88 s on 539 KB) | baseline team (F) | doc pass |
| Q5 | B/D | nanoda does not fit a 16 GB runner (17.6 GB after 10 min 51 s on the witness-sending entry): CI uses the Lean kernel only; the design and results must say so | stage B | doc pass |
| Q6 | B | `harness/FORMAT.md` states `tr.length ≤ qV` before the contract does | baseline team (F) | lands with A's fix pass (RA-M2) |
| Q8 | B | CI `run:` steps use GitHub's default `bash -e` without `pipefail`, so `cmd | tee log` masks failures: in run 39935079265 the `acc` probe crashed (Q1) and the step passed. Set `defaults: run: shell: bash` (→ `-eo pipefail`) in every workflow; print the CPU model (`lscpu`) at the start of every job | CI run 39935079265 | B fix pass |
| Q9 | B | RB-M1 (one `T_V` sample vs a min-of-N cap; `fail-fast: true` cancels the other jobs) and RB-m1…m11 | `docs/v4/reviews/RB-harness-review.md` | B fix pass |
| Q7 | B | `evaluate.py` step 4 (byte-identical rebuild) REJECTs a certified entry: the gate tree builds every `lean/*.lean`, the comparator tree only `Solution`'s closure, and gate-only artifacts count as differences (an undocumented "Solution must import every module" rule). Fix: the gate tree builds `Solution`'s closure plus the badge; require byte equality on that closure and that the badge's import closure lies inside it; say that entry modules outside it are never built by the harness. Evidence: submissions worktree `logs/f3/cert-lean/` (comparator with the Lean kernel accepted in 372 s, peak RSS 3.7 GB) | baseline team (F3) | B fix pass |
| Q10 | B | `timedCheck`'s `if ok then now else now` idiom keeps the check inside the timed region only by today's compiler behaviour (GB's probe moved a discarded computation out); use a real barrier (e.g. `IO.mkRef (check …)`) | golf GB | B fix pass |
