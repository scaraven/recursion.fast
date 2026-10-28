# Stage F-ivc: RESULT (V4-A11, one pure-IVC benchmark scored continuously; `proofCap` removed)

Implementing agent: an Opus subagent, 2026-10-28, in `recursion.fast-v4-ivc` on `v4/ivc-score` (from
`v4/ks-standard` `8ad98e9`). Specification: the V4-A11 draft with its §11 amendments after the rules review
(`docs/v4/reviews/F-ivc-rules-review.md`), now BRIEF §5d. Recorded by the orchestrator from the agent's report.
Logs under `logs/f-ivc/` (gitignored).

## What was built

- **Trusted contract.** `acc`'s first conjunct is `p.π.size < 2^64` (was `≤ proofCap`); `proofCap` is gone.
  `Computes`' domain is `π.size ≤ 8 · outCap` (128 MiB; was `≤ proofCap`). `outCap = 2^24` unchanged, its arithmetic
  redone against the 64 MiB file cap. Headlines of `Certificate`, `Extractor`, `Relation`, `Security`, `Tree`,
  `Contract`. **349 code lines** (350 before; budget 500; `loc-before.log`, `loc-after.log`).
- **Library.** `WitnessSending`: `check` bounds each child below `2^64` bytes; `ext_run`, `pre_mem` for every proof
  below `2^60` bytes; `fits_of_acc`, `computes` re-proved; the certificate proved. `Fast.accF` mirrors `acc`.
- **Controls** (restated): `Relation`, `Certificate`, `Backdoor`, `WitnessSending`, `Compose`, `LogScan`,
  `Extractor`.
- **Harness.** `rfh/draws.py` (new; `secrets`: M = 64 + G, G geometric of mean 16, truncated at 112; lengths i.i.d.
  ∝ 1/n² on [2^17, 2^20]); `rfh/prover.py` (`first` and `step`, `ready_s`, the clock stops when the pid namespace's
  init is dead after `cgroup.kill` or a pidfd `SIGKILL`, `kill_unit` after, kill latency recorded; R-M1: `OSError`
  in the rename or the read is the entry's failure; `setup_cap`); `rfh/sandbox.py` (status mode); `rfh/bench.py`
  (rewritten: one stream on one service lifetime, `/dev/shm` request directories, check batches of 8 between steps,
  best-of-2 `V_i`, canaries on π₁, π₂, π_M, interleaved calibration `c_P` and `T_triv` medians, re-timing by trimmed
  least squares with the kept run scored (R-M2), truncation, DoS on π_M, the score and its diagnostics);
  `tools/calib.c` (new, 152 lines); `run-benchmark.py`, `aggregate.py` (one-job plan; `--rank`: median of the last
  three evaluations per prover hash, a REJECT counted as infinite), `evaluate.py`, `season.toml`, `smoke.toml`,
  workflows, `PROVER.md`, `FORMAT.md`.
- **Provers and tests.** `toy.c` (`first`, `step`), `honest/prover.s` regenerated; `test_tv.py`, `test_stream.py`
  (new), `test_aggregate.py`, `test_dos.py`, `smoke.py`, mock badge; `test_sandbox.py` gains the hostile-clock tests
  (a thread writing after `done`, a forked writer, work left to a child after stdout closes, an orphaned child) and
  the R-M1 tests (`mkdir` on an input name, `chmod 000 /work`).
- **Documents.** BRIEF §5d (V4-A11), design §3.4–§3.6 rewritten and §0–§2.8, §3.7, §4–§7 updated, READMEs,
  `CLAUDE.md` (by the orchestrator).

## Checks (all logs in `logs/f-ivc/`)

| Check | Outcome | Time (measured) |
|---|---|---|
| `lake build` (cold, shared `pkgs-local`) | green, 1,266 jobs, 0 warnings | 1 min 9 s |
| axiom audit | PASS | 4.5 s |
| hygiene, source rule, token sweep, gate fixtures | OK, 0 unreviewed tokens | 5.1 s, 12.8 s, 56 s |
| `test_sandbox.py` | 52 ok | 19.8 s |
| `test_tv`, `test_stream`, `test_aggregate`, `test_dos` | 14, 10, 12, 6 ok | < 2 s each |
| `smoke.py --mock` | 13 ok | 33.8 s |
| `org-setup.sh`; `smoke.py --org` (compiled badge, Lean kernel) | OK; 21 ok (WS certified and ACCEPTed on the stream, PROVISIONAL, source-rule and over-budget paths, five broken provers REJECTed) | 1 min 53 s; 4 min 44 s |
| accprobe and canaries; extractor interpreter; service build | 0 failures; 0 failures; OK | 36 s; —; 14.6 s |

The real-badge smoke ran against a private package copy (`.lake/pkgs-ivc`), then the link was restored and the
cold build and audit re-ran against the shared tree (`find -newer`: 0 files written there). Two later `bench.py`
changes (deadline-aware check batches; the last calibration sample on a re-timed step) were re-checked by the unit
tests and the mock smoke, not by the real-badge smoke.

## Controls

Positive: `deep_accepted` (the k-level WS proof, 9704·2^k − 9656 bytes, accepted for k ≤ 50),
`deep7_over_old_cap` (1,232,456 bytes, above the old cap, accepted), `decodeWit_children_size` and
`child_in_domain` (the `Computes` domain is closed under extraction), `acc_query_at_cap`, `node_children_word`; the
WS certificate controls unchanged. Negative: `acc_over_word` (every `acc` rejects `|π| ≥ 2^64`),
`deep_accepted_but_unwritable`, `ws_output_beyond_domain` (the domain bound is tight), `acc_rejects_all_certified`.

## Deviations from the specification

- **D1. `acc` keeps a word bound** (`|π| < 2^64`) instead of no bound: completeness for every witness makes an
  entry's accepted proofs closed under forming nodes; a WS node contains its children, so without a bound the
  relation holds children no 64-bit length field encodes, and no growing-proof entry is complete. A cap in the
  entry's own `V` (R-M4) fails the same closure argument. The bound caps nothing a runner holds.
- **D2. `Computes` keeps a domain**, `π.size ≤ 8 · outCap` (R-M4 asked for every proof): an extractor that copies
  π cannot output within `outCap` beyond it. The domain is closed under extraction (kernel), so every proof in a
  deployed root's extraction tree is inside it.
- G has mean 16 (the draft's formula had mean 15); the fit starts from Theil–Sen and iterates trimmed least squares
  (a least-squares start mis-trimmed in 52 of 2,000 trials); `build_s` 120 s and `setup_s` 240 s so the one job fits
  `PART_S`; per-step service query counts are not output (the service keeps lifetime totals); `calib_ref_ns` is a
  placeholder until measured on a runner (this VM lacks PCLMULQDQ; `calib` reports `clmul=soft`).

## Open

- No kernel composition theorem for the stream's comb shape (`Compose` is over balanced trees; paper, as in v4).
- Work that starts before `stream_s` (canaries, the closing calibration sample, a re-run's check) can end after it,
  up to about 4 min in the worst case (estimate).
- The two-model paired record (§7) is not implemented (carried gap; a season-1 condition).
- Nothing has run on GitHub or at the season shape; every season-shape number is an estimate.
