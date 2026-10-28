# Stage F-ivc: golf

Golf agent: an Opus subagent, 2026-10-28, with the `lean4:golf` skill, on `80330cb`. Scope: the Lean proofs the stage
added or changed. No statement, definition, structure or docstring changed; no declaration added, removed or
renamed; the contract untouched. A script compared every declaration's docstring and header (text up to the first
`:=`) between `HEAD` and the golfed tree: 0 mismatches over 192 declarations. Logs under `logs/f-ivc-golf/`.
Recorded by the orchestrator from the agent's report.

## Changes

- `Controls/Certificate.lean`: `acc_false` rewrites with `decide_eq_false` instead of `simp` over the whole `acc`,
  which spent its time synthesising `Decidable` for `∀ e ∈ p.tr, …` (**1.44 s → 0.05 s**); `big_computes` by `decide`.
- `Controls/Relation.lean`: `acc_over_word` one `simp only [Submission.acc, decide_eq_false …, Bool.false_and]`
  (**0.75 s → < 0.02 s**); `deep_accepted_but_unwritable` by `omega` alone.
- `Controls/WitnessSending.lean`: `node_children_word` reuses `fits_of_acc`.
- `Library/WitnessSending.lean`: `computes`, one `unfold outCap at *`.
- `Controls/Extractor.lean`: `readBytes_len`, `readNat_len`, `readString_len`, `readDigest_len`, `shrinks_pure`,
  `readSigned_pi`, `decodeWit_children_size` (−15 lines, 0.29 s → 0.20 s), `child_in_domain`: injection patterns
  and term-mode length chains instead of `simp`/`omega` sequences.

## Numbers

Code lines of the nine files the stage touched: 1,591 → 1,566 (−25; `Controls/Extractor.lean` 221 → 200); contract
349, untouched; theorem count 218, unchanged. Elaboration (minimum of 3, `lake env lean`): `Controls/Certificate`
6.09 → 4.92 s, `Controls/Extractor` 8.42 → 7.46 s, others within noise. Cold build of the project, two clean copies
run alternately: 1 min 28.4 s / 1 min 34.3 s before, 1 min 28.0 s / 1 min 35.3 s after (no change: the critical
path is the older hash KATs in `Controls/Relation.lean`, about 20 s).

## Checks

`timeout 1800 lake build`: green, 1,266 jobs, 0 warnings (19.9 s incremental). Axiom audit: PASS. `loc.py` on the
contract: 349 ≤ 500. `check-hygiene.sh`: OK. Shared package tree: 0 files written.

## Not applied

`acc_deepSigned` could avoid two `;` at one line more. Older controls (`child_other_key`, `child_trace_nonempty`,
`acc_trace_over_qV`, `acc_query_over_cap`) still pay about 0.5–0.8 s each for `simp` over a general `acc`; the same
`decide_eq_false` pattern would fix them, left since they predate the stage.
