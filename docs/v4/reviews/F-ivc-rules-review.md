# Stage F-ivc: adversarial review of the V4-A11 draft and the v4 rules as a whole

Reviewer: a Fable subagent, 2026-10-28, applying the `adversarial-review` skill to rules, harness and
design. Read-only: the V4-A11 draft, the loss studies (`sim2.py`, tables S2-T0…T12 and L1-T0…T15), the committed
`v4/ks-standard` (design §2.7–§4.4, BRIEF, PROVER.md, FORMAT.md, `harness/rfh/*`, `evaluate.py`,
`run-benchmark.py`, `aggregate.py`, `season.toml`, the badge templates, `service/PROTOCOL.md` and `main.rs`, the
contract, the workflows), the reviews C, RA, RB, RF, D-trim and E-ks, and the flock-challenge `seed_pipe` bypass (gist
Th0rgal/f34a9a9d) as the model attack. One probe ran (a `rename` onto a directory); no build, no harness.
Recorded by the orchestrator from the reviewer's report; the disposition of each finding is in the draft's §11 and in
BRIEF V4-A11.

## Majors

**M-1. Run and hardware shopping is free; three harness paths turn a run the entry dislikes into an organiser
ERROR.** The prover reads `cpuid` after `ready` (allowed) and, on a CPU model or a start it dislikes, aborts at no
cost: (1) `mkdir /work/chain.json` before `go` makes the runner's input rename (`harness/rfh/prover.py:236`) raise
`IsADirectoryError` (**verified** by probe, errno 21); nothing catches `OSError`, so `run-benchmark.py:126` reports a
harness error and `aggregate.py:95-96` an ERROR, which the design counts as the organiser's. Variants: `chmod 000
/work` makes `read_output`'s `os.open(base, O_DIRECTORY)` (`files.py:18`) raise `PermissionError`; (2) `/work` and
`/setup` are host directories without a quota, so filling the disk makes the runner's own writes fail; (3) a
self-REJECT costs nothing. Gain (estimate, S2-T10): 20 unpaired tries show a false ≥ 3 % gain with probability 0.39,
100 tries 0.90; a model-specific 4 % advantage becomes certain with zero-cost filtering. The draft's defence (two paired
jobs on different models) is unimplemented, so the provisional board is what agents optimise. Fix: `OSError` inside a
request → the entry's REJECT; `/work` on a tmpfs within the cgroup and a `/setup` cap; rule "a run that fails while an
entry process is alive is the entry's failure"; provisional ranking by the median of the last three evaluations with
failures counted as the worst score; implement the two-model paired record before season 1.

**M-2. Re-timing scores the re-run's time against the first run's verifier cost; a detectable re-run lets the entry
swap its slowest steps for a prove-fast, verify-slow variant.** A re-run is detectable (the service's signature
index is a lifetime counter; `CLOCK_REALTIME` is readable, so a stamp in π reads stale). The entry idles its longest
10 % of steps to about 1.5 × the fit (Theil–Sen is robust to 10 % outliers), and in the re-run, whose output is never a
child, witness-sends the leaf: `P` falls to the fold overhead while `V` rises unscored. Gain (estimate): the top decile
of lengths carries about 24 % of `Σ n_i (P_i/n_i)³`, so `P̄` falls about 8 %. The sim assumed honest re-runs
(`sim2.py:789-805`). Fix: `P_i`, `V_i` and `|π_i|` all from the kept run's output; order re-runs by ratio to the fit;
record both runs.

**M-3. The robustness claim hides a decision about compact accumulation.** S2-T5 (B3, K = 1.5): safe 0.68, safe
with compact accumulation allowed 0.97, H-Flock best honest 0.70; S2-T7: a folder with a 2–4 MiB running witness in π
scores 1.15 × H-Flock at base and 0.50 at favourable estimates; one knob (`s_ref`) decides. Fix: decide whether compact
accumulation is a wanted class and write it down (keep `s_ref` = 2 MiB), or exclude it (`s_ref` = 1 MiB: safe 0.85,
H-Flock 0.53); re-run S2-T5/T7 once a folding prototype is measured (D1).

**M-4. Removing `proofCap` leaves `Computes`' domain and the witness-sending child bound undefined.** `Computes`
(`Contract/Extractor.lean:177`) assumes `π.size ≤ proofCap`; without it, it quantifies over every proof, and
`outCap = 2^24` words holds exactly two 64 MiB children with no room for traces, so a `V` accepting children near the
file cap is uncertifiable. The witness-sending entry's child bound came from `acc`
(`Controls/WitnessSending.lean:127-130`, `Controls/Certificate.lean:157-223`, `Controls/Compose.lean:140`). Fix:
`Computes` over every proof; every certifiable `V` bounds its children so that a node witness fits `outCap`, with the
bound named in the design; the WS `V` gets an explicit child cap and its controls are restated.

## Minors

- m-1. The clock-stop path (`proc.kill`, `systemctl --user kill`, `wait`) adds tens of ms of organiser time to each
  `P_i`; stop at bwrap's exit after `SIGKILL`, run `kill_unit` after, record the latency.
- m-2. `T_triv,best` is measured once, right after the untimed 300 s `prover setup` (`run-benchmark.py:85, 103`), so
  heat or cache state can inflate `v_ref`; measure it as interleaved medians like `c_P`.
- m-3. Untimed start-up to `ready` is bounded only by `stream_s` slack (about 6 s per step, estimate) and `step_s`;
  nothing input-dependent is available before `go` (checked). State a `ready_s` cap.
- m-4. Re-timing: order by ratio to the fit; name one estimator; keep first times if `stream_s` is reached during
  re-runs; a re-run's `c_P` is the last sample.
- m-5. The paired job needs one service lifetime per entry.
- m-6. Cross-step side channels exist (the signature index, about 9 bits per step via dummy `SIGN`s;
  `CLOCK_REALTIME`); harmless once M-2 is fixed; list them.
- m-7. Leaf digests (Python BLAKE2s of about 2^24.6 compressions) stay before the first request.
- m-8. Best of 3 only when `x_i > 1` is an asymmetric estimator; use one statistic for every check.
- m-9. Implicit verifier preprocessing (Lean closed-term initialisation in the badge's untimed start); state its
  bounds.
- m-10. PROVER.md: `/proc/stat`, `/proc/cpuinfo`, `/proc/meminfo` are global.
- m-11. `K` and `v0` enter only as `K·v0`.
- m-12. With `proofCap` gone, a 64 MiB `π_M` parses in about 200 ms (estimate) before `V`; the DoS per-input cap must
  cover parse plus `V`.

## Checked and found right

The trace is not a data channel (queries are `V`'s outputs; `runSeq` demands equality). Inputs are staged invisibly
and renamed after the clock starts. Checks and calibration never overlap an entry process. Step counting and the
truncation of M gain about 0.03 % (S2-T8). Deferring chain work pays it later (0.1–0.3 %). Sandbox state channels
(`/tmp`, `/dev/shm`, IPC, network, cgroup, keyring, read-only `/setup` and `/run/rf`) do not persist, and the service
memoises nothing. A pure `V` cannot escape its pinned core, read a clock or do I/O. The trust anchor, fetch by SHA,
one-build binding and attestation are as reviewed in RB, RF and D-trim.

## Simplifications proposed

(1) one constant `K·v0`, with `v0 := v_ref`; (2) drop stratification (S2-T9: calibrated CV 0.022 → 0.0196; paired CV
0.0068 → 0.0157, worse); (3) one calibration mechanism; (4) one `V` statistic; (5) "two consecutive paired jobs,
models recorded" if the two-model rule makes retries unbounded; (6) a `ready` cap.

## Verdict

Not ready for implementation as written; the measurement core is sound and closes the flock-challenge class of attack
(no way found to move timed work off the clock or to carry proving state between steps). With M-1(a), M-2 and M-4
fixed and M-3 decided, the amendment can proceed; M-1(b)/(c) are season-1 conditions.
