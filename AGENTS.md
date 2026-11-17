# recursion.fast: the rules

This file is the rulebook for submitters, human or agent. It states what an entry is, what its
Lean certificate must prove, how it is run and scored, and what makes a record. **Status:
experimental release.** The rules may change; a change moves the core commit that the submissions
repository pins, in its own commit.

**What is binding, in order.** (1) The Lean contract, `RecursionFast/Contract/*.lean`; (2) the
season file [`harness/season.toml`](harness/season.toml) and the normative interfaces
[`harness/PROVER.md`](harness/PROVER.md), [`harness/FORMAT.md`](harness/FORMAT.md) and
[`service/PROTOCOL.md`](service/PROTOCOL.md); (3) this file. Where two disagree, the higher one is
what is checked, and the disagreement is a bug to report.

## 1. What is contested

The fastest **recursive prover for Keccak-256 hash chains** whose soundness is proved in Lean. An
entry is a hash-based non-interactive argument for one relation over 32-byte digests: a leaf digest
commits to a Keccak-256 chain from a secret start, a node digest to two accepted children. The
benchmark is a stream of 8 steps; each step aggregates four fresh chains of `2^20` steps (two levels
of 2→1 merges) and folds them into the running proof. One score ranks it, the prover's wall time
with a factor for the final proof's size (§7), in two tracks with their own records: `every`, where
every proof of the stream must be accepted, and `final`, where only the last one must. The
verifier is capped, not scored. Soundness is not measured: it is a kernel-checked theorem,
knowledge soundness in the random-oracle model, and the oracle is deployed as a secret-keyed
service that signs the answers each proof used (the signed random oracle, §5). The service is not
on the clock: the stream runs once against it, and the timed passes, which get the oracle's key,
must reproduce that run's outputs byte for byte (§6).

## 2. What an entry is

One directory (a *root*) in the submissions repository:

| Path | What | Read by |
|---|---|---|
| `claim.json` | the declared numbers (below) | the challenge renderer |
| `lean/*.lean` | the Lean side: `V`, `P`, `E`, `ext` and the certificate; one module per file, `lean/Solution.lean` required; subdirectories are ignored (a module there cannot be imported) | source rule, `lake build`, comparator, gate, badge |
| `prover/*.s` | the x86-64 prover as GNU assembly ([`harness/PROVER.md`](harness/PROVER.md)) | the prover build |

Everything else in the root (README, NOTES, sources the assembly was generated from) is ignored by
the evaluation and read by people. The root must hold only regular files and directories (no
symbolic links).

The root is size-capped (§9, `[entry]` of the season file), checked before anything else runs.

**`claim.json`** has exactly these keys (strict JSON: no floats, no duplicates;
[`harness/render-challenge.py`](harness/render-challenge.py)). The first recursive entry's:

```json
{"error": "15/5444517870735015415413993718908291383296", "completeness_error": "0",
 "qV": 36000, "fuel_base": 211106232532992, "fuel_per_word": 8192}
```

`error` and `completeness_error` are strings `"a"` or `"a/b"` (non-negative rationals); `qV`,
`fuel_base`, `fuel_per_word` are integers below `2^64`. They are rendered into the challenge
[`harness/challenge/Challenge.lean.in`](harness/challenge/Challenge.lean.in) as `declared : Declared`
(`ε`, `δ`, `qV`, `fuel t = fuel_base + fuel_per_word · t`).

**`lean/Solution.lean`** is the rendered challenge with its two `sorry`s filled: it defines
`RecursionFast.Challenge.submission : Submission` and proves
`RecursionFast.Challenge.certified : CertificateR declared submission`, with `declared` copied
verbatim. The comparator checks that the theorem proved is exactly the rendered one and that
`submission` is the only changed definition; a mismatch, like any proof the kernel rejects, makes
the result PROVISIONAL (§8), not REJECT. A minimal example, certified at errors 0 and not
competitive: the Lean half is [`tests/harness/ws-entry/`](tests/harness/ws-entry/), and the prover
half is [`harness/toy-prover/honest/prover.s`](harness/toy-prover/honest/prover.s), placed as
`prover/prover.s`. It passes the certificate and runs through the benchmark at the smoke's shape
([`harness/smoke.toml`](harness/smoke.toml)). At the season's shape it is REJECTed: its `V`
re-checks every chain of the stream so far (about 1.1–1.2 µs per permutation of history on the
evaluation machine, so about 40 s for the final proof's `2^25` permutations), far above the
verifier cap of 128 ms (§6). It shows the format, not a design.

## 3. The relation and acceptance

*Intuition.* A statement is a digest. A leaf statement says "I know a start whose chain of `n`
steps ends here"; a node statement says "I know accepted proofs of these two children". A child is
judged by a *signed proof* `(π, tr, σ)`: the proof, the oracle answers its verifier reads (the
trace), and the service's signature on the trace. Checking a child therefore never evaluates the
secret-keyed oracle: it checks a signature and runs `V` on the trace.

- **Relation** `Rel acc` ([`Relation.lean#L128-L133`](RecursionFast/Contract/Relation.lean#L128-L133)):
  `c = leafStmt (chainEnd s n) n` with `n ≤ chainCap = 2^20`
  ([`#L54-L55`](RecursionFast/Contract/Relation.lean#L54-L55)), or
  `c = nodeStmt c₁ c₂` with `acc c₁ p₁` and `acc c₂ p₂`.
- **Byte layouts** (normative; the contract, the service and the runner hash the same bytes):
  `chainStep d = Keccak-256(0x43 ‖ d)`, `leafStmt h n = Keccak-256(0x4C ‖ h ‖ enc64 n)`,
  `nodeStmt c₁ c₂ = Keccak-256(0x4E ‖ c₁ ‖ c₂)`, `enc64` = 8 bytes little-endian; Keccak-256 is
  Ethereum's: FIPS 202's sponge over `Keccak-f[1600]`, rate 136 bytes, padding `0x01 … 0x80` (not
  SHA3-256's `0x06`), 32-byte output ([`Hash/Keccak.lean`](RecursionFast/Contract/Hash/Keccak.lean));
  a chain step is 33 bytes, one permutation
  ([`Relation.lean#L61-L95`](RecursionFast/Contract/Relation.lean#L61-L95)); the trace digest and
  the signature ([`Signature.lean#L18-L33`](RecursionFast/Contract/Signature.lean#L18-L33)).
- **Acceptance** `Submission.acc S vk c p`
  ([`Certificate.lean#L96-L104`](RecursionFast/Contract/Certificate.lean#L96-L104)), in this order:
  `|π| < 2^64`; `|tr| ≤ qV`; every query in `tr` at most `queryCap = 2^20` bytes
  ([`Relation.lean#L51-L52`](RecursionFast/Contract/Relation.lean#L51-L52));
  `SigOk vk (traceDigest tr) σ` ([`Signature.lean#L98-L103`](RecursionFast/Contract/Signature.lean#L98-L103));
  and `(V vk c π).runSeq tr = some true`: `V`'s `i`-th query is answered by the `i`-th entry of
  `tr`, which must be for that query, and the trace is used up exactly
  ([`Oracle.lean#L49-L56`](RecursionFast/Contract/Oracle.lean#L49-L56)).
- `acc` is the node clause of the relation, the harness's check of every proof, and anyone's check
  later with the published `vk`. There is no proof-size cap in `acc`: the runner caps `|π|` and the
  verifier's time (§6), and the score prices the final proof's size (§7).

## 4. The certificate

*Intuition.* The entry proves, once and for all, that its verifier is knowledge-sound (from any
prover that convinces it, an efficient extractor recovers a witness) and that its honest prover
convinces it, both in the random-oracle model and **for every public key `vk`**. Every key means
the theorem's adversary may hold the signing key, so a verifier that trusts a signature cannot be
certified; only `acc` trusts signatures.

`Certificate S` ([`Certificate.lean#L106-L118`](RecursionFast/Contract/Certificate.lean#L106-L118))
has four fields, and `CertificateR declared S`
([`#L131-L136`](RecursionFast/Contract/Certificate.lean#L131-L136)) adds that the submission's
`ε`, `δ`, `qV`, `fuel` are within the declared ones and the declared fuel within the budget.

- **`secure : ∀ vk, KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV`**
  ([`Security.lean#L144-L156`](RecursionFast/Contract/Security.lean#L144-L156)). `V` asks at most
  `qV` queries on every input and every oracle function; and for every adversary, a query program
  asking at most `Q` queries on every oracle function and outputting `(c, π)`, with
  `Q + qV ≤ logCap`, run and then followed by `V` against one lazily sampled random oracle
  (`prob`, [`#L133-L142`](RecursionFast/Contract/Security.lean#L133-L142)), the probability that
  `V` accepts on the final query log while `E c π log` returns no witness of the relation is at most
  `(Q + qV) · ε`. The extractor reads the final log, the verifier's answers included (how this
  relates to the textbook notion: §12). The adversary is computationally unbounded, bounded only in
  queries.
- **`complete : ∀ vk, CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) S.δ`**
  ([`Security.lean#L158-L162`](RecursionFast/Contract/Security.lean#L158-L162)): on every statement
  and witness of the relation, `P`'s proof, produced and then verified against one random oracle,
  is rejected with probability at most `δ`. Grinding is admitted. It is required for **every**
  witness, node witnesses with any accepted children included.
- **`computes : Computes S.ext S.E S.fuel`**
  ([`Extractor.lean#L183-L191`](RecursionFast/Contract/Extractor.lean#L183-L191)): the program
  `ext` of the contract's step-counting machine
  ([`Machine.lean#L97-L133`](RecursionFast/Contract/Machine.lean#L97-L133)), on the input tape
  `extractorInput c π L` ([`Extractor.lean#L108-L111`](RecursionFast/Contract/Extractor.lean#L108-L111)),
  halts within `fuel t` steps (`t` the tape's length in words) with at most `outCap` words that
  denote `E c π L` through `decodeWit` ([`#L168-L170`](RecursionFast/Contract/Extractor.lean#L168-L170)).
  This holds for every statement, proof of at most `8 · outCap` bytes (128 MiB) and log whose
  queries are below `2^64` bytes and whose tape is at most `2^64` words. The tape and output formats
  are normative ([`#L13-L33`](RecursionFast/Contract/Extractor.lean#L13-L33)). `E` takes no `vk`.
- **`cap`**: the numbers below.

| Cap | Value | Lean |
|---|---|---|
| `ε ≤ errorCap` (knowledge error per query) | `2^-128` | [`Security.lean#L126-L127`](RecursionFast/Contract/Security.lean#L126-L127) |
| `δ ≤ completenessCap` | `2^-40` | [`Security.lean#L164-L165`](RecursionFast/Contract/Security.lean#L164-L165) |
| `qV ≤` | `2^16` | [`Certificate.lean#L117`](RecursionFast/Contract/Certificate.lean#L117) |
| `fuel t ≤ extractorBudget t` | `2^48 + 2^16 · t` | [`Extractor.lean#L174-L175`](RecursionFast/Contract/Extractor.lean#L174-L175) |
| `ext.body.size ≤ progCap` (statements) | `2^20` | [`Extractor.lean#L180-L181`](RecursionFast/Contract/Extractor.lean#L180-L181) |
| `logCap` (queries for which `KS` is claimed) | `2^96` | [`Security.lean#L129-L131`](RecursionFast/Contract/Security.lean#L129-L131) |
| `outCap` (extractor output words) | `2^24` | [`Extractor.lean#L177-L178`](RecursionFast/Contract/Extractor.lean#L177-L178) |
| `queryCap`, `chainCap` | `2^20` bytes, `2^20` steps | [`Relation.lean#L51-L55`](RecursionFast/Contract/Relation.lean#L51-L55) |

**How to prove it.** Any correct argument is accepted. The organiser library (untrusted,
kernel-checked) offers routes and parts: a potential on logs, `KState`, with its bridge
`KState.ks` to `KS` ([`Library/PaperTheorem.lean`](RecursionFast/Library/PaperTheorem.lean));
`KSTextbook.ks` (textbook soundness implies `KS` at twice the error,
[`Library/KS.lean`](RecursionFast/Library/KS.lean)); the witness-sending entry
([`Library/WitnessSending.lean`](RecursionFast/Library/WitnessSending.lean)); and word-level twins
of Keccak-256 and `SigOk` proved equal to the contract's
([`Library/Fast.lean`](RecursionFast/Library/Fast.lean),
[`Library/KeccakFast.lean`](RecursionFast/Library/KeccakFast.lean)).

**A node witness must fit `outCap`.** A child's signed file of `f` bytes with `m` trace entries
takes at most `(f + 7(m + 1))/8` words of output; with the previous step's output within the 64 MiB
file cap, the leaf child may take up to about 64 MiB, but two children both near the file cap do
not fit ([`Extractor.lean#L57-L67`](RecursionFast/Contract/Extractor.lean#L57-L67)). A certifiable
`V` bounds the children it accepts.

## 5. The deployment: the signed random oracle

*Intuition.* The theorem is for a random oracle. In the run, the oracle is Keccak-256 of a secret
32-byte key, drawn after the entry is frozen, followed by the query, so no verifier can recognise it, and the service that holds
the key signs the trace of answers each proof used, so a node can check its children without the
key.

- **The service** ([`service/PROTOCOL.md`](service/PROTOCOL.md), normative for provers): one
  process per stream, reached through the Unix socket in `RF_ORACLE`. It draws a fresh PRF key `k`
  and an independent signing seed (WOTS, `w = 4`, 133 chains, under a Merkle tree of `2^16`
  one-time keys whose root is `vk`). `QUERY` returns `PRF_k(q)` for a batch; `SIGN` recomputes the
  answers of a batch, forms the trace and signs its digest with the next unused key; `VK` returns
  `vk` (also in `vk.hex`). The signing seed never leaves the service and is destroyed at exit; a
  crash aborts the run. After the service run (§6) the runner switches the service to **replay
  mode**: it hands the runner `k` (never the seed), and from then on a `SIGN` succeeds only if its
  trace digest is the one signed at the same index in the service run, and then returns that same
  signature (otherwise status 4, `MISMATCH`). Replay mode never signs anything new.
- **The prover may:** use any algorithm; precompute in an untimed `setup` (no instance, no service);
  use every CPU and up to 32 connections; batch up to `2^18` queries per `QUERY`; make any number of
  `SIGN`s within `2^16` per stream; dispatch on `cpuid`.
- **The prover must:** in the service run, obtain every oracle answer from the service (the key is
  secret; Merkle and Fiat–Shamir hashes included); in the timed passes, where `/work/oracle.key`
  holds `k`, compute `PRF_k(q) = Keccak-256(k ‖ q)` itself or keep asking the service; be
  **deterministic**: its outputs a function of its inputs, its setup and the oracle's answers, so
  that the timed passes reproduce the service run byte for byte (grinding included: search in a
  fixed order); make one `SIGN` per signed proof with exactly `V`'s query sequence;
  keep every query at most `2^20` bytes, a `SIGN` at most `2^16` items, a request body at most
  16 MiB; carry all state between steps inside `π` (each step is a fresh process; `/setup` is
  read-only after setup).
- **The prover cannot:** reach the network, another process, the key during the service run, the
  signing seed ever, or any file outside its
  sandbox ([`harness/PROVER.md`](harness/PROVER.md) §2); work after reporting `done` (the clock
  stops only when its whole process tree is dead); choose its statement (the runner computes every
  statement and checks each output against its own).
- The native prover is never proved. Only its signed proofs are checked, by `acc`. It need not
  agree with the Lean `P`.

## 6. The benchmark

*Intuition.* One stream of 8 steps. Each step receives four fresh chains of `2^20` steps (a
`2^22`-permutation step) and outputs a proof that aggregates them and extends the running proof. The
stream runs first against the oracle service, which fixes and checks every output. Then the oracle's
key is handed to the prover and the stream is run twice more on the clock; each of those outputs
must be the service run's, byte for byte. So the timed passes measure the prover without the
service, and every accepted proof comes from a run in which the prover never had the key.

- **Statements.** Step `i` gets chains `s_i1 … s_i4` of `n = 2^20` steps each, with leaves
  `L_ij = leafStmt (chainEnd s_ij n) n`, and
  ```
  X_i = nodeStmt (nodeStmt L_i1 L_i2) (nodeStmt L_i3 L_i4)
  c_1 = X_1,      c_i = nodeStmt c_(i-1) X_i      (i = 2 … M, M = 8)
  ```
  so a step needs signed proofs of its four leaves and of the two inner nodes and `X_i` as
  witnesses. Step 1, `prover first`: chains `chain0.json … chain3.json`, output a signed proof of
  `c_1`. Step `i ≥ 2`, `prover step`: also `prev.stmt` and `prev.bin` (the previous statement and
  the service run's output for it), output for `c_i`. `n_i = 4 · 2^20 = 2^22` permutations in every
  step, `2^25` in the stream. The interface and the files are in
  [`harness/PROVER.md`](harness/PROVER.md) §3 and [`harness/FORMAT.md`](harness/FORMAT.md).
- **Starts and keys.** The `4 · M` chain starts (32 bytes each) and the service's keys are fresh
  secret draws per evaluation from the OS CSPRNG; a step learns its chains' starts only when its
  inputs arrive. After the run the result publishes the starts, the leaf digests, the statements
  and `vk`. The signing seed is never written or published.
- **1. The service run.** Steps 1 … M, a fresh process each, against the service, with no key in
  the sandbox. Its times are recorded, not scored. Then, with no entry process alive, the runner
  checks outputs with the compiled `acc` against its own statements: the final output (step `M`)
  always, every intermediate output for the track `every`. **Caps:** every output's size is at
  most `pi_cap` = 1 MiB (`|π|` if it parses as a signed proof that `acc` accepts, else its file size); the final `|π|`
  is at most `final_pi_cap` = 512 KiB; a checked output's `V` (one check, parse included, pinned to
  one core, after an untimed warm-up of its batch) is at most `v_cap` = 128 ms; a check above it is
  timed twice more and the least of the three counts.
- **Statement canaries.** The final output must be rejected against its statement with one bit
  flipped and against its first child's statement; for the track `every`, the outputs of steps 1
  and 2 also.
- **The tracks.** An entry is REJECTed if the final output is rejected, breaks a cap or a final
  canary is accepted, or any output breaks `pi_cap`. It is scored in the track `final` if not. It is
  also scored in `every` if every intermediate output is accepted, within both caps, and its
  canaries are rejected; otherwise the result says why (`tracks_reason`), and that is not a failure.
- **2. The timed passes.** The runner switches the service to replay mode (§5) and runs the
  stream `timed_runs` = 2 more times. Each step is a fresh process with the same chains, the runner's
  statement, the service run's previous output as `prev.bin`, and the file `oracle.key` (`k` as 64
  hex characters), all renamed into `/work` when the clock starts. Every output must be
  byte-identical to the service run's output of that step; a difference is the entry's REJECT, with
  the step, the pass and the first differing byte. Nothing of the service run's requests survives
  into the timed passes (each request's directory is removed; `/setup` is read-only, and before
  every request the runner reads every file of the setup and the prover binary, so their page-cache
  state carries nothing). Every `SIGN` of a timed pass must be the service run's at the same index:
  any `MISMATCH`, or a pass that re-issues fewer or more signatures than the service run made, is
  the entry's REJECT, so a refused `SIGN` cannot be used as a probe.
- **What is timed.** `P_i`: from just before the inputs are renamed into `/work` (a constant-time
  rename) to the death of the last process of the sandbox, the least of step `i`'s two timed
  passes. Start-up to the `ready` line is untimed (capped by `ready_s`).
- **Calibration.** Before the service run, between the runs, and after the timed passes (if 30 s
  of `stream_s` remain), always
  with no entry process alive: three runs of the organiser's prover-shaped workload `calib`
  ([`harness/tools/calib.c`](harness/tools/calib.c), portable C: interleaved Keccak-256 chains and a
  memory sweep on every CPU) and the organiser's chain checker on `2^24` permutations.
  `c_P = median(calib) / ref_ns` is a health check of the machine, not part of the score: once
  `ref_ns` is measured, `|c_P − 1| > c_P_drift` makes the run an organiser ERROR (recorded with its
  reason). `T_triv`, the chain checker's median, is published for scale and not scored.
- **The machine.** Every job of an evaluation runs on the organiser's server, an AMD Ryzen 7 PRO
  8700GE (Zen 4, 8 cores / 16 threads), in a throwaway VM per job, one evaluation at a time. The
  benchmark VM has 4 cores / 8 threads pinned at a fixed 3.65 GHz and 16 GB, with the host CPU
  passed through; the prover's memory cgroup is 8 GiB and the service's 2 GiB. Its instruction set is
  x86-64-v4 (AVX2, FMA, BMI1/2 and AVX-512 F, CD, BW, DQ, VL), plus ADX, AES-NI, SHA-NI, VAES, VPCLMULQDQ, GFNI and AVX-512 IFMA, VBMI, VBMI2, VNNI, BITALG, VPOPCNTDQ and BF16. The machine may change between
  seasons: detect features at run time (`cpuid`) and keep a portable fallback. The result records
  a hash of the machine's fingerprint (CPU model, VM shape, frequency policy, image id) and,
  unhashed, the host kernel version. A benchmark whose fingerprint is missing, unreadable or not
  the season's is an organiser ERROR, re-queued (§8); a machine change between seasons re-baselines
  it (§12).
- **Throughput.** One evaluation at a time. With the core commit's caches in place, one evaluation
  holds the benchmark slot for at most about 2 hours (the certificate job, at most 50 minutes, and
  the benchmark job, at most 70, §9, plus a few minutes of the setup jobs' cache lookups; 130
  minutes with a second kernel); when the caches must first be built, as after a pin move, up to
  about three and a half hours. A full queue with warm caches completes about a dozen evaluations
  a day when every evaluation runs to its limits, more when they end sooner; there is no cap per
  author (§15).

## 7. The score

One score, the same in both tracks, in seconds; lower is better.

```
S   = P̄ · 2^( |π_M| / 1 MiB )
P̄   = n_ref · ( Σ_i n_i · (P_i / n_i)^3 / Σ_i n_i )^(1/3)      = (mean_i P_i^3)^(1/3) / 16
```

`P_i` the step's time (§6, the least of its two timed passes), `n_i = 2^22` its permutations,
`n_ref = 2^18`, so `P̄` is a cubic mean of the step time per `2^18` permutations; `|π_M|` the bytes
of the final output's `π` alone (not the trace or signature).

- **The cubic mean prices uneven work.** Moving work from one step into another costs more than it
  saves: an entry that defers all eight steps' work to the last one quadruples `P̄`. This matters in
  `final`, where intermediate outputs need not be proofs.
- **The size factor** is ×1.19 at 256 KiB and ×1.41 at the 512 KiB cap: halving the final proof
  from 512 to 256 KiB is worth about 16 % of prover time.
- **The verifier is not scored.** It is capped at 128 ms per checked proof (§6).

`score` in [`harness/rfh/bench.py`](harness/rfh/bench.py) computes it and
[`harness/aggregate.py`](harness/aggregate.py) recomputes it; the result's `score` holds `S`, `P_bar`,
`size_factor`, `final_pi_bytes` and `tracks = {"final": "S", "every": "S"}` (without `every` when
the entry is scored in `final` only). Every result also publishes the per-step records
(`stream.jsonl`: the service run's time, both timed times, `|π_i|`, `V_i` where checked).

| Symbol | Value | Meaning |
|---|---|---|
| `M` | 8 | stream steps, the same for every entry |
| `n_i` | `2^22` | permutations per step: four chains of `n = 2^20` |
| `n_ref` | `2^18` | `P̄` is per this many permutations |
| size scale | 1 MiB | the final proof's size doubles `S` per MiB |
| `ref_ns` | 316.2 ms, measured | `calib`'s time (32 rounds, 8 threads) on the machine, fixed per season; `c_P` against it is a health check (§6), never a factor |

## 8. Verdicts and records

| Verdict | Meaning |
|---|---|
| ACCEPT | certificate checked (`certificate: ok`) and every benchmark check passed |
| PROVISIONAL | the Lean build succeeds and the only failures are of the certificate: the kernel rejects it (including a theorem that is not the rendered one), its closure uses `sorryAx`, or the kernel exceeds its time or memory cap; benchmarked and published, never a record |
| REJECT | the entry failed a rule or a cap; the result names the reason |
| ERROR | the organiser's side failed (toolchain, missing or mismatched benchmark part, a machine fingerprint missing, unreadable or not the season's, a stream whose shape is not the season's, a `c_P` drift, a setup job or organiser cache); requeued once. The fingerprint is checked first, in the setup job, and the stream's shape against the season's at aggregation; a fingerprint or shape failure uses up no attempt (a retry at the same pin cannot clear it). A failure of the service run, a byte mismatch of a timed pass, or a service refusal during the entry's requests is the entry's REJECT, never ERROR. Repeated organiser errors, of any kind, pause the queue until the owner acts (the submissions repository's `AGENTS.md` §9: two, where one author's errors of a kind an entry might provoke count once). Named organiser errors (`organiser_error`) never count against the author |

A result is **comparable** iff it is ACCEPT and the job plan matched (an ACCEPT is always on the
season's machine and with the season's shape: anything else is ERROR). A stream that reaches
`stream_s` is the entry's REJECT: the score needs the final proof and both timed passes.

**The record rule.** Each track, `every` and `final`, has its own records. A result is a new
record in a track iff all of:

1. its verdict is ACCEPT and `comparable: true`;
2. its attestation verifies ([`harness/verify-record.sh`](harness/verify-record.sh); its
   `--provenance-only` mode checks this for any verdict): signed by
   `scaraven/recursion.fast/.github/workflows/evaluate.yml` in `scaraven/recursion.fast-submissions`
   on a self-hosted runner, that is a runner registered to the submissions repository, which only
   the owner's server can register; and the signer's commit equals the result's `harness_commit`.
   The runner name (`rf-…`) and label (`rf-bench`; the server's runners carry exactly one label,
   `rf-bench` or `rf-light`) the result records are checked for consistency, but they
   are what the server wrote and prove nothing by themselves;
3. `harness_commit` equals the core commit the submissions repository pins;
4. no record of that track stands at the pin, or `S_t < (1 − margin) · S_t,record`, with `S_t` the
   track's score (`S` in both), `S_t,record` the standing record's own score in that track at the
   pin and `margin = 0.02`;
5. its prover binary's SHA-256 is not that of an earlier record of either track (a resubmitted copy
   is `accepted`, never a record).

Items 1–3 and 5 are the same for both tracks; one result can set both records, and one entry may
hold both.

- **Records are per pin and per track**: a track's standing record is its newest, not retired,
  record evaluated at the pinned core commit. With none, the first result meeting items 1–3 and 5
  is that track's record.
- **A pin move ports the records first.** When the pin moves while a record stands, the bot
  re-evaluates each standing record's retained commit at the new pin before any other entry (one
  run when one commit holds both); a record keeps its crown if that is a comparable, attested ACCEPT.
  If it fails, no record stands in that track. A port competes only in the tracks whose record it
  carries, and item 5 does not refuse a record's own port.
- **The margin (2 %) is the owner's choice**, and it does not keep noise out. The relative
  run-to-run spread of one entry's score on the evaluation machine was σ ≈ 1.75 % under the
  previous rules (ten runs at their smoke shape; mostly per-step process overhead). Each `P_i` is
  now the least of two timed passes, which narrows the spread, but it has not been measured at this
  shape; two runs of one entry differ by about √2·σ, so a near-copy of the record can beat it by
  noise. The margin is the same in both tracks. Byte copies
  of an evaluated root and a record's prover binary are refused (item 5 and the submissions
  repository's copy rule). The owner may change the margin between seasons, which changes this file.
- The owner may retire a record of one track (a near-copy that beat it by noise, say) with the bot's
  `retire`; then no record stands in that track.

The submissions repository's bot applies this rule to the attested results.

## 9. Limits

From [`harness/season.toml`](harness/season.toml) (the CI smoke uses
[`harness/smoke.toml`](harness/smoke.toml)). A breach is the entry's REJECT unless stated.

| Limit | Value |
|---|---|
| entry root: files; bytes; any one file | 2,048; 512 MiB; 128 MiB |
| `lean/`: files, bytes; `prover/`: files, bytes; `claim.json` | 1,024, 32 MiB; 256, 256 MiB; 64 KiB |
| rendering the challenge; the source rule | 30 s; 120 s |
| entry's `lake build` (challenge and `Solution`'s import closure) | 1,200 s |
| kernel replay (comparator, Lean kernel), memory | 600 s (a breach: PROVISIONAL), 14 GiB |
| gate; badge build | 120 s; 180 s |
| prover build; `prover setup` (untimed); setup directory | 120 s; 240 s; 4 GiB, `2^20` entries |
| start-up to `ready`; one request (`step_s`) | 10 s; 60 s |
| the service run, its checks and canaries, and both timed passes (`stream_s`) | 3,000 s wall (reached: REJECT) |
| an output's size (`pi_cap`); the final `|π|` (`final_pi_cap`); a checked proof's `V` (`v_cap`) | 1 MiB; 512 KiB; 128 ms (least of three checks above it) |
| a timed pass's output | byte-identical to the service run's |
| signed-proof file (`file_cap`); a request's `/work` after the step | 64 MiB; 4 GiB, 65,536 entries |
| memory: prover (incl. `/tmp`, `/work` tmpfs); service; badge | 8 GiB; 2 GiB; 4 GiB |
| service: query; request body; items per `QUERY` / `SIGN`; connections; signatures per stream | `2^20` B; 16 MiB; `2^18` / `2^16`; 32; `2^16` |
| jobs: certificate (with nanoda); benchmark; setup, setup-tools; plan, attest | 50 min (60); 70 min; 30 min; 10 min |
| the benchmark VM; evaluations at a time | 4 cores / 8 threads, 16 GB; 1 |

## 10. Hard rules for the Lean side

- **Axioms**: the certificate's closure uses only `propext`, `Classical.choice`, `Quot.sound`. No
  `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` (so no `native_decide`).
- **The source rule** ([`scripts/source-rule.py`](scripts/source-rule.py)) rejects, before
  anything is built, every elaboration-time code form: `#eval` and every `#`-command except
  `#check`, `#print`, `#reduce`, `#guard_msgs`; `run_cmd`, `run_meta`, `run_tac`, `by_elab`, …;
  `elab`, `macro`, `syntax`, `simproc`, `declare_…`; `initialize`, `register_…`; `unsafe`,
  `partial`, `unsafeCast` and relatives; the attributes `implemented_by`, `extern`, `csimp`,
  `cpass`, `computed_field`; compiler, elaborator and debug `set_option`s; `import Lean…`,
  `import Lake…`, `import Qq…`, `open Lean…`, `open Qq…`. It scans comments and strings too (reword
  them).
- **The gate** ([`harness/lean-tools/Gate.lean`](harness/lean-tools/Gate.lean)): no `unsafe`,
  `partial` or `opaque` constant of the entry in the certificate's closure; no attribute that
  substitutes compiled code or runs load-time code (`implemented_by`, `extern`, `export`, `init`,
  `csimp`, `cpass`, `computed_field`); `V`, `P` and `ext` of `submission` have compiled code; no
  entry definition refers to the compiler's or the environment's API; the module declaring
  `submission` reaches, transitively, only entry modules and the import allowlist; organiser modules
  match the olean manifest.
- **Imports**: an entry module imports only its own modules and the import closure of `Mathlib`,
  `RecursionFast.Contract`, `RecursionFast.Library`, `RecursionFast.Controls`,
  `CompPoly.Fields.Binary.BF64.Ext3` and `CompPoly.Fields.Binary.BF64.Bytes`
  ([`harness/org-setup.sh`](harness/org-setup.sh)). Module root names must be new (not `Mathlib`,
  `RecursionFast`, `Challenge`, a package's, …).
- **Only `Solution`'s import closure is built**; other files under `lean/` are still scanned by the
  source rule.

## 11. What is trusted

- **The contract**: 10 Lean files, 328 code lines at this commit (`scripts/loc.py`; CI enforces at
  most 500), Lean core and Mathlib only, no theorem.
- **One kernel**: Lean v4.34.1's, replayed by the comparator (`leanprover/comparator` at `d03acab`
  with lean4export `076e8e5`, pinned and built by
  [`harness/ci/build-kernels.sh`](harness/ci/build-kernels.sh)), with Lean core, Mathlib and the
  pinned packages as hashed in the olean manifest.
- **The record build cache**: a certificate job may seed its build from the record's attested build
  (bound by its manifest's hash): only entry modules whose source is byte-identical are reused,
  never the challenge, and the kernel still replays every proof. A candidate's build stays under
  `build_s`, so a slow build may fit only when the cache hits.
- **Keccak-256** (FIPS 202's `Keccak-f[1600]` sponge with Keccak's padding): collision resistance
  on the seven tagged domains, one-wayness of the chain step, and `Keccak-256(k ‖ ·)` with a secret
  32-byte key `k` as a PRF. The signature's unforgeability (EUF-CMA, each index used once)
  follows from these (on paper). The composition across the tree needs EUF-CMA and collision
  resistance only. A signed trace the log does not hold is reduced, for any tree shape, to an
  EUF-CMA forgery against the service's signed traces or an explicit collision
  ([`Library/Compose.lean`](RecursionFast/Library/Compose.lean), `Forgery.reduce`); the walk
  around it (`walkSigned`, `compose_prob_signed`) is kernel for balanced trees. Security against
  signature-only forgery, which the original signed-oracle construction (Chiesa–Tromer, ICS 2010)
  also assumes, is not used: the walk matches a signed proof to the log by its trace, the signed
  message, not by its signature.
- **The badge**: the code Lean's compiler emits for `acc`, built from the same build the kernel
  checked; and the harness tools (gate, source rule, manifest, renderer, sandbox).
- **The runner and the service**, tested, not proved (the service's replay mode included: it
  re-issues only signatures it already made at the same index) ([`tests/`](tests/), [`.github/workflows/ci.yml`](.github/workflows/ci.yml)).
- **The machine**: the trust anchor is the organiser's server, which runs every job of
  [`evaluate.yml`](.github/workflows/evaluate.yml) in a throwaway VM. GitHub attests the workflow
  and the commit (artifact attestations; a third party can verify only these), and the Actions
  cache carries the organiser's environment between jobs. The server's runner image refuses any
  job that is not one of the submissions repository's workflows on `main` (or this `evaluate.yml`
  called from them), so a fork's workflow never runs there; the bot's workflow lint is advisory.
  The runner's name and labels and the
  machine fingerprint are what the server reports.
- Not trusted: `RecursionFast/Library/`, `RecursionFast/Controls/`, every entry, every prover.

## 12. Known limitations

- **One kernel.** Records are not cross-checked by a second kernel (nanoda reached 17.6–20.9 GB
  without finishing on the first entries). A Lean kernel bug, or a proof exploiting one, would stand.
- **One machine.** Every record is measured on one machine, which an entry can overfit (its cache
  sizes, its ISA extensions), and it is published (§6). The machine may change between
  seasons; records are then re-evaluated at the new pin by the port (§8).
- **A near-copy of the record can win by noise.** The margin (2 %, §8) is below the spread of the
  difference of two runs of one entry (√2·σ ≈ 2.5 %, σ ≈ 1.75 % measured at the smoke shape with
  each `V_i` the best of two checks, so a lower bound for one check), so a
  near-copy that is no faster can still beat the record by more than 2 %. Byte copies and re-used
  record prover binaries are refused, and the owner retires a record won that way.
- **`c_P`'s drift is an organiser ERROR, not a score change**: `ref_ns` (316.2 ms) and
  `c_P_drift` (0.065: about four standard deviations of one `c_P` sample at the higher spread
  measured on the machine, 1.55 %, and far more of the median that is judged) are fixed
  per season, and neither moves `S`. The drift is judged on all the stream's samples, so a drifting
  machine costs a full benchmark job before its ERROR.
- **Retiring a record leaves no record standing in that track**: the record it beat is not
  restored, and that record's prover binary, like every record's, can never take a record of either
  track again.
- **The end of the stream is known** (`M = 8`). The verifier cap (128 ms) bounds what can be left
  to it: at the chain checker's speed about `2^17` permutations, under 0.4 % of the stream.
- **The timed passes trust isolation and determinism.** The timed passes are only a stopwatch:
  every accepted output comes from the service run, in which the prover never had `k`. A timed
  pass could reproduce an output without proving only through a channel from the service run's
  requests, and the per-request sandbox (fresh `/work` and `/tmp`, read-only `/setup`) is the same
  isolation that keeps state between steps inside `π`. Two channels around it are closed by the
  runner: the page cache of the setup and the prover binary (re-read in full before every
  request) and the replay service's answers (a refused `SIGN` is a REJECT). Lower-bandwidth
  micro-architectural state (CPU caches, predictors) is not cleared; the calibration runs between
  requests disturb it. The price is determinism: a prover whose output depends on thread timing or
  fresh randomness fails the byte comparison.
- **A trace is not size-capped beyond `file_cap`.** The caps count `|π|`; an accepted proof's trace
  (at most `qV ≤ 2^16` queries of at most `2^20` bytes, all asked by `V`, so within `v_cap`) is
  bounded only by the file cap. An output `acc` rejects is sized by its whole file.
- **`k` is revealed after the service run.** It then protects nothing: no signature can be made
  without the seed, which never leaves the service, and replay mode re-issues only the service
  run's own signatures. A timed pass may still leak `k` (in its timing or its output), harmlessly.
- **Not adopted this season** (from the review of these rules): a paired, interleaved confirmation
  run of a candidate record against the standing one; a proof-size cap inside `acc` (the caps are
  the runner's, so `acc` itself accepts larger proofs); per-signature digit vectors drawn per run;
  a public, unkeyed hash in place of the signed oracle, which is how leanVM deploys and would need a
  new contract.
- **The score's constants** (the power 3 of `P̄`, the size scale of 1 MiB, the caps) are the
  owner's choices for this season, set from the first recursive entries and leanVM's published
  proof sizes (209–294 KiB), not from entries measured at this shape.
- **Malformed and crafted inputs are not tested, and `acc` has no time bound.** The benchmark
  checks the entry's own outputs and the statement canaries only. Inputs assembled from published
  parts (for example a deep chain of nodes over public signed leaves) took an earlier entry's `acc`
  68–183 s before its authors bounded it; nothing in the rules bounds what such an input costs a
  third party who checks it.
- **The service is trusted runtime**: a bug that signs a wrong answer, reuses an index or exposes
  the key would be accept-all.
- **On paper, not in the kernel**: unforgeability of the signature (EUF-CMA) and the bounds on the
  probabilities of the walk's EUF-CMA and collision outcomes (the per-run reduction to them, given
  the service's signed traces, is kernel; the model has no signing oracle), the PRF step from the
  random oracle to the keyed deployment, and the composition across the stream's comb (the union bound
  over any finite set of paths is kernel; the walk is kernel for balanced trees only).
- **`KS` is textbook knowledge soundness only for adversaries that ask the verifier's queries
  themselves**: its extractor also reads the verifier's answers, so for an adversary that leaves
  fresh queries to the verifier it is weaker than the textbook notion (`Controls/Security.lean`,
  `lucky_ks`). Every prover of the service run asks the service for every answer it signs, so none
  is of that kind.
- **Efficient extraction** is claimed only for proofs up to 128 MiB and logs up to about `2^61`
  entries; beyond, `KS` holds with an unconstrained extractor.
- **The source rule raises the bar; it is not a proof** that no elaboration-time code runs.
- **Per-step service traffic is not published** (the service keeps lifetime totals only).

## 13. Consequences that bit real entries

From the first two certified entries (`spartan-srom`, `flock-recursive`) and the organiser's toy
prover. Their timings were measured on GitHub-hosted runners with a different chain hash, so they
are indicative only, except where a bullet says "on the machine".

- **The verifier cap is per proof and includes parsing.** The first recursive entry's verifier
  took about 500 ms per check; the optimised lvm2-style entries about 40 ms. A recursive `V` that
  re-checks history grows with the stream and breaks the 128 ms cap.
- **Your verifier's start-up is on the stream clock.** Each check batch and the canaries start a
  badge process; one entry's `V` took 11.7 s to initialise on a runner.
- **Determinism is a rule.** Seed every randomised choice from the inputs and the oracle's answers;
  search grinding nonces in a fixed order and take the first; never let the thread schedule pick
  between valid outputs. One-time signature indices follow the order in which `SIGN`s arrive, so
  issue your `SIGN`s in an order fixed by the inputs (not from racing threads). Run your prover
  twice locally and compare the bytes.
- **The certificate build is tight**: a 199-module entry used 968–984 s of the 1,200 s cap on a
  4-vCPU runner. Modules outside the organiser's precompiled closure (`RecursionFast`, the CompPoly
  roots, `Mathlib.Tactic`) are compiled inside the 180 s badge build, about 860 modules;
  `import Mathlib` does not fit.
- **Every step is four chains of `2^20`** within `step_s = 60 s`, in the service run too (where
  every answer is a round trip). Test the service run's time, not only the timed one.
- **`queryCap` is per query**: a transcript that absorbs a long message in one query (a Ligero row
  of 1.57 MB at `n = 2^18`) is refused by the service and the proof fails. Absorb in pieces.
- **A signed child restates every byte its verifier hashed**: a signed `n = 16` leaf was 538,698
  bytes for a `π` of 143,711. Sending children in the clear does not scale.
- **`errorCap = 2^-128` excludes plain GF(2^128) sumcheck** (a degree-2 round costs `2^-127`):
  draw challenges from a larger field (the recursive entry used GF(2^256) and claimed
  `15/2^132`), or repeat.
- **`acc` takes the submission**, so a recursive `V` cannot call it: restate it and prove the two
  equal; mirror every conjunct.
- **`ε` and `δ` must not block compilation**: the badge compiles `submission`; a `noncomputable`
  real literal fails the badge build. Write them as casts from `ℚ≥0`.
- **Compiled `ByteArray.data` copies the array**: a parser reading through it is quadratic (88 s on
  539 KB). Read in place (`b[i]`, `ByteArray.get!`) or use the library's twins.
- **The kernel is slow on evaluation** (Keccak-256: about 11 s per permutation for the contract's
  `keccakF`, about 0.4 s for the word-level twin of `Library/KeccakFast.lean`); large case splits
  or `decide` over concrete words can exhaust the kernel cap. Prove symbolically.
- **Assemble with binutils 2.42** (the evaluation VM's): GCC 15's `.base64` and newer directives do
  not assemble; [`harness/tools/asm-compat.py`](harness/tools/asm-compat.py) rewrites them. The
  machine (§6) has AVX-512 and GFNI but may change between seasons: dispatch on `cpuid` with a
  portable fallback; a `SIGILL` fails the run.
- **Memory**: the 8 GiB cap counts `/tmp` and `/work` (a Spartan+Ligero leaf prover peaked at
  15.1 GiB at `n = 2^16`, 2.47 GiB after restructuring; an lvm2-style GKR prover peaked at 8.2 GiB
  at `n = 2^20` under the old 11 GiB cap). Prove the four leaves one at a time if they do not fit
  together.
- **Fiat–Shamir must bind the statement**: the canaries flip a statement bit and substitute other
  statements.

## 14. Checking locally

Local runs are not attested and are not results. In your own clone (never on a shared package
tree):

```sh
lake exe cache get          # Mathlib from its cache
lake build                  # the contract, library and controls
```

The harness on an entry needs Linux x86-64, `bubblewrap` with unprivileged user namespaces (on
Ubuntu 24.04: `sysctl kernel.apparmor_restrict_unprivileged_userns=0`), a systemd user manager for
the memory caps (without one the sandbox falls back to `prlimit`), Rust (pinned by
`service/rust-toolchain.toml`) and the evaluation VM's GCC 13.3 and binutils 2.42:

```sh
harness/org-setup.sh "$PWD"                                     # organiser build, tools, allowlist, manifest, service
set -a; eval "$(harness/ci/build-kernels.sh "$HOME/rf-kernels")"; set +a   # comparator + lean4export
python3 -I harness/evaluate.py all --entry PATH/TO/ROOT --org "$PWD" \
  --work /tmp/rf-work --out result.json --season harness/smoke.toml   # --work must not exist
```

`evaluate.py cert` and `evaluate.py bench` run the two halves separately. `harness/smoke.toml` is a
small shape (4 steps of four chains of 32, with a verifier cap of 2 s so that the toy example of
§2 passes); `harness/season.toml` is the real one, and it runs only
on the evaluation machine: elsewhere its fingerprint check stops the benchmark as an organiser ERROR
before the prover is built, and its `c_P` drift check would too. To run the season's shape on your
own machine, generate a local copy and pass it to `--season`:

```sh
python3 -I harness/local-season.py > /tmp/season-local.toml   # fingerprint "any", ref_provisional true
python3 -I harness/evaluate.py all --entry PATH/TO/ROOT --org "$PWD" \
  --work /tmp/rf-work-season --out result-season.json --season /tmp/season-local.toml
```

Every shape and every other cap is then the season's; only those two lines and the season's name
differ (as in the smoke), and your machine's speed is not the evaluation machine's. The
witness-sending example of §2 is REJECTed at this shape by the verifier cap, as expected.

Set `RF_HARNESS_COMMIT` when the checkout is not a git checkout. `harness/ci/build-kernels.sh` holds the
kernels' pins; [`scripts/tools.env`](scripts/tools.env) sets the variables from `RF_KERNELS` instead.

## 15. Submitting

Open a pull request in
[`scaraven/recursion.fast-submissions`](https://github.com/scaraven/recursion.fast-submissions)
that changes files under exactly one `submissions/<root>/` (root name `[a-z][a-z0-9-]{0,39}`) and
nothing else; include a `NOTES.md` (idea, result, what failed and why, what to try next). Pull
requests are never merged: a bot evaluates each with the core's attested `evaluate.yml` at the pin,
publishes every verdict, and copies a new record's root to `main` (§8). The queue is round-robin by
author: the author whose last evaluation started earliest goes next, and a new push supersedes the
PR's queued entry and goes to the back. There is no cap per author: one author's entries run back to back
when nobody else is waiting. Re-submitting does not re-roll a record: an unchanged root is
refused, and a prover binary of an earlier record never takes it. That repository's `AGENTS.md`
gives the submission procedure.
