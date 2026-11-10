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
benchmark is incrementally verifiable computation: the prover extends one running proof by one
fresh chain per step, 96 steps, and two scores rank it, each with its own records: the sum of its
prover time per permutation and a charge on its verifier's time and proof size, and the product of
its prover time and a verifier factor (§7). Soundness is not measured: it is a kernel-checked
theorem, knowledge soundness in the random-oracle model, and the oracle is deployed as a
secret-keyed service that signs the answers each proof used (the signed random oracle, §5).

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
([`harness/smoke.toml`](harness/smoke.toml)). At the season's shape it is accepted and scored, and
far from competitive: its `V` re-checks every chain of the stream so far, so its check time grows
with the stream's history (about 10 s around step 31–32 on the evaluation machine, about
1.1–1.2 µs per permutation of history; at that rate about 38 s at step 96) and `V̄` dominates its
score.

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
  later with the published `vk`. There is no proof-size cap in `acc`: size is priced by the sum's
  `s_ref`; in the product only `file_cap` bounds it.

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
  `vk` (also in `vk.hex`). Keys are never written and are destroyed at exit; a crash aborts the run.
- **The prover may:** use any algorithm; precompute in an untimed `setup` (no instance, no service);
  use every CPU and up to 32 connections; batch up to `2^18` queries per `QUERY`; make any number of
  `SIGN`s within `2^16` per stream; dispatch on `cpuid`.
- **The prover must:** obtain every oracle answer from the service (the key is secret; Merkle and
  Fiat–Shamir hashes included); make one `SIGN` per output proof with exactly `V`'s query sequence;
  keep every query at most `2^20` bytes, a `SIGN` at most `2^16` items, a request body at most
  16 MiB; carry all state between steps inside `π` (each step is a fresh process; `/setup` is
  read-only after setup).
- **The prover cannot:** reach the network, another process, the key, or any file outside its
  sandbox ([`harness/PROVER.md`](harness/PROVER.md) §2); work after reporting `done` (the clock
  stops only when its whole process tree is dead); choose its statement (the runner computes every
  statement and checks each output against its own).
- The native prover is never proved. Only its signed proofs are checked, by `acc`. It need not
  agree with the Lean `P`.

## 6. The benchmark

A stream is `M = 96` steps, pure IVC, under one service lifetime, on the organiser's machine
(below). An evaluation runs one stream. Step 1, `prover first`: a signed proof of
`nodeStmt (leaf A) (leaf B)` for two fresh chains. Step `i ≥ 2`, `prover step`: given the previous
statement and signed proof as the runner received them and one fresh chain, a signed proof of
`nodeStmt prev (leaf C)`. The interface, the handshake and the files are in
[`harness/PROVER.md`](harness/PROVER.md) §3 and [`harness/FORMAT.md`](harness/FORMAT.md).

- **Chain lengths and starts.** The chain lengths are one fixed, published sequence, `[stream]
  lengths` in [`harness/season.toml`](harness/season.toml): `M + 1 = 97` values in `[2^17, 2^20]`
  (step 1's two chains, then one per step), the same for every evaluation and every entry. It was
  derived once, from public SHA-256 values through the inverse CDF of the density `∝ 1/n²` (equal
  expected work per octave); the file states the derivation. The chain starts (32 bytes each) are
  fresh secret draws per evaluation from the OS CSPRNG; a step learns its chain's start only when
  its inputs arrive. The service's keys are also fresh per evaluation. After
  the run the result publishes the starts, the leaf digests and statements over them, the
  lengths and the run's public key `vk`; the keys are never written or published. `M` is a
  published constant. The owner may change the sequence between seasons, so tuning a prover to
  these exact lengths is not a lasting gain.
- **What is timed.** `P_i`: from just before the inputs are renamed into `/work` (a constant-time
  rename) to the death of the last process of the sandbox. Start-up to the `ready` line is untimed (capped by `ready_s`).
- **Checks.** Every output is checked with the compiled `acc` against the runner's statement,
  between steps, in batches of 8, with no entry process alive; each batch starts with an untimed
  warm-up check of its first output, and `V_i` is the wall time of one check (parse included)
  pinned to one core, measured once. A rejected output fails the run. No check has a time cap of
  its own: a slow verifier is priced by `V̄` (§7) and bounded only by `stream_s`.
- **Statement canaries.** The outputs of steps 1, 2 and `M` must be rejected against their
  statement with one bit flipped and against their first child's statement; the outputs of steps 1
  and 2 also against the next step's leaf statement.
- **Re-timing.** After the stream, `P ≈ a·n + b` is fitted (trimmed least squares); each step above
  `1.3 ×` the fit, at most 10 % of the steps, is run once more on the same inputs; its output must
  be accepted, and the faster run's `P_i`, `V_i` and `|π_i|` are scored. If `stream_s` is reached
  during a re-run or its check, the first times stand and the stream is not truncated.
- **Calibration.** Before step 1, every 8 steps, and once at the end if the last sample is at least
  4 steps old and 30 s of `stream_s` remain; always with no entry process alive:
  three runs of the organiser's prover-shaped workload `calib`
  ([`harness/tools/calib.c`](harness/tools/calib.c), portable C: interleaved Keccak-256 chains and a
  memory sweep on every CPU) and the organiser's chain checker on `2^24` permutations.
  `c_P = median(calib) / ref_ns` is a health check of the machine, not part of the score: once
  `ref_ns` is measured, `|c_P − 1| > c_P_drift` makes the run an organiser ERROR (recorded with its
  reason). `T_triv` = the chain checker's median; `v_ref = T_triv / 10`, measured on the machine.
- **The machine.** Every job of an evaluation runs on the organiser's server, an AMD Ryzen 7 PRO
  8700GE (Zen 4, 8 cores / 16 threads), in a throwaway VM per job, one evaluation at a time. The
  benchmark VM has 4 cores / 8 threads pinned at a fixed 3.65 GHz and 16 GB, with the host CPU
  passed through. Its instruction set is
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

## 7. The scores

Two tracks are scored from the one stream, each with its own records (§8); both are in seconds per
`2^18`-permutation step, and lower is better.

```
S   = P̄ + V̄                                       the sum
S×  = P̄ · g                                       the product
P̄   = n_ref · ( Σ_i n_i · (P_i / n_i)^3 / Σ_i n_i )^(1/3)
V̄   = κ · (1/M) · Σ_i x_i,           x_i = V_i / v_ref + |π_i| / s_ref
g   = 1 + ( V̄ₘ / v_ref )^2,          V̄ₘ = (1/M) · Σ_i V_i   (seconds)
```

`P̄` is a work-weighted cubic mean of the prover's time per permutation, so work moved into a few
steps costs more than it saves; it is the same number in both tracks.

- **The sum** charges verifier time and proof size linearly, at one exchange rate for every entry:
  one millisecond of check time on every step costs about `K = 5` ms of `S` (exactly when the run's
  `v_ref` equals `v0`; `K · v0 / v_ref` in general), as much as about 5 ms of `P̄`, which is about
  6.2–6.4 ms of prover time on every step (at the season's lengths one millisecond of `P_i` on every
  step moves `P̄` by about 0.8 ms); one MiB of mean proof size costs `κ / 2 ≈ 1.65 s`. `K` is set so
  that at an estimated recursive entry on the machine (`P̄ ≈ 5.2 s`, `V_i ≈ 300 ms`,
  `|π_i| ≈ 300 KB`) the shares of `S` are about 70 % prover and 30 % verifier and proof size
  (73/27 there). Away from that point the shares move with the entry; the exchange rate does not.
- **The product** multiplies the prover's time by a verifier factor: `g = 1` for a free verifier,
  1.05 at `V̄ₘ = 150 ms`, 1.21 at 300 ms, 2 at `v_ref`, quadratic beyond. Its elasticity in `P̄` is
  1 everywhere, so a 10 % faster prover is worth 10 % whatever the verifier; its elasticity in the
  mean check time is `2u² / (1 + u²)` with `u = V̄ₘ / v_ref` (0.34 at 300 ms, 1 at `v_ref`, at most 2).
  Proof size is not scored in the product; `file_cap` bounds it.

Both are computed by `score` in [`harness/rfh/bench.py`](harness/rfh/bench.py) and recomputed by
[`harness/aggregate.py`](harness/aggregate.py); the result's `score` holds `S` (the sum), `S_product`
(the product) and `tracks = {"sum": "S", "product": "S_product"}`. Constants, from
[`harness/season.toml`](harness/season.toml):

| Symbol | Value | Meaning |
|---|---|---|
| `M` | 96 | stream steps, the same for every entry |
| `n_i` | fixed | permutations (chain steps) newly given in step `i` (step 1: `nA + nB`), from the season's `[stream] lengths` (§6) |
| `n_ref` | `2^18` | `P̄` is per this many permutations |
| `ref_ns` | 316.2 ms, measured | `calib`'s time (32 rounds, 8 threads) on the machine, fixed per season; `c_P` against it is a health check (§6), never a factor |
| `v_ref` | `T_triv / R`, `R = 10`, measured | the verifier scale of both tracks: a tenth of the trivial check of `2^24` permutations |
| `s_ref` | 2 MiB | the proof-size scale of the sum; `|π_i|` counts the bytes of `π` only, not the trace or signature |
| `κ` | 3.2975 s | `K · v0`, `K = 5`, `v0 = 659.5 ms` (`v_ref` measured on the machine): seconds of `S` per unit of `x` |

Every result also publishes the per-step records (`stream.jsonl`), the fit, `P̄` per octave, the
marginal values of both scores at the entry's own point, the largest `x_i`, the mean `x_i`, the mean
check time, `g`, the mean `|π_i|` and a batching indicator. None of these is scored beyond the two
scores.

## 8. Verdicts and records

| Verdict | Meaning |
|---|---|
| ACCEPT | certificate checked (`certificate: ok`) and every benchmark check passed |
| PROVISIONAL | the Lean build succeeds and the only failures are of the certificate: the kernel rejects it (including a theorem that is not the rendered one), its closure uses `sorryAx`, or the kernel exceeds its time or memory cap; benchmarked and published, never a record |
| REJECT | the entry failed a rule or a cap; the result names the reason |
| ERROR | the organiser's side failed (toolchain, missing or mismatched benchmark part, a machine fingerprint missing, unreadable or not the season's, a stream whose chain lengths are not the season's or a malformed `[stream] lengths`, a `c_P` drift, a setup job or organiser cache); requeued once. The fingerprint and the well-formedness of the season's lengths are checked first, in the setup job, and the stream's lengths against the season's at aggregation; a fingerprint or chain-lengths failure uses up no attempt (a retry at the same pin cannot clear it). Repeated organiser errors, of any kind, pause the queue until the owner acts (the submissions repository's `AGENTS.md` §9: two, where one author's errors of a kind an entry might provoke count once). Named organiser errors (`organiser_error`) never count against the author |

A result is **comparable** iff it is ACCEPT, its stream was not truncated and the job plan matched
(an ACCEPT is always on the season's machine and with the season's chain lengths: anything else is
ERROR). A stream that reaches
`stream_s` is scored over its completed steps, flagged `truncated` and not comparable.

**The record rule.** Each track, the sum and the product, has its own records. A result is a new
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
   track's score (`S` or `S×`), `S_t,record` the standing record's own score in that track at the
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
  If it fails, no record stands in that track.
- **The margin (2 %) is the owner's choice**, and it does not keep noise out. The relative
  run-to-run spread of one entry's `S` on the evaluation machine with the fixed chain lengths is σ ≈
  1.75 % (ten runs at the smoke shape, [`harness/smoke.toml`](harness/smoke.toml); mostly per-step
  process overhead, which weighs more with the smoke's short chains, so likely smaller at the
  season's shape). Those runs took each `V_i` as the best of two checks; with one check per output
  the spread can only be the same or larger. `S` and `S_record` are two runs, so two runs of one
  entry differ by about √2·σ ≈ 2.5 %: a near-copy of the record can beat it by noise. (A margin that
  kept noise out would be about 3·√2·σ ≈ 7.4 %.) The margin is the same in both tracks; at a
  realistic entry the product moves about 1.6 times as much as the sum for a given relative change
  of every check time (elasticity 0.34 against 0.21), so its spread is a little larger. Byte copies
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
| the whole stream, every request, check, canary, sample and re-run (`stream_s`; no check has a cap of its own) | 3,000 s wall per stream (reached: truncated, §8) |
| signed-proof file (`file_cap`); a request's `/work` after the step | 64 MiB; 4 GiB, 65,536 entries |
| memory: prover (incl. `/tmp`, `/work` tmpfs); service; badge | 11 GiB; 2 GiB; 4 GiB |
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
  32-byte key `k` as a PRF. The signature's unforgeability follows from these
  (on paper).
- **The badge**: the code Lean's compiler emits for `acc`, built from the same build the kernel
  checked; and the harness tools (gate, source rule, manifest, renderer, sandbox).
- **The runner and the service**, tested, not proved ([`tests/`](tests/), [`.github/workflows/ci.yml`](.github/workflows/ci.yml)).
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
- **The end of the stream is known** (`M = 96`). Leaving the last chains to the verifier gains at
  most about 0.2 % in either score (two chains, a verifier at the chain checker's speed), below the
  record margin (2 %).
- **The scores' constants** (`K = 5`, `s_ref`, the power 3 of `P̄`, the exponent 2 of `g`, the
  re-timing rule) come from a reference operating point estimated from the first recursive entries
  and from a study of trivial entries, not from entries measured on the machine.
- **Malformed and crafted inputs are not tested, and `acc` has no time bound.** The benchmark
  checks the entry's own outputs and the statement canaries only. Inputs assembled from published
  parts (for example a deep chain of nodes over public signed leaves) took an earlier entry's `acc`
  68–183 s before its authors bounded it; nothing in the rules bounds what such an input costs a
  third party who checks it.
- **The service is trusted runtime**: a bug that signs a wrong answer, reuses an index or exposes
  the key would be accept-all.
- **On paper, not in the kernel**: unforgeability of the signature, the PRF step from the random
  oracle to the keyed deployment, and the composition across the stream's comb (the union bound
  over any finite set of paths is kernel; the walk is kernel for balanced trees only).
- **`KS` is textbook knowledge soundness only for adversaries that ask the verifier's queries
  themselves**: its extractor also reads the verifier's answers, so for an adversary that leaves
  fresh queries to the verifier it is weaker than the textbook notion (`Controls/Security.lean`,
  `lucky_ks`). Every prover of the deployment asks the service for every answer it signs, so none
  is of that kind.
- **Efficient extraction** is claimed only for proofs up to 128 MiB and logs up to about `2^61`
  entries; beyond, `KS` holds with an unconstrained extractor.
- **The source rule raises the bar; it is not a proof** that no elaboration-time code runs.
- **Per-step service traffic is not published** (the service keeps lifetime totals only).

## 13. Consequences that bit real entries

From the first two certified entries (`spartan-srom`, `flock-recursive`) and the organiser's toy
prover. Their timings were measured on GitHub-hosted runners with a different chain hash, so they
are indicative only, except where a bullet says "on the machine".

- **The verifier weighs as much as the prover.** The first recursive entry's verifier and proof
  size cost several times its prover time. Under the sum one millisecond of check time on every
  step costs as much as 5 ms of `P̄`; under the product a verifier at four times `v_ref` multiplies
  the prover time by 17. Size `V` and `|π|` with the prover.
- **Your verifier's start-up is on the stream clock.** Each check batch (12), the canaries (1) and
  each re-run's check (at most 9) start a badge process; one entry's `V` took 11.7 s to initialise
  on a runner, so 1 s of start-up costs 13–22 s of `stream_s`.
- **The certificate build is tight**: a 199-module entry used 968–984 s of the 1,200 s cap on a
  4-vCPU runner. Modules outside the organiser's precompiled closure (`RecursionFast`, the CompPoly
  roots, `Mathlib.Tactic`) are compiled inside the 180 s badge build, about 860 modules;
  `import Mathlib` does not fit.
- **Step 1 is the worst request**: two chains of up to `2^20` steps each within `step_s = 60 s`.
  Test that case. Re-timing re-runs count against `stream_s` (208 s in one run).
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
- **Memory**: the 11 GiB cap counts `/tmp` and `/work` (a Spartan+Ligero leaf prover peaked at
  15.1 GiB at `n = 2^16`, 2.47 GiB after restructuring).
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
small shape (6 steps, chains of 16 to 128); `harness/season.toml` is the real one, and it runs only
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
witness-sending example of §2 spends about 2,100 s of `stream_s` on its checks at this shape on the
evaluation machine (about 2,350 s for the whole stream); on a slower machine it can reach `stream_s`
and be truncated, which is expected and not a harness fault.

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
