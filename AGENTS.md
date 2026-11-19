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

The fastest **recursive prover for batches of Keccak-256 hashes** whose soundness is proved in
Lean. An entry is a hash-based non-interactive argument for one relation over 32-byte digests: a
leaf digest commits to a Keccak-256 Merkle root over `n` runner-supplied 32-byte blocks, a node
digest to two accepted children. The benchmark is a stream of 16 steps, each one fresh leaf: each
step proves a Merkle root over `2^18` blocks (about `2^19` permutations) and folds it into the
running proof. It is ranked in two tracks with their own records: `every`, where every proof of
the stream must be accepted, and `final`, where only the last one must. The score is the median of
three timed passes' total wall times, with a factor for the final proof's size in `final` and for
the largest proof's in `every` (§7). The verifier is capped, not scored. Soundness is not
measured: it is a kernel-checked theorem, knowledge soundness in the random-oracle model, and the
oracle is deployed as a secret-keyed service that signs the answers each proof used (the signed
random oracle, §5). The service is not on the clock: the stream runs once against it, and the
three timed passes, which get the oracle's key, must reproduce that run's outputs byte for byte
(§6).

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
`submission` is the only definition of the rendered challenge that changed. The entry's modules may
add any other declarations, instances and notations included, which the comparator does not
compare. They reach the badge's checks through `submission`, and two more ways (§6, §11): the
entry's compiled modules are linked into the badge, so their top-level constants are evaluated when
it starts (untimed, capped by `badge_start_s`) and keep their values across the checks of one
process; and the entry's notations are in scope where the badge's one per-entry module is
elaborated, which gate rule 9 checks after the build. A mismatch, like any proof the
kernel rejects, makes
the result PROVISIONAL (§8), not REJECT. A minimal example, certified at errors 0 and not
competitive: the Lean half is [`tests/harness/ws-entry/`](tests/harness/ws-entry/), and the prover
half is [`harness/toy-prover/honest/prover.s`](harness/toy-prover/honest/prover.s), placed as
`prover/prover.s`. It passes the certificate and runs through the benchmark at the smoke's shape
([`harness/smoke.toml`](harness/smoke.toml)). At the season's shape it is REJECTed at step 1,
before any `V` is timed: its first output is a leaf proof that sends the leaf's data whole,
`16 + 2^23` bytes, above `pi_cap` = 1 MiB (§6). It shows the format, not a design.

## 3. The relation and acceptance

*Intuition.* A statement is a digest. A leaf statement says "I know `n` 32-byte blocks whose
Merkle root is this value" (the runner supplies the blocks and computes the root); a node
statement says "I know accepted proofs of these two children". A child is
judged by a *signed proof* `(π, tr, σ)`: the proof, the oracle answers its verifier reads (the
trace), and the service's signature on the trace. Checking a child therefore never evaluates the
secret-keyed oracle: it checks a signature and runs `V` on the trace.

- **Relation** `Rel acc` ([`Relation.lean#L157-L162`](RecursionFast/Contract/Relation.lean#L157-L162)):
  for a leaf witness `xs` (its blocks in order), `c = leafStmt (dataRoot xs) |xs|` with
  `|xs| ≤ leafCap = 2^20` blocks
  ([`#L69-L70`](RecursionFast/Contract/Relation.lean#L69-L70)), or
  `c = nodeStmt c₁ c₂` with `acc c₁ p₁` and `acc c₂ p₂`. Completeness is asked for every leaf up
  to `leafCap`, odd sizes and `n = 0` included
  ([`Certificate.lean`](RecursionFast/Contract/Certificate.lean)), though the benchmark uses one
  `n`.
- **Byte layouts** (normative; the contract, the service and the runner hash the same bytes):
  `leafItem x = Keccak-256(0x48 ‖ x)` (33 bytes, one permutation),
  `dataNode l r = Keccak-256(0x44 ‖ l ‖ r)` (65 bytes, one permutation), `dataLevel` (adjacent
  digests paired by `dataNode`, an odd last digest carried up unhashed), `dataRoot xs` (`dataLevel`
  applied `|xs|` times to the block hashes, then the first digest: the zero digest for no block,
  `leafItem x` for one), `leafStmt h n = Keccak-256(0x4C ‖ h ‖ enc64 n)`,
  `nodeStmt c₁ c₂ = Keccak-256(0x4E ‖ c₁ ‖ c₂)`, `enc64` = 8 bytes little-endian; Keccak-256 is
  Ethereum's: FIPS 202's sponge over `Keccak-f[1600]`, rate 136 bytes, padding `0x01 … 0x80` (not
  SHA3-256's `0x06`), 32-byte output ([`Hash/Keccak.lean`](RecursionFast/Contract/Hash/Keccak.lean));
  eight tags, one per hash input: `H` item, `D` data node, `L` leaf, `N` node, `T` trace, `W`, `K`,
  `M` the signature's
  ([`Relation.lean#L76-L125`](RecursionFast/Contract/Relation.lean#L76-L125)); the trace digest and
  the signature ([`Signature.lean#L18-L32`](RecursionFast/Contract/Signature.lean#L18-L32)).
- **Acceptance** `Submission.acc S vk c p`
  ([`Certificate.lean#L102-L110`](RecursionFast/Contract/Certificate.lean#L102-L110)), in this order:
  `|π| < 2^64`; `|tr| ≤ qV`; every query in `tr` at most `queryCap = 2^20` bytes
  ([`Relation.lean#L66-L67`](RecursionFast/Contract/Relation.lean#L66-L67));
  `SigOk vk (traceDigest tr) σ` ([`Signature.lean#L105-L110`](RecursionFast/Contract/Signature.lean#L105-L110));
  and `(V vk c π).runSeq tr = some true`: `V`'s `i`-th query is answered by the `i`-th entry of
  `tr`, which must be for that query, and the trace is used up exactly
  ([`Oracle.lean#L48-L55`](RecursionFast/Contract/Oracle.lean#L48-L55)).
- `acc` is the node clause of the relation, the harness's check of every proof, and anyone's check
  later with the published `vk`. There is no proof-size cap in `acc`: the runner caps `|π|` and the
  verifier's time (§6), and the score prices the proofs' size (§7).

## 4. The certificate

*Intuition.* The entry proves, once and for all, that its verifier is knowledge-sound (from any
prover that convinces it, an efficient extractor recovers a witness) and that its honest prover
convinces it, both in the random-oracle model and **for every public key `vk`**. Every key means
the theorem's adversary may hold the signing key, so a verifier that trusts a signature cannot be
certified; only `acc` trusts signatures.

`Certificate S` ([`Certificate.lean#L112-L124`](RecursionFast/Contract/Certificate.lean#L112-L124))
has four fields, and `CertificateR declared S`
([`#L137-L142`](RecursionFast/Contract/Certificate.lean#L137-L142)) adds that the submission's
`ε`, `δ`, `qV`, `fuel` are within the declared ones and the declared fuel within the budget.

- **`secure : ∀ vk, KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV`**
  ([`Security.lean#L150-L162`](RecursionFast/Contract/Security.lean#L150-L162)). `V` asks at most
  `qV` queries on every input and every oracle function; and for every adversary, a query program
  asking at most `Q` queries on every oracle function and outputting `(c, π)`, with
  `Q + qV ≤ logCap`, run and then followed by `V` against one lazily sampled random oracle
  (`prob`, [`#L140-L148`](RecursionFast/Contract/Security.lean#L140-L148)), the probability that
  `V` accepts on the final query log while `E c π log` returns no witness of the relation is at most
  `(Q + qV) · ε`. The extractor reads the final log, the verifier's answers included (how this
  relates to the textbook notion: §12). The adversary is computationally unbounded, bounded only in
  queries.
- **`complete : ∀ vk, CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) S.δ`**
  ([`Security.lean#L164-L168`](RecursionFast/Contract/Security.lean#L164-L168)): on every statement
  and witness of the relation, `P`'s proof, produced and then verified against one random oracle,
  is rejected with probability at most `δ`. Grinding is admitted. It is required for **every**
  witness, node witnesses with any accepted children included.
- **`computes : Computes S.ext S.E S.fuel`**
  ([`Extractor.lean#L198-L206`](RecursionFast/Contract/Extractor.lean#L198-L206)): the program
  `ext` of the contract's step-counting machine
  ([`Machine.lean#L95-L131`](RecursionFast/Contract/Machine.lean#L95-L131)), on the input tape
  `extractorInput c π L` ([`Extractor.lean#L123-L126`](RecursionFast/Contract/Extractor.lean#L123-L126)),
  halts within `fuel t` steps (`t` the tape's length in words) with at most `outCap` words that
  denote `E c π L` through `decodeWit` ([`#L183-L185`](RecursionFast/Contract/Extractor.lean#L183-L185)).
  This holds for every statement, proof of at most `8 · outCap` bytes (128 MiB) and log whose
  queries are below `2^64` bytes and whose tape is at most `2^64` words. The tape and output formats
  are normative ([`#L11-L32`](RecursionFast/Contract/Extractor.lean#L11-L32)). `E` takes no `vk`.
- **`cap`**: the numbers below.

| Cap | Value | Lean |
|---|---|---|
| `ε ≤ errorCap` (knowledge error per query) | `2^-128` | [`Security.lean#L132-L133`](RecursionFast/Contract/Security.lean#L132-L133) |
| `δ ≤ completenessCap` | `2^-40` | [`Security.lean#L170-L171`](RecursionFast/Contract/Security.lean#L170-L171) |
| `qV ≤` | `2^16` | [`Certificate.lean#L123`](RecursionFast/Contract/Certificate.lean#L123) |
| `fuel t ≤ extractorBudget t` | `2^48 + 2^16 · t` | [`Extractor.lean#L189-L190`](RecursionFast/Contract/Extractor.lean#L189-L190) |
| `ext.body.size ≤ progCap` (statements) | `2^20` | [`Extractor.lean#L195-L196`](RecursionFast/Contract/Extractor.lean#L195-L196) |
| `logCap` (queries for which `KS` is claimed) | `2^96` | [`Security.lean#L135-L137`](RecursionFast/Contract/Security.lean#L135-L137) |
| `outCap` (extractor output words) | `2^24` | [`Extractor.lean#L192-L193`](RecursionFast/Contract/Extractor.lean#L192-L193) |
| `queryCap`, `leafCap` | `2^20` bytes, `2^20` blocks | [`Relation.lean#L66-L70`](RecursionFast/Contract/Relation.lean#L66-L70) |

**How to prove it.** Any correct argument is accepted. The organiser library (untrusted,
kernel-checked) offers routes and parts: a potential on logs, `KState`, with its bridge
`KState.ks` to `KS` ([`Library/PaperTheorem.lean`](RecursionFast/Library/PaperTheorem.lean));
`KSTextbook.ks` (textbook soundness implies `KS` at twice the error,
[`Library/KS.lean`](RecursionFast/Library/KS.lean)); the witness-sending entry
([`Library/WitnessSending.lean`](RecursionFast/Library/WitnessSending.lean)); and word-level twins
of Keccak-256 and `SigOk` proved equal to the contract's
([`Library/Fast.lean`](RecursionFast/Library/Fast.lean),
[`Library/KeccakFast.lean`](RecursionFast/Library/KeccakFast.lean)).

**A node witness must fit `outCap`.** A leaf witness of `n` blocks takes `2 + 4n` output words
(at most `2^22 + 2` at `leafCap`). A child's signed file of `f` bytes with `m` trace entries
takes at most `(f + 7(m + 1))/8` words of output; with the previous step's output within the 64 MiB
file cap, the leaf child may take up to about 64 MiB (a leaf proof that sends its `2^20` blocks
whole, `601 + 4n` words as a child, fits beside it: `2^23 + 2^22 + 57,954 < 2^24` words), but two
children both within about 458,800 bytes of the file cap may not fit (with word-aligned fields
they fit up to 36 bytes below it) ([`Extractor.lean#L60-L75`](RecursionFast/Contract/Extractor.lean#L60-L75)). A certifiable
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
  mode**: it hands the runner `k` (never the signing seed), and from then on a `SIGN` succeeds
  only if its trace digest is the one signed at the same index in the service run, and then
  returns that same signature (otherwise status 4, `MISMATCH`). Replay mode never signs anything
  new.
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
- **The prover cannot:** reach the network (only Unix sockets can be opened), another process, the
  key during the service run, the signing seed ever, the leaf data before `go` or the seeds it is
  drawn from, any file outside its sandbox, or the machine's counters (the sandbox's `/proc` shows
  its own processes and no machine-wide file, [`harness/PROVER.md`](harness/PROVER.md) §2); work
  after reporting `done` (the clock
  stops only when its whole process tree is dead); choose its statement (the runner computes every
  statement and checks each output against its own).
- The native prover is never proved. Only its signed proofs are checked, by `acc`. It need not
  agree with the Lean `P`.

## 6. The benchmark

*Intuition.* One stream of 16 steps. Each step receives 8 MiB of fresh data from the runner and
must prove its Merkle root, folded into the running proof. The stream runs first against the oracle
service, which fixes and checks every output. Then the oracle's key is handed to the prover and the
stream is run three more times on the clock; each of those outputs must be the service run's, byte
for byte. So the timed passes measure the prover without the service, and every accepted proof
comes from a run in which the prover never had the key.

- **Statements.** Step `i` gets its data `xs_i`, `n = 2^18` blocks of 32 bytes, with the leaf
  `L_i = leafStmt (dataRoot xs_i) n`, and
  ```
  c_1 = L_1,      c_i = nodeStmt c_(i-1) L_i      (i = 2 … M, M = 16)
  ```
  Step 1, `prover first`: `leaf.json` (`{"n": N}`) and `leaf.bin` (the data, exactly `32 · N`
  bytes, `x_0 ‖ … ‖ x_(N−1)`), output a signed proof of `c_1`. Step `i ≥ 2`, `prover step`: also
  `prev.stmt` and `prev.bin` (the previous statement and the service run's output for it), output
  for `c_i`. Every step's leaf is `2^18` block hashes and `2^18 − 1` tree nodes (one permutation
  each, about `2^19`), about `2^23` in the stream. The interface and the files are in
  [`harness/PROVER.md`](harness/PROVER.md) §3 and [`harness/FORMAT.md`](harness/FORMAT.md).
- **Data, seeds and keys.** Per step the runner draws a fresh secret 32-byte seed `s_i` from the
  OS CSPRNG and expands it to the step's data,
  `xs_i = SHAKE-256("recursion.fast/leaf-data/v1" ‖ s_i)` truncated to `32 · n` bytes; the
  service's keys are fresh secret draws per evaluation too. A prover never sees a seed, and a step
  sees its data only when its inputs arrive. The runner writes every step's data before the first
  request to a directory of its own that no sandbox binds (not the store the badge binds), and
  computes every statement from it. After the run the result publishes the seeds, the expansion
  (`stream.leaf_data`: the XOF and the domain string), the leaf digests, the statements and `vk`,
  so anyone can regenerate the data and recompute every statement. The signing seed is never
  written or published.
- **1. The service run.** Steps 1 … M, a fresh process each, against the service, with no key in
  the sandbox. Its times are recorded, not scored. Then, with no entry process alive, the runner
  checks outputs with the compiled `acc` against its own statements: the final output (step `M`)
  always, every intermediate output for the track `every`. **Caps:** every output's size is at
  most `pi_cap` = 1 MiB (`|π|` if it parses as a signed proof that `acc` accepts, else its file size); the final `|π|`
  is at most `final_pi_cap` = 512 KiB; a checked output's `V` is at most `v_cap` = 64 ms.
- **The verifier check.** Every checked proof is judged in three separate badge runs, each a fresh
  process, and `V_i` is the median of its three times, one from each run (published as
  `V_runs_ns`, in run order, and `V_ns`). One time is one check, the file's read and parse
  included, pinned to one core. All three runs must accept: a proof accepted in one run and
  rejected in another is rejected (`recheck_rejected`). The intermediate outputs are checked in
  batches of `check_every` = 8 between steps, each batch in three runs that each check every
  proof of the batch once; the final output is judged the same way, in three runs of its own.
  Every judged run first checks the organiser's warm-up input (a fixed signed file under a fresh
  random key and statement, never an output; an entry can tell it apart, and that gains nothing)
  and then distinct outputs: no proof is checked twice in one process, so a verifier that
  remembers its work across checks pays it inside every judged window. The process's start-up, to
  the warm-up's answer, is at most `badge_start_s` = 2 s (the entry's top-level constants are
  evaluated then, untimed; measured about 0.08 s); past it the check fails (a REJECT for the final
  output, the track `every`'s for an intermediate one). Each check is timed twice at once: by the
  runner, around the request to the badge process (about 0.3 ms plus 0.4 ms per MiB of file beyond
  the check itself), and by the badge's own clock; the larger counts
  ([`harness/rfh/checks.py`](harness/rfh/checks.py)). A judged run of `c` intermediate proofs is
  bounded by `60 s + 2 (c + 1) · v_cap`; the final output's runs by the stream's cap alone.
- **Statement canaries.** The final output must be rejected against its statement with one bit
  flipped and against its first child's statement; for the track `every`, the outputs of steps 1
  (a leaf: only the flipped statement) and 2 also. Each canary is checked once, in one badge run:
  canaries test rejection, not time.
- **The tracks.** An entry is REJECTed if the final output is rejected, breaks a cap or a final
  canary is accepted, or any output breaks `pi_cap`. It is scored in the track `final` if not. It is
  also scored in `every` if every intermediate output is accepted, within both caps, and its
  canaries are rejected; otherwise the result says why (`tracks_reason`), and that is not a failure.
- **2. The timed passes.** The runner switches the service to replay mode (§5) and runs the
  stream `timed_runs` = 3 more times. Each step is a fresh process with the same leaf (the same
  `leaf.json` and `leaf.bin` bytes), the runner's statement, the service run's previous output as
  `prev.bin`, and the file `oracle.key` (`k` as 64 hex characters), all renamed into `/work` when
  the clock starts; the oracle socket `/run/rf/oracle.sock` also appears only then, in every run, so
  nothing that depends on `k`, the data, the statement or the service can run in the untimed
  start-up (connect after `go`). The start-up (up to `ready_s` = 10 s, on every core) does see
  `vk.hex`, already in `/work`, and may do any work that depends on nothing else (pre-fault
  memory, build tables). Every output must be byte-identical to the service run's output of that
  step; a difference in any pass is the entry's REJECT, with the step, the pass and the first
  differing byte. Nothing of the service run's requests survives into the timed passes: each
  request's `/work` is a private tmpfs of its own, gone with the request, so no file, inode number
  or free-space count of it reaches a later request; `/setup` is read-only, and before every
  request the runner reads every file of the setup and the prover binary, so their page-cache
  state carries nothing; a request's directories outside the sandbox have random names, so
  nothing a prover can read (`/proc/self/mountinfo` included) names its pass or its step
  <!-- c4: confirm -->. Every `SIGN` of a timed pass must be the service run's at the same index:
  any `MISMATCH`, or a pass that re-issues fewer or more signatures than the service run made
  (the service's `replays` must be `3 · signatures`), is the entry's REJECT, so a refused `SIGN`
  cannot be used as a probe. A pass that does not finish (a request's failure, `stream_s`
  reached) is the entry's REJECT: there is no median over the passes that finished.
- **What is timed.** `P_{i,t}`: in timed pass `t`, from just before step `i`'s inputs are renamed
  into `/work` (a constant-time rename) to the death of the last process of the sandbox.
  Start-up to the `ready` line is untimed (capped by `ready_s`). The score takes the pass whose
  total is the median of the three (§7).
- **Calibration.** Before the service run's steps 1 and 9 (every `every` = 8 steps), before each
  timed pass, and after the timed passes (if 30 s of `stream_s` remain), always
  with no entry process alive: three runs of the organiser's prover-shaped workload `calib`
  ([`harness/tools/calib.c`](harness/tools/calib.c), portable C: interleaved Keccak-256 chains and a
  memory sweep on every CPU). `c_P = median(calib) / ref_ns` is a health check of the machine, not
  part of the score: once `ref_ns` is measured, `|c_P − 1| > c_P_drift` makes the run an organiser
  ERROR (recorded with its reason).
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
- **Throughput.** One evaluation at a time. The benchmark's capped entry steps sum to 2,420 s
  (`build_s` 120 + `setup_s` 240 + the setup tree's hash 60 + `stream_s` 2,000), inside the
  benchmark job's 64 minutes for its parts. With the core commit's caches in place, one evaluation
  holds the benchmark slot for at most about 2 hours (the certificate job, at most 50 minutes, and
  the benchmark job, at most 70, §9, plus a few minutes of the setup jobs' cache lookups; 130
  minutes with a second kernel); when the caches must first be built, as after a pin move, up to
  about three and a half hours. A full queue with warm caches completes about a dozen evaluations
  a day when every evaluation runs to its limits, more when they end sooner; there is no cap per
  author (§15).

## 7. The score

One score per track, in seconds; lower is better. Each track prices its own proofs' size.

```
T_t      = Σ_{i=1..M} P_{i,t}                              the total of timed pass t (t = 1, 2, 3)
t*       = the pass whose total is the median of T_1, T_2, T_3 (ties: the lowest such index)
P_total  = T_{t*}
S        = P_total · 2^( |π_M| / 512 KiB )                 the track `final`
S_every  = P_total · 2^( max_i |π_i| / 512 KiB )           the track `every`
```

`P_{i,t}` step `i`'s wall time in timed pass `t` (§6), `|π_M|` the bytes of the final output's `π`
alone (not the trace or signature), `max_i |π_i|` the largest output's `π` (every output of an
entry in `every` is accepted, so each is its `π`). A step's `P_i` is its time in pass `t*`, so
`Σ_i P_i = P_total`.

- **Wall time, nothing else.** How the work is spread over the steps is the entry's choice, within
  `step_s` (which applies to the service run too, where every oracle answer is a round trip) and
  the memory cap. Hashing cannot be deferred: a step's data (8 MiB) exceeds `pi_cap`, so it
  cannot be carried to a later step, and its hashing is proved in the step that receives it.
  Recursion can: in `final`, where intermediate outputs need not be proofs, an entry may defer
  it, and a final compression wrap of the last proof pays there.
- **The size factor** is ×1.41 at 256 KiB and ×2 at `final_pi_cap` (512 KiB); in `every` an
  intermediate proof may reach `pi_cap` (1 MiB), a factor of ×4. 1 KiB is about 0.135 % of the
  score, and cutting prover time by 10 % is worth about 78 KiB.
- **Why `every` prices its largest proof.** With only `|π_M|` priced, an entry would run steps
  1 … 15 with the fastest parameters and proofs up to 1 MiB and shrink only the last. In `every`,
  where every output is a checked proof, every proof's size counts; `final` keeps `|π_M|`, as a
  deployment that ships one last aggregate does.
- **The median of pass totals.** Taking each step's faster pass would reward variance the prover
  controls. Against the median of three pass totals a gamble on per-step variance gains about
  nothing (an estimate), and one bad pass is discarded; a rare slow step is forgiven too (§12).
- **The verifier is not scored.** It is capped at 64 ms per checked proof, the median of three
  fresh judged runs (§6).

`score` in [`harness/rfh/bench.py`](harness/rfh/bench.py) computes it from the per-step records
alone and [`harness/aggregate.py`](harness/aggregate.py) recomputes it with the same function; the
result's `score` holds `S`, `P_total_s` (`T_{t*}`), `size_factor`, `final_pi_bytes`,
`pass_totals_s` (the three `T_t`, in pass order), `median_pass` (`t*`) and, when the entry is in
`every`, `S_every`, `size_factor_every` and `max_pi_bytes`; `tracks = {"final": "S", "every":
"S_every"}` names each track's field (without `every` when the entry is scored in `final` only,
with the reason in `tracks_reason`). Every result also publishes the per-step records
(`stream.jsonl`: the service run's time, the three timed times `P_timed_s` in pass order, `P_s` the
time in pass `t*`, `share_P`, `|π_i|`, `V_i` where checked). A step record without exactly three
timed times is a runner fault, an organiser ERROR named `malformed` (§8).

| Symbol | Value | Meaning |
|---|---|---|
| `M` | 16 | stream steps, the same for every entry |
| `n` | `2^18` | blocks of 32 bytes per step (one leaf, 8 MiB) |
| `timed_runs` | 3 | timed passes; `P_total` is the median of their totals |
| size scale | 512 KiB | a proof of 512 KiB doubles its track's score |
| `ref_ns` | 316.2 ms, measured | `calib`'s time (32 rounds, 8 threads) on the machine, fixed per season; `c_P` against it is a health check (§6), never a factor |

## 8. Verdicts and records

| Verdict | Meaning |
|---|---|
| ACCEPT | certificate checked (`certificate: ok`) and every benchmark check passed |
| PROVISIONAL | the Lean build succeeds and the only failures are of the certificate: the kernel rejects it (including a theorem that is not the rendered one), its closure uses `sorryAx`, or the kernel exceeds its time or memory cap; benchmarked and published, never a record |
| REJECT | the entry failed a rule or a cap; the result names the reason and the stage, `reject_stage`: `certificate` (the certificate job), `prover` (the prover's build or setup), `request` (a service-run request failed: a timeout, an exit, a cap), `check` (an output's check by the badge failed or broke a cap, the canaries included), `timed-pass` (a byte or replay mismatch, or a timed request failed) or `stream-cap` (`stream_s` reached) <!-- c4: confirm --> |
| ERROR | the organiser's side failed (toolchain, missing or mismatched benchmark part, a machine fingerprint missing, unreadable or not the season's, a stream whose shape is not the season's, a stream record no score can be computed from (`malformed`), a `c_P` drift, a setup job or organiser cache); requeued once. The fingerprint is checked first, in the setup job, and the stream's shape against the season's at aggregation; a fingerprint or shape failure uses up no attempt (a retry at the same pin cannot clear it). A failure of the service run, a byte mismatch of a timed pass, or a service refusal during the entry's requests is the entry's REJECT, never ERROR. Repeated organiser errors, of any kind, pause the queue until the owner acts (the submissions repository's `AGENTS.md` §9: two, where one author's errors of a kind an entry might provoke count once). Named organiser errors (`organiser_error`) never count against the author |

A result is **comparable** iff it is ACCEPT and the job plan matched (an ACCEPT is always on the
season's machine and with the season's shape: anything else is ERROR). A stream that reaches
`stream_s` is the entry's REJECT: the score needs the final proof and all three timed passes.

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
   track's score (`S` in `final`, `S_every` in `every`), `S_t,record` the standing record's own
   score in that track at the pin and `margin = 0.02`;
5. its prover binary's SHA-256 is not that of an earlier record of either track (a resubmitted copy
   is `accepted`, never a record);
6. **a confirmation run agrees**: a result that meets items 1–5 in a track is not crowned at once.
   The bot evaluates the same commit once more at the same pin, ahead of other entries; the record
   is taken only if that run also meets items 1–5 in the track, and the record's score is the worse
   (larger) of the two. Otherwise the entry is `accepted`. A confirmation that ends in an organiser
   ERROR is queued again, as a port is. A port (below) is not confirmed: it re-measures a
   standing record at a new pin, and its author cannot re-roll it.

Items 1–3, 5 and 6 are the same for both tracks; one result can set both records, and one entry may
hold both. The confirmation makes a noise-won record need two lucky runs, not one: re-submitting
the same prover (a NOTES edit, a one-byte change to the assembly) no longer re-draws the noise for
a record.

- **Records are per pin and per track**: a track's standing record is its newest, not retired,
  record evaluated at the pinned core commit. With none, the first result meeting items 1–3 and 5
  is that track's record.
- **A pin move ports the records first.** When the pin moves while a record stands, the bot
  re-evaluates each standing record's retained commit at the new pin before any other entry (one
  run when one commit holds both); a record keeps its crown if that is a comparable, attested ACCEPT.
  If it fails, no record stands in that track. A port competes only in the tracks whose record it
  carries, and item 5 does not refuse a record's own port.
- **The margin (2 %) is the owner's choice**, and it does not keep noise out. The relative
  run-to-run spread of one entry's score on the evaluation machine was σ ≈ 1.75 % under earlier
  rules (ten runs at their smoke shape; mostly per-step process overhead). `P_total` is now the
  median of three 16-step pass totals. A model from the per-step spread measured on the machine
  (about 0.9 %) gives about 0.15 % for it; an estimate for the score, `c_P`'s drift included, is
  0.2–0.5 % per evaluation. Neither is measured at this shape (§12). Two runs of one entry differ
  by about √2·σ, so a near-copy of the record can beat it by noise. The margin is
  the same in both tracks. Byte copies
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
| start-up to `ready`; one request (`step_s`) | 10 s; 20 s |
| the service run, its checks and canaries, and the three timed passes (`stream_s`) | 2,000 s wall (reached: REJECT) |
| an output's size (`pi_cap`); the final `|π|` (`final_pi_cap`); a checked proof's `V` (`v_cap`) | 1 MiB; 512 KiB; 64 ms (the median of three fresh judged runs) |
| a badge process's start-up to its warm-up answer (`badge_start_s`) | 2 s |
| timed passes (`timed_runs`); a timed pass's output | 3; byte-identical to the service run's |
| signed-proof file (`file_cap`); a request's `/work` after the step | 64 MiB; 4 GiB, 65,536 entries |
| memory: prover (incl. `/tmp`, `/work` tmpfs); service; badge | 8 GiB; 2 GiB; 4 GiB |
| service: query; request body; items per `QUERY` / `SIGN`; connections; signatures per stream | `2^20` B; 16 MiB; `2^18` / `2^16`; 32; `2^16` |
| jobs: certificate (with nanoda); benchmark; setup, setup-tools; plan, attest | 50 min (60); 70 min; 30 min; 10 min |
| the benchmark VM; evaluations at a time | 4 cores / 8 threads, 16 GB; 1 |

The prover's 8 GiB is its memory cgroup's charge. The page cache of the setup directory and the
prover binary is read by the runner before every request (§6), so those pages are charged to the
runner's cgroup, not the request's: read-only setup data (at most 4 GiB) that a prover maps or
reads is in effect outside the 8 GiB. This is open to every entry. (Charging it to the request
would mean evicting and re-reading the setup from disk before every request.) The inputs a request
receives at `go` (`leaf.bin`'s 8 MiB among them) are written by the runner, so their pages are
charged to the runner too; a copy the prover makes counts toward its cap and `work_cap`.

`stream_s` covers 64 requests (16 in the service run, 48 in the timed passes), each up to
`ready_s + step_s` = 30 s (1,920 s in all), plus the checks, the calibration samples and the
runner's re-read of the setup before every request. So the per-request caps bind first, except
when an entry uses nearly every cap at once (start-ups near 10 s, steps near 20 s, a setup
directory near 4 GiB); there `stream_s` binds.

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
  match the olean manifest; and, after the badge build, the badge's per-entry module holds
  `main := RFBadge.main RecursionFast.Challenge.submission` and nothing else (rule 9: an entry's
  `notation` can turn the text `RFBadge.main` into another term in every module that imports it).
- **Imports**: an entry module imports only its own modules and the import closure of `Mathlib`,
  `RecursionFast.Contract`, `RecursionFast.Library`, `RecursionFast.Controls`,
  `CompPoly.Fields.Binary.BF64.Ext3` and `CompPoly.Fields.Binary.BF64.Bytes`
  ([`harness/org-setup.sh`](harness/org-setup.sh)). Module root names must be new (not `Mathlib`,
  `RecursionFast`, `Challenge`, a package's, …).
- **Only `Solution`'s import closure is built**; other files under `lean/` are still scanned by the
  source rule.

## 11. What is trusted

- **The contract**: 10 Lean files, 339 code lines at this commit (`scripts/loc.py`; CI enforces at
  most 500), Lean core and Mathlib only, no theorem.
- **One kernel**: Lean v4.34.1's, replayed by the comparator (`leanprover/comparator` at `d03acab`
  with lean4export `076e8e5`, pinned and built by
  [`harness/ci/build-kernels.sh`](harness/ci/build-kernels.sh)), with Lean core, Mathlib and the
  pinned packages as hashed in the olean manifest.
- **The record build cache**: a certificate job may seed its build from the record's attested build
  (bound by its manifest's hash): only entry modules whose source is byte-identical are reused,
  never the challenge, and the kernel still replays every proof. A candidate's build stays under
  `build_s`, so a slow build may fit only when the cache hits. A REJECT the cache can have caused
  (`reject_stage` `certificate`, or `check`: a restored module's `.c` is what the badge is compiled
  from) is re-run without it by the submissions repository's bot; a REJECT at any other stage is
  final, since the prover is built from the entry's `.s`, not from the cache <!-- c4: confirm -->.
- **Keccak-256** (FIPS 202's `Keccak-f[1600]` sponge with Keccak's padding): collision resistance
  on the eight tagged domains, and `Keccak-256(k ‖ ·)` with a secret
  32-byte key `k` as a PRF (also under the signing seed: the chain starts `chainStart` are
  pseudorandom), and **tweakable multi-target one-wayness of the WOTS chain step** `wotsStep`
  with pseudorandom starts: no adversary outputs *the honest* chain value at a position below
  every position the signer revealed of that chain, except with small probability (about
  `2^16 · 133` targets, each tweak `(j, i, s)` targeting one value; for a key the signer never
  used, that is guessing a value derived from the PRF). It is hard only because the starts are
  random and unknown: a forger with `sk` built in reaches it for every fixed `sk`. The
  signature's unforgeability (EUF-CMA, one message per index) is reduced in the kernel to a
  Keccak-256 collision or such a chain inversion
  ([`Library/WotsReduce.lean`](RecursionFast/Library/WotsReduce.lean), `wotsReduce`,
  `eufReduce`), given that the signed traces are the service's **complete** transcript
  (`Transcript`: every signature the reference signer's `sign sk j (traceDigest tr)`, one message
  per index, replays allowed); an issued signature missing from it can be replayed and is then
  reported as an inversion. The inversion's probability stays on paper. The composition across
  the stream needs collision resistance, the PRF and the chain's one-wayness only. The leaves' data
  the walk extracts are the runner's, or two block lists of one leaf, of one length and one root,
  give an explicit collision over the data tree (`dataCollision`, `Outcome.data_or_collision`). A signed trace
  the log does not hold is reduced, for any tree shape, to an EUF-CMA forgery against the
  service's signed traces or an explicit collision
  ([`Library/Compose.lean`](RecursionFast/Library/Compose.lean), `Forgery.reduce`); the walk
  around it is kernel for the stream (`walkStreamSigned`, `compose_prob_stream_signed`, a union
  bound over its `2M - 1` members, and `compose_prob_stream_wots`, its EUF-CMA term split into a
  collision and a chain inversion) and for balanced trees (`walkSigned`, `compose_prob_signed`,
  `compose_prob_wots`). Security against signature-only forgery, which the original
  signed-oracle construction (Chiesa–Tromer, ICS 2010) also assumes, is not used: the walk
  matches a signed proof to the log by its trace, the signed message, not by its signature.
- **The badge**: the code Lean's compiler emits for `acc`, built from the same build the kernel
  checked, and the badge's glue (the file and hex parsers, the timer, the command line:
  [`RecursionFast/Badge.lean`](RecursionFast/Badge.lean)), compiled with the organiser's package
  before any entry exists (its `.olean` in the olean manifest, and the compiled code a badge links,
  the glue's and every organiser module's `.c` and objects, hashed after `org-setup.sh` builds them
  and checked after every badge build, which sees the organiser's build read-only), so that no
  instance or notation an
  entry declares is in scope where it is elaborated. The one module elaborated with the entry in
  scope ([`harness/badge/Verify.lean.in`](harness/badge/Verify.lean.in)) passes `submission` to the
  glue and holds nothing else (gate rule 9). The executed code is still compiled code, not the
  kernel's term: an elaboration-time metaprogram that rewrites the compiler's data (the known raw
  route passes the gate; only the lexical source rule stops it) or a compiler bug would make it
  differ from the certified `acc`
  ([`docs/assurance/CONTRACT-REVIEW-2026-11.md`](docs/assurance/CONTRACT-REVIEW-2026-11.md), the
  open item). And the harness tools (gate, source rule, manifest, renderer, sandbox).
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
- **The margin is not matched to the score's spread.** Under earlier rules the spread of one
  entry's score was σ ≈ 1.75 % (measured at their smoke shape), so two runs differed by about
  √2·σ ≈ 2.5 %, above the 2 % margin (§8). At this shape the median of three pass totals is
  estimated at 0.2–0.5 % per evaluation, `c_P`'s drift included, but it is not measured. If the
  spread is that small, 2 % keeps out real improvements below it; if it is near 1.75 %, a
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
- **The end of the stream is known** (`M = 16`), and an entry may defer recursion to the last
  step (§7); hashing cannot be deferred. The verifier cap (64 ms) bounds what can be left to the
  verifier itself.
- **The leaf is an emulation, not leanXMSS.** It has the hash count and witness density of
  signature aggregation (`2^18` blocks: about the Keccak calls of 2,800 leanXMSS signatures; 8 MiB,
  16 bytes per permutation), but none of its irregular work (digit-dependent chain lengths,
  checksums, selection) and no per-signature authentication paths.
- **The split between hashing and fixed cost is measured on a proxy.** Fitted on the evaluation
  machine over the previous season's best entry, whose leaf committed one 32-byte digest per hash:
  about 1.6 µs per permutation and a fixed 0.39 s per step. That projects hashing at about 61–71 %
  of a step of about 1.3 s for the best code today. The committed-data leaf commits a different number of words per
  permutation, and with one fixed `n` the split cannot be watched in season. A later season can move
  `n` without a contract change.
- **Short steps weigh fixed costs more.** About 0.4 s of a 1.3 s step is fixed cost, mostly the
  commitment's opening and the recursion.
- **The verifier cap is tighter.** The best entries' `V` averaged 39–41 ms under the previous
  rules, and a larger committed witness may raise opening costs.
- **The median forgives rare slow steps.** A step the prover makes slow on purpose, rarely, costs
  little when one pass of three is discarded, and a REJECT costs only queue time.
- **The `final` track allows a final compression wrap**: its intermediate proofs may be up to
  1 MiB, and only the last one is priced.
- **The scored size is `|π|` alone.** A signed file also carries the trace's answers and a
  4,768-byte signature, which a public-hash deployment would not ship; the result publishes the
  whole file size beside `|π|`.
- **The timed passes trust isolation and determinism.** The timed passes are only a stopwatch:
  every accepted output comes from the service run, in which the prover never had `k`. A timed
  pass could reproduce an output without proving only through a channel from the service run's
  requests, and the per-request sandbox (a private tmpfs `/work` and a fresh `/tmp`, read-only
  `/setup`) is the same isolation that keeps state between steps inside `π`. Closed by the runner
  and the sandbox: the page cache of the setup and the prover binary (re-read in full before every
  request); the replay service's answers (a refused `SIGN` is a REJECT); `/proc`'s machine-wide
  counters and the live counters of `/sys/devices/system/cpu` (masked); sockets other than Unix
  ones (refused, so no network counter moves); the inode numbers and free space of `/work` (a
  tmpfs of its own per request); and the request's directory names (random)
  <!-- c4: confirm -->. Left open:
  - **the clocks**: a service-run step can stretch its own untimed duration, and a timed step can
    read the clock against a timestamp kept in `/setup`: about 9 bits per stream (an estimate);
    accepted;
  - **kernel-wide counters the sandbox cannot mask**: `sysinfo(2)` (the load averages, free memory,
    the number of processes) and the inode numbers of pipes, sockets and memfds, which come from
    one counter of the kernel's; their capacity is not measured <!-- c4: confirm -->;
  - **micro-architectural state** (CPU caches, predictors), not cleared between requests; the
    calibration runs between requests disturb it.

  The price is determinism: a prover whose output depends on thread timing or fresh randomness
  fails the byte comparison.
- **A trace is not size-capped beyond `file_cap`.** The caps count `|π|`; an accepted proof's trace
  (at most `qV ≤ 2^16` queries of at most `2^20` bytes, all asked by `V`) is bounded only by the
  file cap. Its queries are a function of `vk`, `c`, `π` and the answers, so it moves no data out of
  `π`. Asking them takes `V`'s time, which `v_cap` bounds where `V` is capped: the final output,
  and every output for the track `every`; an intermediate output of an entry scored in `final`
  only is accepted or rejected but not `V`-capped. An output `acc` rejects is sized by its whole
  file. A signed proof is one `SIGN`, whose request body the service caps at 16 MiB, below the
  `qV · 2^20` bytes `acc` admits: an entry whose honest traces are larger can be complete in the
  model and still unable to sign them.
- **`k` is revealed after the service run.** It then protects nothing: no signature can be made
  without the signing seed, which never leaves the service, and replay mode re-issues only the
  service run's own signatures. A timed pass may still leak `k` (in its timing or its output),
  harmlessly.
- **Not adopted this season** (from the review of these rules): a paired, interleaved confirmation
  run of a candidate record against the standing one; a proof-size cap inside `acc` (the caps are
  the runner's, so `acc` itself accepts larger proofs); per-signature digit vectors drawn per run;
  a public, unkeyed hash in place of the signed oracle, which is how leanVM deploys and would need a
  new contract.
- **The score's constants** (the size scale of 512 KiB, the caps, `n`, `M`) are the owner's
  choices for this season, set from the previous season's entries and leanVM's published proof
  sizes (209–294 KiB), not from entries measured at this shape. `stream_s` binds only in the corner
  where an entry uses nearly every cap at once (§9).
- **Malformed and crafted inputs are not tested, and `acc` has no time bound.** The benchmark
  checks the entry's own outputs and the statement canaries only. Inputs assembled from published
  parts (for example a deep chain of nodes over public signed leaves) took an earlier entry's `acc`
  68–183 s before its authors bounded it; nothing in the rules bounds what such an input costs a
  third party who checks it.
- **The service is trusted runtime**: a bug that signs a wrong answer, reuses an index or exposes
  the key would be accept-all.
- **On paper, not in the kernel**: that the signature's chain starts are pseudorandom, and the
  bounds on the probabilities of the walk's collision and chain-inversion outcomes (the per-run
  reduction to them is kernel: `Forgery.reduce`, then `eufReduce` from EUF-CMA to a collision or
  the honest chain value below every revealed position, given the service's complete signing
  transcript, `Transcript`: the reference signer's signatures, one message per index; the model
  has no signing oracle), lazy sampling against a random function, randomised adversaries (an
  average of deterministic ones), and the PRF step from the random oracle to the keyed
  deployment. The composition across the stream is kernel for one deterministic query program
  against the lazily sampled oracle, given the service's signed traces (`compose_prob_stream`,
  `compose_prob_stream_signed`, `compose_prob_stream_wots`).
- **`KS` is textbook knowledge soundness only for adversaries that ask the verifier's queries
  themselves**: its extractor also reads the verifier's answers, so for an adversary that leaves
  fresh queries to the verifier it is weaker than the textbook notion (`Controls/Security.lean`,
  `lucky_ks`). In the service run every signed answer is in the run's log (`SIGN` computes the
  answers it signs), so the run as a whole, the prover together with the service's evaluations,
  is of the normalised kind; the composition matches every signed trace to that log or reduces it
  to a forgery (`Library/Compose.lean`).
- **Efficient extraction** is claimed only for proofs up to 128 MiB and logs whose queries are
  below `2^64` bytes each and whose tape is at most `2^64` words (about `2^61` entries); beyond,
  `KS` holds with an unconstrained extractor. (One query of `2^64` bytes takes a log out of the
  domain; `acc` rejects any query above `2^20` bytes, so no accepted trace has one.)
- **The source rule raises the bar; it is not a proof** that no elaboration-time code runs.
- **Per-step service traffic is not published** (the service keeps lifetime totals only).

## 13. Consequences that bit real entries

From the first two certified entries (`spartan-srom`, `flock-recursive`) and the organiser's toy
prover. Their timings were measured on GitHub-hosted runners with a different chain hash, so they
are indicative only, except where a bullet says "on the machine".

- **The verifier cap is per proof and includes parsing.** The first recursive entry's verifier
  took about 500 ms per check; the optimised lvm2-style entries about 40 ms. A recursive `V` that
  re-checks history grows with the stream and breaks the 64 ms cap.
- **Your verifier's start-up is on the stream clock.** Each check batch starts three badge
  processes (one per judged run) and the canaries one more, each start-up capped by
  `badge_start_s` (2 s); one entry's `V` took 11.7 s to initialise on a runner.
- **Determinism is a rule.** Seed every randomised choice from the inputs and the oracle's answers;
  search grinding nonces in a fixed order and take the first; never let the thread schedule pick
  between valid outputs. One-time signature indices follow the order in which `SIGN`s arrive, so
  issue your `SIGN`s in an order fixed by the inputs (not from racing threads). Run your prover
  twice locally and compare the bytes.
- **The certificate build is tight**: a 199-module entry used 968–984 s of the 1,200 s cap on a
  4-vCPU runner. Modules outside the organiser's precompiled closure (`RecursionFast`, the CompPoly
  roots, `Mathlib.Tactic`) are compiled inside the 180 s badge build, about 860 modules;
  `import Mathlib` does not fit.
- **Every step is a `2^18`-block leaf** (about `2^19` permutations, 8 MiB of data to commit to)
  within `step_s = 20 s`, in the service run too (where every answer is a round trip), and more if
  you defer recursion. Test the service run's time, not only the timed one.
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
  at `2^20` hashes under the old 11 GiB cap). Stream the leaf's hashes in batches if they do not
  fit.
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
small shape (4 steps of 6 blocks each; the season's size caps, its own verifier and time caps: its
`v_cap` is 128 ms, the one documented exception, because the toy's witness-sending `V` grows with
the stream and CI runs the smoke on shared runners); `harness/season.toml` is the real one, and it
runs only on the evaluation machine: elsewhere its fingerprint check stops the benchmark as an
organiser ERROR before the prover is built, and its `c_P` drift check would too. To run the
season's shape on your own machine, generate a local copy and pass it to `--season`:

```sh
python3 -I harness/local-season.py > /tmp/season-local.toml   # fingerprint "any", ref_provisional true
python3 -I harness/evaluate.py all --entry PATH/TO/ROOT --org "$PWD" \
  --work /tmp/rf-work-season --out result-season.json --season /tmp/season-local.toml
```

Every shape and every other cap is then the season's; only those two lines and the season's name
differ (as in the smoke), and your machine's speed is not the evaluation machine's. The
witness-sending example of §2 is REJECTed at this shape at step 1 by `pi_cap`, as expected.

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
