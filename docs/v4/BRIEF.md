# recursion.fast v4 (SROM): orchestration brief

Status: the working brief of the v4 build (2026-10-22). It records the user's request, the
orchestrator's critical review of it, the decisions taken in the user's absence, the normative
interfaces every stage builds against, and the stage plan. The reader-facing normative design is
`docs/DESIGN-v4-srom.md` (written in stage D); where the two disagree, the design document wins
once it exists, and the disagreement is reported.

## 0. The request, in one paragraph

Implement the next rules of recursion.fast as the **signed random oracle (SROM)** variant of the
relativized design: keep most of v3 (digest relation, potential-form knowledge soundness,
step-counted extractor, completeness with error, Lean-checked certificate), replace "BLAKE2s
instantiates the oracle" by **a separate oracle service with a keyed BLAKE2s (a PRF) that also
signs the answers a proof used**, adopt the additive score `S = T_tree + K·t_link`
(`docs/DESIGN-cost-incentive-model.md`), use **GitHub Actions CI as the trusted machine** that
compiles everything and measures wall time, and let the **efficient prover be an x86-64 assembly
program** executed natively (agents write it in any language and submit the assembly). Keep the
trusted base minimal. Open a PR to `scaraven/recursion.fast`; then, through a separate
orchestrating agent, submit a **Flock-based baseline** to `scaraven/recursion.fast-submissions` and
use it as feedback on the rules.

## 1. Critical review of the request, and how each point is resolved

| # | Point | Resolution (orchestrator's decision; the user is away) |
|---|---|---|
| P1 | "The SROM idea from docs/" names two variants in the CGH guide: D3 (signed answers, checked in-circuit) and D4 (attested answers, an online membership query). The D4 proposal recommends D4 unless offline verification is needed. | **D3, the SROM, as asked.** Its decisive advantage here: every check the harness makes, and every check a third party makes later, is offline and stateless (`vk` is public), so there is no designated-verifier window, no key release, no `attest`/`certify` state machine, and records are transferable proofs. Cost: one hash-based signature check per child in-circuit (about 300–500 compressions). |
| P2 | "NP^h design" is not defined anywhere in the repository. | Read as `NP^H`, the relativized node relation (children accepted *relative to the oracle*). Under the SROM the relativization is carried by the signature: a child is accepted against a **signed trace** of oracle answers, so the relation itself never evaluates the oracle and is an ordinary relation given the public key. |
| P3 | "Use the CI as the trusted machine": which CI, and what hardware? | GitHub-hosted runners on the public repositories: `ubuntu-24.04`, x86-64, 4 vCPU, 16 GB RAM, 14 GB disk, 6 h per job, heterogeneous CPU models (AMD EPYC and Intel Xeon; carry-less multiply available; AVX-512 and GFNI not guaranteed). Consequences: (a) the benchmark shape must fit 16 GB; (b) `T_V` is calibrated **in the same job** against the organiser's chain checker on that runner; (c) every result records the CPU model; (d) comparisons for records are paired within one job (v3's ABBA rule); (e) the job time limit bounds the stream. Larger (paid) runners are not assumed. |
| P4 | "The prover is an assembly program": ISA, syntax, linking, libraries? | x86-64 Linux, GNU `as` syntax (AT&T or `.intel_syntax`), one or more `prover/*.s` files, linked by the harness with the runner image's pinned `gcc -static -pthread … -lm` (glibc static, libgcc). No other inputs to the build. Source in any language may sit beside it for readers (unbuilt). The binary must run on every CPU model the runners use (dispatch on `cpuid`); a `SIGILL` fails the run. |
| P5 | Does the Lean honest prover `P` go away? | **No.** Completeness is a theorem about a Lean `P` (V3-4); the assembly prover replaces only the native prover, which v3 already executed and measured without proof. |
| P6 | The Flock baseline: Flock is BLAKE3-oriented, not recursive, and its PCS (Ligerito in the list-decoding regime) has no Lean proof; a full knowledge-soundness certificate for it is research-scale. | The baseline orchestrator decides the scope, with this guidance: a certified entry is preferred (port what exists: the v3 `spartan-chain` entry's Lean, 16.7k lines, Spartan+Ligero over GF(2^64)); a Flock-style native prover in assembly; the harness's **provisional** status (§3, V4-15) lists an entry whose certificate is incomplete, runs its benchmark, and never ranks it. Its main product is feedback on the rules. |
| P7 | "<100/200 ms 2→1 recursion" was set against M4 Max figures. | The targets stay reference lines on the board (CM-7); on CI runners they are re-read in the runner's units once a recursive entry exists. `K` is a season parameter (§3). |
| P8 | Open decisions in the merged proposals (RU-1…6, CM-1…8, RR-n) | Taken in §3 with a one-line reason each; listed again in the design document for the user to reverse. |
| P9 | Process | Stages on branch `v4/srom-rules` (worktree `recursion.fast-v4`), each implemented by an Opus agent, then adversarially reviewed by a Fable agent and golfed by an Opus agent in parallel, then fixed; the orchestrator commits. One PR to `main` at the end. Pushing the branch and opening the PRs is authorised by the request. |

## 2. The design in one page

**Model (unchanged from v3).** The submitter proves, in the random-oracle model with v3's potential
`KState`, one-level knowledge soundness of their verifier `V` for the relation below, and
completeness with error of their Lean prover `P`, **for every public key `vk`**; the extractor is a
step-counted program (`XProg`, `Computes`, budget `B t`). The signer is not in the model.

**Relation.** A leaf digest commits to a BLAKE2s chain from a secret start (v3). A node digest
commits to two child digests; its witness is two **signed proofs** `(π, tr, σ)` each *accepted*:

```
acc vk c (π, tr, σ)  :=  |π| ≤ proofCap  ∧  (V vk c π).runSeq tr = some true  ∧  SigOk vk (traceDigest tr) σ
```

`runSeq tr` answers the program's `i`-th query from the `i`-th trace entry, and rejects on a
mismatch or when the trace runs out. `SigOk` is a contract-fixed hash-based signature check
(WOTS, `w = 4`, under a Merkle tree of height 16). Every hash in the relation is **public** BLAKE2s;
none is the oracle. So the relation is oracle-free given `vk`, completeness keeps v3's form, and a
node circuit proves the children's acceptance by hashing their traces and checking one signature
each, never by evaluating the oracle.

**Deployment.** The CI runner starts, per timed run, a **service** in its own uid holding a fresh
PRF key `k` and a fresh signing key `(sk, vk)`. It answers `query(q) = BLAKE2s-256 keyed by k`
(RFC 7693 keyed mode) and `sign(q₁…q_m)`, which computes the answers itself and returns them with a
signature on the digest of that trace. The prover (assembly, in a sandbox, another uid, no
network) can reach the service only through its socket. The harness checks every proof it is given
with the compiled `acc` (offline: no service needed), so does any third party later with the
published `vk`.

**Why it closes O-25.** Every CGH backdoor compares an oracle answer with a value the verifier
computes about the instantiation; with a secret key fixed after the verifier is frozen no such value
exists (PRF security). Composition across the tree is the straight-line argument of CGSY24 Thm 5.1:
on the run's one query log, the root's signed trace is genuine (unforgeability), so `V` accepts on
the log, `final` extracts children whose signed traces are genuine again, down to the leaves. The
paper bound: `Q·ε + Adv_PRF + Adv_EUF-CMA + BLAKE2s collisions`.

## 3. Decisions (V4-n)

| Id | Decision | Reason |
|---|---|---|
| V4-1 | v3's knowledge-soundness definition (potential `KState`, `logCap`, `errorCap`), completeness (`failProb`, `CompleteWithError`, `completenessCap`), extractor machine and budget are kept **verbatim**; `KS` and completeness are required `∀ vk`. | Minimal change; every v3 control carries over. `∀ vk` makes a verifier that trusts signatures uncertifiable (the theorem's adversary may hold `sk`). |
| V4-2 | The oracle is deployed as keyed BLAKE2s-256 (`PRF_k`, RFC 7693 keyed mode, 32-byte key, no tag on queries), behind a service; `k` fresh per service lifetime. `blake2sOracle`, `tagRO` and `Submission.Vb` are deleted. | CGH needs a public seed; the keyed mode differs from public BLAKE2s on every input. |
| V4-3 | SROM (D3), not D4: answers are certified by a contract-fixed **stateful hash-based signature** (WOTS `w = 4`, `ℓ = 133` chains, Merkle height `h = 16`, `vk` the Merkle root), fresh `(sk, vk)` per lifetime; the service signs the digest of a whole trace (hash-then-sign). | P1. Hash-based keeps V3-5 (no groups); BLAKE2s-based keeps one gadget for agents. `w = 4` minimises in-circuit cost (≈ 200 average chain hashes + 67 leaf compressions + 32 path compressions). |
| V4-4 | Sequential trace semantics (`runSeq`), not first-match lookup. | Linear for the harness; a node circuit walks the trace in order with no lookup argument. |
| V4-5 | No trace cap in the relation. Injectivity of the trace encoding needs `|q| < 2^64`, which holds for every trace the composition argument touches (extracted witnesses decode from 64-bit length words; the root's trace is a file). The harness caps file sizes. | Minimal trusted base; argued in the design. |
| V4-6 | `E` does not take `vk`; `V` and `P` do. The extractor tape is v3's. | A node extractor decodes children from the node proof's committed witness; it never needs `vk`. |
| V4-7 | The harness's one check is the compiled `acc vk c p` (root, samples, canaries, every stream output). Root proofs are signed proofs. | One trusted predicate for the node clause, the harness and third parties. |
| V4-8 | Composition: a Library theorem (untrusted, kernel-checked) that walks the harness tree and returns the leaf starts, a BLAKE2s collision, or an explicit **forgery** (a valid signature on a trace not contained in the log); the probability of the last outcome is the paper reduction to EUF-CMA. | Kernel content for CGSY24's argument; only the probabilistic reductions stay on paper. |
| V4-9 | The prover is x86-64 assembly (P4); the Lean `P` stays (P5). | The request. |
| V4-10 | Score `S = T_tree + K·t_link` (CM-1, CM-4 mean link time, 1→1 links and higher arity counted); `K = 20` provisional for season 1 (CM-2, recomputed from the leader per season); targets 100/200 ms are reference lines (CM-7); a fresh process per stream request, untimed start-up (CM-6). | The cost-model proposal as written; its open values set to its own illustration. |
| V4-11 | Season-1 shape on CI (CM-3, CM-5): tree `r = 6`, `n = 2^18` (64 leaves, `2^24` compressions; a `2^20`-step leaf does not fit 16 GB for a Flock-class prover); stream `M = 512`, `n_f = 2^16`. All shape values live in one season file; the CI smoke uses `r = 2`, `n = 16`, `M = 4`. | 16 GB runners; same total chain work as the long shape. |
| V4-12 | `T_V`: CPU time of one `acc` check on one pinned core ≤ `T_triv,best / R`, `R = 10` (CM-8), with `T_triv,best` measured in the same job by the organiser's interleaved compiled-Lean chain checker over the tree's chains. Applies to the root, samples and every stream output. | C6; self-calibrating on heterogeneous runners. |
| V4-13 | Caps kept from v3: `proofCap = 1 MiB` on `π` (not on the trace or signature), `qV ≤ 2^16`, `errorCap = completenessCap = 2^-128`, `logCap = 2^96`, `B t`, `outCap`, `progCap`, `chainCap = 2^20`. Memory: the runner's (cgroup cap 13 GB for the prover and service together). | Minimal change. |
| V4-14 | D4+ (oracle-chain leaf), W5 (channel split) and W4 (key release) are **not** adopted: the leaf stays a public chain; every oracle query, Merkle hashes included, goes to the service; nothing is released (signed proofs are already transferable). | No extractability heuristic; W5 recorded as the optimisation if service traffic dominates. |
| V4-15 | **Provisional** listing: an entry whose Lean builds but whose certificate does not check (a `sorry`, a failed gate) may still be benchmarked; it is published as PROVISIONAL and never ranked or recorded. | Lets real entries (the Flock baseline) be measured before their proofs are done; changes nothing about ranked records. |
| V4-16 | The tree is unchanged (`treeRoot`); the leaf clause, `chainCap`, `leafStmt`, `nodeStmt`, tags `C`, `L`, `N` unchanged; new tags `T` (trace), `W` (WOTS chain), `K` (WOTS leaf key), `M` (signature Merkle node). | Distinct first bytes for every contract hash input. |

## 4. Normative interfaces (stages A and B build against these)

### 4.1 Lean (trusted contract; names may be adjusted by stage A, semantics may not)

```lean
abbrev Trace := List (ByteArray × Digest)              -- (query, answer) in the order asked
structure Sig where
  idx  : ℕ              -- one-time key index, < 2^sigHeight
  ots  : List Digest    -- wotsLen = 133 chain values
  path : List Digest    -- sigHeight = 16 siblings, leaf level first
structure Signed where
  π : Proof
  tr : Trace
  σ : Sig
inductive Wit | leaf (s : Digest) (n : ℕ) | node (c₁ c₂ : Digest) (p₁ p₂ : Signed)
def Rel (acc : Digest → Signed → Bool) : Digest → Wit → Prop
  | c, .leaf s n         => n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n
  | c, .node c₁ c₂ p₁ p₂ => c = nodeStmt c₁ c₂ ∧ acc c₁ p₁ = true ∧ acc c₂ p₂ = true

def OProg.runSeq : Trace → OProg α → Option α
  | _, .ret a => some a
  | (q', a) :: tr, .query q k => if q' = q then runSeq tr (k a) else none
  | [], .query _ _ => none

structure Submission where
  V : Digest → Digest → Proof → OProg Bool        -- vk, statement, proof
  P : Digest → Digest → Wit → OProg Proof         -- vk, statement, witness
  E : Digest → Proof → Log → Option Wit
  ext : XProg ; ε δ : ℝ≥0 ; qV : ℕ ; fuel : ℕ → ℕ
def Submission.acc (S) (vk c : Digest) (p : Signed) : Bool :=
  p.π.size ≤ proofCap && (S.V vk c p.π).runSeq p.tr == some true && SigOk vk (traceDigest p.tr) p.σ
structure Certificate (S) : Prop where
  secure   : ∀ vk, KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV
  complete : ∀ vk, CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) S.δ
  computes : Computes S.ext S.E S.fuel        -- decodeWit extended to signed children
  cap      : (v3's caps)
```

### 4.2 Byte layouts (normative; the service, the Lean contract and the runner agree byte for byte)

- `enc64 n`: 8 bytes little-endian of `n mod 2^64` (v3).
- `traceDigest tr = BLAKE2s-256(0x54 ‖ item₀ ‖ item₁ ‖ …)`, `itemᵢ = enc64 |qᵢ| ‖ qᵢ ‖ aᵢ`.
- WOTS digits of a 32-byte message `m`: for byte `i` (0…31), digits `4i+t = (m[i] >> 2t) & 3`,
  `t = 0…3` (128 digits); checksum `C = Σ (3 − dᵢ)` over those 128 (≤ 384); digits
  `128 + t = (C >> 2t) & 3`, `t = 0…4`. `ℓ = 133`.
- Chain step: `F(j, i, s, x) = BLAKE2s-256(0x57 ‖ enc64 j ‖ byte i ‖ byte s ‖ x)` (43 bytes),
  `j` the key index, `i < 133` the chain, `s ∈ {0,1,2}` the step taken from position `s` to `s+1`.
- Secret chain start `skᵢ` (service only): any secret derivation; the reference is
  `BLAKE2s-256 keyed by the signing seed of (enc64 j ‖ byte i)`.
- Signature of `m` with key `j`: `ots[i] = F` applied for `s = 0 … dᵢ − 1` to `skᵢ`.
- Verification: `endᵢ = F` applied for `s = dᵢ … 2` to `ots[i]`;
  `leaf = BLAKE2s-256(0x4B ‖ enc64 j ‖ end₀ ‖ … ‖ end₁₃₂)` (4,265 bytes);
  Merkle node `= BLAKE2s-256(0x4D ‖ left ‖ right)`; at level `t = 0…15` the current value is the
  left child iff bit `t` of `j` is `0`, with `path[t]` the sibling; `SigOk` iff `j < 2^16`,
  `|ots| = 133`, `|path| = 16` and the computed root equals `vk`.
- `vk` is the Merkle root over the leaves `j = 0 … 2^16 − 1`.

### 4.3 The service (trusted runtime; stage B fixes the wire format and documents it)

One process per timed run, own uid, `k` and the signing seed from `getrandom`, never written to
disk, destroyed at exit. Operations: `query` (a batch of byte strings → their `PRF_k` answers);
`sign` (a batch of byte strings → their answers and a signature on the trace digest; refuses after
`2^16` signatures); `vk`. Every request is a batch so a prover amortises the round trip. In
liveness mode it also writes its full query log (every `query` and every query `sign` evaluated)
for the extractor check. It runs on the same CPUs as the prover (no free co-processor) and is
tested against Python `hashlib.blake2s(key=…)` and against the compiled Lean `SigOk`.

### 4.4 The prover (untrusted, x86-64 assembly)

`PROVER tree DIR`, `PROVER leaf DIR`, `PROVER node DIR` as in v3 and the cost model, plus
`DIR/vk.hex` and the service socket path in `RF_ORACLE`. Every output is a **signed proof file**
(format fixed by stage B: `π`, `tr`, `σ`, length-prefixed). The ready handshake of the cost model
applies to `leaf` and `node`.

## 5. Stages

| Stage | Owner | Content | Done when |
|---|---|---|---|
| A, contract | Opus | v3 contract ported and changed per §3–§4 (`RecursionFast/Contract/`); Library (paper theorem, witness-sending entry under v4, `runSeq → runLog` lemma, Lean reference signer with `sign → SigOk` theorem, composition theorem V4-8); Controls (positive and negative for every trusted definition, the backdoor ported and shown certified in the model); `scripts/loc.py` ≤ 500 | `lake build` green, axiom audit clean, RESULT written |
| B, harness | Opus | Rust service; Python runner (sandbox, assembly build, tree, stream, `acc` badge, canaries, `T_V` calibration, liveness, DoS, score JSON, season file); gate/source rule/axiom audit ported; CI workflows (core CI; the evaluation workflow the submissions repository calls); an end-to-end smoke with the witness-sending entry and a toy assembly prover | the smoke passes locally and in a CI-equivalent sandbox; RESULT written |
| C, attack | Fable | adversarial review of the design (this brief) in parallel with A/B: backdoors under the SROM, the composition argument, the signature's security model, sandbox and CI isolation, the assembly route, the score under signing | findings file |
| D, document | Opus | `docs/DESIGN-v4-srom.md` (normative, for cryptographers and zkVM engineers), `README.md`, `CLAUDE.md`, `docs/README.md` | reviewed with A/B |
| R, review + golf | Fable + Opus | adversarial review of A+B+D (skill `adversarial-review`, `lean4:review`); golf of proofs (`lean4:golf`) and of run time (service, runner, badge) | findings fixed or answered |
| PR | orchestrator | push `v4/srom-rules`, open the PR | — |
| F, baseline | separate Opus orchestrator | Flock-based entry in the submissions repository with its own subagents; feedback report on the rules | PR opened; feedback folded back |

## 5a. Amendments after the design attack (stage C, `docs/v4/reviews/C-design-attack.md`)

All four majors and the minors are adopted; these override §3–§4 where they differ.

| Id | Amendment | From |
|---|---|---|
| V4-A1 | **Trust anchor.** Evaluation runs only from an organiser-controlled workflow definition (`pull_request_target` gated by a maintainer label, or `workflow_dispatch` with a PR number), `permissions` minimal, `persist-credentials: false`, the fork fetched by SHA into a directory that is executed **only inside the sandbox** (the Lean build, gate and axiom audit included, not only the prover), the environment cleared for every untrusted process. The result JSON (with `vk`, CPU model, runner image, harness commit, service binary hash) is signed with GitHub artifact attestations; a record is accepted only if `gh attestation verify --signer-workflow scaraven/recursion.fast-submissions/.github/workflows/<eval>.yml` (or the core's reusable workflow) passes. Maintainer approval of first-time contributors is compute admission, not a verdict. | C-M1, C-m7, C-m13 |
| V4-A2 | **Certificate job and benchmark job are separate.** The certificate job (source rule, build, kernel check, gate, axiom audit) is deterministic and may run on any runner with a cached package tree; only the benchmark job must be the GitHub-hosted runner. The Lean kernel is mandatory; the second kernel (nanoda) runs where it fits and its absence is stated in the result. Caps for the build are set from a measurement on a runner, recorded in `logs/`. | C-M2 |
| V4-A3 | **Exact trace consumption and a query cap.** `runSeq [] (.ret a) = some a`, `runSeq (_ :: _) (.ret _) = none`; `acc` also requires `∀ e ∈ tr, e.1.size ≤ queryCap` with `queryCap = 2^20` (the service's cap). The signed trace is then exactly the verifier's query sequence; `traceDigest` is injective on accepted traces by a relation-internal fact; V4-5 is withdrawn. `acc`'s conjuncts are ordered cheapest-rejection first: size cap, query cap, `SigOk`, then `runSeq`. Sharing one signature between two children remains possible only through dummy queries counted in `qV`; cost statements per child are upper bounds. | C-M3, C-m5 |
| V4-A4 | **Signature: the theorem and key separation.** No public seed (the scheme stays as §4.2). The design document states EUF-CMA of this exact variant from (i) collision resistance of tagged BLAKE2s, (ii) multi-target one-wayness of `F(j,i,s,·)`, (iii) PRF security of keyed BLAKE2s for the chain starts, plus the operational conditions; keyed BLAKE2s as a PRF is named as the design's one idealised assumption about BLAKE2s (its analysis, LMN16, is in an ideal-cipher model). The PRF key `k` and the signing seed are **independent** draws; the chain start is `BLAKE2s-256 keyed by the seed of (0x53 ‖ enc64 j ‖ byte i)` (tag `S`); separation from the oracle comes from the **independence of the two keys**, not from the tag (oracle queries are untagged, so `0x53 ‖ …` is itself a legal query; correction by stage D); the index is assigned under one lock and committed before the signature is returned; a restart is a new key and aborts the run. The Lean reference signer is the specification the service is tested against, derivation included. | C-M4 |
| V4-A5 | **Service.** No answer memoisation (a timing channel across stream requests); explicit caps on query bytes, batch items and bytes, connections, each refused as an error that aborts the proof as a reject; `oom_score_adj` so the prover is killed before the service; the empty-message keyed vector tested; `sign` re-evaluates every query (one extra PRF per query, documented for provers); the service's measured calls/s and compressions/s are published in each result as a calibration column, like `T_triv,best`. | C-m2, C-m4, C-m8 |
| V4-A6 | **Assembly build inside the sandbox** (`.incbin`/`.include` can read any file the builder can); image version, `gcc`/`as` versions and the binary's hash recorded; seccomp deny-list for the prover; the AppArmor user-namespace restriction on Ubuntu 24.04 handled explicitly in the workflow. | C-m7 |
| V4-A7 | **Controls and Library** (stage A): the "no certified `V` trusts a signature" impossibility as a Library theorem/control (`sigTrust_kstate_iff` shape); the node-clause positive control built with the Lean reference signer, proved symbolically; negatives: a child signed under another key, a changed answer, `|ots| ≠ 133`, a malformed trace length in `decodeWit`; the badge path uses a word-level BLAKE2s twin proved equal to the contract's. | C-m1, C-m3, C-m11, C-m12 |
| V4-A8 | **Design document must state**: the impossibility of C-m1 as the answer to O-25 §6.7's rule; that a published `vk` certifies relative to the organiser's key management (bound into the attested result); that `E` without `vk` restricts nothing (a design may put `vk` in `π`); that no certified entry can yet run the season-1 shape (the ranked path is exercised end to end at the smoke shape only); that the composition's split of the "forgery" outcome into EUF-CMA forgery or collision is paper; the in-circuit trace-hash cost (about 1.6× a public-hash Merkle step per 64-byte preimage, on top of the signature). | C-m6, C-m9, C-m10, §2 item 4, unsettled 4 |

## 5b. Amendment V4-A9: the trim (the user's decisions of 2026-10-26)

The user cut every check and step that serves neither goal: (a) agents submit valid, sound
verifier designs; (b) fast hash-chain proving with honestly priced recursion and minimal cheating.
These override §3–§4, V4-A1 … A8 and the stage B harness where they differ; the design's §4.4 says
what each remaining rule is for. Implemented in stage D-trim (`docs/v4/stages/D-trim-RESULT.md`).

| Item | Decision | Reason |
|---|---|---|
| 1 | **Every GitHub job at most 30 minutes**, the caps inside each nested below it: certificate job build 10 min, kernel 10 min, gate 2 min, badge 3 min; prover build 5 min, setup 5 min, tree run 10 min, stream 15 min (a hard deadline, checks included), one stream request 60 s, one `acc` check 10 s, DoS column 3 min. The organiser's setup (package tree, build, manifest, comparator, service) is cached per core commit by its own job, which never fetches the entry. The caps bind entries: their Lean must build and check within them on a 4-vCPU runner | a slow or hung entry must end as its REJECT with a reason, not as a killed job (a missing part, ERROR); a cache miss must never cost an entry's time; runners are not held for hours |
| 2 | **One run of the tree and one of the stream; no repeats, no medians.** Two parallel benchmark jobs: (calibration, tree, DoS) and (calibration, stream) | records are decided by the paired comparison anyway |
| 3 | **Stream `M = 512 → 256`** (`n_f = 2^16`) | the stream fits its cap; the escaped tail grows from about 4.7% to about 9.4% of the merges (`c ≈ 2^24 / (R · n_f) ≈ 25`) |
| 4 | **No per-entry liveness** (the badge's `liveness`, the service's logging mode); the core CI runs the compiled extractor interpreter on the library's witness-sending entry | the extractor's correctness and cost are the kernel-checked `Computes` |
| 5 | **Canaries**: the non-malleability canaries `pi±1` dropped; the canaries that never reach the entry's `V` (`file±1`, `trace-answer`, `trace-query`, `trace-extra`, `sig-ots`, `sig-idx`) move to the core CI; per entry only `stmt-bit` and `swapped-child`, on 2 proofs per kind | non-malleability is required by nothing and can reject a sound entry; the others test organiser code |
| 6 | **DoS column: 100 inputs**; it fails only on time (an input above 10 × `T_V`, the column above its cap) and on a crash of the checker; an accepted input is recorded. A crafted-input column (FB-5) is a follow-up | an accepted mutation of a true statement's proof is malleability (item 5); random inputs never found a slow input |
| 7 | **Only the tree's root is read and checked**; inner proofs, if written, are ignored; the statement canaries run on the root and on stream outputs | the root's certificate covers its children; the stream prices recursion |
| 8 | **`completenessCap = 2^-128 → 2^-40`** | a completeness failure only costs its entrant a run: about 640 proofs per evaluation at `2^-40` each fail a run with probability about `2^-30.7` |
| 9 | **One Lean build** instead of the byte-identical rebuild: the comparator, the gate and the badge use the build the kernel's exports were made from | the binding (the badge runs code compiled from exactly the checked modules) holds without a second build; it saved 173 s on the baseline |
| 10 | **`errorCap = 2^-128 → 2^-120`** per fresh query; `logCap = 2^96` unchanged | admits GF(2^128) designs such as Flock (a degree-2 sumcheck round costs `2^-127`, the univariate-skip round `126/2^128 ≈ 2^-121`; FB-9), and keeps the whole-run bound negligible (about `2^-90` at `2^30` queries) |
| 11 | **The submission pipeline and the organiser's CI are separate**: every check whose subject is organiser code (`acc` before `V`, the file parser, the service, the sandbox, the badge template, the compiled extractor interpreter, the harness) runs only in the core repository's `ci.yml`; an evaluation runs only what is about the entry, plus the environment it runs in (the package tree and its manifest check, the comparator, the service, `T_triv,best`) | each check runs once per harness commit where its subject changes, not once per entry |

## 6. Conventions for every agent

- Work only in `/home/devops/Verified-zkEVM/recursion.fast-v4` (branch `v4/srom-rules`); never in
  the main checkout, `recursion.fast-rules` or `recursion.fast-design`. Do not commit or push; the
  orchestrator does.
- `.lake/packages` is a symlink to a shared, read-only, prebuilt tree: never `lake update`, never
  `lake exe cache get` there, never edit `[[require]]` or the manifest.
- Every build or probe that may run long gets a `timeout`; if a build runs unusually long, inspect
  it (`ps -o etime`), find the cause, kill and fix it. Logs go under `logs/` (gitignored).
- Hard rules: axioms `propext`, `Classical.choice`, `Quot.sound` only; no `sorry` (except where a
  stage explicitly allows a provisional entry), no `native_decide`, no code-changing attributes, no
  `unsafe`/`partial`/`opaque`; positive and negative control for every trusted definition; a proof
  never changes the statement it proves; every trusted definition has a docstring saying what it
  means.
- Kernel evaluation of BLAKE2s costs about 2.4 s per compression: controls evaluate few hashes;
  prove properties symbolically instead.
- No time estimates; measured durations are quoted with their log.
- Keep finding and decision ids (V3-n, O-n, RR-n, CM-n, V4-n) when quoting.
