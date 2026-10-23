# Stage C: adversarial review of the v4 (SROM) design

Status: findings against `docs/v4/BRIEF.md` (commit `191baec`), written while stages A and B were
being implemented; nothing here has been checked against stage A's Lean or stage B's code. Each
finding names the claim attacked, the attack or counterexample, its evidence tag (**paper** for an
argument written here, **probe** for a kernel-checked Lean file under `logs/c-probes/`, **literature**
with a link, **measurement** for a number quoted from the record), the fix and its cost. Ids: `C-Mn`
major (the design is wrong or a guarantee fails without a fix), `C-mn` minor.

Probe: `logs/c-probes/C1_runSeq.lean`, run with `timeout 300 lake env lean` on the worktree's
toolchain (Lean v4.34.1), log `logs/c-probes/C1_runSeq.log`; every theorem with axioms
`[propext, Quot.sound]`. It transcribes `runSeq` and `runLog` from BRIEF §4.1 in core Lean.

---

## 0. Summary of the attack

The SROM core survives. I could not build an acceptance backdoor: with knowledge soundness and
completeness required **for every `vk`** against a **computationally unbounded** ROM adversary
(V4-1), a signature carries no information inside the theorem, so any verifier whose acceptance of
a false statement rests on a `vk`-valid signature, on knowledge of `sk`, or on a match between an
oracle answer and a signed value in the proof has no knowledge state below `ε = 1` (§1, stated as
an impossibility, C-m1). The composition argument of §2/V4-8 is sound in outline and I confirmed
its one non-trivial lemma (`runSeq → runLog`) in the kernel (probe). The design fails, as written,
in four places outside the core: the trusted machine has no trust anchor (C-M1); the certificate
check does not fit the machine (C-M2); the trace is uncapped and suffix-tolerant, which breaks the
completeness story for a fixed-circuit node prover and the cost accounting (C-M3); and the
signature scheme is a variant nobody has proved, with a key-separation hazard in the reference
derivation (C-M4).

---

## 1. CGH and its disguises under the SROM

**Claim attacked** (BRIEF §2 "Why it closes O-25"; V4-1, V4-2): no certified `V` can recognise
the deployment.

**What a certified `V` can see.** `V vk c π` receives `vk`, `c`, `π` and the oracle answers it
asks for. The adversary (the prover) can put into `π` anything it has: PRF answers it queried,
signed traces `(tr', σ')` from the service for any queries it chose (V4-3 `sign` signs digests of
prover-chosen traces), `vk`, chain values of signatures (the WOTS `ots` entries are
`F`-images of secret chain starts). The recognition sites of O-25 §3 need a value about the
instantiation that reached `V` *not* through a query. I checked each channel:

| Channel | Does it carry a value about `PRF_k`? | Why the certificate catches a `V` that uses it |
|---|---|---|
| the empty query, or any query | yes, `PRF_k(q)`, but only through a query | through the oracle: the ROM adversary queries first, the answer is in the log, `final` must extract (O-25 §2) |
| `vk` | no: a Merkle root of `F`-images of the signing seed, independent of `k` if the two keys are independent (C-M4 if they are not) | a branch on `vk = vk*` is uncertifiable under `∀ vk` |
| a signed trace in `π` whose answer `V` compares with the oracle's | in deployment, yes (both are `PRF_k(q)`) | the ROM adversary is **unbounded**: it forges `σ'` for whatever answer the oracle gave, so the branch fires on every log; `final` then needs a witness for a false `c`, none exists within `Computes`' budget (`enum_no_computes`), so no `KState` exists below `ε = 1` |
| `sk` or a WOTS secret in `π` | no information about `k`; but the attempt "accept if `π` proves knowledge of `sk`" | the theorem's adversary may hold `sk` (V4-1's reason); same as the row above |
| the post-hoc challenge verification (O-25 §6.1) with BLAKE2s wires | the wires would have to compute keyed BLAKE2s with `k`, or with the chaining state after the key block; neither leaves the service (the empty query's answer is the *finalised* key block, `f0` set, not the chaining state) | in deployment the identity never holds; in the ROM it is `2^-192` as before, so the branch is dead, not a backdoor |
| the post-hoc attack with a **signed trace** as the "wires" | in deployment `c₁ = tr'(prefix₁)` always | unbounded adversary forges `σ'`: fires on every log, uncertifiable (row 3) |
| the sequential trace (`runSeq`) | the trace only feeds `V`'s own answers; `V` is the same program in both worlds | nothing new |
| the liveness mirror (reject honest proofs on the deployment) | needs a recognition site; none; a `vk`-conditional rejection violates `∀ vk` completeness | uncertifiable; and harms only its author |
| cross-run, cross-entry, key reuse | `vk` and `k` fresh per lifetime (V4-2, V4-3); a record publishes `vk` and the root's trace, which reveals `PRF_k` on the root's queries after `k` is destroyed | nothing to reuse; see C-m9 for what a published `vk` does mean |
| the service's `sign` on traces that are not a verifier's trace | gives signatures on genuine answers; in the SROM these are available to everyone | harmless; the queries land in the log and count in `Q` |

**Impossibility (paper, C-m1 asks to record it).** Let `V` be any verifier and `B` a branch of `V`
whose acceptance of some `(c, π)` with `c` outside the language depends on a predicate `Φ(vk, π,
answers)` that an unbounded adversary with oracle access can make true for every oracle (a
signature check under `vk`, a check that `π` contains `sk`, a comparison of an answer with a
signed value). Then `KS (Rel (acc vk)) (V vk) E ε qV` holds only at `ε ≥ 1` for that `vk`: on every
log `L` of the adversary's queries, `(V vk c π).runLog L = some true`, so `final` needs `E c π L =
some w ∧ Rel c w`, impossible for `c` outside the language, so `μ L ≥ 1` on every reachable `L`,
and `step` from `μ [] = 0` forces `ε ≥ 1`. This is exactly why V4-1's `∀ vk` and the unbounded
adversary are load-bearing: **a certified `V` can never trust a signature**; only the contract's
`acc` does, and `acc` never sees the oracle. The brief says this in one clause of V4-1; the design
document should state it as the theorem it is, since it replaces O-25 §6.7's rule.

**Verdict on §1.** No acceptance backdoor found. The residual is the deployment argument
(PRF hybrid), which is a paper reduction as in the D4 proposal §4.9; see C-M4 for the signature's
part of it.

---

## 2. The composition argument (BRIEF §2, V4-8)

**Claim attacked.** On the run's one log, the root's signed trace is genuine, `V` accepts on the
log, `final` extracts children whose traces are genuine again, down to the leaves; bound
`Q·ε + Adv_PRF + Adv_EUF-CMA + Adv_CR`.

**Checked and confirmed (paper, probe).**

1. **Signer as a query algorithm.** The deployed prover plus the signer holding `sk` is one
   query algorithm; the kernel `paper` theorem quantifies over every deterministic adversary of at
   most `logCap` queries, randomisation by averaging as in v3. `Q` must count the signer's
   re-evaluation of every trace it signs (BRIEF §4.3 says it does); at the season shape `Q` is
   about `2^28–2^30`, far below `logCap = 2^96` and the `Computes` domain of about `2^61` entries.
2. **`runSeq → runLog`** (probe `runSeq_runLog`): if every entry of the consumed trace is the
   log's first match for its query, a sequential verdict is the log verdict. The hypothesis holds
   for service-signed traces because the service computed each answer by a query, and the lazily
   sampled oracle of the kernel theorem has one entry per query.
3. **`final` level by level with the same `L` and the same `μ`** needs only `μ L < 1` once; this is
   CGSY24 Thm 5.1's structure (one extractor run per node on the whole transcript, no factor per
   node; `docs/reference/papers/CGSY24…pdf` §5, `s' = s + O(N·t_ARG)`) and D4's kernel
   `compose`. The signed trace replaces CGSY24's `VerifyTrace^f` (Def. 5.3, split verification) by
   a signature, which is the SROM move (§2.2, §6.2 of the paper).
4. **Forgery vs collision.** An extracted `(trᵢ, σᵢ)` with `SigOk` whose entries are not all in `L`:
   either the service signed some `tr'` with `traceDigest tr' = traceDigest trᵢ`, and `tr' ≠ trᵢ`
   since `tr'` is in `L`, a collision of two distinct encodings once both have `|q| < 2^64`
   (V4-5's domain argument holds for extracted traces by `decodeWit`'s 64-bit length words and for
   signed traces by the service's wire cap); or no signed trace has that digest, an EUF-CMA
   forgery. The reduction to EUF-CMA runs the evaluation and the walk, about `2^58` steps (D4
   §4.9 fine print), against a scheme with 200+ bits of margin.
5. **Fiore–Nitulescu** ([ePrint 2016/112](https://eprint.iacr.org/2016/112)) does not bite: their
   counterexamples are for black-box extractors that cannot see the signing oracle's answers;
   here the signatures a node needs are committed in the node's witness and decoded from the
   log by a straightline extractor, and the signer's own queries are in the same log.
6. **Completeness `∀ c w, Rel c w → …`** is meaningful because the relation is oracle-free given
   `vk`: the game samples a fresh oracle only for `P`'s and `V`'s own queries, and a node witness
   carries its children's signatures as data. This is better than D4's log-dependent relation,
   which needed honest contexts. (But see C-M3 for what the uncapped witness space costs.)
7. **`∀ vk` is the right quantifier** (§1). `E` not taking `vk` (V4-6) is harmless: a prover whose
   commitment encoding depends on `vk` puts `vk` in `π` (C-m6).
8. **The PRF hybrid with a signer.** The distinguisher samples `(sk, vk)` itself, runs the
   evaluation and the walk with the challenge oracle, outputs "bad". It needs `k` and the
   signing seed to be **independent**: if they are not (C-M4), the hybrid is not a PRF game.

**Not confirmed, open.** Whether the whole-tree walk's third outcome is stated as the right
object: "a valid signature on a trace not contained in the log" is what the kernel can return; the
reduction then splits it into collision or forgery on paper (item 4). The design document must
say this split is paper, not kernel.

---

## 3. Findings

### C-M1. The trusted machine has no trust anchor: nothing in the design says which workflow definition produces the result, or stops the submission from producing it

**Claim attacked.** P3, V4-7, V4-11, V4-12, stage B: "GitHub Actions CI as the trusted machine that
compiles everything and measures wall time"; "the evaluation workflow the submissions repository
calls".

**Attack (paper, literature).** An entry arrives as a pull request from a fork of the submissions
repository. Three ways to run it, each broken as the brief stands:

- Under the `pull_request` event the workflow file that runs is **the pull request's own**. The
  submitter edits `.github/workflows/eval.yml` in the PR to print a score JSON of its choosing, or
  to call the organiser's reusable workflow with a doctored harness path. The job has a read-only
  token and no secrets, so GitHub considers this safe for GitHub, but the *result* is the
  submitter's. Nothing in the brief says how a maintainer or a third party tells the organiser's
  harness output from a forgery.
- Under `pull_request_target` the base repository's workflow runs, with the base's `GITHUB_TOKEN`,
  secrets and cache; checking out and executing the fork's code there is the classic pwn request
  (GitHub's secure-use guidance: "Workflows that use these triggers must not explicitly check out
  untrusted code, including from pull request forks"), and since June 2026 `actions/checkout` v7
  **refuses** the fork checkout by default in `pull_request_target` and in `workflow_run` runs
  triggered by a pull request, with an explicit `allow-unsafe-pr-checkout` opt-out
  ([changelog 2026-06-18](https://github.blog/changelog/2026-06-18-safer-pull_request_target-defaults-for-github-actions-checkout),
  [secure use](https://docs.github.com/en/actions/reference/security/secure-use)).
- The entry's **Lean build is code execution**: `lake build` runs the submission's lakefile and
  elaborates its files; macros, `#eval`, `initialize` and Lake scripts run arbitrary code as the
  job user, outside any sandbox, before the gate, the source rule or the axiom audit see the
  entry. The same holds for the stage-B smoke. v3 sandboxed only the native prover's build.

**Consequence.** A published record is a JSON file plus a job log. Without an anchor binding
that JSON to *the organiser's* workflow at a known commit, running on a GitHub-hosted runner, the
leaderboard trusts the submitter.

**Fix.** (a) Evaluation runs only from an organiser-controlled definition: `workflow_dispatch` or a
`push` to a staging branch after a maintainer labels the PR, or `pull_request_target` with the
fork checked out by commit SHA into a directory that is **never executed outside the sandbox**,
`permissions: {}` (read-only `contents`), `persist-credentials: false`, no secrets in the job, and
the opt-out flag documented as a deliberate decision. (b) **Attest the result**: the evaluation
job signs its result JSON (and `vk`, the CPU model, the image version, the harness commit) with
[artifact attestations](https://cli.github.com/manual/gh_attestation_verify); records are accepted
only when `gh attestation verify --signer-workflow scaraven/recursion.fast/.github/workflows/eval.yml`
passes, which rejects a fork's copy of the workflow (its `job_workflow_ref` differs). (c) The
entry's `lake build`, gate and axiom audit run **inside the same bwrap sandbox** as the prover's
build (read-only toolchain, no network after the cache is in place), and the harness reads only
their declared outputs. (d) First-time contributors' workflows already require maintainer
approval on public repositories; say so, and say that it is a compute-admission step, not a
verdict step (criterion 3 of O-25 §11 is about the verdict).

**Cost.** Zero trusted Lean lines; stage-B workflow text; one attestation step per job; a
verification command in the record rule.

### C-M2. The certificate check does not fit the trusted machine as specified; "CI as the trusted machine" is established for the benchmark half only

**Claim attacked.** P3 ("the benchmark shape must fit 16 GB"), stage B ("gate/source rule/axiom
audit ported; CI workflows"), V4-13 ("caps kept from v3").

**Attack (measurement, from the record).** The v3 harness chain is `lake build` of the entry
(cap ≤ 1 h, **≤ 48 GB**, v3 §8.6), the second kernel nanoda (**52 GB** on one field lemma,
proposed cap 16 GB, v3 §8.6 and §15.4), the comparator, the gate and the axiom audit. The runner
has 16 GB RAM and **14 GB** of SSD, and the pinned toolchain is Mathlib v4.34.1 plus CompPoly,
ArkLib, VCVio and PolyFun: Mathlib's oleans alone are several GB from `lake exe cache get`;
ArkLib, VCVio and CompPoly have no cache and build from source, hours on 4 vCPU. The honest v3
entry is 16.7k Lean lines over CompPoly's field. No number in the brief shows that any certified
entry's `lake build` plus a second kernel completes on this machine, and the record's one data
point (nanoda at 52 GB) says it does not. Criterion 10 of O-25 §11 ("built against a real entry
first") is exactly the test that has not been run.

**Consequence.** Either the ranked path has no second kernel and a looser build cap (a change of
the trusted toolchain rules, C10), or no real entry can be certified on CI and the trusted machine
is only the benchmark's.

**Fix.** Split the evaluation into a **certificate job** and a **benchmark job**; the certificate
job is deterministic and may run anywhere reproducible (a larger self-hosted or paid runner, or a
published container image with the prebuilt pinned package tree), while only the benchmark job
must be the GitHub-hosted runner. Before stage B fixes any cap: run the v3 honest entry's
`lake build` and nanoda on `ubuntu-24.04` with the pinned tree restored from `actions/cache`
and record peak RSS, disk and time under `logs/`. Set the build and nanoda caps from that
measurement; if nanoda cannot be made to fit, say in the design that the second kernel is
dropped for CI and why (v3 §15.4's lesson becomes a stated risk).

**Cost.** Zero trusted lines; a second workflow; a container image or cache the organiser
publishes; a measured number before the rules are frozen.

### C-M3. The trace is uncapped and suffix-tolerant: the honest node prover is not complete without a fallback branch, V4-5's injectivity argument lives outside the relation, and "one signature per child" is not what the relation requires

**Claim attacked.** V4-4 (`runSeq`), V4-5 ("no trace cap in the relation"), §2 ("completeness
keeps v3's form"), V4-3 and P1 ("one hash-based signature check per child").

**Attack (probe, paper).**

1. `runSeq` ignores trailing entries: `runSeq tr (.ret a) = some a` for every `tr`
   (probe `ret_ignores_trace`), and a verdict read from `tr` is read from `tr ++ junk` for every
   `junk` (probe `runSeq_append`). So the set of signed proofs `acc` accepts for one `(c, π)` is
   infinite in a new dimension: every `(π, tr ++ junk, σ')` with `σ'` a service signature on the
   padded trace, and the service signs any trace on request. Each of them is a child witness in
   `Rel`, and `CompleteWithError` is `∀ c w, Rel c w → …`: the honest `P` must prove **every** such
   node witness, including one whose child trace is gigabytes of junk that `P` cannot truncate
   (truncation changes `traceDigest`, and the theorem's `P` has no signer). A fixed-size node
   circuit cannot hash an unbounded trace, so `P` needs a fallback branch of `V` (a
   witness-sending node) for oversized witnesses, which the liveness rule (#9 item 1) then has to
   police. v3 did not have this problem because child proofs were bounded by `proofCap`; the
   D4 proposal had it and bounded lists in `Valid` (RR-4, D4 §4.3); V4-5 dropped the cap citing
   the trusted budget without the completeness analysis.
2. `|q|` is uncapped in the relation. V4-5's injectivity argument ("every trace the composition
   touches has `|q| < 2^64`") is true of *extracted* and *signed* traces but is a property of
   `decodeWit` and of the service's wire format, not of `Rel`: a witness in `Rel` is not by itself
   genuine under the assumptions, and the composition theorem must carry a domain hypothesis.
3. Sharing a signature (probe `skip_consumes`): a verifier that first asks the `|pre|` dummy
   queries listed in `π` consumes a shared trace `pre ++ tr`, so a node can hold **one** signed
   trace `tr₁ ++ tr₂` for both children (child 1 reads `tr₁` and ignores `tr₂`; child 2 skips
   `tr₁` by dummies, then reads `tr₂`), hashing the trace once and checking one signature. This is
   sound (the trace is genuine) and is a legitimate optimisation, but the brief's cost
   statements and the in-circuit estimate in V4-3 assume two signatures per node, and `qV` must
   count the dummies.

**Fix.** Two trusted lines in `acc` (or in `runSeq`): (a) **exact consumption**, `runSeq [] (.ret a)
= some a` and `runSeq (_ :: _) (.ret _) = none`, so the signed trace is the verifier's query
sequence and nothing else; (b) **`∀ (q, _) ∈ tr, q.size ≤ queryCap`** with `queryCap` the
service's own cap (D4 used `2^20`). Then every accepted trace has at most `qV` entries of at most
`queryCap + 40` bytes, the witness space is bounded, `traceDigest` is injective on `Rel`'s
traces by a relation-internal fact (`enc64 |q|` is exact), and V4-5's domain hypothesis
disappears from the composition theorem. If the orchestrator prefers to keep the sharing
optimisation, keep suffix tolerance deliberately, state it, and still add (b). Either way,
rewrite V4-3's cost line as an upper bound.

**Cost.** +2 trusted lines; the positive control `leaf → node` must sign exactly the consumed
trace (the Lean reference signer does); in-circuit cost unchanged for honest entries, since their
traces are exactly their verifiers' query sequences already.

### C-M4. The signature scheme is an unpublished variant whose EUF-CMA claim is asserted, not reduced, and the reference key derivation invites a key-separation bug that would hand the prover the signing key

**Claim attacked.** V4-3, BRIEF §4.2–§4.3, §2's bound term `Adv_EUF-CMA`.

**Attack (literature, paper).**

1. **Which theorem?** The scheme is WOTS with `w = 4`, chain function tweaked by `(j, i, s)`, **no
   public seed and no bitmasks**, an **untweaked** Merkle tree, hash-then-sign of a 32-byte
   digest. That is none of: WOTS+ (Hülsing 2013, bitmasks, proof from second-preimage
   resistance), XMSS/RFC 8391 (public seed in every hash call), WOTS-TW as proved by
   Hülsing–Kudinov ([ePrint 2022/346](https://eprint.iacr.org/2022/346), tweakable hash with a
   public parameter `P`, properties SM-TCR, SM-UD, SM-PRE/DSPR, non-adaptive CMA; the proof that
   fixed a flaw in the original SPHINCS+ argument), or the original WOTS (proof from PRF,
   Buchmann et al. 2011). The CGH guide §4 warned: "check the proof model of the exact variant
   chosen before claiming no random oracle anywhere". The brief does not. Without the public
   parameter, SM-TCR is not even definable (there is no `P` for the challenger to sample after
   the targets), so the WOTS-TW proof does not transfer as written.
2. **What a proof needs here.** The classical Merkle argument gives EUF-CMA for this variant from
   three assumptions, all already in the trust statement's family: (i) **collision resistance** of
   BLAKE2s on the tagged domains `K`, `M`, `T`, `W` (a forgery with a different leaf, node, trace
   or chain value colliding somewhere yields the pair constructively); (ii) **one-wayness** of
   `F(j, i, s, ·)` on uniformly random 32-byte inputs, multi-target over the about `2^16 · 133 · 3
   ≈ 2^24.4` chain values of one key and over every key ever published (the tweak has no key
   identifier, so cross-key targets accumulate; at 256 bits the loss is irrelevant, but say it);
   (iii) **PRF security of keyed BLAKE2s** for the chain-start derivation. The signer refusing
   after `2^16` signatures and never reusing an index is a fourth, operational, condition. This is
   a standard-model argument; keyed BLAKE2s as a PRF rests on Luykx–Mennink–Neves' analysis of
   BLAKE2's modes in an ideal-cipher model
   ([ePrint 2016/827](https://eprint.iacr.org/2016/827)), which the trust statement should cite
   as the model behind both the oracle and the signer.
3. **Key separation.** §4.3: "`k` and the signing seed from `getrandom`"; §4.2: "the reference is
   `BLAKE2s-256 keyed by the signing seed of (enc64 j ‖ byte i)`". The oracle is `BLAKE2s-256
   keyed by k`, same construction, no tag on queries (V4-2). If an implementer derives the signing
   seed from `k`, or uses `k` as the seed, then `sk_{j,i} = PRF_k(enc64 j ‖ byte i)` **is the
   oracle's answer to the ten-byte query `enc64 j ‖ byte i`**, the prover asks it through
   `query`, and forges every signature. Nothing in the brief forbids it, and V4-2's "no tag on
   queries" removes the domain separation that would have saved it. Even with independent keys,
   the PRF hybrid of §2 item 8 needs the independence stated.
4. **Statefulness.** A concurrent `sign` that assigns one index twice, or a service restarted with
   its seed, signs two messages under one WOTS key; two WOTS signatures on distinct digests
   reveal enough chain values to forge a third. The brief says "stateful index" and "fresh per
   lifetime" but not atomicity or that a restart is a new lifetime (which aborts the run, since
   earlier proofs no longer verify).
5. **Is a cheaper scheme available?** In-circuit per child the brief counts about 200 (chains) +
   67 (leaf) + 32 (path) ≈ 300 compressions. Alternatives I sized: `w = 2` (265 chains, 133 + 133
   + 32 ≈ 300, no gain); `w = 16` (67 chains, about 500 + 34 + 32, worse); height 11–12 instead
   of 16 (the honest run needs at most about 1,025 signatures per lifetime: saves 8–10
   compressions, 3%); an L-tree for the leaf (worse). `w = 4` with a flat leaf is near the
   optimum for this leaf size. The one real saving is structural: a node that verifies its
   **children's** signatures natively (in `V`, with public BLAKE2s) instead of in-circuit pays
   nothing for them, but whoever proves that `V` in-circuit one level up pays, so in a recursive
   chain only the root's children's signatures are ever free. Keep the scheme; fix its statement.

**Fix.** In the design document's trust statement: the exact EUF-CMA theorem for this variant
from (i)–(iii) with the multi-target counting, the signer's two operational conditions, and the
model behind the PRF claim. In §4.2/§4.3: **`k` and the signing seed are independent `getrandom`
draws; the chain-start derivation uses a distinct tag or personalisation (e.g. `BLAKE2s-256
keyed by seed, personal = "RF-WOTS"`, or `0x53 ‖ enc64 j ‖ byte i` as the message) so that no
oracle query can equal a key-derivation input even under a shared key**; the index is assigned
under one lock and committed before the signature is returned; a restart is a new key and aborts
the run. Stage A's Lean reference signer should be the specification the Rust service is tested
against for the derivation too. Optional, if a reviewer insists on a published scheme: add a
per-run public seed `ps` to every `F`, leaf and node hash and publish `(vk, ps)`; +1 trusted line
and 1 field in `Sig`, no in-circuit cost.

**Cost.** Zero to one trusted line; design-document text; a service test (concurrent `sign`
stress, derivation test vector against the Lean signer).

---

### C-m1. Record the "no certified `V` trusts a signature" theorem and give it a control

§1's impossibility is the design's answer to O-25 and to the liveness mirror. State it in the
design document and add a Library negative control: a `V` that accepts `(c, magic c)` whenever `π`
holds a `vk`-valid signed trace agreeing with the oracle on one query has a `KState` for
`Rel (acc vk)` iff every digest has a witness (the shape of `acceptAll_kstate_iff`), so it is
certified only together with an accept-all extractor, which `Computes` excludes. Probe statement:
`sigTrust_kstate_iff : Nonempty (KState (Rel (acc vk)) (Vsig vk) E ε) ↔ ∀ c, ∃ w, Rel (acc vk) c w`
for `ε < 1`. Cost: Library only.

### C-m2. The service must not memoise answers, and the index is a 16-bit state channel

The cost model's stream rule is "no process holds state from one request to the next". The
service persists across the stream's requests. If it caches PRF answers, a request can write
state by asking chosen queries and the next request reads it by timing (`hit` vs `miss`), a
free channel of as many bits as queries; with a PRF, recomputation costs what a lookup costs, so
**no answer cache**, and no `attest`-like set. The signature index visible in each `Sig.idx` is a
16-bit counter the previous request can advance; harmless at that width, but say so. Also the
empty query: keyed BLAKE2s of the empty message finalises the key block itself (RFC 7693 §3.3),
so the cached-state fast path does not apply; the service needs the test vector the CGH guide §9
asked for. Cost: service text and tests.

### C-m3. `traceDigest` puts the contract's BLAKE2s on the badge's critical path for every proof

`acc` hashes the whole trace with the contract's reference BLAKE2s. v3 measured the certified
reference at about 5 µs per compression against 150–160 ns unrolled (v3 §8.5). A real root trace
(about 5,000 queries of about 100 bytes) is about 8,000 compressions: 40 ms of the `T_V` budget,
which at `R = 10` on the season shape is of the order of 250 ms, so 16% of the cap is spent by
the trusted code, and more if the shape or `R` tightens. The badge must use a word-level twin
proved equal to `blake2sDigest` (C9, C10) for `traceDigest`, `SigOk` and `chainStep`, and stage B
should measure `acc` on a synthetic 2^16-query trace. Cost: Library twin plus one equality
theorem; no trusted lines.

### C-m4. Service caps and the shared cgroup

The relation caps nothing on the trace, the brief caps "file sizes". The service needs explicit
caps on a query's bytes, a batch's items and bytes, and the number of open connections, each
refused as an error (a refused call aborts the proof as a reject, as D4 said); otherwise a prover
can make the service allocate the 13 GB cgroup and the OOM killer may choose the **service**,
aborting a run the prover could then blame on the harness. Set `oom_score_adj` so the prover dies
first, and record the kill reason. Also `sign` on an adaptive trace is not one round trip: the
prover must `query` each answer before it knows the next query and then `sign` the sequence,
which the service re-evaluates; the honest overhead is one extra PRF per query, fine, but
document it so that stage F's prover does not budget one call. Cost: service and runner text.

### C-m5. Conjunct order in `acc`

`acc` as written runs `V` on the trace before `SigOk`. For the DoS column and for every bogus
proof, `SigOk` (about 300 compressions) is the cheapest rejection; `runSeq` then rejects at the
first mismatch. Compiled `&&` short-circuits, so put `SigOk` first and the size check before both.
Cost: a reordering, no semantics change.

### C-m6. `E` without `vk`

V4-6 is harmless but restricts nothing a designer would want: a prover whose committed-witness
encoding depends on `vk` writes `vk` into `π` and `E` reads it there. Say so in the design
document so stage F does not read V4-6 as a prohibition.

### C-m7. The assembly route: build inside the sandbox, pin and record the image

Nothing an assembly program can do inside bwrap matters for soundness (`acc` is the only check)
or for the score beyond what any native prover could do; the differences are operational. (a) The
harness links `prover/*.s` with the runner's `gcc` **outside** the sandbox: `as` honours `.incbin`
and `.include`, so a source file can embed any file the job user can read, for example
`.git/config` with persisted credentials, into the binary and hence into a proof file that is
uploaded as an artifact; build in the sandbox, `persist-credentials: false` (also C-M1). (b) The
image's `gcc`, `as` and static glibc change monthly: record `ImageVersion`, `gcc --version` and
the binary's hash in the result, and build the incumbent for ABBA pairing from its own `.s` in the
same job. (c) `cpuid` dispatch is allowed; a `SIGILL` is a failed run, and a result records the
CPU model, so cross-model records are only ever paired (P3(d)). (d) Threads: the prover may
`clone`; the cgroup counts all. (e) seccomp: deny `ptrace`, `process_vm_readv`, `perf_event_open`,
`bpf`, `io_uring_setup`, `userfaultfd`, `keyctl`; the uid split already stops reads of the
service's memory, this is depth. (f) Ubuntu 24.04 restricts unprivileged user namespaces by
AppArmor (`kernel.apparmor_restrict_unprivileged_userns=1`); the runner has passwordless `sudo`,
so stage B must either run bwrap setuid-free as root-created uids or relax the sysctl in the job,
and say which.

### C-m8. The service's throughput is in every score (CM-R6 is live on 4 vCPU)

Under V4-14 every Merkle hash of every commitment is a service call: about `10^8` calls per tree
(D4 §4.8), on 4 vCPU shared with the prover. The D4 proposal measured +30–110% leaf time with a
naive service on 32 vCPU. So `T_tree` and `t_leaf` measure the organiser's IPC and SIMD BLAKE2s
as much as the entry; a faster service in season 2 moves every score, not uniformly (entries with
more Merkle traffic gain more). Publish the service's measured calls/s and compressions/s in each
result as a calibration column, like `T_triv,best`, and state in the design that the organiser's
hashing speed is part of the rules. The flip side is a benefit worth stating: the entry no longer
competes on Merkle-hashing craft, only on proving.

### C-m9. What a published `vk` certifies

"Records are transferable proofs" (P1) is true relative to the organiser's key management: a
third party verifying `acc vk c p` trusts that `vk` was generated by the service of that job, that
`sk` never left it and was destroyed, and that the service answered with a PRF under a key
independent of `sk`. That is the same trust as D4's, moved from "online during the window" to
"the organiser's statement in the record". Write it into the trust statement, and bind `vk`, the
service binary's hash and the job identity into the attested result (C-M1) so that the statement
is checkable.

### C-m10. No certified entry can run the season-1 shape

V4-11's shape (`r = 6`, `n = 2^18`) was sized for a Flock-class prover in 16 GB. The only certified
entry on record (spartan-chain) needed about 62 GB and a proof above `proofCap` at `n = 2^18` by
linear scaling (v3 lessons, D4 cost model §3.2), and the Flock baseline will be PROVISIONAL. So
the ranked path is exercised end to end only at the smoke shape (`r = 2`, `n = 16`), and criterion
10 of O-25 §11 is met for the contract but not for the rules. State it; plan the first ranked
shape as the one the first *certified* entry can run.

### C-m11. `decodeWit` for signed children, and `outCap`

The extractor output must now denote two `(π, tr, σ)` triples with variable-length traces; the
trusted decoder grows by about ten lines (length-prefixed items, 133 + 16 digests, an index) and
needs its own positive and negative controls (a malformed trace length, `|ots| ≠ 133`). `outCap =
2^24` words (128 MiB) holds traces to about `2^20` entries of 100 bytes in total, enough for any
honest node, but the design should say that a node whose children's traces exceed `outCap` cannot
be extracted and is therefore not certifiable, which is the right outcome.

### C-m12. Completeness and KS positive controls need the Lean reference signer

`∀ vk` completeness is vacuous for a `vk` with no signatures; the positive control for the node
clause (an honest node of two leaf children) must produce its children's signatures with stage
A's Lean signer and prove `SigOk` symbolically (kernel evaluation of 300 compressions is about
12 minutes). Negative: a node witness whose child is signed under a different key is not in
`Rel`; a trace with one answer changed is rejected by `SigOk` (collision-free assumption aside,
the control shows the hash changes). This is the stage-A checklist the brief implies; recorded so
it is not skipped.

### C-m13. Provisional entries

V4-15 lets an entry with a `sorry` run the benchmark. Its Lean still elaborates (C-M1 (c)), its
prover still gets 6 h of 4 vCPU, and its numbers are published. Keep the gate, source rule and
sandbox mandatory for provisional runs; mark the provisional numbers as uncomparable (no `T_V`
calibration is meaningful without a certificate's `qV`); and require maintainer approval to run,
which GitHub already does for first-time contributors.

---

## 4. Verdict

**The SROM design is sound at its core and unsound at its edges as written.** The relation,
the `∀ vk` quantifier against an unbounded ROM adversary, and the composition on one log do what
§2 says; I found no acceptance backdoor, and the one lemma the composition needs beyond v3's
kernel is proved in the probe. The design must be fixed before stage B freezes workflows and
before stage A freezes `acc`: C-M1 (trust anchor and attested results, sandboxed Lean build),
C-M2 (certificate job separated from the runner and measured on the honest entry), C-M3 (exact
trace consumption and a query cap, two trusted lines), C-M4 (the signature's theorem and key
separation). With those four, the trust statement a cryptographer would accept is: knowledge
soundness of the whole tree from one log at `Q·ε`, plus PRF security of keyed BLAKE2s against a
`2^30`-query distinguisher, plus EUF-CMA of the stated WOTS variant from collision resistance,
one-wayness and the PRF, plus constructive collision resistance of tagged BLAKE2s, plus a correct
service and the organiser's key management, plus an attested harness.

**Not settled here.**

1. Whether keyed BLAKE2s "is a PRF" is an acceptable named assumption for the design's audience,
   given that its only analysis (LMN16) is in an ideal-cipher model; the alternative is to call it
   the one heuristic of the design.
2. The actual CPU models of `ubuntu-24.04` public runners (GitHub does not document them) and
   whether `pclmulqdq` and AVX2 are on every one; stage B should assert them at job start.
3. Whether bwrap runs on the runner without relaxing AppArmor's user-namespace restriction, and
   whether the 13 GB cgroup is enforceable for a non-root uid (needs `cgroup v2` delegation).
4. The in-circuit cost of hashing a child's **trace** under the SROM relative to v3's recursion:
   each 64-byte Merkle preimage becomes a 104-byte trace item, about 1.6× the compressions, on
   top of the signature; P1's "about 300–500 compressions per child" is the signature only. An
   honest entry's sizing against `proofCap` (C5) has not been redone for v4.
5. Whether the composition theorem's third outcome should be refined in the kernel to "forgery or
   collision" by carrying the service's signed set as a parameter, which would move item 4 of §2
   from paper to kernel at the price of a Library definition of the signed set.
