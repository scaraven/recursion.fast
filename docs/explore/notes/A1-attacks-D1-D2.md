# A1. Attacks on D1 and D2 (relativized NARK, priced or run)

Adversarial note, 2026-10-20, against `docs/explore/BRIEF.md` §3 variants **D1** (relativized `KS`
certified, leaves timed, oracle calls charged at a `t_hash` taken from the leaf measurement, recursion
never run) and **D2** (same relation, v3's whole tree, oracle a secret-keyed harness service, a charge
per verifier call). Numbers: spartan-chain at `n = 2^14` (S2b RESULT §5, **measured** on the 32-vCPU
VM): proof 1,464,107 B, 5,156 queries, prove 7.4–8.0 s, native verify 0.81–0.84 s, peak RSS 3.95 GB;
issue #6 (**measured**): witness-sending root check 20.9–21.2 s reference, 0.64–0.69 s unrolled
sequential (151–164 ns per compression), 37–43 ms unrolled + `Task.spawn`. Everything else is marked
**paper** or **estimate**. Findings: `M<i>` major, `m<i>` minor. `qV` is v3's verifier query bound.

## Verdict

1. **The relativized requirement is vacuous for the strategies that need excluding and prohibitive for
   the one that needs rewarding.** Witness-sending and concatenation satisfy `RelO`-`KS` with potential
   `μ := 0` and node error `0`, because the node clause asks only that child proofs *exist in the clear*.
   Any node that compresses must make the root re-ask every descendant query (M2, an elementary ROM
   argument, below the paper's theorem). At `r = 8` that is about 2.6 M root queries and a 250 MB root
   proof: 40× over `qV ≤ 2^16`, 250× over `proofCap`. No honest recursive entry is certifiable and
   admissible under v3's caps beyond `r = 2`.
2. **No cap on any measurable quantity (proof size, verifier time, query count, cycle count) separates
   honest relativized recursion from witness-sending in the right direction** at `r = 8`, `n = 2^14`:
   the honest entry loses on every axis, by 10²–10⁴ (M6). The break-even chain length for a succinct
   leaf verifier against recomputation is about `2^22` for Ligero-class and `2^15`–`2^16` for
   WHIR-class verifiers; the first exceeds `chainCap`.
3. **The oracle charge rewards flattening, not recursion.** Children that use no oracle are re-asked
   for free, so "witness-sending below level `j`, one flat SNARK above" is the charge's optimum (M7).
   Every way of measuring `t_hash` from the submitter's own run is gameable (M3), and the charge leaves
   the verifier's local computation, the only cost of a witness-sending child, unpriced (M4).
4. **Per-proof statistics over a million chains measure one-leaf latency and take 35–90 machine-days**
   (M5). The only meaningful statistic is makespan over a few thousand fresh leaves, which is v3's.
5. **O-25.** With a public BLAKE2s oracle (D1, or D2 without the service) nothing changes: the
   kernel-checked backdoor is zero-query and certifies under `RelO` unchanged (M8). The secret service
   closes the CGH family *provably modulo PRF security* with a fresh key per evaluation: all five F2
   disguises and the liveness mirror die. Its price is a designated-verifier competition (proofs
   unverifiable without the organiser), a key-reuse hole that reinstates CGH from published logs (M9),
   RPC latency inside the timed region, an infeasible DoS column, and online-only grinding.
6. **What wins** is a BLAKE2s chain prover with any verifier: snark.fast, not a Flock 2.0 (M10). The
   hash is never in a circuit, so the verifier's hash-friendliness is invisible, and the one
   architecture signal the charge sees (compressions per verification) is readable off the certificate
   without a benchmark. D1 and D2 cannot be repaired by caps; the exploration should move to a model
   where the root re-asks `O(#children)` attestations, not `O(#queries)` (D3/D4), or back to v3.

## 1. Vacuity: what `RelO`-`KS` forces

**M1. Witness-sending and concatenation satisfy `RelO`-`KS` for free; node error is 0.**
*Defect.* `RelO^O c (node c₁ c₂ π₁ π₂) := c = nodeStmt c₁ c₂ ∧ V^O c₁ π₁ ∧ V^O c₂ π₂`, and in the log
form `final` demands `V.runLog L cᵢ πᵢ = some true`. A node verifier that parses `π = (c₁, c₂, π₁, π₂)`
and *runs `V` on both children itself* makes exactly the children's queries, so they are in `L`; its
extractor returns the four fields; `final` holds with `μ := 0` and `ε = 0` at the node, whatever the
child verifier is, sound or not. The witness-sending node (zero queries) is the special case already
certified in v3 (**kernel**: `Controls/Certificate.lean`, `ws_certificate`, state `μ := 0`; for a
zero-query `V`, `runLog L` is total and `RelL L` coincides with `Rel Vb`, so the same state certifies
`RelO`). *Why.* The node clause says "`V` accepts the child", not "the child statement is true"; the
hard content of knowledge soundness is confined to the leaf clause, which is concrete and unchanged
from v3. *Consequence.* The relativized requirement excludes none of the strategies issue #6 lists;
D1 certifies a submission whose node branch is never executed and whose node `KS` is one line.
*Smallest fix.* None inside `KS`: "recursion" is not a knowledge-soundness property (m1).

**M2. Any compressing node forces the root to re-ask every descendant query; nothing recursive is
certifiable and admissible at `r = 8`.** *Attack (paper, elementary).* Let the root `V` omit some
query `q` that a child's verdict depends on. The adversary fabricates `π₁` for a leaf statement
`c₁ = leafStmt(h, n)` with `h` random (no chain start known), answering `q` with a value of its own
and never querying it; it proves the node honestly over the fake transcript. The root accepts; `L`
contains nothing about `q`; `final` demands `π₁'` with `V.runLog L c₁ π₁' = some true`, which for a
SNARK-shaped `V` needs Fiat–Shamir answers that are not in `L`, and for any `V` needs a witness for
`h`. The bad event has probability 1, so no `KState` exists at any `ε`. Sampling a subset of child
queries detects a single fake answer with the sampled fraction, nowhere near `2^-128`. A random
oracle's answer at `q` is independent of every other answer, so no other query substitutes.
Hence `qV_root ≥ Σ_descendants qV`, and the root must know *which* queries to ask: either the proof
lists them (`as ≥ 96 B × Σ qV`) or the root recomputes them by running each child's verifier
locally, which is concatenation. This is [CGSY24]'s "relativized NARK by sacrificing succinctness"
(paper §1.2) in concrete form, and the tight statements are the paper's Theorems 1 and 2
(`vq = o(t)` and `as = o(t)` both impossible). *Numbers (estimate from S2b).* 511 proofs × ≈5k
queries ≈ 2.6 M root queries; ≈ 96 B per `(q, a)` ⇒ ≈ 250 MB root proof; root RPCs at 10–50 µs ⇒
26–130 s. Against the caps: `qV ≤ 2^16` admits ≤ 12 spartan-chain-sized proofs (`r ≤ 2`);
`proofCap = 1 MiB` is exceeded 250×; `verify_s = 60 s` and `T_V = 2 s` are exceeded. Even
"witness-sending below `j`, recursion above" lists `(2^{9-j} − 1) × 5k × 96 B`: 1.7 MB at `j = 7`.
*Consequence.* Under v3's caps the admissible set under `RelO` is witness-sending and witness-sending
with small SNARK pieces; honest recursion is not in it. *Smallest fix.* Raise `qV` to ≈ 2^22 and
`proofCap` to ≈ 512 MB, accept minutes-long root checks and a `2^26`-word extractor tape (within
`B t`), and state that the root proof is linear in the tree's query count. That makes the entry
admissible, not competitive (M6, M7). The real fix is a richer oracle model where the root checks
one attestation per child (D4) or signature (D3), which leaves the pure ROM.

**m1. "Recursion-amenable" is not expressible as a `KS` property in the ROM.** Beyond leaf `KS`,
`RelO`-`KS` is equivalent to "node proofs decode to child proofs that verify under the final log",
satisfied by concatenation. A definition that rewarded *compressing* nodes would assert the existence
of a node verifier with `o(Σ qV)` queries, which Theorem 1 denies for the general relation and M2
denies for this one. In D1 the node branch is never run, so the relativized clause is paperwork: a
submitter ships the SNARK leaf branch plus a witness-sending node branch and the certificate costs
one lemma. *Fix.* Say in the design that amenability is a measurement (v3) or a property of a richer
oracle model (D3/D4), never of `KS`.

**m2. `CompleteWithError` is not well typed for an oracle-dependent relation.** v3's
`CompleteWithError R P V δ := ∀ c w, R c w → failProb ((P c w).bind (V c)) [] ≤ δ` takes `R c w` as a
`Prop` outside the lazily sampled game; `RelO`'s node clause depends on the oracle, so "`R^O c w`" has
no meaning before `O` is sampled. The paper's completeness (§2.1) conditions on `(x, w) ∈ R^f` for the
*same* `f`. The contract must check the relation inside the game: run `V` on the children as an
`OProg`, and count a failure only on the branch where both accept. That changes `Rel` from a `Prop` to
a program in the trusted base (about 10 lines) and makes the honest node `P` re-ask the children's
queries. Not a loophole, a well-definedness gap the brief's D1/D2 text does not close.

## 2. The cost term

Let `T` be the leaf time and `k` the verifier's oracle calls. The charge is `t_hash · k`.

**M3. Every self-referential `t_hash` is gameable, each in a different direction.**

| `t_hash` from | Attack | Effect |
|---|---|---|
| `T / n` (leaf time per chain step) | witness-sending leaf: hash natively (≈ 2.1 ms per `2^14` chain in Rust, issue #6, **measured**), output the start | `t_hash ≈ 0.13 µs`, `k = 0`: charge 0, score ≈ 2 ms |
| marginal slope in `n` (two sizes) | pad every leaf to a fixed circuit size (slope 0); or sleep at the smaller `n` (slope < 0, charge negative) | charge ≤ 0 for any `k` |
| fixed organiser constant | minimise *calls*: `OProg.query` takes any length, so one call hashing all `2^14` leaf digests (512 KB, inside `proofCap`) replaces a depth-14 Merkle path per column; ≈ 260 + 2 calls instead of 5,156 | charge ÷ 20, honest in-circuit cost unchanged |
| a reference system | the reference's per-hash cost prices *my* verifier; my prover's speed never enters the charge | the charge is a constant per architecture, computable from the certificate (M10) |

*Consequence.* Under the first two the charge is 0 for the strategy it exists to price; under the
third it rewards wide hashing, which the real recursion circuit does not reward (a 512 KB input is
8k compressions in circuit). *Smallest fix.* Charge per 64-byte compression over the verifier's
query bytes (`Σ ⌈|q| / 64⌉`, readable from `queries H`), at an organiser constant taken from a
reference BLAKE2s prover, and publish the constant. That is the only unriggable form, and it is then a
*paper* quantity: no run is needed to compute it.

**M4. The charge prices oracle calls only; the cheapest verifier does no oracle calls.** A node whose
children are witness-sending does `2^{j+14}` chain compressions *locally* in `V` and makes 0 oracle
calls; under `RelO` that local work is in the node circuit (public BLAKE2s arithmetised, about `2^14`
R1CS constraints per compression, issue #8 **estimate**), and the charge sees none of it. Also
unpriced: field arithmetic of the child verifier (Ligero: 260 columns × `2^14` rows ≈ 4 M field
multiplications per verification, **estimate**, small beside the hashes for spartan-chain but 100% of
a witness-sending child), non-native fields (a verifier over a 256-bit prime inside a `GF(2^64)`
circuit, 10–50× **estimate**, free), memory (3.95 GB per leaf, free), and the recursion circuit's
fixed overheads (public-input handling of a 250 MB `(q, a)` list, free). *Consequence.* The gradient of
the score points from oracle work to local work, the opposite of in-circuit cost. *Smallest fix.* No
proxy of oracle calls can price local work. A cycle count prices it (m3) and reopens other channels.

**m3. A RISC-V cycle count for `V` prices local work, with four holes.** (i) Oracle calls would be a
syscall at 1 cycle whatever the input length: price per byte, as in M3. (ii) Instruction mix: in the
vendored Rv64 with Zbc, `clmul`, `mulhu`, `divu` and a 64-bit load are one cycle each and tens to
hundreds of constraints in any zkVM; a verifier written around them is cheap in cycles and dear in
circuit, so the count needs a per-instruction cost table, which is a cost model (DISCUSSION Q6
avoided one). (iii) Prover-supplied hints (inverses, decompositions) are legitimate and shrink the
count; fine. (iv) The direction problem of M6 survives: the trivial verifier is `2^14 × ≈400–1000`
cycles ≈ `2^23`–`2^24`, the Ligero-class verifier ≈ `2^31` (0.81 s × 3 GHz), so a cycle cap tight
enough to exclude recomputation excludes every leaf SNARK at `n = 2^14`. The brief (row 7) keeps `V`
as an `OProg`; agreed, and a bytecode `V` would also make the `KS` proof a program-verification
effort (DESIGN §6.5).

**m4. Addition versus multiplication.** Additive `T + t_hash · k` has units of time and, with
`t_hash = T / n`, equals `T · (1 + k / n)`: for spartan-chain `7.7 s × 1.31 = 10.1 s`. Multiplicative
`T · (1 + c · k)` is the same shape with a free constant. Both are a monotone function of `T` times a
factor between 1 and 2 for any sound verifier (`k ≤ n` is not succinctness), so both rank by `T`
alone; a verifier that doubles `k` for a 1.4× faster prover wins. Neither form can make a verifier
with `k = 0` lose, which is the case that matters.

## 3. The statistic

**M5. Per-proof statistics over "a million chains" measure one-leaf latency and are unrunnable.**
*Defect.* If each leaf is timed start-to-finish with the prover free to use all cores, the statistic
(mean, geomean or median) is the latency of one leaf with 32 threads: v3's board L, retired because a
recomputing prover wins it (S9I-M1). If leaves are timed from a global start, every statistic is a
function of the prover's schedule, not its speed (the median is the time at which half the leaves are
done, about half the makespan under any order). *Length.* `10^6 × 7.7 s = 89` machine-days at one
leaf at a time; with independent single-threaded leaves the throughput is better but RSS 3.95 GB per
leaf allows ≤ 24 concurrent under the 96 GB cgroup, so 35–90 machine-days (**estimate**). The runner
must also compute `10^6` chain ends (`1.6 × 10^10` compressions, ≈ 45 min single-thread, fine) and
hold 32 MB of fresh starts. *Consequence.* The ranked quantity is either the wrong one or unmeasurable.
*Smallest fix.* Makespan of one process over `2^8`–`2^12` fresh leaves (v3 §6.1, one hour), reported
as throughput; drop per-proof statistics.

**m5. Distribution gaming.** If any leaf may be dropped or retried outside the clock, the prover
aborts the slow ones (grinding-heavy or unlucky-schedule leaves) and the geomean or median falls; the
mean is pulled by the retries. If none may be dropped (v3's rule: a missing accepted proof fails the
evaluation), the sum is the only consistent aggregate, and that is the makespan. Fresh starts per
evaluation stop precomputed proofs, as in v3; an untimed `setup` is the only amortisation, which is
correct.

## 4. Succinctness and compression under the re-ask rule

**M6. No measurable cap separates honest relativized recursion from witness-sending in the right
direction.** Whole ranked tree, `r = 8`, `n = 2^14`:

| Quantity at the root | witness-sending | honest `RelO` recursion (spartan-chain-class, **estimate**) | ratio |
|---|---|---|---|
| proof size | 256 × 40 B ≈ 10 KB | ≈ 250 MB `(q, a)` lists + SNARKs | 2.5 × 10⁴ |
| oracle calls | 0 | ≈ 2.6 M | ∞ |
| local work | `2^22` compressions: 0.67 s one core, 40 ms threaded (**measured**) | ≥ 2.6 M-entry public input + own SNARK check | ≥ 1 |
| wall time (public oracle / service) | 40 ms–0.7 s | ≈ 1 s local + 26–130 s RPC | 10²–10³ |
| cycles (m3) | ≈ `2^31`–`2^32` | ≫ `2^31` per inner verification, 511 of them | ≥ 10² |

Every axis a harness can measure is worse for the honest entry, so any cap tight enough to exclude
witness-sending excludes recursion first. *Where it flips.* At the leaf, a succinct verifier beats
recomputation when `n × 160 ns > T_verify`: Ligero-class (0.81 s) needs `n ≈ 2^22.3 > chainCap`;
a WHIR-class verifier with ≈ `2^15` compressions plus small field work (≈ 5–10 ms, **estimate**)
needs `n ≈ 2^15`–`2^16`, and `n ≈ 2^19` for a 10× margin. At the node the re-ask rule removes
compression altogether (M2). *Consequence.* D1 without a cap is won by witness-sending at ≈ 2 ms;
with any cap, by whichever strategy the cap happens to let through, never by recursion. *Smallest
fix.* Change the benchmark shape to `n ≥ 2^19`, `r ≤ 4`, price the verifier per compression (M3), and
accept that the root still gains nothing from recursing (M7). A semantic rule ("`V` may not hash
chain steps locally") is the v3 §6.7 rule with the F2 §1 disguises (embedded image, vendored
compression) intact; the service only makes it enforceable for the *oracle*, not for the public chain
hash.

**M7. The charge and the re-ask rule both reward flattening.** A child that makes no oracle calls is
re-asked for free. So the optimum under D2's charge is: witness-sending below the largest level `j`
whose flat SNARK fits memory, then concatenation or witness-sending above. Memory sets `j`: 3.95 GB at
`2^28` constraints scales to ≈ 63 GB at `2^32` (16 leaves, `j = 4`, **estimate**) under 96 GB; the
full flat SNARK (`2^36`, ≈ 1 TB) is infeasible. The entry then has 16 SNARKs of 16 leaves each
(`16 × 6k ≈ 96k` queries, 16 × 0.7 MB WHIR-class ≈ 11 MB), against 2.6 M queries and 250 MB for
recursion; it is still over `qV` and `proofCap`, which only means the caps exclude everyone but
witness-sending. *Consequence.* Under every variant of the charge the number of recursive node proofs
in the winning entry is zero. *Smallest fix.* None within D1/D2. A charge that *rewards* oracle use
(a floor on queries) is absurd; the only consistent rule prices the in-circuit cost of a child's
verification, which is what the hash-in-circuit of v3 does and the attested list of D4 approximates
(hash the `(q, a)` list with concrete BLAKE2s in circuit: about the cost of a real public-hash
recursion step).

## 5. O-25 under each deployment

**M8. Public BLAKE2s oracle (D1 as read; D2 without the service): O-25 is unchanged.**
`Controls/Backdoor.lean` (**kernel**, `backdoor`) is a one-query `V` whose magic branch is a `2^-256`
event over oracle functions; it is a leaf verifier, so it certifies under `RelO` verbatim, and under
D1 a magic leaf proof costs the prover nothing: score ≈ process start-up. All five F2 disguises
(literal trigger, kernel-checked in ADV-M5; trace-check trigger; partial and spread recognition;
recomputed Fiat–Shamir) and the liveness mirror apply unchanged, because they live in the leaf `V`
and the leaf is concrete BLAKE2s plus a public oracle, exactly v3. *Fix.* None short of the service.

**The service closes the CGH family (paper, modulo PRF).** With `O := F_k`, `k` uniform, sampled after
the entry is frozen and never released, the submitter's `V`, `P`, extractor and prover are fixed
independently of `k`. A prover that produces an accepted-but-unextractable proof under `F_k` with
probability `p` gives a PRF distinguisher with advantage `p − (Q + qV) · ε`: run the prover with the
challenge oracle, run `V` and `E`, output "accepted and unextractable". All three are efficient
(`E` by its step bound). So the deployed knowledge soundness follows from "keyed BLAKE2s is a PRF", a
standard falsifiable assumption, far weaker than "BLAKE2s is a random oracle"; `V` cannot compute,
recognise or partially recognise `F_k`, has no clock, and the liveness mirror ("reject only under the
deployed oracle") has nothing to detect. This is the one result in D2 that is strictly stronger than
v3, and F2's "the only way to make the instantiation unknowable is to make it external, which
recursion forbids" is indeed what `RelO` lifts. It is also exactly why `RelO` is expensive (M2): the
recursion never evaluates the oracle because nobody can.

**M9. The service's holes.** (a) **Key reuse reinstates CGH.** If `k` lasts a season and any proof or
query log is published (the design publishes records, proofs feed the challenge period), a submitter
learns `(q₀, a₀)` pairs and its *next* `V` compares the re-asked answer to `q₀` with the literal `a₀`:
one bad answer in `2^256`, certified at `errorCap`, deployed-true. Within one evaluation the same
trick is caught, because the pair must enter through the proof and the ROM adversary that predicts an
answer has queried it (F2 §2). *Fix.* Fresh `k` per evaluation and per repeat, from a beacon after
freeze; never publish answers; treat the key schedule as trusted process. (b) **Designated-verifier
competition.** Nobody can check a published proof without the organiser's service; records are
unverifiable by third parties, and the challenge period (F2's load-bearing defence) loses its public
witness. (c) **RPC in the timed region.** The honest prover makes every verifier query once
(≈ 2.6 M at `r = 8`); at 10–50 µs per local-socket round trip that is 26–130 s against ≈ 33 min of
leaf proving, organiser-owned and noisy; `OProg.query` is sequential, so `V` cannot batch, and the
root check (step 4) pays the same 26–130 s against `verify_s = 60 s` and `T_V = 2 s`. (d) **DoS
column.** 1,000 random proofs × a `V` that re-asks up to millions of queries is hours of service time;
a random proof is rejected early only if `V` is written to fail fast, which the column should
require. (e) **Rate limits become caps.** Any limit on prover calls bounds grinding (m8) and must be
in the rules; a prover that floods the service degrades a concurrent evaluation. (f) **Trusted base.**
A key-holding service, its PRF, its logging (needed by the liveness check, §6.3 step 8) and its
availability are trusted infrastructure outside Lean and outside V3-5's "ROM only".

**m6. The remaining service attacks, with status.** Key extraction through queries: infeasible for a
keyed BLAKE2s PRF with a 256-bit key (no length extension; do not use `BLAKE2s(k ‖ q)` with a
variable-length `q` tag-free, use the keyed mode). Timing: `V` has no clock; the prover can time
responses but a constant-time PRF leaks nothing about `k`. Prover relaying or caching answers:
harmless, the root re-asks; a cache across the three repeats is legitimate only if the key does not
rotate, and with rotation the proofs differ anyway. Replay of proofs across evaluations: dead with
per-evaluation keys (and with fresh starts already). A `V` that learns `k` from the proof: the prover
never has `k`. Denial of service: (d), (e) above. The prover measuring its own time: excluded by
having the harness time the process, as v3 does; self-reported per-leaf times would be the first
thing gamed in D1.

**m7. One rule becomes a type.** v3 §6.7's "`V`'s local computation must not evaluate the oracle's
instantiation" is over-broad and disguisable (issue #4 §3). Under the service it is enforced
physically for the oracle: a concatenation node must *query* to verify its children, which is why its
`qV` explodes (M2). The same rule for the *chain* hash is still a review rule, and still the thing
that decides M6.

## 6. What wins

Ranking by the score as the brief reads it, with v3-style fresh instances and the harness timing the
process. "Admissible" is under v3's caps (`proofCap`, `qV`, `T_V`); every row is **estimate** from the
S2b and issue #6 measurements.

**D1** (leaf time plus `t_hash · k`, any of the M3 forms):

| Rank | Strategy | `T_leaf` | `k` | Score | Admissible |
|---|---|---|---|---|---|
| 1 | witness-sending leaf (hash natively, output the start, or every 128th chain value for a threaded check) | ≈ 2 ms | 0 | ≈ 2 ms | yes (`T_V` passes, issue #6) |
| 2 | minimal-call verifier: one 512 KB query over all leaf digests, ≈ 260 column calls | ≈ 7.7 s | ≈ 260 | ≈ 7.8 s per call, ≈ 10 s per compression | no (`proofCap`) |
| 3 | spartan-chain leaf SNARK | 7.7 s | 5,156 | 10.1 s | no (`proofCap`) |
| 4 | WHIR-class leaf (fewer compressions, similar prover) | ≈ 5–10 s | ≈ 2–3k | ≈ `T × 1.15` | yes, barely (issue #8) |

**D2** (tree makespan plus a charge per root call, service oracle):

| Rank | Strategy | Root proof | Root calls | Tree time | Admissible |
|---|---|---|---|---|---|
| 1 | witness-sending tree | 10 KB | 0 | ≈ 20 ms–0.5 s (native chain hashing) | yes |
| 2 | witness-sending below `j = 4`, 16 flat SNARKs of 16 leaves, concatenation above | ≈ 11 MB (WHIR) | ≈ 96k | ≈ 33 min | no |
| 3 | leaf SNARKs + concatenation (spartan-chain's own shape) | 180–374 MB | ≈ 1.3 M | ≈ 33 min | no |
| 4 | honest relativized recursion | ≈ 250 MB | ≈ 2.6 M | ≈ 33 min leaves + cheap nodes (no hash in circuit) | no (M2) |
| — | one flat SNARK of `2^22` compressions | ≈ 1 MB | ≈ 6k | memory-infeasible (≈ 1 TB) | — |

Ranks 2–4 are over the caps, so under the caps rank 1 is alone; without the caps rank 1 still wins by
three orders of magnitude; with a rule that bans chain hashing in `V` (review, disguisable) the winner
is rank 2, and recursion is rank 4 under every scoring that has been proposed.

**M10. The winner is a chain prover, not a Flock 2.0.** Flock's contribution is a verifier
architecture whose cost *inside the recursion circuit* is small: cheap-to-arithmetise hashing and
few, cheap verifier operations. D1 never runs a node; D2 runs nodes whose circuits contain no hash;
so in neither does the hash-friendliness of `V` enter the score. The one architectural quantity the
charge can see, compressions per verification, is a number in the certificate (`queries H` of `V`),
and a competition on it needs a formula, not a reference machine. The remaining scored quantity is
leaf proving time of BLAKE2s chains: snark.fast's board. *Fix.* Put the child's verification cost
back into something that is *proved and timed*: v3 (hash in circuit), or D4 (hash of the attested
`(q, a)` list in circuit, about the same cost, with the oracle secret). Both make "recursion-friendly"
a measured property of `V` again.

## 7. Completeness with small error, grinding, the extractor

**m8. Grinding is online-only under the service, and the recognition site dies.** A prover grinding
`g` bits per round makes `2^g` service calls per round; at 50 µs per call and `g = 20` that is 50 s
per round, ≈ 30 rounds per spartan-chain leaf: proof-of-work soundness boosting (leanVM-style,
issue #8) is effectively unavailable unless the prover's client batches, which it may (the harness
API, not `OProg`, serves the prover). The root re-asks only the final transcript's queries, not the
failed attempts, so `qV` is unaffected. F2 §11.1's worry that `leadZeros` is a recognition primitive
is moot: nothing about `F_k` is recognisable. δ aggregates over 511 proofs to ≤ `2^-119`, inside the
cap. The completeness statement itself must be restated (m2).

**m9. The extractor.** Node extraction is still decoding (issue #7): `π₁` is a witness of the node
circuit, committed, not listed; the `(q, a)` lists in the clear only let `E` replay `runLog` once it
has `π₁`. The tape grows to ≈ `2^26` words (250 MB proof plus 2.6 M log entries), and
`B t = 2^48 + 2^16 · t ≈ 2^48 + 2^42` still holds; the liveness check (§6.3 step 8) must run `V` on
the extracted children against the logging service, so the service must log every evaluation, which
(a) of M9 then forbids publishing.

**m10. Composition across levels becomes a theorem, at linear cost.** Because the root log contains
every descendant query (M2), `final` at the root yields child proofs accepted under the *same* `L`,
and peeling the tree is an induction over one log: DESIGN §5.4's first unclaimed bullet closes. This
is the second genuine gain of D2 beside the PRF closure of O-25, and it is bought with exactly the
linearity that kills the ranking. D4's attested lists are the attempt to keep both gains with
`O(#children)` root work; that is the variant worth attacking next.

## Summary table

| Id | Finding | Rank consequence | Smallest fix |
|---|---|---|---|
| M1 | witness-sending and concatenation satisfy `RelO`-`KS` with node error 0 | the requirement excludes nothing | none inside `KS` |
| M2 | compressing nodes force the root to re-ask every descendant query: ≈ 2.6 M calls, 250 MB | no recursive entry certifiable and admissible beyond `r = 2` | raise `qV`, `proofCap`; or D3/D4 |
| M3 | every self-referential `t_hash` is gamed (0, ≤ 0, or per-call minimisation) | the charge is 0 for the strategy it should price | organiser constant per compression |
| M4 | local work unpriced; the cheapest verifier does only local work | gradient points away from in-circuit cost | none within a call proxy |
| M5 | per-proof statistics measure one-leaf latency; `10^6` chains is 35–90 machine-days | wrong quantity or unrunnable | makespan over `2^8`–`2^12` leaves |
| M6 | no measurable cap separates recursion from witness-sending in the right direction at `n = 2^14` | witness-sending wins; recursion loses on every axis | `n ≥ 2^19`, per-compression budget; still M7 |
| M7 | the charge and the re-ask rule reward flattening | zero recursive node proofs in the winner | price in-circuit verification (v3, D4) |
| M8 | public oracle: O-25 unchanged, zero-query backdoor certifies under `RelO` | magic proofs score ≈ 0 under D1 | the service |
| M9 | service holes: key reuse reinstates CGH; designated-verifier; RPC in the clock; DoS column; rate limits; trusted infra | noise, unverifiable records, new trusted base | fresh key per evaluation; never publish answers; batched prover API |
| M10 | the winner is a BLAKE2s chain prover with any verifier | not a Flock 2.0 | v3 or D4 |
| m1–m10 | amenability not a `KS` property; completeness ill-typed; cycle count holes; add vs mul; distribution gaming; other service attacks; a rule becomes a type; online grinding; extractor tape; composition provable | — | as stated |
