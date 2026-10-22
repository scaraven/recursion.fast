# Cost and incentive model: chain-first scoring with an additive recursion term

Status: **proposal, not in force** (2026-10-22). v3 is frozen ([V3] §1) and the relativized design
([RD]) left the benchmark shape and the recursion incentive to the user (its RU-4, RR-13). This
document proposes the scoring for the next iteration: what is timed, how the times combine into one
rank, and why the combination resists the strategies found so far. It changes no relation, no
security definition and no trusted Lean line; it replaces v3's scoring section ([V3] §8.2–§8.3,
§8.5's recursion paragraph, §8.7) and answers [V3] §16 C7 and issue #6 (b).

**Provenance.** The user's statement of the goal and of the shape of the incentive (2026-10-22,
quoted in §1); the cost figures of the relativized exploration ([C1], [A1], [A3], on the branch
`explore/relativized-nark`); v3's design record ([V3]) and the relativized design ([RD]). The
measurement protocol of §3.3 is new in this document. Its first form was broken by an adversarial
review ([CREVIEW]: six major findings, eleven minor); §3.3 is the protocol after the fix pass, and
§10 lists what changed. A verification pass of the fix was stopped unfinished at the user's request,
so the fix pass is unreviewed; the document is to get its own independent adversarial review.

**Evidence tags**, as in [RD]: **measured** (a log), **published** (a cited README or paper),
**estimate** (arithmetic from measured or published inputs), **paper** (an argument). No reference
machine exists ([V3] §16 C13), so every time below is from the shared development VM or from
leanVM's published M4 Max figures, and every value of `K`, `T_V` and the targets is a placeholder
until the reference machine calibrates it.

| Term | Meaning |
|---|---|
| leaf, node, merge | a leaf proof shows one chain of `n` BLAKE2s compressions from a secret start; a node proof shows two accepted children; a **merge** is the operation that turns two children into one node proof (`PROVER node`, [V3] §8.3) |
| `T_tree` | v3's board T: wall time of one prover process proving a whole tree, root proof accepted ([V3] §8.3) |
| the stream; a link | the recursion workload of §3.3: `M` short chains arrive one at a time, and each **link** proves one of them and merges it into the running proof |
| `t_leaf`, `t_merge`, `t_link` | the stream's mean leaf time, mean merge time, and their sum: the time per link |
| recursion overhead `o` | the part of a link that is recursion rather than chain proving: `t_link` minus the entry's own time for `n_f` chain compressions; published as an estimate, `t_link − T_tree · n_f / 2^24` (§3.6) |
| `K` | the number of links the score charges: the exchange rate between the two terms (§3.4) |
| ν | one node's proving cost in units of one leaf's proving cost |
| flattening; proof of parent | proving a subtree of `2^j` chains as one flat SNARK instead of recursing; reusing that one flat proof as the accepted proof of every statement inside the subtree ([A3] M1) |
| bundling | a node "proof" that is its child proofs side by side, each verified by `V`: witness-sending for one level, certifiable as concatenation is ([V3] §8.7) |
| shapes | **ranked v3**: `r = 8`, `n = 2^14` (256 leaves, `2^22` chain compressions); **long**: `r = 4`, `n = 2^20` (16 leaves, `2^24`) |
| leanVM-class | a prover at Flock's published rate, 485,033 compressions/s on an M4 Max, with leanVM's published 2→1 recursion step: 0.394 s, 206.3 KiB proof, verified in 14.6 ms ([C1] §1, **published**) |

---

## 0. Summary

**The goal** (the user): a very fast prover for BLAKE2s hash chains whose recursion step is good
enough, with a target of 100–200 ms per step, not a maximally succinct recursive verifier. Chain
proving comes first; faster recursion must always pay; there is no pass/fail cliff, so the
competition can start far from the targets, move towards them and pass them.

**The score** (lower is better, in seconds):

```
S = T_tree + K · t_link
```

- `T_tree` is the chain term: board T at the **long shape** (`r = 4`, `n = 2^20`), any method,
  flattening allowed.
- `t_link` is the recursion term: the mean time per link of a timed **stream** of `M = 512` short
  chains (`2^16` steps each), each added to a running proof as it arrives, every request in a fresh
  prover process on the clock (§3.3). An entry may add a chain by a 2→1 merge of a separate leaf
  proof or, usually cheaper, by a 1→1 step that proves the chain inside the step; the user's
  original brief allowed both. The recursion overhead per link, `o`, is the number compared with
  the 100–200 ms targets.
- `K` is one published number per season: one millisecond off a link is worth `K` ms off the tree.
  It is set from the **leading entry**, so that recursion is a stated minority share `p` of the
  leader's score, and raised each season as the leader's recursion gets faster (§3.4). In the
  illustration, `p = 15%` gives `K ≈ 20` for a leader whose overhead is leanVM's published 0.394 s
  step.

**What changes against v3.** (1) The ranked shape moves from `r = 8, n = 2^14` to `r = 4, n = 2^20`.
(2) Recursion gets its own term with an explicit weight instead of whatever share the shape gives
it. (3) Flattening and bundling inside the tree become legitimate engineering; column R and the
per-level CPU cap are dropped as answers to #6 (b). (4) The caps (`T_V` by CPU time, `proofCap`,
`qV`, memory) stay pass/fail: they define a valid entry and bound the verifier, and are not
performance targets.

**What it closes.** #6 (b) and C7, by pricing recursion directly (§2.1, §3). For #6 (a), full
witness-sending is excluded with a window of 30–766 ms of one core at the long shape (§3.2). In the
stream, no proof is prepared off the clock and no process holds state across links, so the work it
times is the work it asks for, up to one bounded escape, the last few links (at most about 5%,
CM-R2). It counts 1→1 links and higher-arity merging as recursion, since each still absorbs every
proof in a circuit once (CM-R3, CM-4).

**What it leaves open.** A root verifier may finish up to `T_V/T_triv` of the chain work natively,
10% under v3's proposed `/10` rule (CM-R7); the value of `K` and `T_V` on a reference machine that
does not exist; memory for a `2^20` leaf; and the spartan-chain baseline, which cannot run at the
long shape (§3.2). Eight decisions are the user's (§8).

---

## 1. Goal and requirements

The user, 2026-10-22: *"The 'final goal' of Flock 2.0 is that we want a super fast hash chain prover
which is able to perform recursion in under 100/200ms. So recursion needs to be 'good' enough as
opposed to be primarily a extremely succint recursive verifier"*, and: *"Rather than have a
hard/pass fail, we should still provide an incentive mechanism (so that we can start high and slowly
progress to our desired targets, and exceed them as well) but it should be mostly 'additive' in
that hash chains should be prioritised but we always could increase recursion speed."*

As requirements on a scoring rule:

- **G1 (chains first).** At the leading entry's recursion speed, and at the targets, proving the
  chains is most of the score.
- **G2 (recursion always pays).** The score strictly improves when recursion gets faster, at every
  speed, including past the targets.
- **G3 (no cliff).** Every entry that produces accepted proofs is ranked, however slow its
  recursion; no measure of prover performance is a threshold. (The caps of §3.5 bound the verifier
  and the resources; they define what a valid entry is.)
- **G4 (bounded gaming).** No strategy gains more than a bounded, stated amount by not doing the
  work a term is meant to measure.
- **G5 (soundness untouched).** The scoring rule adds no trusted Lean and changes no relation; the
  caps that make a proof succinct stay.

---

## 2. Why v3's scoring does not serve the goal

### 2.1 One wall time cannot weight recursion

Let ν be a node's proving cost in leaf units. A tree of `2^r` leaves proved with full recursion costs
`2^r + (2^r − 1)·ν` leaf units. Flattening the bottom `j` levels costs `2^r + (2^{r−j} − 1)·ν`, so
the saving is a factor of about `(1 + ν)/(1 + ν/2^j)`, which is always below `1 + ν`. Under full
recursion, recursion's share of the work is about `ν/(1 + ν)`. **Both numbers are set by ν**: if
proving the whole tree flat may save at most a factor `g`, then `ν ≤ g − 1` and recursion is at most
`(g − 1)/g` of the work. Holding flattening's gain to 15% holds recursion to at most 13% of board T
(paper, arithmetic).

v3 chose `n = 2^14` so that "one leaf is comparable to one node, so neither dominates" ([V3] §7.3).
That is the regime ν ≥ 1, where flattening pays most (**estimate**, [C1] §2.2):

| Prover class, ranked v3 shape | ν | full recursion against flattening at `j = 4` ([A3] M1) |
|---|---|---|
| R1CS of bits, WHIR-class children | 1.46 | 2.3× more work |
| R1CS of bits, spartan-chain children | 3.16 | 3.5× |
| leanVM-class (34 ms leaf, 0.394 s node) | 11.6 | 7.5× |
| leanVM-class at the long shape (2.16 s leaf) | 0.18 | under 15% at `j = 2`; 1.17× against fully flat |

So at the ranked v3 shape the winner flattens, and at the long shape recursion is about 15% of the
work and nearly irrelevant to the rank. No shape gives a fast chain prover **and** a recursion
incentive of chosen strength. A separate, weighted term does.

### 2.2 Flattening is certifiable and invisible

A verifier with a flat branch accepts one SNARK over a level-`j` subtree, plus a path, as the proof
of every statement inside that subtree ([A3] M1, paper). Its extractor hands back the same flat
proof with the path extended, which the verifier accepts by construction; it is complete, within
`proofCap` and `qV`, and a relabelled flat proof verifies as fast as a recursive one. Hence:

- knowledge soundness cannot force recursion ([V3] §6.6; [RD] §3.3, kernel `lift`);
- v3's first answer to #6 (b), a CPU-time cap on every sampled proof ([V3] §8.5), has nothing to
  measure: it was designed against witness-sending below level `j`, and proof of parent is not that;
- memory, not any rule, bounds flattening (`j ≤ 4` for spartan-chain under 96 GB, [C1] §2.2).

### 2.3 Column R measures a step that need not be done

v3's second answer was to rank column R: the time of one fresh `PROVER node` run on the two level-7
proofs of the T run ([V3] §8.2–§8.3). Under v3's public oracle, a verifier with a **bundling**
branch (the root proof is the two child proofs, each checked by running `Vb` locally) is
certifiable as concatenation is: [V3] §8.7 treats "concatenation above" as certifiable and excludes
it only by size and time. One level of it fits `proofCap` for children up to about 512 KiB, and
fits `T_V` for children that verify in under half of `T_V`: under 38 ms at the long shape's 77 ms,
under 9.5 ms at the ranked shape's 19 ms. For such entries column R times a file copy, and board T
saves the root step. v3's defence ("R is measured on the T run's own level-7 outputs, in a fresh
process") does not touch it (paper; found for this document).

Under the relativized design the query cap decides it: with D4 alone a bundling verifier must make
each child's queries through the oracle service, so `qV ≤ 2^13` ([RD] §6.3) excludes two children
that each need more than 4,096 queries, and column R would survive; the channel split W5 counts only
the secret channel's roughly 500 queries per proof ([RD] §5.1) and reopens it ([CREVIEW] M5).

### 2.4 Witness-sending's margin at the ranked shape is thin

At `r = 8, n = 2^14` the best witness-sending root check takes about 191 ms of one core against
8–45 ms for real recursion, D4 and flat SNARKs, a margin of about 2–2.5× each side for any CPU-time
cap (**estimate**, [C1] §2.3). The rule `T_V ≤ T_triv,best / 10` gives 19 ms there, below some
honest recursive verifiers.

### 2.5 Scoring forms already rejected

- **A charge per oracle call** (the original relativized proposal): every self-measured form is
  gameable in a different direction: a padded or sleeping prover makes the slope in `n` zero or
  negative, one large query replaces hundreds, and local work goes unpriced ([A1] M3, M4; [C1] §3).
- **A statistic over many independent chains** ("a million chains"): measures single-leaf latency,
  8–41% of a tree's work, and takes 89 days at spartan-chain speed ([C1] §6, [A1] M5).

---

## 3. The model

### 3.1 The score

```
S = T_tree + K · t_link,        t_link = t_leaf + t_merge        (seconds; lower is better)
```

All components and `S` are published for every entry (§3.6). `S` is the time of a workload: prove
the benchmark tree, then `K` links of the stream.

### 3.2 The chain term `T_tree`

**What.** Board T as in [V3] §8.3 steps 1–5 and 7–10, at the long shape `r = 4`, `n = 2^20`
(`n` = v3's `chainCap`): 16 fresh secret starts, one `PROVER tree` process, all cores, 96 GB cgroup,
three repeats, median. Step 6 (column R) is replaced by §3.3. The root check keeps v3's succinctness
cap (§3.5).

**Anything goes inside.** Flattening, proof of parent, bundling near the root, higher-arity nodes
and grinding are all allowed in the T run: they change how the chains get proved, and the
recursion the competition wants is charged separately. Bundling near the root is small at the long
shape: at leanVM-class sizes `T_V` and `proofCap` admit a root bundle of at most 4 proofs, so it
saves at most two node latencies on the tree's critical path, about 0.8 s against roughly 41 s
(**estimate**).

**Why the long shape.**

- **Chains dominate** (G1): a leanVM-class tree is about 16 × 2.16 s ≈ 35 s of chain proving at
  Flock's published M4 Max rate, plus up to 15 × 0.394 ≈ 6 s of node steps, about 41 s in all
  (**estimate**).
- **Full witness-sending is excluded with room** (#6 (a)): the best witness-sending root check
  takes about 766 ms of one core against 8–30 ms for a real or flat root; `T_V = T_triv,best/10` =
  77 ms passes a real root by 2.6–10× and fails witness-sending by 10× (**estimate**, [C1] §2.3).
  *Partial* witness-sending is not excluded: the root verifier may finish up to `T_V/T_triv,best` of
  the chain work natively (CM-R7).
- **Concatenation stays excluded**: 16 leaf SNARKs verify in about 0.22 s, 2.8× over 77 ms
  (**estimate**, [C1] §2.2), and 16 leanVM-class proofs are 3.2 MiB against `proofCap = 1 MiB`.

**What it costs.**

- **The spartan-chain baseline cannot run it**: a `2^20`-step leaf scales to about 250 GB and a
  10.2 MiB proof, against 96 GB and 1 MiB (**estimate** by linear scaling, [C1] §6.1). The next
  baseline needs a leaner prover or a leaf that splits its chain internally.
- **Memory for a `2^20` leaf is unmeasured for the target class too**: Flock's published point is
  `2^18` compressions ([C1] §1), and a nearly flat 16-leaf proof, which §2.1 says such an entry would
  prefer, is 64 times that (CM-R5).
- **16 leaves are fewer than the cores**, so `T_tree` measures how well one large chain proof uses
  the whole machine, not throughput over many small proofs as v3's 256 leaves did.
- **Four times the chain work of v3's ranked tree** (`2^24` against `2^22` compressions).

### 3.3 The recursion term: the stream

The stream is built so that every proof in it is made on the clock, no process holds state from one
request to the next, and no process ever holds two chain starts.

**The workload.** Link `i = 0 … M` draws a fresh secret start `s_i` at length `n_f`; the runner
computes `d_i = leafStmt (chainEnd s_i n_f) n_f`. Link 0 proves leaf 0, and the running statement and
proof start as `(c_0, π_0) = (d_0, ℓ_0)`. Link `i ≥ 1` proves leaf `ℓ_i` and merges:
`π_i` proves `c_i = nodeStmt c_{i−1} d_i` from the children `(c_{i−1}, π_{i−1})` and `(d_i, ℓ_i)`.
Defaults: `M = 512`, `n_f = 2^16`.

**Protocol (one repeat).**

1. **A fresh process for every request.** Every leaf and every merge runs in a new prover process,
   in a new sandbox and cgroup. Its only writable path is its own directory; its only readable paths
   are the read-only setup directory (built in [V3] §8.3 step 2, before any instance existed) and
   the inputs the runner places in its directory. The runner kills the cgroup when the process
   answers. Nothing persists between requests except what the runner copies: proofs and digests.
2. **Ready, then timed.** A process starts, loads its setup and signals ready; start-up is untimed.
   The runner then writes the inputs and starts the clock, and stops it when the output is written.
   A leaf request (`PROVER leaf DIR`, new: one start and `n_f`, like `tree` with one leaf) outputs
   `ℓ_i`; a merge request (v3's `PROVER node DIR`, with the ready handshake added) outputs `π_i`.
   Each request is capped at `step_s = 600 s`, and the whole stream at `stream_s` (proposed 4 h).
3. **One thing at a time.** `s_{i+1}` is not released before `π_i` is written, and only one process
   works at a time, so each request has the whole machine.
4. **Checks** (untimed). Every `ℓ_i` and every `π_i` must be accepted for its statement by the
   compiled verifier, within the `T_V` cap and `proofCap` (§3.5); the canaries of [V3] §8.3 step 7
   run on `ℓ_0` and `π_1`.
5. **Values.** `t_leaf` is the sum of the `M + 1` leaf times over `M`; `t_merge` the sum of the `M`
   merge times over `M`; `t_link = t_leaf + t_merge`. Three repeats, each with fresh starts and fresh
   sandboxes and nothing shared between them; each value is the median of the three.

**Why each element is there.**

| Element | Strategy it stops |
|---|---|
| a fresh process per request, no persistent writable path | state across requests: a warm process could keep the uncompressed witness or accumulator of its own last output and fold the next child into it without verifying anything; here state survives only inside a proof, under `proofCap`, as it would between the nodes of a tree |
| every leaf proved on the clock, in the same term as the merges | preparation off the clock: the first form of this protocol prepared its inputs in untimed runs, where a prover could grind or pre-commit for free ([CREVIEW] M3). Now moving work between a leaf and a merge is score-neutral, since both weigh `K/M` per second |
| one start per process, released one at a time | precomputation and batching; and proof of parent, since no process ever holds two starts and so cannot make one flat proof that covers the running proof and the new leaf |
| each output is the next merge's input | bundling and partial proving defer work into a later timed merge instead of avoiding it; only the tail escapes (CM-R2) |
| the mean over links | a median ignores a schedule in which most merges bundle (near-zero time) and every few links one slow merge absorbs the backlog; the mean charges that slow merge in full |
| `M = 512` | bounds the tail (CM-R2) |
| `n_f = 2^16` | a merge process that learns the starts (CM-R1) and re-proves the whole stream so far instead of absorbing the running proof pays for `i + 1` chains of `2^16` (135 ms each at Flock's rate), more than one absorption (about 197 ms, half of leanVM's step) from the second link on; at `2^10` that re-proving would be cheaper for about the first 100 links. And a witness-sending chain of `2^16` takes about 3 ms to check natively, which bounds the tail (CM-R2) |

**What it measures.** The cost of extending a running proof by one fresh chain, with the running
proof made by another process, so it must be absorbed as a proof: nothing about it is in memory.
The entry chooses how to add the chain. A **2→1** link proves a separate leaf and merges the two
proofs: one leaf proof plus two absorptions. A **1→1** link sends a witness-sending leaf (its start)
and proves the chain inside the step: one absorption plus the chain. Since proving a chain inside
the step costs about what proving it as a leaf does, 1→1 saves one absorption and is the rational
choice (about 0.33 s against 0.53 s per link at leanVM-class speed, **estimate**, taking one
absorption as half of leanVM's 0.394 s step). Either way every link absorbs the running proof, so
the stream prices recursion; but its overhead `o` is one absorption under 1→1 and two under 2→1, and
no sequential, on-the-clock protocol can force a 2→1 merge of two independently made proofs,
because the prover can always fold the second child's work into the step instead (decision CM-4).
The 2→1 merge of two proofs is still what the tree's nodes do, in `T_tree`. When the stream does
2→1, every merge joins a deep proof and a leaf proof, as a tree's lowest nodes join leaves
(CM-R4).

**Shape requirements on the entry.** The stream builds a left-deep tree of depth up to `M`. The node
clause is shape-agnostic in v3 ([V3] §4), and v3's completeness quantifies over every statement and
witness, so the statements are in the relation and covered; under the relativized design,
completeness over honest contexts already covers them, since `Honest.node` takes any two honest
contexts ([RD] §4.5). The verifier must be fast on proofs of depth 512, far below the lopsided
depths that broke v3's verifiers (275 s at depth 6,000, [V3] §8.7, C9).

**What it costs to run** (**estimate**, leanVM-class): per repeat, 513 leaves of `2^16` at about
0.135 s and 512 merges at 0.15–0.4 s are about 2.5–4.5 minutes timed (less under 1→1), plus about
1,025 process start-ups, untimed (CM-R8).

### 3.4 The weight `K`

**Calibration from the leader.** Split a link into its chain part `t_c` (the entry's own time for
`n_f` chain compressions) and its recursion overhead `o`, so `t_link = t_c + o`. Recursion's share of
an entry's score is `K · o / S`. Choose `K` so that this share is `p` for the **leading** entry,
with its `T_tree`, `t_c` and `o`:

```
K = p · T_tree / ((1 − p) · o − p · t_c)
```

The denominator must be positive: `p` must be below `o/(t_c + o)`, recursion's share of a link. Setting `K` from the leader keeps chains first at every stage (G1): a target-based
`K` makes recursion the larger term for every entry slower than about 0.9 s per step, and most of
the score for the first entries, which is the opposite of the user's ordering ([CREVIEW] M6).

**Illustration** (**estimate**, not a proposal of a value): a leader at leanVM-class speed,
`T_tree ≈ 41 s`, `t_c ≈ 0.135 s` (`2^16` at 485k/s), an overhead `o = 0.394 s` (leanVM's published
2→1 step, as if each link were one such step), and `p = 15%` give `K ≈ 20` for the first season:

| overhead `o` | `K · t_link` (K = 20) | `S` | recursion's share of `S` |
|---|---|---|---|
| 2.0 s (a slow entry) | 42.7 s | 83.7 s | 48% |
| 1.0 s | 22.7 s | 63.7 s | 31% |
| 0.394 s (the leader) | 10.6 s | 51.6 s | 15% |
| 0.200 s | 6.7 s | 47.7 s | 8% |
| 0.150 s (the target) | 5.7 s | 46.7 s | 6% |
| 0.100 s | 4.7 s | 45.7 s | 4% |

Halving the leader's `T_tree` (−20.5 s) beats halving its overhead (−3.9 s): chains come first
(G1), while every millisecond off the overhead is worth 20 ms off the tree (G2). An entry with slow recursion
pays for it in proportion; it is ranked, not excluded (G3).

**Seasons: start high, then tighten.** `K` is fixed for a season and announced before it opens;
records are per season. At each season boundary `K` is recomputed from the current leader, so as
the leader's overhead falls, `K` rises and recursion keeps its share `p` of the leader's score: a
leader at 0.15 s gives `K ≈ 57` by the same formula. Because all components are published, `S`
under a new `K` can be recomputed for every past entry.

**The targets.** 150 ms is the middle of the user's 100–200 ms range and is used above for
illustration; 100 ms is the stretch. Both lines are drawn on the board as references and do not
enter `S`.

### 3.5 What stays pass/fail

The caps define a valid entry and bound the verifier. They are not performance targets, and without
them witness-sending would score `T_tree ≈ 0` and win.

| Cap | Applies to | Source |
|---|---|---|
| `T_V`: CPU time of one verification on one pinned core, `T_V ≤ T_triv,best / R` against the organiser's best interleaved chain checker, with `R = 10` as proposed in v3 (or 20: decision CM-8) | the root check of every T repeat, and every `ℓ_i` and `π_i` of the stream | [V3] §8.5 (V3-S2R-A7), calibrated at the long shape |
| `proofCap = 1 MiB`; `qV ≤ 2^16`; memory 96 GB | every proof the runner checks; every certified verifier; every prover process | [V3] §8.6 |
| `tree_s ≤ 4 h`; `step_s ≤ 600 s` per stream request; `stream_s` (proposed 4 h); `verify_s ≤ 60 s` | liveness bounds, not targets | [V3] §8.6; §3.3 |
| root, sample, canary, liveness and DoS checks | unchanged | [V3] §8.3 |

`T_V` by CPU time is itself unvalidated: CPU time does not remove SIMD ([V3] §16 C6, H-m10). At the
long shape its window is about 30–766 ms ([C1] §2.3), so the exact measure matters less there than
at the ranked v3 shape. The ratio `R` also sets how much chain work a root verifier may do natively
(CM-R7).

### 3.6 What is published, and records

Per entry: `T_tree` (median and the three repeats); `t_leaf`, `t_merge` and `t_link` (medians, the
three repeats, every request's time); the estimated overhead `o ≈ t_link − T_tree · n_f / 2^24`,
which charges the chain part at the entry's own tree rate (slightly high, since `T_tree` includes
the tree's nodes, so `o` reads slightly low) and is the number drawn against the reference lines;
the slowest merge and the mean of the slowest half of the merges (unranked latency columns, CM-R3);
`K`, `S`, and the reference lines. v3's record rule
(paired ABBA confirmation, median ratio ≤ 0.97, [V3] §8.4) applies to `S`. A record states the
season's `K`.

---

## 4. Why a weighted sum

| Property | How the sum meets it |
|---|---|
| G2, G3: monotone, no cliff | `∂S/∂t_link = K > 0` at every speed; no performance number is a threshold |
| G1 and the progression | `K` is set so the leader's recursion is a minority share `p`; each season's recomputation raises `K` as recursion improves, so the pressure on recursion grows while chains stay first |
| G4: bounded gaming | a strategy that fakes recursion can save at most `K · o`, a share `p` of the leader's score by construction, and the stream leaves only the escapes of §6 |
| interpretability | `S` is the wall time of a stated workload |
| re-weighting | components are published, so a change of `K` re-ranks old entries exactly |

Alternatives considered:

| Form | Why not |
|---|---|
| pass/fail gate on the recursion time | a cliff (G3); rejected by the user |
| product, `S = T_tree · t_link^α` | rewards each halving equally forever (G2), but the payoff of a near-zero recursion time is unbounded, so any flaw in the measurement becomes the winning strategy (G4) |
| board T alone, at any shape | recursion's share and flattening's gain are the same number ν (§2.1) |
| ranked column R | the bundling root makes it a file copy (§2.3) |
| CPU cap on every sampled proof | blind to proof of parent (§2.2) |
| a cap on each stream output's verification time relative to its inputs' ([CREVIEW] M2's rule: at most `α · min` of the two, `α < 2`) | defeated by a verifier that pads only its top-level verification: with padding `B` on every proof checked on its own, and none on children checked inside a bundle, a two-proof bundle verifies in `2v + B` against `v + B` for each input, a ratio under 1.8 once `B ≥ v/4`, which fits `T_V` (paper; found in the fix pass). Proof size and query count fall to the same padding |
| per-oracle-call charge; per-chain statistics | gameable; measure the wrong work (§2.5) |

---

## 5. Incentive analysis

| Strategy | Effect on `S` | What bounds it | Evidence |
|---|---|---|---|
| Full witness-sending tree | `T_tree` would be near zero | the root check fails `T_V` by about 10× at the long shape; the stream's outputs fail it after a few links | estimate, [C1] §2.3 |
| Partial witness-sending: the root verifier finishes chains natively | up to `T_V/T_triv` of the chain work skipped | accepted as a discount, 10% at `R = 10`, 5% at `R = 20`; about 0.2% under D4+ (CM-R7) | paper [CREVIEW] M4; [RD] §6.2 |
| Concatenating the 16 leaf SNARKs | skips all node steps in the T run | about 0.22 s against 77 ms (2.8×); 3.2 MiB against `proofCap` for leanVM-class proofs | estimate, [C1] §2.2 |
| Flattening, proof of parent in the T run | lower `T_tree` | allowed; under 15% of `T_tree` at the long shape; the stream is charged regardless | paper [A3] M1; estimate [C1] §2.2 |
| Bundling near the root of the T run | saves a few node latencies | allowed; `T_V` and `proofCap` bound it to two levels at leanVM-class sizes | estimate (§3.2) |
| Proof of parent in the stream | would make a merge free | no process ever holds two starts (§3.3) | protocol |
| Folding a child from memory | skips verifying one child | a fresh process per request; state only inside proofs, under `proofCap` | protocol |
| Starts smuggled inside proofs to a merge process | a merge proves the newest chain itself (1→1), or flat-proves the stream so far | 1→1 is legitimate and counted (§3.3); re-proving the stream costs more than absorbing from the second link on (CM-R1) | paper |
| Preparation off the clock | — | none remains: every leaf is proved on the clock, weighted like the merges | protocol |
| Bundling, partial proving inside the stream | defers work to a later timed merge | only the tail escapes: CM-R2 | paper |
| Absorbing several bundled proofs in one merge | lower mean link | counted as real aggregation (CM-R3, CM-4); latency columns published | paper |
| A merge specialised to deep-plus-leaf children | lower `t_merge` than a tree's upper nodes | a note (CM-R4) | paper |
| Precomputation | — | fresh starts per repeat, one per process, released one at a time; `setup` sees no instance | [V3] §8.7 |
| A recursion specialist with slower chains, or the reverse | — | legitimate: `S` trades them at the rate `K` | — |
| Grinding, retries | costs its time | on the clock everywhere ([V3] §6.4) | — |
| The oracle service as a free co-processor (relativized design) | — | the service runs in the prover's cgroup ([RD] §4.8) | — |

---

## 6. Residual risks

- **CM-R1: starts smuggled inside proofs.** A leaf process may put its start inside `ℓ_i` (a
  witness-sending leaf is a valid proof), and a process may copy starts into its output, so a merge
  process can learn every start so far. It holds no other state, so it can prove the newest chain
  inside the step (the 1→1 link of §3.3, legitimate and counted), or re-prove every chain so far
  instead of absorbing the running proof. At `n_f = 2^16` the latter costs more than one absorption
  from the second link on; a later season with much cheaper absorption may need a larger `n_f`.
- **CM-R2: the tail.** The last few merges can bundle, or leave chain hashing to the verifier, and
  never pay. A final output holds at most `c` deferred units, where `c` is the smallest of
  `T_V / t_v` (with `t_v` the native check of one proof or one witness-sending chain),
  `proofCap / |π|` and, under the relativized design, `qV / q_child` ([CREVIEW] M5). At `n_f = 2^16`
  a chain checks in about 3 ms, so `c ≤ 77 / 3 ≈ 25` at `R = 10`, and about 12 at `R = 20`;
  leanVM-class proofs give 4. So at most `c − 1` merges escape: under 5% of the merge time at
  `M = 512`, under 2.2% at `R = 20` (**estimate**).
- **CM-R3: higher arity.** A prover that bundles `j` merges and absorbs them in one verifies `j + 1`
  proofs in one circuit instead of two per merge, and its mean merge falls by up to about half as `j`
  grows (paper). Every proof is still verified in a circuit once, so this is real aggregation,
  legitimate inside a tree too; but it rewards throughput over the latency of one 2→1 merge, which
  the 100–200 ms target names. No statistic found separates the two robustly: a relative
  verification-time cap falls to top-level padding (§4), and a latency statistic such as the
  slowest half of the merges falls when a design's fixed cost per merge exceeds its cost per child.
  The mean is ranked and the latency columns are published (decision CM-4). The same holds for
  1→1 against 2→1 links (§3.3): the stream ranks the cheapest way to add a chain.
- **CM-R4: a merge specialised to the stream's shape** (a note). Every merge joins a deep running
  proof and a fresh leaf proof. A level-aware verifier (allowed, [V3] §8.7) may make leaf proofs
  cheaper to absorb than node proofs, which a tree benefits from only at its lowest level. At
  `r = 4` that level holds 8 of the tree's 15 nodes, so the bias is modest.
- **CM-R5: calibration and memory.** `K`, `T_V`, the targets and every time here wait for the
  reference machine ([V3] §16 C13). Flock's published rate and leanVM's step are on an M4 Max; the
  development VM lacks carry-less multiply and runs Flock about 400× slower (14.25 s against 34 ms
  for `2^14` compressions, [C1] §6.1). Memory for a `2^20` leaf, and for a nearly flat 16-leaf
  proof, is unmeasured for any prover class.
- **CM-R6: the oracle service under the relativized design.** With every hash going through the
  service (D4 alone), a Flock-class leaf's Merkle traffic costs about +30–110% of leaf time with a
  naive service, so `T_tree` and `t_leaf` would measure the service ([RD] §7.3, **estimate**). The
  channel split (W5, [RD] §5) reduces it to about 1.4% with a spinning ring, at the price of its
  extractability heuristic; a faster service ([RD] RO-9) is the alternative.
- **CM-R7: the root verifier's native share.** The rule `T_V ≤ T_triv,best / R` lets a verifier do
  up to `1/R` of the chain work natively: the root proof carries each chain's state a little before
  its end, `V` finishes the chains, and one proof, relabelled with a path as in proof of parent,
  covers the rest ([CREVIEW] M4). At `R = 10` that is about 10% of the chain work, roughly 3.5 s of
  a 35 s chain term, open to every entry. `R = 20` (38 ms) halves it and still admits real roots up
  to 38 ms; a real root at 8–30 ms needs `R` at most 25–95, so no ratio removes it. D4+ (R3) bounds
  it by `proofCap` to about `2^15` compressions, 0.2% ([RD] §6.2). In the stream the same trick only
  defers work to the next merge, except at the tail (CM-R2).
- **CM-R8: evaluation time.** About 1,025 process start-ups per repeat are untimed but take machine
  time; at one second each that is 17 minutes per repeat. A prover with a slow start-up makes
  evaluations long, not scores worse.

---

## 7. Effect on the other documents

**v3's record ([V3]), if this is adopted for the next iteration.** §7.3: the ranked shape becomes
`r = 4`, `n = 2^20`. §8.2: board T becomes the chain term, column R is replaced by the stream, and
`S` is ranked. §8.3: step 6 is replaced by §3.3, with a new `PROVER leaf` request and a ready
handshake on `leaf` and `node`. §8.5: the "recursion incentive" paragraph and both of its options
are superseded; the CPU-time `T_V` rule stays and also applies to every stream proof. §8.6: adds
`stream_s`. §8.7: the rows on witness-sending below level `j` and on column R are replaced by §5.
§16 C7 ("the score must price recursion or forbid flattening") is met by pricing.

**The relativized design ([RD]), if both are adopted.**

- **RU-4 is answered**: the long shape, with flattening openly allowed and recursion priced
  separately (RR-13).
- **R3 (D4+, the oracle-chain leaf) is not needed for #6 (a)**: at the long shape the CPU-time rule
  excludes full witness-sending with a window of 30–766 ms, and the stream's proofs face the same
  cap. It still buys one thing: it bounds the root verifier's native share of the chain work to
  about 0.2%, against `1/R` without it (CM-R7). Against that stand its costs: the tight `qV ≤ 2^13`
  (418 spare queries at `n = 2^20`), the `chain` call and key-dependent instances ([RD] §6). Whether
  that discount is worth R3 is decision CM-8.
- **R4 (W5) gains priority** because the chain term is the ranked priority and D4 alone taxes a
  Flock-class leaf (CM-R6). Note that W5 also loosens the query cap's hold on bundling (§2.3,
  CM-R2).
- **§4.5 needs no change** (`Honest.node` covers the stream's left-deep statements). **§4.8**: each
  T run and each stream repeat is one service lifetime with its own key and state; the stream's
  leaves and merges share it, and nothing is shared across repeats.

---

## 8. Decisions for the user

- **CM-1.** Adopt `S = T_tree + K · t_link` (§3.1), replacing board T alone and the two options of
  [V3] §8.5.
- **CM-2.** The share `p` that recursion should have in the leader's score (§3.4), from which each
  season's `K` follows, and the season length.
- **CM-3.** The ranked shape `r = 4`, `n = 2^20` (§3.2), accepting that the spartan-chain baseline
  cannot run there and that leaf memory is unmeasured.
- **CM-4.** Rank the stream's mean time per link, which counts 1→1 links and higher-arity merging
  as recursion (§3.3, CM-R3), and publish the overhead and latency columns beside it. A ranked 2→1
  merge of two independently made proofs is not on offer: on the clock the prover can always fold
  the second child's work into the step, and making that child off the clock (this document's first
  form) forces a real merge but reopens untimed preparation, worth up to about half a merge
  ([CREVIEW] M3). Which of the two the user prefers is this decision.
- **CM-5.** The stream's length `M` (default 512) and chain length `n_f` (default `2^16`) (§3.3).
- **CM-6.** A fresh process per stream request, with untimed start-up (§3.3, CM-R8).
- **CM-7.** The targets, 100 ms and 200 ms per merge, as reference lines on the board (§3.4).
- **CM-8.** The verifier ratio `R` (10 or 20) and whether to run R3 to remove the root verifier's
  native share of the chain work (CM-R7, §7).

---

## 9. Sources

[V3]: v3-design-agent-written-ROM-SNARK-verifier-for-BLAKE2s-hash-chain-trees-with-Lean-certified-knowledge-soundness.md
[RD]: DESIGN-relativized-recursion.md
[C1]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/C1-cost.md
[A1]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/A1-attacks-D1-D2.md
[A3]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/A3-attacks-D4plus.md
[CREVIEW]: reviews/DESIGN-cost-incentive-model-review.md

- **[V3]** the v3 design record, `docs/` on `main`: §4 (relation), §6.4 (completeness, grinding),
  §6.6 (recursion), §7.3 (shape), §8 (scoring), §16 (constraints C6, C7, C9, C13).
- **[RD]** the relativized design, `docs/` on `main`: §3.3 (flattening), §4.5, §4.8, §5 (W5), §6
  (D4+), §7 (benchmark), RU-4, RR-13.
- **[C1]** the exploration's cost note: §1 (inputs, with leanVM's and Flock's published figures),
  §2.2 (ν and the long shape), §2.3 (what a `T_V` cap separates), §3 (the oracle charge), §6 (the
  million-chains benchmark).
- **[A1]** attacks on the priced and pure-ROM designs: M3, M4 (the charge), M5 (per-proof
  statistics), M7 (flattening).
- **[A3]** attacks on D4+: M1 (proof of parent).
- **[CREVIEW]** this document's adversarial review (`docs/reviews/`), with the fix pass appended and
  a note that its verification was stopped unfinished.

---

## 10. Fix pass

The review ([CREVIEW]) found six major and eleven minor problems in the first form of this
document. What changed:

- **M1, M3** (isolation gaps; inputs prepared off the clock, and a candidate fix that broke the
  calibration). The recursion term is now the stream: every leaf and merge in a fresh process on the
  clock, one start per process, nothing shared across repeats. CM-R1's old form and decision CM-6's
  old form are gone. The review's own proposal (a warm third process proving small inputs on the
  clock) was not taken as written: a warm process keeps state across requests, and with small inputs
  a merge process that learns the starts could re-prove the stream so far more cheaply than it
  absorbs the running proof for many links, so the stream uses fresh processes and `n_f = 2^16`.
  Moving the inputs onto the clock also lets an entry add each chain by a 1→1 step, which §3.3 and
  CM-4 now state.
- **M2** (the tail bound was specific to leanVM; periodic bundling halves the mean). The tail bound
  is now general (CM-R2, including witness-sending chains and the query cap), with `M = 512`.
  The review's relative verification-time rule was not adopted: top-level padding defeats it (§4).
  Higher-arity merging is counted and the latency is published (CM-R3, CM-4).
- **M4** (the root verifier may do `1/R` of the chain work natively). Stated as CM-R7 and in §3.2,
  §5 and §7; R3's remaining value is now stated, and the ratio is decision CM-8.
- **M5** (the bundling analysis depends on the oracle model). §2.3 and CM-R2 now cover v3, D4 and W5.
- **M6** (a target-based `K` inverts chain priority at the start). `K` is now set from the leader
  each season (§3.4); G1 is stated for the leader and the targets.
- **Minor.** m1: [CREVIEW] is published beside this document, in `docs/reviews/`. m2: §2.3 states the `T_V` condition at
  both shapes. m3: `T_tree ≈ 41 s` in the calibration. m4, m5: the stream's requests are capped
  (`step_s`, `stream_s`), every stream proof is checked under the caps, and the interface is
  specified (`PROVER leaf`, the ready handshake). m6: [RD] §4.5 needs no change; the service
  lifetime is per run and per repeat. m7: G3 refers to prover performance. m8: leaf memory is an open
  measurement (§3.2, CM-R5). m9: CM-R4 is a note. m10: the `M` row cites CM-R2. m11: why 150 ms is
  stated (§3.4).
