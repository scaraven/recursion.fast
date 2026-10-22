# Adversarial review: DESIGN-cost-incentive-model.md (2026-10-22)

Reviewed against the user's goal (§1, G1–G5), [V3] §4, §6.6, §7, §8, §16, [RD] §3.3, §4.5, §4.8,
§5–§7, §12, and the branch notes C1, A1, A3, T1, W2. Tags as in the document: **paper**,
**estimate**, **measured**, **published**. Findings `M<i>` must be fixed; `m<i>` are answered or
argued.

## Verdict

The score's *shape* (`S = T_tree + K·t_step`, lower is better, caps pass/fail) is the right answer to
the user's words and meets G2, G3 and G5 as stated. The document is not adoptable as written because
its two load-bearing bounds do not hold: the recursion term can be cut by about half without a
faster 2→1 step through three channels the document under-sizes or leaves open (M1 isolation gaps
that let `t_step` fall to about zero if the protocol is implemented as written; M2 tail and periodic
bundling whose bound is entry-dependent, not 5%; M3 a CM-R1 candidate fix that contradicts the
calibration), and the chain term keeps a free 10% shortcut that the `T_V = T_triv/10` rule admits by
construction (M4), which also inverts the claim that R3 is not needed. The bundling analysis is
specific to v3's public oracle and changes under [RD] (M5). The first-season `K` makes recursion the
*larger* term for every entry slower than about 0.9 s per step, the opposite of "start high, chains
first" (M6). Each has a small fix; M2's fix (a relative verification-time cap on chain outputs)
removes CM-R2, CM-R3 and decision CM-4 in one rule, and M3's (time the fresh inputs inside the chain)
removes CM-R1 and CM-6. The arithmetic is otherwise right and every number I traced is in its cited
source with the right tag.

## Major findings

**M1. The protocol's isolation statements are incomplete, and the gaps are each a full break.**
*Location.* §3.3 steps 1–3: "in a separate sandboxed run", "no shared writable path and no channel
between them", "Three repeats, each with fresh processes", "Fresh input `i + 1` is not released
before `π_i` arrives". *Problem.* Four things the argument needs are not said:
(a) the fresh runs must be unreadable by X and Y and by *each other*. If fresh run `i` can read run
`i−1`'s sandbox it learns instances `0 … i−1`'s starts and embeds in `f_i` one flat proof of the
left-deep tree of instances `0 … i` (4·(i+1) chains, hours of untimed work, no cap on fresh-run time:
m4); X at step `i` then outputs that proof relabelled with a path (proof of parent, [A3] M1) at zero
cost: `t_step → 0`. The row "proof of parent: impossible" in §5 is only true with this isolation.
If a fresh run's sandbox is readable by X, the state "inside the proof, under the caps" argument of
the two-process row fails: the fresh run leaves the uncompressed witness of `f_i` on disk, unbounded.
(b) each repeat needs a fresh sandbox, not only a fresh process. The three repeats share the fresh
inputs ("shared by the three repeats"); if repeat 1's step directories persist, repeat 2's X copies
repeat 1's `π_i` for the same inputs and the median of three means is about zero. [V3] §8.3 step 9
has this rule for the T run; §3.3 does not inherit it.
(c) fresh input `i` must be released only to the process doing step `i`. If both see `f_{i+1}`, X at
step `i + 2` holds its own uncompressed state for `c_i` and `f_{i+1}`, and rebuilds a proof of
`c_{i+1}` from memory instead of verifying Y's `π_{i+1}` in circuit: exactly the "folding from memory"
the alternation exists to stop.
(d) the idle process must be frozen (cgroup freezer or SIGSTOP) between its steps; otherwise it
computes during the other's step on the same cores, and "each step has the whole machine" is false.
*Fix.* Add to step 2: one sandbox per fresh run, per step process and per repeat, each the only
writable path of its process and unreadable by every other; `f_i` and `d_i` are copied into the
working process's directory at release and nowhere else; the idle process is frozen while the other
works; the runner verifies each `f_i` under `T_V` and `proofCap` before the chain (see m4).

**M2. The tail-bundling bound (CM-R2, "at most 5%") is leanVM-specific; for an entry with small,
fast-verifying proofs it is 20–60%, and the default (the mean, CM-4) lets periodic bundling halve
`t_step` with no faster 2→1 step.** *Location.* §6 CM-R2 "4 for leanVM-class proofs … at most
`k = 3` steps escape … about 5%"; §3.3 table row "`M = 64` bounds what bundling at the end of the
chain saves"; CM-R3 and CM-4. *Problem.* The bundle capacity `min(T_V/t_verify, proofCap/|π|)` is
the entry's choice. A hash-based node proof of 75 KiB verifying in 5 ms (within reach of a WHIR-JB
class proof with a strong conjectured-soundness regime, [C1] §1 Table 5: 274–339 KiB at
`2^22`–`2^28` with `λ = 128`; smaller at lower security or with grinding) has capacity
`min(77/5, 1024/75) = 13`, so the last 12 steps are file copies and the mean falls 19%; at 2 ms and
30 KiB it is 34 steps and 53%. The bias rewards small proofs with fast verifiers, which is unrelated
to step speed. Independently, with capacity `c` a prover bundles `c − 1` steps and absorbs `c`
proofs in one circuit: per child it saves the per-proof fixed cost and the extra verifications of a
binary tree (`c` verifications against `2(c−1)`), so the mean falls towards a half; the document
concedes this as CM-R3 and leaves it to CM-4 with the only remedy an unranked column. Under the
default, the quantity the "100–200 ms" target names is not what `t_step` measures. *Fix.* One rule on
chain outputs, in addition to `T_V`: the CPU time to verify `π_i` (median of five runs, pinned core)
must be at most `α · min(t_V(π_{i−1}), t_V(f_i))` with `α < 2`, say `α = 1.8`. A bundle carries both
inputs raw, so its verification time is at least the sum, at least `2·min`, and is rejected whatever
the sizes; padding cannot help, because the rule is by time and the bundle's time is additive, and a
verifier that burns time on padding raises both sides. A step that verifies one input in circuit and
carries the other raw costs `t_V(carried) + t_V(SNARK)`, admitted only while the raw chain is short
(it grows by one proof per step and the bound does not), and every carried proof is still verified in
circuit exactly once later, so this variant is work-conserving. Honest fixed-circuit recursion
verifies every proof in about the same time and passes with margin. With the rule, CM-R2 and CM-R3
are closed, the mean is the latency of a 2→1 step, and CM-4 is decided. Bundling inside the T run
stays allowed. (The rule is mine, not in any note; it needs a paragraph of its own attack pass.)

**M3. The candidate fix for CM-R1 (fresh runs at weight 1, `K < M`) contradicts the calibration;
no weight on the fresh runs works; and CM-R1's size, which the document declines to estimate, is up
to half of a verifier-dominated step.** *Location.* §6 CM-R1 "add the fresh runs' times to the chain
term with weight 1 and choose `K < M` … never pays"; §3.4 `K ≈ 40`, `p = 15%`; §8 CM-6.
*Recomputation.* 65 fresh runs at leanVM-class rates cost `65 × (4 × 2.16 + 3 × 0.394) ≈ 640 s`.
With them in the chain term at weight 1 and `K < M = 64`, the recursion term is at most
`64 × 0.15 = 9.6 s` of `S ≈ 640 + 35 + 9.6`, a share of 1.4%, not 15%; restoring `p = 15%` needs
`K ≈ 800` and hence `M > 800`, 2.7 hours of fresh runs and 2–5 minutes of chain per repeat. Weighting
the fresh runs at `K/M` instead (score-neutral for moved work) makes the term
`K · (t_step + T_fresh) ≈ 40 × 10 s = 400 s`, again not 15% unless `K ≈ 0.6`, at which 1 ms off the
step buys 0.6 ms off the tree and G2 is nominal. Charging only the excess of a fresh run over
`T_tree/4` is defeated by padding `T_tree` (each second of padding lowers 65 charges by a quarter
second). So the candidate fix must be withdrawn, and CM-6 falls. *Size of CM-R1.* A step absorbs two
children and prepares one output; a tree node pays `P(p) + 2A(p)` at its best preparation level `p`,
a chain step pays at most `P(p) + A(p) + A(p_max)`, so the free amount is `A(p*) − A(p_max)`, up to
one absorption, which for a leanVM-class step (two verifier circuits are the node, [V3] §7.2) is up to
about half of `t_step`, i.e. up to `K·t_step/2 ≈ 8 s` of `S` at today's step. A concrete mechanism
is allowed by [V3] §6.4: proof-of-work soundness boosting. A fresh run grinds for minutes (nothing
caps it, m4) to cut its proof's query count, which cuts the in-circuit cost of absorbing `f_i`; a tree
node cannot afford that grind on the clock. *Fix.* Make the fresh inputs inside the clock. A third
process Z (`PROVER tree` kept warm, same isolation as X and Y) proves, on the clock, a tiny instance
(`d_f = 2`, `n_f ≈ 2^10`) whose root is `f_i`; then X or Y does the step. Z sees starts but never
merges; X and Y never see starts; Z's over-preparation costs Z's timed seconds. Per chain step the
clock then holds three Z nodes, four tiny leaves and one merge; define `t_step` as the chain's time
over `4M` node operations and publish the tiny-leaf bias (it is the entry's own fixed per-proof cost,
measurable from Z's leaf times). No untimed preparation remains, nothing is shared across repeats,
and the 10 minutes of fresh runs disappear. Two processes do not suffice: if X made the leaves Y
absorbs, X would hold a full witness for every `c_i` and never verify `π_i`.

**M4. The `T_V = T_triv,best/10` rule leaves one tenth of the chain work to the native root
verifier, free, at any shape; "witness-sending is excluded with room" holds for full
witness-sending only; and this is exactly what R3 (D4+) closes, so §7's "R3 is not needed" is
wrong on this count.** *Location.* §3.2 "Witness-sending is excluded with room … fails
witness-sending by 10×"; §3.5; §7 "R3 (D4+ …) is not needed". *Attack (paper, certifiable as [A3] M1
is).* The root proof is `(m_1 … m_16, π*)`: `m_i = chainEnd(s_i, n − t)` in the clear, `π*` one proof
(flat or recursive, the prover's own statement type) that each `m_i` is reached from a secret start in
`n − t` steps. `V` computes `h_i = chainStep^t(m_i)`, the 16 `leafStmt`s and `treeRoot` natively and
verifies `π*`; its extractor returns the starts and, for the node clause, the same `π*` relabelled
with a path for each child, as proof of parent does; the sample checks pass. The root check costs
`16·t` native compressions, interleaved and 8-way SIMD at 45.6 ns ([C1] §1, measured): under
`T_V = 77 ms` that is `16·t ≤ 1.69·10^6`, 10% of the `2^24` chain compressions, so about 3.5 s of a
35 s `T_tree` is never proved. The fraction is `T_V/T_triv,best` by the rule's own definition, so
"/10" means 10% at every shape; a real root at 8–30 ms needs `T_V ≥ 1–4%` of `T_triv` at the long
shape, so no ratio brings the shortcut below 1–4%. Under D4+ the verifier cannot compute chain
digests and the shortcut is bounded by `proofCap` to about `2^15` compressions, 0.2% ([A3] m3). *Fix.*
Either state the shortcut as an accepted, sized discount of the chain term (≤ `T_V/T_triv`) and say
that this, not only #6 (a), is what R3 buys; or keep R3 in the plan. Rewrite §7's R3 paragraph.

**M5. The bundling analysis (§2.3, CM-R2, CM-R3, CM-4, §7's R3 and R4 claims) is specific to v3's
public oracle; under [RD] the query cap decides it, in different directions for D4 and W5.**
*Location.* §2.3 "certifiable as concatenation is … fits every cap"; §6 CM-R2 "`min(T_V / t_verify,
proofCap / |π|)`"; §7. *Problem.* Under v3 a bundling `V` runs `Vb` on each child *locally* with
concrete BLAKE2s, so `qV` never sees it. Under D4 all-oracle it cannot evaluate `PRF_k` and must make
each child's verifier queries through the service, so a bundle of `b` children costs `b · q_child`
of `qV`: with the contract's `2^16` it fits for `b ≤ 6` at about 10k queries per leanVM-class child;
with [RD] §6.3's `qV ≤ 2^13` (which nothing ties to R3; spartan-chain fits it at both shapes) no
bundle of two leanVM-class children fits, column R is not a file copy, and CM-R2/CM-R3 are closed by
the cap. Under W5 (R4), which §7 says "gains priority", `qV` counts secret-channel entries only, about
500 per proof ([RD] §5.1), and a bundle of 8 fits `2^12` again. So the three decisions depend on
which design is adopted and the document does not say so. *Fix.* A third bound `qV / q_child` in
CM-R2's capacity, a sentence in §2.3 and §7 that under D4 with `qV ≤ 2^13` bundling is excluded and
column R viable, and that W5 reopens it; M2's rule works in every case and should be the primary
defence.

**M6. G1 holds only at the targets; for every entry slower than about 0.9 s per step recursion is
the larger term, and the first season's `K` is set from the target rather than from the field, which
inverts "start high … hash chains should be prioritised".** *Location.* §1 G1 "At the targets";
§3.4 table and "Seasons"; §4 "the score steers effort to recursion first". *Recomputation.* At
`K = 40`, `T_tree = 35 s`: `t_step = 0.5 s` gives 36%, `0.9 s` 51%, `2 s` 70%. An early entry whose
node is a spartan-chain-class circuit (ν = 3.16 leaf units at `n = 2^14`, [C1] §2.2) has a step of
tens of seconds and a score that is 95% recursion; the user asked for the opposite ordering at the
start. The document's own "Seasons" rule (set `p` at the leading step time) is the right one but is
applied only to later seasons. *Fix.* State G1 as "at the current leading step time and at the
targets"; set the first `K` from the leading step (`K = p/(1−p) · T*/t_lead`), with `K` rising per
season as the lead improves, which is the "start high" the user described; keep the table but add the
rows above 0.4 s.

## Minor findings

**m1. `[CREVIEW]` is a dangling reference.** §0 and §9 cite
`docs/reviews/DESIGN-cost-incentive-model-review.md` on `explore/relativized-nark`; the branch has no
such path (`git ls-tree` lists `DESIGN-relativized-recursion-review.md` and `EXPLORE-report-review.md`
only). Say "to be written" or drop the entry until it exists.

**m2. §2.3 contradicts §2.4 on `T_V`.** §2.3: a bundle of two is "twice a child's verification well
inside `T_V`"; §2.4: the `/10` rule gives `T_V = 19 ms` at the ranked shape, below `2 × 14.6 ms`. The
claim holds under a 75–93 ms cap (C1 row 6), not under the rule the document keeps. Qualify it.

**m3. `T*` is chain proving, not `T_tree`.** §3.2 puts the tree at "roughly 35–40 s" (35 s of chains
plus `15 × 0.394 = 5.9 s` of nodes, about 41 s); §3.4 calibrates with `T* ≈ 35 s`. With 41 s the
formula gives `K ≈ 48`, not 41. Harmless for a placeholder; say which it is.

**m4. The fresh runs are uncapped and unchecked.** §3.3 step 1 records their time but bounds nothing:
a run may take hours (M3's grind, M1(a)'s flat proof) and the harness budget is open-ended. Nothing
says `f_i` is verified under `T_V` and `proofCap` before the chain; an invalid `f_i` surfaces only as a
failed `π_i`. At `d_f = 1` ("halves the preparation") a witness-sending `f_i` covers `2^21`
compressions, 96 ms on one core, 1.25× over 77 ms: thin; at `d_f = 0` a single chain is 130 ms
sequential, 1.7×. Cap each fresh run (for example `tree_s/4`), verify every `f_i` under the caps, and
keep `d_f ≥ 2`.

**m5. `PROVER serve` is a new interface.** [V3] §8.3 defines `tree`, `node`, `setup`, `verify`; a
long-lived request-serving process is not among them. Specify the request format, how `(c, π)` and
`(d, f)` are delivered (files in the process's own directory per M1), and that a process that exits
or answers out of order fails the evaluation. Also: the chain's liveness budget is unstated; 64 steps at
`step_s = 600 s` is 10.7 h, above `tree_s = 4 h`.

**m6. [RD] interactions are stated once wrongly and once incompletely.** (i) §3.3 and §7 say [RD]
§4.5 "must count the chain's left-deep statements as honest contexts". It already does:
`Honest.node x y` takes any two honest contexts, of any depth; no amendment is needed. (ii) Under D4
the chain's `attest` calls on `f_i`'s list hashes succeed only if the fresh runs' `certify` calls and
the chain share one service state `S` and key `k`; [RD] §4.8 resets both per timed run, and the fresh
inputs are "shared by the three repeats". Either the whole chain evaluation (65 fresh runs and three
repeats) is one service lifetime, which should be said and weighed against [W2] M2's replay concern,
or the fresh inputs are regenerated per repeat (three times the 10 minutes).

**m7. G3 and `T_V`.** G3 says "no threshold on a performance number"; `T_V` is a threshold on the
verifier's CPU time. The document's position (an admission criterion, not a target) is defensible;
say in G3 that it means *prover* performance, so a reader does not read §3.5 as a violation.

**m8. The long shape's runnability by the target class is assumed.** §3.2 shows spartan-chain cannot
run it; nothing is said about memory for a leanVM-class leaf of `2^20` compressions (Flock's published
point is `2^18`, [C1] §1) under the 96 GB cgroup, or for a nearly flat 16-leaf proof, which §2.1 says
such an entry would prefer. Add an estimate or mark it an open measurement beside CM-R5.

**m9. CM-R4's mitigation addresses the wrong side.** At `r = 4` every tree node absorbs proofs of
depth ≤ 3, so a verifier specialised to shallow children is simply the tree's verifier; a random `d_f`
changes little. The chain's only asymmetry is the deep running child, which a design can only be
*worse* at (a format growing with depth), never better. CM-R4 can be downgraded to a note.

**m10. "`M = 64` bounds what bundling at the end saves" (§3.3 table) is not a bound** without M2's
rule; after M2 the row should cite the rule instead.

**m11. `t* = 150 ms`.** The user wrote "under 100/200ms"; the document calibrates at 150 ms without
saying why. One sentence (the midpoint; the 100 ms line is the stretch) suffices.

## Checked and found correct

- §2.1's algebra: full recursion `2^r + (2^r − 1)·ν`, flattening `2^r + (2^{r−j} − 1)·ν`, factor
  `(1 + ν)/(1 + ν/2^j) < 1 + ν`, share `ν/(1 + ν)`, `g = 1.15 ⇒ 13%`; the table's 2.3×, 3.5×, 7.5×,
  0.18, 1.17× and "under 15% at `j = 2`" (13%) all recompute from [C1] §2.2's ν values.
- §2.2 (flat branch, relabelled extractor, complete, within caps, invisible to a per-level `T_V`)
  matches [A3] M1 and [RD] §6.2; §2.3's bundling verifier is certifiable under v3 exactly as
  `concatState` and [V3] §8.7 row 2 say (local `Vb`, zero queries; see M5 for [RD]).
- §2.4: 191 ms, 8–45 ms, 2–2.5×, 19 ms are [C1] §2.3 row "ranked". §2.5: [A1] M3–M5, [C1] §3, §6.
- §3.2: `2^20/485,033 = 2.16 s`, `16 × 2.16 ≈ 35 s`; 766 ms (`2^24 × 45.6 ns`), 77 ms, 2.6–10×,
  10×; `16 × 13.5 ms = 0.22 s`, 2.8×; `16 × 206.3 KiB = 3.2 MiB`; 250 GB and 10.2 MiB as [C1] §6.1
  states them; root bundle of 4 at leanVM sizes, two latencies ≈ 0.79 s.
- §3.3: `65 × 4 = 260` chains, about 10.6 min with nodes; depth 66 against [V3] §8.7's 6,000; the
  per-step accounting ceiling (one absorption) is right (M3 sizes it); the mean is the right statistic
  against periodic bundling; the first chain output covers 8 chains at `d_f = 2`.
- §3.4: `K = 0.15/0.85 × 35/0.15 = 41.2`; the five table rows (15.8 s/31%, 8.0/19%, 6.0/15%,
  4.0/10%, 2.0/5%); `−17.5 s` against `−3 s`.
- §3.5's caps and sources ([V3] §8.5, §8.6); CM-R5's 400× (`14.25 s / 33.8 ms = 421`); CM-R6's
  +30–110% ([C1] §5.4) and 1.4% ([RD] §7.3).
- §4's monotonicity (`∂S/∂t_step = K`), the rejection of the product form, and the interpretation of
  `S` as a workload.
- G5: nothing in the proposal touches the relation, `Security.lean` or the trusted base.
- The left-deep statements are in [V3] §4's shape-agnostic relation and covered by v3's
  `CompleteWithError` (`∀ c w`) and [RD] §4.5's `Honest` (m6 (i)).
- Precomputation, grinding, the runner's digests and the oracle service rows of §5: the digests carry
  no information; grinding is on the clock inside the chain; the service is in the prover's cgroup.

## Fix pass (the author, 2026-10-22)

Every major finding was acted on; the document's §10 lists the changes finding by finding. In short:

- **M1, M3.** The recursion term is now a stream in which every leaf and every merge runs in a fresh
  prover process on the clock, with one start per process and nothing shared across repeats (§3.3).
  The warm third process proposed in M3 was not taken: a warm process keeps state across requests,
  and with small inputs a merge process that learns the starts could re-prove the stream so far more
  cheaply than it absorbs the running proof, so the stream uses `n_f = 2^16`. Putting the inputs on
  the clock lets an entry add each chain by a 1→1 step that proves the chain inside the step; §3.3
  and decision CM-4 now say so.
- **M2.** The tail bound is now general (CM-R2: the native check of one proof or one
  witness-sending chain, `proofCap`, and `qV` under the relativized design), with `M = 512`. The
  relative verification-time rule was **not adopted**: a verifier that pads only its top-level
  verification makes a two-proof bundle verify in `2v + B` against `v + B` for each input, a ratio
  under 1.8 once `B ≥ v/4`, inside `T_V`; proof size and query count fall to the same padding
  (document §4). Higher-arity merging is counted and latency columns are published (CM-R3, CM-4).
- **M4.** Stated as CM-R7 (the root verifier's native share, `1/R` of the chain work), with R3's
  remaining value and the ratio `R` as decision CM-8.
- **M5.** §2.3 and CM-R2 now cover v3, D4 alone and W5.
- **M6.** `K` is set from the leading entry each season (§3.4); G1 is stated for the leader and the
  targets.
- **m1–m11.** Answered in the document's §10 (m1: this file is published beside the document).

## Verification of the fix pass

A verification pass by the same reviewer was started on the fixed document and **stopped
unfinished at the user's request** on 2026-10-22, before it wrote any finding. The fix pass is
therefore unverified; the user has said the document will get its own independent adversarial
review.
