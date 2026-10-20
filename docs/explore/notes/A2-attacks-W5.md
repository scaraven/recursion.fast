# A2. Attacks on W5 (the channel split) with W4 attestation

Adversarial note, 2026-10-20, against W1 §6–§7 (`W1-workarounds.md`), read with W2 (D4, which W5
modifies), C1 §4–§5, L1, and the F2 memo's §1.2 and §14. Tags as in the brief: **kernel**, **paper**,
**measured**, **estimate**. Findings `M<i>` must be fixed before W5 is adopted; `m<i>` are answered.
Numbers are spartan-chain at `n = 2^14` (brief §2, **measured**) unless tagged. The P3 probe of
`pubStep` was running in parallel; nothing here waits for it, and §8 says what it must test.

## Verdict

1. **W5's model is broken as written, in three places, all fixable.** (M1) `final` quantifies over
   every `pubConsistent` log, but `V` hashes locally and reads only `sec` entries, so the honest log
   with its `pub` entries deleted still makes `V` accept and leaves `E` nothing to decode from: no
   compressing verifier has a `KState`. (M2) `pubStep` is false for the natural Merkle potential,
   because a deterministic channel lets the adversary log a preimage *after* using its digest (a late
   preimage is neither a collision nor a charged event). (M3) `Collision L` ("a collision is in the
   log") cannot state the tree theorem, whose collisions are between the harness's digests and the
   extracted ones, so the escape must be W2's constructive `Out.coll`. The fixes are two trusted
   definitions (`V` queries the public channel, and a log-ordering hypothesis `pubOrdered`) plus
   W2's `Out`/`Sound`: about +20 code lines over W1's estimate (§7).
2. **With the fixes, W5's security story holds, but its headline is overstated.** The third
   assumption is not "preimage-aware use of BLAKE2s" as a falsifiable hash assumption: it is the
   ideal-compression-function heuristic restricted to extractability (M4), which BCPR14 says cannot be
   upgraded to a standard-model assumption. W5 therefore trades D4's two falsifiable assumptions
   (PRF, CR) for PRF, CR and one ROM-type heuristic, in exchange for `10^3` less service traffic.
   That heuristic is strictly weaker than v3's (it drops unpredictability, which is what CGH attacks),
   and no competitor can exploit it (§1.4): the F2 disguises and the liveness mirror all stay closed.
3. **W4's attestation needs W2's recursive `att` items and a clean-replay session rule (M5)**; W1
   omits both, and without them neither the "≈ 500 entries" nor the one-log composition hold.
4. **The incentive claim (1.00× + 2%) checks out** for spartan-chain and shrinks to ≈ 0.5% once
   challenges are bit-sliced from answers (which the model forces, m6). Nothing games W5 that does not
   game D4 and v3 identically (#6 is untouched). The one new engineering hazard is latency, not
   throughput: ≈ 500 sequential RTTs per proof cost a Flock-class leaf 1.4% at 1 µs and 52% at a
   futex (m9).
5. **Ranking:** W5+W4 (fixed) > D4 all-oracle > v3, with the proviso that D4 is the design to choose
   if the user refuses any ROM-type heuristic at all. Confidence that the fixed W5 is sound: ~75%
   (paper); that its Lean form lands in one stage: ~40% (the ordering hypothesis is the risk).

## 0. The laws under attack (W1 §7.1, restated)

`Log := List Entry`, `Entry = sec (q, a) | pub (q, a)`; `V.runLog L` reads `sec` only; `V` computes
BLAKE2s locally; `pubConsistent L := ∀ pub (q, a) ∈ L, a = blake2sDigest q`. `KState`: `empty`;
`step` on fresh `sec` queries (average over `2^256` answers rises `≤ ε`); `pubStep : pubConsistent L →
μ (L ++ [pub (q, a)]) ≤ μ L`; `final : pubConsistent L → μ L < 1 → V.runLog L c π = some true →
(∃ w, E c π L = some w ∧ RelL L c w) ∨ Collision L`, `Collision L := ∃ q ≠ q', pub (q, a), pub (q', a)
∈ L`. Deployment: `sec` is the harness's `PRF_k`, `pub` is BLAKE2s computed by whoever; the child's
`sec` answers are attested by W4's session list; "the deployment adversary is any program whose
BLAKE2s outputs come from calling BLAKE2s".

## 1. The public-channel model

### 1.1 M1. `final` is unsatisfiable for every compressing verifier (the stripped log)

*Attack (paper, elementary).* Take the honest prover's proof `π` for a leaf and the honest log `L`;
let `L⁻` be `L` with every `pub` entry deleted. `pubConsistent L⁻` holds vacuously. `V` reads only
`sec` entries and hashes locally, so `(V c π).runLog L⁻ = some true` exactly as on `L`. `μ L⁻ < 1`:
`L⁻` is reached from `[]` by `sec` steps alone, so by `step` the average of `μ L⁻` over the squeeze
answers is `≤ Q_sec · ε`, and for most honest answer sequences `μ L⁻ < 1`. `Collision L⁻` is false
(no `pub` entries). So `final` demands `E c π L⁻ = some w` with `RelL L⁻ c w`: a chain start from the
proof and the squeeze answers alone. A succinct proof opens `t ≈ 190` of `2^17` columns; the rest of
the codeword is nowhere. The submitter cannot define `μ` around it: `μ` is a function of the log, and
`μ L⁻ ≥ 1` on every accepting `L⁻` would make the first squeeze raise the average from `0` to `≈ 1`,
violating `step`. This is P1's `lazy_no_kstate` (**kernel**) in the new clothes: a verifier whose
hash checks are not oracle queries has no knowledge state.
*Consequence.* No Merkle-based `V` is certifiable under W1 §7.1; only witness-sending is (`μ := 0`).
W1 §7.4 item 1 silently assumes the adversary logs the leaves and that "already-logged digest"
includes digests `V` only computes locally; neither is in the laws.
*Smallest fix.* `V` (and `P`) are query programs over **both** channels: `OProg` gains `pubq (q : ByteArray)
(k : Digest → OProg α)`; `runLog` answers it from the log's first `pub (q, _)` entry and returns `none`
if there is none; `run H` answers it with `blake2sDigest q`. Then `V`'s every hash check is a lookup
the adversary must have logged, the stripped log makes `V` return `none`, and "`V` computes BLAKE2s
locally" is still allowed but useless (a local check that is not a `pubq` cannot be used by `E`, so a
`V` that relies on one is uncertifiable, which is the right incentive). About +6 trusted lines. The
deployment reading changes accordingly (§1.3).

### 1.2 M2. `pubStep` is false under late preimages; the channel needs an ordering hypothesis

*Attack (paper).* With M1 fixed, let `V` be an honest Merkle verifier with one `sec` squeeze. The
natural potential is W1's: after the squeeze, `μ = 1` iff all `t` squeezed positions have complete
logged paths and the logged leaves are below the decoding threshold. The adversary logs nothing,
squeezes on a root `r` it merely wrote down, learns the positions, then logs the `t` paths it needs,
bottom-up, ending with `pub (c₁ ‖ c₂, r)`. Every entry is `pubConsistent`; no two entries share a
digest, so there is no `Collision`; `V`'s lookups all succeed. Before the last entries `μ = 0` (no
complete path); after them the positions are all "known" with `|K| = t` leaves: `μ = 1`. A `pub` entry
raised the potential, so `pubStep` fails for this `μ`; and no other `μ` works, because the same log
with `E` unable to decode is accepted at `μ < 1` unless some `pub` entry raised `μ`. W1 §7.4's case
split ("the logged preimage, or a second preimage") misses the third case: a digest that appeared in
an input (the squeeze's, a parent's) before any entry produced it. In the ROM this costs `2^-256` per
fresh answer; a deterministic channel charges nothing. W1's fallback law (`∨ Collision (L ++ [e])`)
does not help: there is no collision.
*Consequence.* `pubStep` as stated is unprovable for every honest compressing `V`; the "one-day probe"
will fail or, if it builds the potential on the final log's `pub` set, will fail `final` instead.
*Smallest fix.* A hypothesis on logs that says what "the adversary's hash values enter through the
box" means: **`pubOrdered L`: for `i < j` with `L[j] = pub (x, d)`, the digest `d` does not occur
(as a substring at any offset) in the input of `L[i]`, `sec` or `pub`, unless `x` begins with a
relation tag (`tagChain`, `tagLeaf`, `tagNode`).** The exemption is needed because the honest prover
receives statement digests it may recompute late (column R's `node` mode is handed child digests),
and such preimages are 65-byte tagged strings that no commitment path contains if the submitter's
`V` keeps its commitment inputs off the relation tags (its own obligation, as with `tagRO` today).
With `pubOrdered`, the Merkle argument goes through: the root is in the squeeze input, so its entry
precedes the squeeze; its input holds the level-1 digests, so their entries precede it; by induction
every path `V` looks up was logged before the squeeze, the squeezed positions lie in `K(prefix)`, and
the potential "some squeeze in `L` landed in a `K(prefix)` below threshold" is raised only by `sec`
steps (`≤ (|K|/N)^t ≤ ε`) and never by `pub` entries (prefixes are fixed). A later second preimage
of a logged digest is W2's `Out.coll`. About +8 trusted lines (a substring predicate over
`ByteArray`), one hypothesis in `pubStep` and `final`, and a deployment claim stated in §1.3.

### 1.3 M4. The third assumption is a ROM-type heuristic, not a falsifiable hash assumption

*Defect.* W1 §7.3 names "preimage awareness (Dodis–Ristenpart–Shrimpton 2009)" and concludes "hash
assumptions only". DRS define PrA for a hash `H^P` built from an ideal primitive `P`: the extractor
sees the adversary's `P`-queries, and Merkle–Damgård/HAIFA with an ideal compression function is PrA
(**paper**, DRS09 Thm 4.1–4.2; BLAKE2s is HAIFA-shaped). In the standard model there is no "trace of
the adversary's compression calls": an obfuscated BLAKE2s has none. The assumption W5 deploys under
is therefore: *the prover's BLAKE2s evaluations, in the order it used their outputs, form a log that
is `pubConsistent` and `pubOrdered`*, which is PrA with the identity extractor relative to an ideal
compression function, i.e. the ROM for BLAKE2s's inner primitive, used only for its extractability
consequence. It is not falsifiable in Naor's sense (no challenger can check what an adversary "did
not compute"), and Bitansky–Canetti–Paneth–Rosen (STOC 2014) show that extractable one-way functions
with arbitrary auxiliary input do not exist if indistinguishability obfuscation does, so no
standard-model replacement exists. What W5 honestly drops from v3's heuristic is *unpredictability*
(the half CGH breaks); what it keeps is *extractability* (the half CGSY24 Fig. 1 calls "attacks on
hash-based PCD are no more effective than on the idealised non-succinct PCD").
*Consequence.* W1's comparison table should read "PRF, CR (falsifiable); extractability heuristic
on BLAKE2s" for W5 against "PRF, CR" for D4 all-oracle, where the service's log *is* the trace
(W2 m7) and no heuristic is needed. The whole-tree bound at deployment becomes
`(Q_sec + qV)·ε + Adv_PRF + Pr[E outputs a collision] + Pr[the trace is not pubOrdered]`, the last
term being the heuristic (plus `≤ 2^-160`-order accidents, which only remove the theorem's coverage).
*Smallest fix.* State it so in §5.4's replacement and in the trust statement; keep D4's all-oracle
form as the no-heuristic fallback; have the harness check `pubConsistent ∧ pubOrdered` on the native
prover's emitted log at liveness size (§6.3 step 8 already checks every entry's hash), so the
heuristic is at least tested on one real trace per entry.

### 1.4 Can a competitor exploit the gap? No (paper); the two sides separated

- **V-side recognition (CGH).** Needs a value in `V` correlated with the deployed function but not
  obtained through a query. `sec`: `PRF_k`, no such value before `k` exists (L1 §11 fact 2).
  `pub`: with M1 fixed, `V`'s hash answers come from the log and equal BLAKE2s in the model and at
  deployment; a local BLAKE2s in `V` agrees with them in both worlds. So every branch of `V` has the
  same truth value in the model as at deployment, and a branch accepting a magic proof is
  unconditional, hence uncertifiable by the accept-all argument (`acceptAll_kstate_iff`, **kernel**
  today; `Computes` with the named `E`). Closed without review.
- **Prover-side non-black-box hashing.** The theorem covers every trace that is a `pubOrdered`
  log; the gap is a trace that is not: a digest used before its preimage was computed. Sources of
  such digests: offline work by the submitter (count it as a log prefix: the adversary is the
  submitter plus its binary, and `E` is never run on ranked proofs anyway, so only the paper claim
  changes); digests the harness hands over (statements: exempted by tag; `sec` answers: not `pub`
  outputs, so unconstrained); invented bytes later shown to be an image (a preimage attack, or the
  heuristic failing). To turn any of these into a cheap trash proof, the prover must make a certified
  `V` accept a proof for a **fresh** statement `c = leafStmt (chainEnd s n) n`; by `final` on the
  trace-as-log, acceptance at `μ < 1` means the logged leaves decode to a witness for `c` (or a
  collision), and no offline table holds a chain for a start sampled after freeze. An iO-style
  counterexample (an obfuscated program answering openings for a root it "does not know") would have
  to produce accepting transcripts under `PRF_k` for fresh `s`: a soundness break of the SNARK, not
  an extractability failure. So the gap costs the paper claim a heuristic and the competition
  nothing, provided M1–M2 are fixed so that the heuristic has a precise hypothesis to discharge.

## 2. The F2 disguises and the liveness mirror, one by one

| Disguise | Under W5 (with M1–M2 fixed) | Status |
|---|---|---|
| §1.2 literal trigger | against a `sec` answer: fires w.p. `≤ Adv_PRF + 2^-256`; against a `pub` answer or a local BLAKE2s: same truth value in the model, so the accepting branch is unconditional and `final` fails on the honest log (port of `Controls/Backdoor.lean`, the 40-line negative control W1 proposes) | closed |
| §14.1 `evalPoly` recognition | the interpolated set would have to be `PRF_k` challenges; proof-supplied coefficients fixed before `k` exists | closed |
| §14.4 position channel | positions are bit-slices of `sec` answers (m6); a constant position fires w.p. `2^-ℓ` in both worlds | closed |
| §14.5 liveness mirror | `sec`: `V` cannot single out the deployment (PRF); `pub`: the channel is concrete in the model too, so a rejection keyed to a hash property fails `CompleteWithError` for the same `(c, w)` in the model (`∀ c w`, δ over `sec` answers only). The harness's root, sample and liveness checks stay as defence in depth | closed |
| §14.6 review evasion | nothing to recognise; review is hygiene | moot |
| R2.1 post-hoc verification | `c₁ = Σ outbitᵢ·βⁱ` over BLAKE2s wires never equals a `PRF_k` challenge; over a `pub` value it is an identity true in both worlds, i.e. a redundant check. The node circuit's checks on the *child's* challenges (W4 list items) satisfy (INV): they are witness data committed before the node's own squeezes | closed |
| **New: two-channel comparison** | `V` tests a relation between `sec (q)` and `pub (k' ‖ q)` for a `k'` in the proof: certifiable by F2 §6's two-point counting, fires only on proofs carrying `k`, which exist only after key release (§4) | closed before release; see m10 |
| **New: service symbols** | a refused call (cap, malformed, crash) must abort as a reject, never return a value `V` can branch on (W2 M11 caveat) | rule |
| **New: `Published` as an oracle** | `V` may probe `Published h` for any `h`; the model quantifies over every set `S` consistent with `L`, so no randomness is exposed | closed |

The two-channel model closes the disguises by *removing divergence* on `pub` and *removing
knowledge* on `sec`; neither argument uses review, and both are kernel-checkable as negative controls
(a `V` comparing channels has no `KState` on logs where the two values differ, i.e. all but `2^-256`).

## 3. The new laws: `pubStep` and "witness or collision"

**M3. The collision escape must be constructive, or the tree theorem is vacuous or unstatable.**
*Defect.* W1's `Collision L` is non-vacuous at a node (the submitter cannot put a BLAKE2s collision
into the honest log), but the whole-tree statement (W2 A.6, `treeExtract`) meets collisions that are
*not in `L`*: an extracted `(c₁, c₂)` with `nodeStmt c₁ c₂ = nodeStmt c₁* c₂*` against the harness's
pair, whose two 65-byte preimages nobody logged; a list mismatch `enc xs ≠ enc xs'` with equal hashes
where only one side is a `pub` entry. The Library theorem would have to say "… or a collision
exists", which Lean proves by pigeonhole (`Finite.exists_ne_map_eq_of_infinite`, W2 M5), making it
true of every verifier. *Fix.* W2 A.4 verbatim: `E : … → Option Out`, `Out = wit w | coll x y`,
`Sound (R L) c (.coll x y) := x ≠ y ∧ blake2s256 x = blake2s256 y`, with `Computes` binding the
step-bounded program to the output. Node, list and tree collisions are then all *returned*. Drop
`Collision L`; the liveness check must accept a `.coll` output only after checking the two strings
(two hashes), so that a `V` whose `E` "always finds a collision" fails liveness (W1 §7.8.3).

**m1. Vacuity and unsatisfiability checks on the fixed laws, for honest verifiers.**
- *Late preimages:* excluded by `pubOrdered` (M2); the honest prover never uses a commitment digest
  before computing it, and may recompute statement digests late by the tag exemption.
- *Merkle caps, shared prefixes, batched openings:* the cap digests are in the squeeze input, so
  their entries precede it; shared prefixes are shared lookups; a batched opening of `t` positions
  is `t` lookups per level. All fit the induction of M2 unchanged.
- *Openings spanning several squeezes (WHIR/STIR-class):* the potential is the product form of
  `Controls/Potential.lean` (`twoLucky`) over `sec` entries only, each squeeze's factor computed on
  the `pub` prefix before that squeeze. `pubStep` holds because prefixes are fixed; the open question
  W1 §12 names is only whether the product bound meets `errorCap` for the design's `t`, as in v3.
- *A collision existing classically:* `Sound`'s `.coll` names concrete strings; the submitter cannot
  exhibit one; a public BLAKE2s collision would let any prover log it, after which every certified
  `V`'s `final` is discharged by `.coll`: that is "collision resistance is the assumption", a
  one-shot public event that breaks every hash-based SNARK, and it is at least constructive here.
- *Truncated labels or non-BLAKE2s modes:* a `V` comparing 16-byte Merkle labels cannot charge a
  `2^64`-work truncated collision (no `.coll` on full digests, no randomness to charge): uncertifiable,
  as v3's `logCap` arithmetic makes 224-bit comparisons the minimum. A compression-only tree (raw
  `compress` without finalisation) has no `pub` representation: uncertifiable. Both are features; a
  64-byte node input is one compression in finalised BLAKE2s too, so the honest design pays nothing.

**m2. `logCap` and the tape.** `step`'s guard `L.length < logCap` now counts `pub` entries; W1 says
`logCap` counts `sec` entries only, so the guard must be `(L.filter isSec).length < logCap`. The
`pub` entries are bounded only by the extractor's tape (`2^61` entries): at ranked size the trace is
the evaluation's whole hash log (gigabytes, as W2 M6 says for D4), at liveness size megabytes.

**m3. `pubStep` should take `a = blake2sDigest q`, not `pubConsistent L` alone**, else the law
also constrains inconsistent appends, which `final` never sees; harmless but it costs the submitter
a case. `pubConsistent` is a `Prop`; no proof ever evaluates BLAKE2s.

**m4. Challenge-free and local-challenge verifiers.** A compressing `V` with no `sec` query must
satisfy `final` on every ordered log, including one whose root was chosen after a local-BLAKE2s
challenge; uncertifiable (W1 §7.4.3, correct). Witness-sending (no `sec`, no `pub` lookups it needs)
keeps `μ := 0` as in v3 and D4: issue #6 is untouched.

## 4. Challenge-only attestation (W4 session lists)

**M5. Recursive attestation is forced and W1's W4 omits it; a session protocol must be in the rules.**
*Defect.* The node circuit proves "`V` accepts the child reading `xs`", and the child's `V` itself
checks `Published h` for the grandchildren's lists. Inside the circuit that answer must come from
`xs`, so lists need W2's `att h` items, checked by the service at `close` against its own log (W2
A.1: "recursive attestation is forced, not optional"). W1 §6 describes `Published` as a file lookup
at the root only, which is the flat variant: `2^{r+1} − 1 = 511` hashes carried to the root, linear in
the tree. *Second defect.* The service lists *everything it returned in the session, in order*. An
honest prover grinds (`2^g` tries per round), retries after self-checks, and runs 32 threads; a
session scoped to "the proving of one leaf" holds `2^g×` the final transcript's entries and in
thread order, and the circuit hashes all of them. The prover must therefore replay the final
transcript's ≈ 500 queries, in order, in a fresh clean session after proving, and close that one
(answers are `PRF_k`, so a replay returns the same values; in the model a repeated query is not a
`step`, and `Valid`'s "first answer" semantics cover it). *Consequence.* Without `att` items the
composition from one log fails at depth 2; without the replay rule the "2%" is `2^g · 2%`.
*Fix.* Adopt W2 A.1–A.2 for the list (items `ans`/`att`, `tagList`, prefix-free `enc`, caps
`|xs| ≤ 2^16`, `|q| ≤ 2^20`), with `close` playing `certify` (it also checks `att` items) and the
root's `Published` replacing `attest`; write the clean-replay session into the prover interface.

**m5. Binding of a list to its roots.** A list is a set of true `(q, PRF_k q)` facts bound to no
statement; the binding is inside `q` (the transcript state containing the root) for any `V` that
squeezes on its transcript. Superset lists, lists shared by two children, lists holding answers to
queries no verifier makes: all harmless (`V` reads what it asks; extra items cost circuit bytes).
A `V` squeezing `PRF_k (counter)` with no root in `q` is uncertifiable (the model's adversary builds
the tree after the squeeze and `pubOrdered` does not constrain it), as it should be.

**m6. The model forces challenge entropy to be read as bit-slices of `sec` answers.** A `V` that
squeezes one seed and expands it by local BLAKE2s (`pos_i = BLAKE2s(a ‖ i)`, WHIR/STIR practice)
must prove, in `step`, a bound over `2^256` seeds on how often *BLAKE2s's* expansion lands in `K`:
a statement about the concrete function, not provable in Lean. Linear use (positions as 17-bit
slices of `a`, field challenges as 64-bit slices) gives the exact `(|K|/N)^t` count. So an honest
`V` takes ≈ 13 answers for 190 positions plus ≈ 100 for field challenges: a list of 100–150 items,
not 476, and the attested share of the node falls to ≈ 0.5% (**estimate**). W1 should say so: it is
a redesign for seed-expanding verifiers and a cost saving for everyone.

**m7. Grinding and re-querying.** Grinding tries are independent queries (`transcript ‖ nonce_i`),
so the prover's client batches them (W2 A.1's rings); the final transcript is replayed (M5); every
try is charged by `step` at its first query, none by the circuit. Grinding `h_s` is useless (W1).

**m8. Replay, sessions across repeats and column R.** Fresh `k` and a fresh log per timed run (W2
M2); the root, sample, canary and column-R checks run before the reset so that `node` mode attests
level-7 lists from the same run. Cross-evaluation replay is already dead by fresh starts (the
statement differs), and additionally by the per-evaluation log. The log must be per evaluation,
never global, else an old `h` is `Published` and only the statement mismatch saves the root.

**m9. Latency, not throughput, is the service's cost under W5.** Per tree ≈ 511 × 476 ≈ 2.4·10^5
calls, negligible CPU (C1 §5). But Fiat–Shamir calls are sequential within a proof: 476 RTTs per
leaf cost 0.48 ms at 1 µs (spinning shared-memory ring, C1 §5.2 row `B = 1` spin ≈ 1 µs), 4.8 ms
at 10 µs, 17.6 ms at a futex round trip (37 µs): **1.4%, 14% and 52% of a 34 ms Flock-class leaf**
(**estimate** from C1 and L1 §9); 0.006–0.2% of a 7.7 s spartan-chain leaf. The ring must spin,
one service thread suffices, and its core is charged to the prover's cgroup (W2 M4). With m6's
≈ 120 calls the worst case is 13%.

**m10. Key release.** Released `k` makes every session list recomputable and every record proof
re-verifiable offline (the claimed benefit). Hazards: (a) a certified `V` with the two-point
backdoor (F2 §6, table row "two-channel comparison") accepts magic proofs that carry `k`, which exist
only after release, so the rules must say that post-release proofs are not evidence in the challenge
period and the DoS column, and the challenge period itself must run against the service (sessions
open to challengers) or after release on the frozen record only; (b) the window between the run and
release is designated-verifier: the organiser is the only verifier of a record for that time, and
the record should state the release date; (c) the next evaluation's `k` must be independent (A1
M9a): a reused `k` is a published oracle, and the submitter's next `V` recognises it by literals.
Release is an audit feature, as W1 says; it is also the only reason W4 beats W3.

**m11. Use the keyed mode, not `BLAKE2s (k ‖ q)`.** W2 A.1 writes `PRF_k q = BLAKE2s-256 (k ‖ q)`,
which makes every `sec` answer a `pub` value at input `k ‖ q`: harmless before release (nobody can
form the input) but it couples the channels at release and complicates `pubOrdered`'s deployment
reading (a `sec` answer absorbed into a transcript is then a `pub` output used before its entry).
BLAKE2s's keyed mode sets the parameter block, so `PRF_k` and `blake2sDigest` are different
functions on every input (A1 m6 says the same for length reasons).

## 5. Recursion and composition

**Does P1's one-log composition survive?** Yes, with M1–M3 (paper; P1 `compose`/`paper_tree` are
**kernel** for the one-channel form). `final`'s hypotheses `pubConsistent L`, `pubOrdered L` and
`μ L < 1` are properties of the one log and the one potential, so applying `final` to the root and
then to the extracted children needs nothing new; the inner verifiers' `sec` queries are in `L`
(they are the attested lists' `ans` items, present by `Valid`), their `pub` lookups are in `L`
(the honest node prover logged the child's tree before hashing its list), and `pub` entries are
deterministic, so sharing them across levels is a lookup, not an event. The error is
`(Q_sec + qV)·ε` once, no factor per level (CGSY24 Thm 5.1, L1 §4); the conclusion gains "or
`treeExtract` returns `.coll`", constructive by M3. The `cert`/`close` moves of W2 A.6 are
`pubStep`-shaped (non-increasing) and need the same one-line extension of `PaperTheorem`.

**Per-level loss.** None in the bound. One in the *tape*: `E` at level `k` decodes the child's proof
and list from the node's committed word, whose leaves are `pub` entries found by walking `L` from
the root digest by lookup (a hash map over `L`, `O(|L| log |L|)` inside `B t = 2^48 + 2^16·t`).
The trace is the whole evaluation's hash log, as in D4 (W2 M6); the liveness smoke at `r = 1`,
`n = 16` is megabytes. **Issue #7 is unchanged**: extraction is decoding, now from `pub` entries
instead of oracle preimages, with the same decoder and the same `2^43`-step real-size estimate; the
list comparison of W2 M6 is added. Nothing in W5 makes node extraction cheaper or dearer than D4.

**A composition hazard W1 does not mention.** `pubOrdered` is global: a `pub` entry that is late
relative to *any* earlier input violates it, including inputs of other subtrees. For the honest
`tree` prover this is automatic (bottom-up, compute-before-use). For a cheating prover it is the
heuristic of M4 applied once to the whole trace, not per node, which is the right granularity.

## 6. Incentives and realism

**The "1.00× + 2%" claim (W1 §7.5), checked (estimate from C1 §1, §4.1).** A deployed public-hash
node for a spartan-chain child computes Merkle paths (13.0k compressions) + transcript absorbs
(12.5k) + squeezes (390) = 25.9k. The W5 node computes the paths and absorbs in-circuit through the
`pub` channel (25.5k, identical gadget, identical count) and, instead of the squeezes, hashes the
list: 476 items × ≈ 70 B = 33 KB = 521 compressions. 26.0k against 25.9k: **+0.5%**, within W1's
"+2%" (which hashed 476 items at the D4 rate). With m6's ≈ 120 items it is +0.1%. Absorbs routed
through `sec` instead cost the same in the list (`(71 + L)/64` compressions, C1 §4.1 row "FS absorb")
and only move service bytes; large absorbs are capped off `sec` by `|q| ≤ 2^20`. The sumcheck and
field work are in-circuit in both. So the node *is* a deployed recursion step, and every hashing
trick a Flock 2.0 would use is computed by the circuit and rewarded; the "flat list" blindness of
D4 (W1 §7.5) is real and W5 removes it. The transfer claim holds.

**Strategies, against D4 and v3.**

| Strategy | W5+W4 | D4 (W2 §C) | v3 |
|---|---|---|---|
| Witness-sending (no proving) | certified, `μ := 0`, no `sec`, no lists; `T_V` rule only (#6a) | same | same |
| Witness-sending below level `j`, flat SNARK at `j` | level-`j` children need no attestation; `≈ 0.5×` the tree's work at `j = 4`; nothing in the theorem (#6b) | same | same |
| Concatenation | `qV` counts `sec` only, so `256 × 476 = 1.2·10^5 > 2^12`; `proofCap` | dead by `qV`, `proofCap` | dead |
| Merkle hashing through `sec` | certifiable (it is v3's `V`); node cost 1.09× (D4's); `10^8` service calls charged to the prover's cgroup; binding becomes a ROM count instead of CR: *more* secure, slower. Harmless | the only option | n/a |
| Challenges through `pub` (local FS) | uncertifiable (m4) | uncertifiable | certifiable (CGH open) |
| Seed expansion by local BLAKE2s | uncertifiable in practice (m6); bit-slicing instead | same | certifiable |
| Attested list as a free commitment (1 MB `q` in one `ans` item) | the circuit hashes it; no gain | same | n/a |
| Precomputed trees in the binary | offline hashes are log prefix; fresh `s` makes them useless; a `V` keyed to a constant root still needs a statement-bound word to be certified | same | same |
| Service as a hashing co-processor | ≈ `2.4·10^5` calls: nothing to offload | `2^33–2^35` compressions: W2 M4's placement | n/a |
| Latency in the timed region | m9: spin ring or 14–52% on Flock-class | the same calls plus `10^8` commitment calls | none |
| Post-release magic proofs | m10 rule | n/a (online attest, no release) | n/a |

Nothing games W5 that does not game D4 and v3 the same way; the two W5-specific rows (`sec`-routed
Merkle, seed expansion) point the submitter towards the honest design. The incentive defect that
remains is issue #6 on both halves, which no oracle model prices (W2 M7; D4+'s oracle leaf is the
only lever found, and W5 is compatible with it).

**Realism of the comparison baseline.** "Real recursion" here is v3's node with public BLAKE2s; W5's
only unreal elements are the attested list (≤ 0.5%) and the fact that the child's challenges are
witness data rather than recomputed hashes, which is what a hash-based recursion would *like* to do
and cannot. A winning W5 node transfers to a deployment as "replace the list by in-circuit squeezes",
+1.5% for spartan-chain's 390 squeezes.

## 7. What the user would have to accept beyond v3

| Item | v3 | D4 all-oracle (W2) | W5+W4 (fixed) |
|---|---|---|---|
| Assumptions at deployment | "BLAKE2s is a random oracle" (unpredictability and extractability; CGH open); CR for the statement tree | PRF security of keyed BLAKE2s; CR of BLAKE2s-256, constructive | PRF; CR, constructive; **the extractability heuristic** (`pubOrdered` traces, M4), ideal-compression-function grade, not falsifiable |
| Lazy sampling → random function, randomised adversaries | paper | paper | paper, `sec` only |
| Trusted runtime | none that answers the theorem's questions | the service: key, `certify`/`attest`, state, reset; bug = accept-all (W2 M8) | the service: key, sessions, `close` with `att` checks, the published log, key custody and release schedule; same bug class; plus the log format and release rule as trusted process |
| Trusted contract lines (**estimate**) | 328 (288 in the rules worktree) | +50 (W2 A.8) | W1's +60–100, plus `pubq` (+6), `pubOrdered` (+8), `Out`/`Sound` (+8), minus `Collision` (−4): **+80–120**, to ≈ 370–450 of 500 |
| Record verifiability | anyone, any time | organiser only (online attest) | organiser only until release; anyone after (designated-verifier window, m10) |
| Challenge period and DoS column | public | against the service | against the service, or post-release on the frozen record; post-release proofs excluded (m10) |
| Verifier design constraints | none | all hashing through the service | challenges as bit-slices of `sec` answers (m6); commitment hashes as full finalised BLAKE2s on inputs off the relation tags (M2, m1); `V`'s hashes as `pubq` lookups (M1) |
| Prover constraints | none | every hash is an IPC call | compute-before-use (automatic); a clean-replay session per proof (M5); a spinning client (m9) |
| What leaves §5.4 | — | composition, "BLAKE2s is a RO", O-25, "honest proofs verify under BLAKE2s" | the same four; one sentence enters: "commitment binding is CR plus extractability of BLAKE2s, not a ROM count" |
| Service load | none | `6.7·10^7–2.7·10^8` calls per tree, 0.3–0.6× in-process on a naive service; up to 2× on Flock-class leaves | `≈ 2.4·10^5` calls; latency-bound (m9) |

The user's decision reduces to one question: is a non-falsifiable extractability heuristic on
BLAKE2s acceptable in exchange for a trivial service and a node circuit that is the real recursion
step? If yes, W5+W4. If every deployment assumption must be falsifiable, D4 all-oracle with an
engineered service (SIMD multi-buffer, double-buffered rings, cgroup placement) is the design, at
a measured 1.1–2× penalty on hashing-bound provers that may close with engineering (C1 §7).

## 8. Findings, comparison, and what P3 must test

| Id | Finding | Consequence | Smallest fix |
|---|---|---|---|
| M1 | `final` over all `pubConsistent` logs with `V` hashing locally: the stripped log accepts and nothing decodes | no compressing `V` certifiable | `V`, `P` query the `pub` channel; `runLog` answers from the log or `none` (+6) |
| M2 | late preimages are free on a deterministic channel; `pubStep` false for the natural potential | the probe fails; W1 §7.4 has a gap | `pubOrdered L` with the relation-tag exemption, as a hypothesis of `pubStep` and `final` (+8) |
| M3 | `Collision L` cannot state the tree theorem; "a collision exists" is pigeonhole-trivial | vacuous composition | W2's `Out`/`Sound`, `E` returns the pair; liveness checks it |
| M4 | "preimage-aware use" is the ideal-compression heuristic, not a falsifiable assumption (DRS09, BCPR14) | W1's trust table and §5.4 sentence overstate | say so; keep D4 as the no-heuristic fallback; check `pubOrdered` on the liveness log |
| M5 | W4 lacks `att` items and a session protocol; raw sessions hold `2^g×` entries | composition fails at depth 2; "2%" becomes `2^g·2%` | W2 A.1–A.2 lists with `close` as `certify`; clean-replay rule |
| m1–m4 | honest-verifier checks of the laws: caps, multi-squeeze, classical collisions, truncation, modes; `logCap` counts `sec`; `pubStep` on consistent appends; challenge-free `V` | none, or features | as stated |
| m5–m8 | list binding, bit-sliced challenges (list ≈ 120 items), grinding, replay and column R | redesign for seed-expanding verifiers; saves 1.5% | state in the design |
| m9 | ≈ 500 sequential RTTs per proof: 1.4–52% of a Flock-class leaf | fairness for the target class | spinning ring, one service thread in the prover's cgroup |
| m10 | key release: post-release magic proofs, designated-verifier window, key independence | rules | exclude post-release proofs; run challenges against the service; fresh `k` |
| m11 | `BLAKE2s (k ‖ q)` couples the channels | release-time coupling | keyed mode |

**Comparison.** *Against D4 (W2):* same relation, same `Out`/`Sound`, same `failCtx` and
`treeExtract`, same issue #7 and #6; W5 adds two trusted definitions and one heuristic, and removes
`10^3` of service traffic and the D4 flat-list blindness that hides a Flock 2.0's hashing tricks
(W1 §7.5, confirmed in §6). D4 is the stronger *theorem at deployment* (its trace is the service's
log); W5 is the stronger *benchmark*. *Against v3:* W5 (fixed) closes O-25 and every F2 disguise
without review (§2), proves composition, and replaces "BLAKE2s is a random oracle" by PRF + CR +
extractability; it costs a trusted service, a designated-verifier window, +80–120 lines, and a
verifier-design discipline (m6, m1). v3 keeps a smaller trusted base and public verifiability and
keeps the kernel-checked backdoor on the board. *Ranking:* W5+W4 (fixed) > D4 all-oracle > v3; the
first two are the same contract stage (W2's minimal version) with a channel switch, so the honest
plan is W2's: land D4's contract, then W5 as a delta once P3 passes on the *fixed* laws.

**What P3 must test, given M1–M3.** A probe of W1's §7.7 statement as written will either fail on
the stripped log (M1) or, if its `V` reads `pub` entries from the log, fail on the late-preimage
log (M2). It should build: (i) a Merkle `V` whose hashes are `pubq` lookups and whose positions are
bit-slices of one `sec` answer; (ii) the potential "some squeeze landed in `K(prefix)` with `|K|`
below threshold"; (iii) `pubStep` and `final` under `pubOrdered`; (iv) two negative controls: the
stripped log makes `V` return `none`, and without `pubOrdered` the late-preimage log is accepted at
`μ = 0` with `E` failing (no `KState` for the natural `E`, the shape of P1 `lazy_no_kstate`); (v) the
ported backdoor comparing a `pubq` answer with a literal has no `KState`. About 250 lines, not 150.

*Postscript (the probe's shape as of 18:40, `RecursionFast/Explore/TwoChannel/Model.lean`, read, not
built).* P3 does not probe W1's laws as written. Its `V` is a two-channel `TProg` whose `pub` queries
are log lookups (M1's fix, built in), and it treats the late preimage as an **escape** `Esc.late` in
`final`'s conclusion (mode "collisions and late preimages in the log") rather than as a hypothesis
`pubOrdered`: the theorem is then total over all logs and reads "witness, or a collision in `L`, or a
late preimage in `L`", and the deployment heuristic (M4) is "black-box traces contain no late
preimage", the same content as `pubOrdered`. Either form works; the escape form costs no substring
predicate but shares the statement-digest problem (an honest prover recomputing `leafStmt` late makes
the escape valid on the honest log, so a liveness check must reject an escape output on honest
proofs, and the relation-tag exemption is still needed somewhere). It also proves `blake2s_collides`
by pigeonhole, which is M3's reason to keep collisions in-log or constructive. So M1–M3 stand as
findings against W1 §7.1 and §7.7, and the fixed model P3 is probing is the one this note recommends.
