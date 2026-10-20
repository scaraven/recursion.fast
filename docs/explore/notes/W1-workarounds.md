# W1. Workarounds: designs that keep the oracle secret and still reward real recursion

Ideation note, 2026-10-20, for `docs/explore/BRIEF.md` §4 Q5 (and Q2, Q3). Evidence tags as in the
brief: **kernel** (Lean, file and name), **paper** (argument, cited), **measured** (a log), **estimate**.
Sibling notes cited by name: A1 (attacks on D1/D2), C1 (cost), L1 (literature), P1 (Lean probes); their
numbers are quoted with their tags, not re-derived. F2 = the O-25 memo in the submissions repository.

## Summary

1. **The tension is a channel problem.** A hash-based verifier asks the oracle for challenges (≈ 400–500
   calls per spartan-chain proof, C1 §5.1 [E]) and for Merkle-path hashes (≈ 4,700 of its 5,156 queries
   [M]; `h_V` = 10k–26k compressions for WHIR/leanVM-class verifiers [E]). Only challenges need an
   *unpredictable* answer; commitments need only *binding*. One oracle for both is what hurts: in the
   pure ROM (W1) every fresh answer is incompressible at every level (§1), and all-oracle attestation
   (W2/W3/W4) routes the prover's whole commitment phase through the harness (6.7·10^7–2.7·10^8 calls
   per tree at 0.3–0.6× in-process speed, C1 §5 [E/M]), penalising the hashing-optimised provers a
   Flock 2.0 is.
2. **Recommendation, W5 "channel split" with W4 attestation:** secret PRF oracle for challenges, local
   public BLAKE2s for commitments, the child's ≈ 500 challenge answers attested by a published session
   log (key released after freeze). The node circuit verifies the child's Merkle paths in-circuit exactly
   as deployed recursion does (1.00× real cost + ≈ 2% [E]); the service sees ≈ 2.5·10^5 calls per tree;
   CGH and every F2 disguise close (paper, §7.3); P1's composition theorem carries over. The honest price:
   the commitment half leaves the counting form. `final` becomes "extract a witness **or** exhibit a
   BLAKE2s collision in the log", the deployment claim names PRF security, collision resistance and
   preimage-aware (black-box) use of BLAKE2s: hash assumptions only, within V3-5, and the same
   heuristic every deployed recursion makes, now written down. One new potential law, `pubStep`, is the
   load-bearing unknown: a one-day probe (§7.7).
3. **Ranking (§12):** W5+W4 > W5+W3 > W3 (D4 all-oracle) > W1 (D1 priced: closes CGH, ranks chain
   provers, A1 M10) > W2 (D3: 0.5–12% per child in-circuit and a trusted signature spec; its offline
   verification W4 gets from key release) > W7 (accumulation: the relation change to make after W5) >
   W6 (harness-served LDROM/AROM: unservable at digest-sized domains, and its only practical
   instantiation is a public hash plus its circuit, i.e. v3 with CGH open). Confidence that W5 is the
   right direction ~65%; that its Lean form lands in one stage ~50%.

## 0. Conventions and what is fixed

- Leaf relation concrete (BLAKE2s chain, `chainCap = 2^20`); node relation `RelL` (P1 `Defs`): child
  verdicts read from the same log. Ranked shape `r = 8`, `n = 2^14`; spartan-chain numbers **measured**
  (brief §2); `h_V` = compressions a verification feeds to the oracle (C1).
- "Real cost" of a node = what a deployed public-hash recursion computes in-circuit for one child:
  `h_V` compressions ≈ 25.9k for a spartan-chain child, 9.2k–28.3k across designs (C1 §4.1 [E]).
- "Closes CGH" means: no `V` certified in the model can behave differently at deployment on a magic
  proof, up to a named computational loss; "closes the disguises" lists F2 §1.2 (literal trigger),
  §14.1 (`evalPoly` recognition), §14.4 (position channel), §14.5 (liveness mirror), §14.6 (review
  evasion) and R2.1 (post-hoc challenge verification).
- Contract today: 689 lines across `Contract/*.lean`, 328 code lines against the 500 budget
  (CLAUDE.md). Deltas below are **estimates** of code lines.

## 1. The premise every candidate must answer: fresh answers are incompressible

**Paper.** In the ROM an unqueried answer `f(q)` is independent of everything a verifier holds, so no
proof can convince a verifier of the value `f(q)` without the verifier asking `q`. A node verifier for
`RelL` must therefore ask every oracle point on which the child verdict depends. This is below the
BCG24 theorems (which are for the worst relation in `NTIME^O[t]`): it is the flipping step of their
§2.4 applied to one query (L1 §1 "derivation", A1 M2). Kernel evidence that the lazy parent fails and
that every extractor certifying it must output collisions: P1 `lazy_no_kstate`,
`lazy_extractor_collides`. Consequences at the ranked shape, all **estimate** unless tagged:

- Per level the re-asked set doubles: the root re-asks `511·h_V` = 2.6–13.2 M compressions and the
  root proof carries every descendant's Merkle data, ≥ 80–850 MB (C1 row 4; A1: 250 MB, 40× over
  `qV ≤ 2^16`, 250× over `proofCap`). Witness-sending re-hashes `2^22` chain steps: the relativized
  tree does 0.6–3.2× **more** root work than the thing it was meant to beat.
- What *can* be compressed in the pure ROM is only the oracle-free part of a verification: sumcheck
  arithmetic, FRI folds, field decoding. For a hash-based verifier that is a small minority of the
  cost (C1 §3.3: a hash charge captures 93–99.6% of an R1CS-of-bits step).
- CGSY24's "relativized NARK by sacrificing succinctness" (Constr. 6.8, L1 §4) is exactly this trace
  re-check: size `ℓ + O(q_C·λ)`, verifier re-asks every pair.

So any design in which the node *compresses* oracle work must change the oracle model, and the only
two levers are **authentication** (the node proves "this answer is genuine" without the verifier
asking: SROM-like, W2/W3/W4) and **channel separation** (make the incompressible channel tiny: W5).
Algebraic structure (W6) is a third lever in theory and fails on deployment.

## 2. Candidate template

Each candidate states: model (harness provides; theorem quantifies over; deployment match); escape
from the impossibility; O-25 and the disguises; in-circuit node cost against real recursion; trusted
base; harness and engineering; Lean cost with the potential-form `KState`; best attack; verdict.

## 3. W1 — Pure-ROM relativized NARK, oracle work carried and priced (the brief's D1; D2 is not viable)

**Model.** Harness: a secret-keyed PRF service (fresh key per evaluation and per repeat, never
published: A1 M9), or lazy sampling. Theorem: `KSRel` over `RelL` with the potential (P1 `Defs`),
completeness with error over a random oracle. Deployment: the root check runs `V` online against the
service (D2) or, in D1, no tree is ever run and the score is `T_leaf` plus a charge per verifier
query priced at `t_hash`.

**Impossibility.** Not escaped, obeyed: nodes carry their children's oracle data. D2 at `r = 8` breaks
`proofCap` and `qV` by two orders (§1), so only `r ≤ 2` is admissible (A1 verdict 1). D1 avoids the
question by never running a node.

**O-25.** Closed modulo `Adv_PRF` with a secret per-evaluation key (L1 §11 fact 2; A1 verdict 5), for
every disguise: all of them compute the instantiation, and there is none to compute. With a public
BLAKE2s oracle (D1 as literally read) nothing changes: the zero-query backdoor certifies under `RelL`
unchanged (P1 `Backdoor.backdoor`, **kernel**; A1 M8).

**Node cost.** Zero in-circuit hashing. The node SNARK, if any, proves only sumcheck/FRI arithmetic
over carried transcripts. In D1 the node prover is never measured; in D2 the node is a concatenation.
Nothing resembling a deployed recursion step is ever built: C1 §3.3 and A1 M10 ("the hash is never in
a circuit, so the verifier's hash-friendliness is invisible").

**Trusted base.** +10–15 contract lines (`RelL`, `KSRel`), `CompleteWithError` (planned anyway), no
new assumption beyond the PRF for the service. Smallest of all candidates.

**Harness.** D1: a leaf benchmark plus a charge; the "million chains" statistic takes 35–90
machine-days (A1 M5, C1 §6 [E]); the charge is self-referential and gameable in every variant (A1 M3,
M4, M7: children with no oracle calls are re-asked for free, so flattening wins). D2: 2.6 M root
queries at 10–50 µs local-socket RTT is 26–130 s against `verify_s = 60 s` (A1 M9c); the prover's
≈ 10^6 commitment calls per leaf go through the service at 0.3–0.6× in-process speed (C1 §5.2 [M]).

**Lean.** Cheapest: `RelL` already probed, composition a theorem (P1 `paper_tree`). Node extraction is
decoding-free (the child proofs are carried), which incidentally dissolves issue #7 for this design.

**Best attack.** Witness-sending below level `j`, one flat SNARK above, with `t_hash` driven down by a
chain-specialised leaf prover (A1 M3, M7). Nothing in the model distinguishes this from recursion.

**Verdict.** A clean theory with no recursion in it. Keep as the fallback that closes O-25 cheaply;
do not expect it to rank a Flock 2.0.

## 4. W2 — Signed oracle (SROM, the brief's D3; CT10)

**Model.** Harness: the PRF service plus a hash-based signing key; `certify(list)` returns a
signature on `BLAKE2s(enc list)`. Theorem: ROM plus a signing oracle the adversary reaches only
through `certify`; EUF-CMA of the signature either proved in Lean (hash-based, in the ROM) or
trusted. Deployment: the root verifier checks signatures offline with `pk`; no service at verify time.

**Impossibility.** Escaped as in CT10: the node verifier asks none of the child's queries; it checks
one signature per child list (4 queries per proof in CT10's SIR oracle, L1 §2). The relation is still
`RelL` at the leaves; at nodes the clause is "the child's list is signed and `V` on that list accepts".

**O-25.** Closed as W1 (secret challenges). The signature's hash is public BLAKE2s and `V` computes
it locally, so no model/deployment divergence exists on that channel (the argument of §7).

**Node cost.** D4's list hash (1.09× real for a spartan-chain child, 0.79–1.56× per node query, C1
§4.1 [E]) plus one signature verification per child: 145 (XMSS, leanSig parameters), 532 (SPHINCS,
leanVM parameters) or 556–1,059 (WOTS+ `w = 16` with a height-20 path) compressions, 0.5–11.5% of a
child (C1 §4.2 [E]). The all-oracle form inherits W3's service load (prover commitments through the
service); the hybrid form (W5 with W2 attestation) does not.

**Trusted base.** The largest of the attestation designs: a trusted Lean specification of the
signature's verification algorithm (WOTS+ chains, L-tree, Merkle authentication: ≈ 100–200 code
lines, against a 500-line budget), the signing-oracle model, and either a kernel-checked EUF-CMA
theorem in the ROM (weeks) or a trusted axiom-like hypothesis, which the trust policy forbids.

**Harness.** `certify` re-evaluates listed pairs (511 × 9.2k–28.3k = 4.7–14.5 M compressions per
tree, 0.07–0.22 s, C1 §4.3 [E]); a stateful XMSS key with `h = 20` signs 511 lists per evaluation for
≈ 2,000 evaluations (C1 §4.2). Offline verification is the whole benefit: records are checkable by
third parties with `pk`, which W3 lacks (A1 M9b).

**Lean.** `KState` must absorb a second oracle (signing) whose answers are not uniform digests: the
potential's `step` law averages over `2^256` answers of a fresh *random-oracle* query, and a signature
is deterministic given the key. One needs either a signing oracle modelled as lazily sampled
one-time keys (then `step` applies to the key material and EUF-CMA becomes a counting lemma, the
clean route, but a substantial library) or a hypothesis. Hardest formalisation of the set.

**Best attack.** A forged signature; or, cheaper, key compromise/reuse across evaluations: the same
`pk` for a season lets a submitter whose earlier proofs were published learn signed `(q, a)` pairs
and build a `V` that recognises them (A1 M9a's trick on the signed channel). Per-evaluation keys
remove it and also remove the offline-verification benefit after the evaluation unless `pk` is
published with the record (fine: a published `pk` verifies that evaluation only).

**Verdict.** Correct, expensive, and dominated by W4 (same offline property, no in-circuit signature,
no signature theory in the trusted base).

## 5. W3 — Attested oracle (the brief's D4; the other agent's depth target)

Stated only as far as the comparison needs; the dedicated D4 note owns the analysis.

**Model.** PRF service with `certify(list) ↦ h = BLAKE2s(enc list)` stored, `attest(h)` online; the
model is the SROM with the organiser as the MAC holder and decider (L1 §2/§4: "query accumulation
with the organiser as decider"). Theorem: ROM plus an honest predicate `Certified h`; node clause
"the child's list hash is certified and `V` reading that list accepts". Composition from one log by
CGSY24 Thm 5.1 (`κ_PCD ≤ κ_ARG(λ, q)`, no factor `N`, L1 §4) and P1 `paper_tree`.

**Impossibility.** Escaped by authentication: the root asks `O(#children)` attestations, not
`O(#queries)` (A1 verdict 6).

**O-25.** Closed modulo `Adv_PRF` for every disguise, with A1 M9's conditions (fresh key per
evaluation, no published answers).

**Node cost.** 1.09× real (spartan-chain child), 0.79–1.56× per Merkle node query (C1 §4.1 [E]),
flat root: 511 attest calls ≈ 0.3 ms batched (C1 §4.2).

**Trusted base.** +40–80 contract lines (the `Certified` predicate, the list encoding, the attest
oracle in `OProg` or as a trusted input to `V`), no signature theory. A trusted harness process
(certify/attest) joins the trusted base.

**Harness, the all-oracle defect.** Every prover Merkle hash is a service call: 262,614 calls (4.47 M
compressions, 278 MB) per spartan-chain leaf, ≈ 10^6 per WHIR-class leaf; per ranked tree
6.7·10^7–2.7·10^8 calls (C1 §5.1 [E]), served at 10–12.5 Mcalls/s machine-wide = 0.3–0.6× the
in-process rate (C1 §5.2 [M]), on organiser cores inside the timed region. For spartan-chain the
Merkle phase is 0.1 s of 7.7 s and this is noise; for a hashing-bound Flock-class prover (34 ms per
leaf on an M4 Max, L1 §9) it is the entire prover, slowed 2–3× and metered on someone else's CPU.
Designated-verifier records (A1 M9b) and a DoS column that costs hours (A1 M9d) remain.

**Lean.** Moderate: one new honest oracle; the potential is unchanged on the random channel.
Node extraction is decoding (issue #7) because the child list is inside the node's committed witness.

**Best attack.** `certify` is a BLAKE2s-of-a-chosen-string service the prover can use as a free hash
accelerator (C1 §4.3); meter it. Key reuse (A1 M9a). A `V` that moves all its hashing into `certify`
lists to shift CPU to the harness: the charge must count certified bytes.

**Verdict.** Sound and formalisable; the engineering defect is the all-oracle commitment channel,
which W5 removes while keeping W3's attestation for the challenge channel.

## 6. W4 — Session-committed oracle with a published log and end-of-epoch key release (new)

**Model.** The service answers `PRF_k` and keeps, per prover session, the ordered list of `(q, a)` it
returned; at `close(session)` it publishes `h_s = BLAKE2s(enc list_s)` to an append-only log the
harness owns (the "oracle transparency log"). The node proves in-circuit, as in W3, that `V` accepts
the child reading a list whose hash it computes; the public input carries `h_s`. The root verifier is
the harness: it checks each carried `h_s` against the log (a trusted-input predicate `Published h`,
the same shape as W3's `Certified h` but read from a file, not asked of a service). At the end of the
evaluation (after the record is frozen) the harness publishes `k`: anyone can recompute every
session list from its published transcript and re-run the root check offline. Theorem: identical to
W3's (ROM plus an honest predicate on digests). Deployment: the predicate is "`h` is in the log for
this evaluation"; after key release it is additionally recomputable.

Two variants, rejected in favour of the session list: (a) one global Merkle log with per-answer
inclusion proofs: ≈ 30 compressions per answer in-circuit, 20–30× worse than hashing a session list
(**estimate**: `log₂` of 2.7·10^8 answers per tree, C1 §5.1); (b) committing to the whole oracle: the
domain is unbounded, and a commitment to `k` opens nothing without revealing `k`.

**Impossibility.** Escaped exactly as W3 (authentication by the organiser's records).

**O-25.** Closed as W3 within the evaluation. Key release re-opens CGH **only for proofs produced
after release**, which no record scores: a `V` that recognises `PRF_k` after `k` is public accepts
magic proofs in third-party re-verification of *new* proofs, never in the frozen record. The brief's
"time-released keys" direction is therefore an audit feature, not a security fix (§8.2). Residual:
the organiser's log and key schedule are trusted process (A1 M9a's fix, "treat the key schedule as
trusted process", becomes a published artefact instead of a secret one).

**Node cost.** W3's (1.09× real for the list, C1 §4.1), nothing for the attestation itself (a
public-input digest). Root: 511 file lookups, microseconds.

**Trusted base.** As W3 (+40–80 lines) minus the online service at verify time; plus the log format
(a list of digests per evaluation) and the rule that `k` is published after freeze.

**Harness.** The all-oracle service load of W3 if used alone (C1 §5.1–5.2); negligible when combined
with W5. No `attest` RPC in the root check (A1 M9c's 26–130 s disappears for the attest part; the
root verifier's own ≈ 500 challenge calls remain, ≈ 25 ms at 50 µs). Third-party verification:
offline after release (A1 M9b closed). The DoS column: `V` on random proofs makes only its own
challenge calls; carried hashes against a random proof fail the file lookup instantly.

**Lean.** W3's statement with `Published` in place of `Certified`; both are an honest predicate
quantified over in `KState.final` ("for every set `S` of certified hashes consistent with the log
`L`"), so one formalisation serves both. Consistency of `S` with `L`: every `h ∈ S` is the hash of a
sublist of `L`'s entries for one session, in order. Node extraction is decoding (issue #7), as W3.

**Best attack.** Session mixing: a prover opens many sessions and closes a list that interleaves
answers obtained in different sessions, or closes a list omitting the answers that would have made
`V` reject. The first is prevented by the service hashing only what *it* returned in *that* session,
in order; the second is harmless (omitting an answer `V` needs makes `V` fail on the list). Replay:
a list from a previous evaluation has a different `k`, so its answers do not match the new root
verifier's online challenges; the log is per evaluation. Grinding the list hash `h_s` by closing
sessions repeatedly is free for the prover but useless (the hash binds the list, nothing is chosen
by it).

**Verdict.** W3 with the online attestation replaced by a published log and post-hoc auditability.
Strictly better engineering at the same theorem; the attestation mechanism I would pair with W5.

## 7. W5 — The channel split: public BLAKE2s for commitments, secret oracle for challenges (new)

### 7.1 Model

- **Two channels.** `V` and `P` remain `OProg`s over one oracle, the **secret** one (Fiat–Shamir
  squeezes, position sampling, grinding targets); they compute BLAKE2s **locally** for everything
  else (Merkle paths, leaf hashing, transcript absorption of large messages). Domain separation by
  tags, as today (`tagRO` for the secret channel).
- **Log.** `Log := List (Entry)` with `Entry = sec (q, a) | pub (q, a)`. `runLog` reads only `sec`
  entries (what `V` asks). `pub` entries are the adversary's BLAKE2s computations, with the model
  hypothesis `pubConsistent L := ∀ pub (q, a) ∈ L, a = blake2sDigest q`.
- **Knowledge state.** `μ : Log → ℝ≥0`, `empty`; `step` only for a fresh `sec` query (average over
  `2^256` answers rises `≤ ε`, within `logCap`); `pubStep : pubConsistent L → μ (L ++ [pub (q, a)])
  ≤ μ L` (a deterministic entry never raises the potential); `final : pubConsistent L → μ L < 1 →
  V.runLog L c π = some true → (∃ w, E c π L = some w ∧ RelL L c w) ∨ Collision L`, where
  `Collision L := ∃ q q' a, q ≠ q' ∧ pub (q, a) ∈ L ∧ pub (q', a) ∈ L`.
- **Attestation of child challenges.** The node clause of `RelL` reads the child verdict from the
  log; a compressing node proves in-circuit that `V` accepts the child on a *carried* list of `sec`
  answers whose hash is attested by W4 (or W3). Lists are now ≈ 500 entries, not 5–26k.
- **Deployment.** The secret channel is the harness PRF service with a fresh key per evaluation
  (L1 §11 fact 1: loss `Adv_PRF`, or none under lazy sampling); the public channel is the BLAKE2s
  the prover and `V` compute themselves; the attested lists go through W4's log. The theorem's
  adversary is "any log"; the deployment adversary is any program whose BLAKE2s outputs come from
  calling BLAKE2s (black-box use). The root check runs `V` online for its own ≈ 500 squeezes.

### 7.2 Does it escape the impossibility?

**Paper.** Yes, by both levers. The incompressible channel (§1) is the secret one, and it now holds
≈ 400–500 answers per proof (C1 §5.1 [E]) instead of 5k–26k compressions; those are authenticated,
not re-asked (W4). Everything else a child verifier does is standard-model computation (public hash
evaluations and field arithmetic), which a SNARK compresses as usual. This is the split the positive
results already use: CCS22's LDROM SNARK and CCGOS23's AROM PCD pair the idealised oracle with a
standard-model CRH for commitments (BCG24 §2.8; L1 §3 item 2, "both still need a CRH, so there is no
assumption gain over D4"). W5 just makes the CRH BLAKE2s and keeps the idealised oracle for
challenges only.

### 7.3 O-25 and every disguise

**Paper.** Two channels, two arguments.

- *Secret channel.* `V` cannot compute `PRF_k`; any branch comparing a squeeze answer with anything
  `V` or the proof computes fires in deployment with probability `≤ Adv_PRF + 2^-256·(#comparisons)`.
  This kills F2 §1.2 (literal trigger: the literal is compared to an unpredictable answer), §14.1
  (`evalPoly`: the interpolated set `S` is BLAKE2s challenges, not `PRF_k` ones), §14.4 (positions are
  `PRF_k` outputs), §14.5 (the liveness mirror: `V` cannot single out the deployment to reject
  either), R2.1 (post-hoc verification: `c₁ = Σ outbitᵢ·βⁱ` with BLAKE2s wires never holds against a
  `PRF_k` challenge), and §14.6 (review is no longer load-bearing for CGH).
- *Public channel.* `V` may compute BLAKE2s and compare with a `pub` entry; by `pubConsistent` the
  comparison has the same truth value in the model as in deployment, so a branch accepting a magic
  proof on it is unconditional in the model and cannot be certified (its `final` fails on the honest
  adversary's log, which has no collision). No divergence, hence no CGH. Kernel-checkable as a
  negative control: port `Controls/Backdoor.lean` to compare a local BLAKE2s with a `pub` entry and
  show no `KState` exists (≈ 40 lines, **estimate**).
- *Residual, named.* `Adv_PRF` for keyed BLAKE2s against the submitter; collision resistance of
  BLAKE2s (the `∨ Collision L` disjunct is the extractor's escape, and the deployment claim is "the
  adversary found a collision"); and the model assumption that the adversary's hash values enter
  through the box (preimage awareness, Dodis–Ristenpart–Shrimpton CRYPTO 2009, for which
  Merkle–Damgård-style hashes with an ideal compression function are proved; for BLAKE2s it is a
  heuristic). All three are hash assumptions: V3-5 compliant.

### 7.4 What straight-line extraction loses (the brief's question)

1. **Merkle binding is no longer a probability.** v3 charges a collision with a logged digest at the
   birthday rate over `logCap` (Security.lean header, `2^-160` per full-digest comparison). In W5 the
   `pub` channel has no randomness; the Merkle-path argument becomes deterministic: at the squeeze
   (a `sec` entry) the log fixes the root and the set of positions with a complete logged path; a
   later `pub` entry that completes a path to an already-logged digest is either the logged preimage
   (so the leaf was already known) or a second preimage (`Collision L`). The extractor decodes from
   the logged leaves as today, or outputs the collision. C1 §5.1's objection ("a commitment under a
   concrete hash binds only by collision resistance, which the counting form cannot charge") is
   answered not by charging it but by making it an output of `E`.
2. **The paper theorem gains an additive term.** Advantage `≤ (Q_sec + qV)·ε + Pr[the adversary's
   log contains a BLAKE2s collision]`; the second term is not bounded by the contract, it is the
   named assumption. `logCap` counts `sec` entries only; `pub` entries are bounded only by the
   extractor's fuel (they are its input).
3. **No grinding defence on the public channel is needed or available.** A `V` whose challenges are
   local BLAKE2s has no `sec` queries, so its `KState` would have to hold for every log, including
   the one containing a bad transcript: uncertifiable. The model forces challenges through the
   secret channel, which is what we want.
4. **Lazy sampling of the public channel is impossible** (its answers are fixed), so the "deployed
   game is the ROM game" argument of L1 §11 holds for the secret channel only.
5. **Composition.** P1's `paper_tree` reads child verdicts from one log; the `pub` entries are
   deterministic and shared across levels, so the same proof applies once `pubStep` holds (§7.7).

### 7.5 In-circuit node cost against real recursion

**Estimate.** The node circuit verifies the child's Merkle paths with in-circuit BLAKE2s on the
child's own data: this is real recursion's `h_V` by definition (9.2k–28.3k compressions per child,
C1 §4.1), 1.00×. It additionally hashes the carried challenge list: ≈ 476 FS entries × 70 B ≈ 33 KB
≈ 520 compressions for a spartan-chain child, 2% (W3 attests the whole 1.81 MB list, 28.3k
compressions). Every trick a deployed recursion uses to cut hashing (shared path prefixes, Merkle
caps, batching openings, choosing a circuit-friendly arity) is available and rewarded, because the
circuit computes the real hashes; in W3/W4-all-oracle the circuit hashes a flat list and those
tricks are invisible. With R1CS-of-bits BLAKE2s (`2^14` rows per compression, issue #8) the node is
≈ 4.2·10^8 rows for a spartan-chain child, 1.5× the ranked leaf; with plonkish/AIR BLAKE2s
(`2^10`–`2^11` cells) ≈ `2^24`–`2^25`. The root proof is one node proof: 0.2–0.8 MiB, 8–30 ms to
check on a machine with carry-less multiply (C1 row 2), so the `T_V` separation of C1 §2.3 applies.

**Transfer.** The winning design is a verifier whose Merkle hashing is cheap in its own circuit and
whose challenge count is small: Flock's design space. The only unreal element is the attested
challenge list, ≈ 2% of the node and the same in every entry.

### 7.6 Trusted base, harness, engineering

- **Contract** (**estimate** +60–100 code lines): `Entry`/two-channel `Log` and `pubConsistent`
  (+10), `Collision` (+4), the `KState` changes (`pubStep`, the `final` disjunct, +8), `RelL` and
  `KSRel` (+12, P1), the attestation predicate and list encoding of W4 (+40–60). `Certificate.Vb`
  becomes `V` run against the deployed service, which the contract can only name abstractly
  (`V.run O` for the harness's `O`); the concrete-oracle `blake2sOracle` leaves `Certificate.lean`
  and the ROM heuristic of §5.4 bullet 2 is replaced by the three named assumptions of §7.3.
- **Harness.** Service calls ≈ 500 per proof × 511 proofs ≈ 2.5·10^5 per tree plus the root check:
  seconds of RTT at most, against ≈ 33 min of leaf proving (A1). The service's CPU is negligible
  and fairness is moot. W4's log and key release. The native prover must still emit its public-hash
  log for the liveness run (§6.3 step 8 already requires a log); for scoring it emits nothing.
- **Caps.** `qV` counts `sec` queries only (≈ 500; cap `2^12` would do); the verifier's local hashing
  is bounded by `T_V` as now; `proofCap` is unchanged and W5 fits it where v3 does (issue #8's
  WHIR-class sizing, inherited unchanged).

### 7.7 Lean cost with the potential-form `KState`

- The statement changes are small (above). The library work is the two-channel paper theorem
  (`Library/PaperTheorem.lean` rerun with `pub` steps interleaved: the supermartingale argument
  needs only `pubStep`), **estimate** 1–2 weeks.
- **The one load-bearing unknown is `pubStep` for the honest Merkle verifier**: that the natural
  potential (the one v3's `Collision`-charging potential becomes once collisions are an output) never
  rises on a deterministic entry. The §7.4 argument says it holds; a probe (≈ 150 lines: a Merkle
  verifier over `pub` hashes, positions from one `sec` squeeze, the potential as the number of
  unknown positions, and `pubStep`/`final`) is the first thing to run. If `pubStep` fails for a
  natural `V`, the fallback law is `pubStep` with `≤ μ L + 0` replaced by the disjunction "or
  `Collision (L ++ [e])`", which is weaker but still deterministic.
- Node extraction is decoding (issue #7) as in W3/W4; the extractor budget decision is orthogonal.
- Controls: positive (witness-sending; a toy Merkle SNARK), negative (the ported backdoor on the
  public channel has no `KState`; the local-FS verifier has no `KState`; a lazy parent still fails).

### 7.8 Best attacks

1. **Shift hashing to the secret channel to dodge collision accountability.** A `V` that routes
   Merkle hashes through the secret oracle is still certifiable (it is v3's `V`) and pays the service
   load; nothing breaks, the submitter just loses time. Harmless.
2. **White-box BLAKE2s.** An adversary that produces a path digest without a logged preimage
   (second-preimage cryptanalysis) is outside the model; this is the named residual, the same as
   every deployed hash-based SNARK's. Not a competition attack at `2^-128`.
3. **Collision laundering.** The disjunct lets `E` escape with a collision; a submitter cannot
   manufacture one in the honest log, and the harness's liveness run checks `E` outputs a witness on
   honest proofs, so a `V` whose `E` "always finds a collision" fails liveness. The control for this
   is cheap.
4. **Side channels on the service** (timing of keyed BLAKE2s, answer ordering) to learn `k`: a
   constant-time keyed hash and per-evaluation keys; standard.
5. **Attested-list substitution** (W4's attacks, §6) and **key reuse** (A1 M9a): same mitigations.
6. **Pre-challenge grinding of public data** (choosing a Merkle root to steer a later secret squeeze):
   impossible, the squeeze is `PRF_k` of the root; the model charges it through `step`.

**Verdict.** The only candidate whose node circuit is a deployed recursion step, whose service load
is trivial, and whose CGH closure is a PRF statement rather than a review. Its cost is one honest
sentence in §5.4 ("Merkle binding is collision resistance of BLAKE2s with preimage-aware use, not a
ROM count") and one probe (`pubStep`).

## 8. W6 — Arithmetised or low-degree oracle served by the harness (rejected)

**Model.** The harness holds a secret random low-degree polynomial (LDROM, CCS22) or a random
low-degree extension of `[ro(x) = y ∧ wo(x) = z]` (AROM, CCGOS23) and answers evaluation queries;
nodes use the oracle's algebra to check batched claims about child answers with `O(1)` queries (the
decider makes 2, L1 §3).

**Why it is rejected, in order of severity.**
1. **Unservable at cryptographic size.** A random individual-degree-`d` polynomial in `m` variables
   has `(d+1)^m` coefficients, and the LDE of a random function on `{0,1}^m` costs `2^m` evaluations
   per off-cube query; with `m ≥ 256` input bits (a digest) neither fits any machine (**estimate**,
   elementary). A servable instance needs `m ≈ 20–30` and a field of `2^64`: a toy domain the
   relation cannot use for digests. CCS22's "trusted party" is a thought experiment at these sizes.
2. **The only practical instantiation is public.** AROM's heuristic instantiation is "`H` and its
   3-SAT arithmetisation `P_H`" (L1 §3): a public hash plus its circuit. That is v3 (`Vb` with
   BLAKE2s) and reopens CGH in full (L1 §3 item 4; A1 M8).
3. **No assumption gain, worse cost.** Both models still need a CRH (BCG24 §2.8), LDROM extraction
   rewinds (constant depth only), and the in-circuit accumulation verifier hashes `≈ n·m·d` field
   elements, `d·log|F|` times D4's list (L1 §3 items 1–3 [E]).
4. **Lean.** A new oracle type (field-valued, low-degree), a polynomial-identity library, and a
   different potential (answers are correlated across queries, so `step`'s independent average is
   wrong): the largest formalisation of any candidate, for a model nobody can deploy.

**Verdict.** Theoretically the right escape (statistical soundness is open there, BCG24 §2.8),
practically dead. W5 takes its structural lesson (idealised oracle for challenges, CRH for
commitments) without the algebra.

## 9. W7 — Accumulation-shaped node relation (a relation change layered on W5)

**Model.** Replace "a node verifies two child SNARKs" by "a node folds two child claims into an
accumulator" (Arc, WARP, BMNW: L1 §8): the node checks the fold's consistency (openings of the
input rows at positions drawn from a fresh squeeze, a random linear combination) and a single
**decider** at the root checks the final accumulator (reads one codeword of fixed size, `O(n)`,
WARP Thm 10.3). `Wit.node` gains the accumulators; `RelL`'s node clause becomes "acc' is a correct
fold of acc₁, acc₂ and the children's claims, read from the log"; the root relation adds the decider.

**Impossibility.** Pure ROM: not escaped (the openings at each fold are oracle queries the parent
must re-ask: WARP's verifier makes `O(t + ℓ₂t + ℓ₂t log n)` Merkle-RO queries). With W5: the
openings are public-hash work in-circuit and only the fold's squeezes (tens, not hundreds) are
attested, so the attested list shrinks below W5's ≈ 500. Hash-based accumulation is exactly D4's
natural honest workload (L1 §8, item 7), and the model's secret channel makes its PCD claim, which
Arc/WARP leave heuristic, a theorem of the W5 kind.

**Node cost.** Below a full child verification: no proximity test per node (deferred to the root),
`t·depth` openings per input only; **estimate** 0.3–0.6× of W5's node for WARP-class parameters, the
decider ≈ one PCS check at the root. Realism: this is the current frontier of recursion design
(WARP, Arc), so the incentive transfers directly.

**Trusted base.** +30–60 contract lines (accumulator type, fold clause, decider at the root). The
knowledge statement changes shape: `final` must extract *all* accumulated claims from one log
(straight-line, as CGSY24's split verification), not two child proofs.

**Lean.** Moderate-high: a new relation and a new positive control (a toy fold over `pub` hashes with
a `sec` combination challenge); the W5 machinery is reused.

**Best attack.** A fold that is sound only for *honest* accumulators (the classic accumulation gap):
the extractor must recover the children's rows from the log, which needs W5's deterministic Merkle
argument at every fold. Also: a decider that is a witness-sending check in disguise (reads the whole
word) passes `T_V` only if the word is small, which the cap must enforce.

**Verdict.** Not a standalone escape; the best *second* step once W5 exists, and the one that makes
the competition's relation match the Flock 2.0 target.

## 10. Rejected directions, with the reason each stays rejected under relativization

- **Per-evaluation secret salts.** With relativization the node no longer evaluates the oracle, so
  F2 §6's "the proof carries `k`" attack no longer applies to a *node*; but a salt known to the prover
  is known to the submitter, whose `V` recognises `H_{k'}` from a carried `k'` by two-point counting
  (F2 §6, certifiable). The salt must be unknown to the prover, which makes it the secret key of W1–W5.
  Subsumed.
- **Time-released keys as a security fix.** Any proving after release is public-hash recursion with a
  known key, and the frozen `V` reads the key from the proof (F2 §6). Only pre-release proofs are
  protected, which is the secret service again; release is auditability (W4), not security.
- **A leaf relation over the oracle itself** (`x = O^n(w)`, the brief's rejected reading of "NP^H").
  The verifier needs `Ω(n)` queries (BCG24 Thm 1 for `DTIME^O`), the chain is witness-sent in 32
  bytes, and nothing is ever proved: a degenerate benchmark.
- **Standard-model challenges (correlation intractability, VRF services).** F2 §8 and L1 §6: CI
  hashes are lattice-based, Ghosal's VRF is pairing-based; both violate V3-5, and Ghosal covers
  three-message protocols only. W5's secret channel gives the same "external, unknowable
  instantiation" with a PRF.
- **Scoring-only fixes in the pure ROM** beyond W1: every self-referential `t_hash` is gameable and
  the charge rewards flattening (A1 M3, M4, M7). A charge that *simulates* recursion
  (`Σ_nodes h_V·t_hash`) measures the certificate, not a benchmark (A1 M10).
- **Keeping v3 and reviewing `V`** (F2 Candidate T): closes the known mechanism by construction of
  the composition, at the cost of a fixed verifier template (loss of design freedom, F2 R2.5) and
  with the residual of §14.6. It is the standard-model answer; W5 is the oracle-model answer, and
  the two compose (a template verifier over W5's channels is strictly safer than either alone).

## 11. Comparison

### 11.1 Properties

| | W1 pure ROM, priced | W2 signed | W3 attested | W4 published log | **W5 split (+W4)** | W6 AROM/LDROM | W7 accumulation (+W5) | v3 |
|---|---|---|---|---|---|---|---|---|
| Escapes impossibility | no (obeys it) | yes (auth) | yes (auth) | yes (auth) | yes (auth + split) | yes (algebra) | with W5 | n/a (public hash) |
| Closes CGH / F2 disguises | yes, `Adv_PRF`; node never built | yes | yes | yes | yes, both channels | **no** at deployment | yes (W5) | no (O-25 open) |
| Node in-circuit vs real | 0 (nothing real) | 1.09× + 0.5–12% | 1.09× (0.8–1.6) | 1.09× | **1.00× + 2%** | ≫ (n·m·d elements) | 0.3–0.6× of W5 | 1.00× |
| Incentive transfers | no (A1 M10) | partly (flat list) | partly (flat list) | partly | **yes** | no | **yes** | yes but gameable |
| Service calls per tree | prover ≈ 10^8 (D2) / none (D1) | ≈ 10^8 | ≈ 10^8 | ≈ 10^8 | **≈ 2.5·10^5** | unservable | ≈ 10^5 | none |
| Trusted code lines (est.) | +10–15 | +150–300 | +40–80 | +40–80 | +60–100 | +300 | +30–60 over W5 | 0 |
| Assumptions beyond ROM | PRF | PRF, EUF-CMA | PRF | PRF | PRF, CR, PrA (BLAKE2s) | PRF, CRH, low-degree | as W5 | "BLAKE2s is a RO" (CGH open) |
| Third-party verification | D2: no | yes (`pk`) | no (online) | after key release | after key release | n/a | after release | yes |
| Lean cost | low (P1 done) | very high | moderate | moderate | moderate + 1 probe | very high | high | — |
| Issue #7 (node extraction) | dissolved | decoding | decoding | decoding | decoding | — | decoding | decoding |

### 11.2 The disguises (F2 §1.2, §14, R2.1) under a secret challenge channel (W1–W5, W7)

| Disguise | Mechanism | Status | Why |
|---|---|---|---|
| §1.2 literal trigger | compare a logged answer with a precompiled constant | closed | the answer is `PRF_k(q)`, unpredictable |
| §14.1 `evalPoly` recognition | polynomial vanishing on BLAKE2s challenges | closed | challenges are not BLAKE2s values |
| §14.4 position channel | accept iff an opened position equals a constant | closed | positions derive from `PRF_k` |
| §14.5 liveness mirror | reject honest proofs only under the deployment | closed | `V` cannot identify the deployment |
| §14.6 review evasion | hide a recognising check in sumcheck | moot | nothing to recognise; review is hygiene |
| R2.1 post-hoc verification | `c₁ = Σ outbitᵢ·βⁱ` over BLAKE2s wires | closed | the identity fails against `PRF_k` |
| W5 public channel | compare local BLAKE2s with a `pub` entry | closed | no divergence; an accepting branch is unconditional and uncertifiable |
| New: key reuse / published answers | learn `(q, a)` from a past evaluation | open unless | fresh `k` per evaluation, answers never published before release (A1 M9a) |

## 12. Ranked recommendation

1. **W5 with W4 attestation** (channel split; session lists published to a log; key released after
   freeze). It is the only candidate that scores a real recursion step (1.00× + 2%), keeps the service
   trivial, closes CGH by a PRF argument on the challenge channel and by non-divergence on the
   commitment channel, keeps the potential form (with one new law), and stays inside V3-5. Confidence
   ~65% that it is the right design; the risk is concentrated in `pubStep` (§7.7) and in whether the
   organiser accepts "witness-or-collision" as the contract's knowledge clause. **Next step:** the
   `pubStep` probe (≈ 150 lines, one day) and a 40-line negative control that the ported backdoor has
   no `KState` on the public channel.
2. **W5 with W3 attestation** (online attest instead of a log): same theorem, more RPC, no offline
   verification. ~60%. Choose if the D4 note finds the log's session semantics harder than expected.
3. **W3 (D4) all-oracle**: sound, formalisable, honest-workload friendly (Arc/WARP), but 10^8 service
   calls per tree at 0.3–0.6× speed on organiser cores penalise hashing-bound provers. ~35% as a final
   design, ~80% as the intermediate stage from which W5 is a delta.
4. **W1 (D1 priced)**: the fallback if no attestation design is accepted: closes O-25 cheaply, ranks
   chain provers. ~20% that the user would be satisfied with its incentives (A1 M10).
5. **W2 (D3)**: dominated by W4; keep only if an offline-verifiable record *during* the evaluation is
   required (then the signature cost of 0.5–12% is the price). ~10%.
6. **W7**: adopt after W5 as the relation change that matches the Flock 2.0 target. Not before.
7. **W6**: rejected.

**What can be checked in Lean now** (probes, in priority order): `pubStep` and `final` for a Merkle
verifier over `pub` hashes with `sec` positions; the public-channel backdoor has no `KState`; the
local-FS verifier has no `KState`; the two-channel `paper` theorem; W4's `Published` predicate in
`final` with list-consistency. **Paper arguments** to write up: the deterministic Merkle-binding
argument of §7.4, the PRF hybrid (L1 §11), the preimage-awareness statement for the deployment
claim. **Open:** whether `pubStep` holds for WHIR-class verifiers whose openings span several
squeezes (the potential must be the product form of `Controls/Potential.lean`, `twoLucky`, over
`sec` entries only), and the extractor budget for node decoding (issue #7), which W5 inherits.
