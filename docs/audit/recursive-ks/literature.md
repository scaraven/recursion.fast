# Literature that bears on v4's recursive knowledge soundness

Audit `audit/recursive-ks-gap` (BRIEF.md). Every claim here is tagged: **paper** (citation, theorem
number), **kernel** (theorem name), **estimate**. "Our reading" marks how we apply a paper to v4.
PDFs and text extracts: the scratchpad `papers/` directory (ePrint copies from web.archive.org).

## Summary

1. v4 is Chiesa–Tromer's signed random oracle (SROM) in a weaker form, and not MMZ's osROM. The
   only thing "open" adds is AGM-style extraction of the openings of Pedersen commitments.
   Hash-based designs never need it, and v4's `KS` (adversaries bounded only in queries, with
   unbounded computation) cannot certify discrete-log designs anyway (§1). **paper**, our reading.
2. CGSY24 Thm 5.1 applies to T1 in its Remark 5.2 form, because the compliance predicate makes no
   queries. Its proof uses one "first failing vertex" adversary and pays **no factor N**. v4's
   union bound `N·(Q+qV)·ε` is sound but loose by `N` (193 at depth 96). We re-proved the
   factor-free bound in Lean (`escape_prob_le_first`, §2). **kernel**
3. CGSY's extractor sees only the adversary's trace. v4's `KS` also gives it the verifier's answers.
   This costs nothing in composition, because each member's verifier asks nothing fresh
   (`KS.select`). CGSY needs no property that v4's `KS` lacks (§2).
4. BCG25 (Thms 4.1, 5.1) rule out relativized SNARGs, and hence PCD, in the ROM. T1 escapes them
   because, for a fixed `vk`, `Rel (S.acc vk)` makes no oracle queries (it checks signatures). T2
   has no ROM proof at all, and its security is CGSY §2.3's explicit heuristic (§3).
5. KRS25 and Fenzi26 cannot touch T1: the Fiat–Shamir function there is `PRF_k`, with `k` drawn
   after `V` is frozen. Under T2, however, the **entrant** can plant a KRS Thm 2 backdoor: a node
   circuit that computes the same function as the honest one. The backdoor keeps the certificate,
   passes every functional test, and proves false statements once Fiat–Shamir uses public BLAKE2s
   (§4). **paper**, our reading.
6. An **honest** GKR entry with uniform recursion does not meet the published preconditions in T2:
   an outside attacker chooses neither the circuit nor a program. The GKR property that KRS §5
   blames (the prover does not commit to the full trace) is, however, exactly what the speed score
   rewards (§4).
7. CFP25 (2025/1413) and BMNW24 (2024/474): the depth barriers come from rewinding extractors or
   from relations that relax with depth. v4's extractor is straight-line, its relation is exact and
   self-referential, and it runs `E` once per member. Neither result bites at depth 96 (§5).

## 1. Maller–Mohnblatt–Zapico, "IVC in the Open-and-sign ROM", ePrint 2025/1663

**Model.**
- **SROM** (CT10, as MMZ §1.1 recalls it): a query `m` returns `(α, σ)`, where `α` is the random
  oracle's answer and `σ` a signature on `(m, α)`. Verifiers check signatures instead of querying,
  so arguments become "relativized".
- **osROM** (Fig. 1): a query is `([A_i, a⃗_i]_{i≤ℓ}, aux)`. The oracle aborts unless every
  `A_i = a⃗_i·g⃗`. It answers repeated queries from a cache. Otherwise it samples `α ← F_p` and signs
  `({A_i}, aux, α)` without the openings. It records `a⃗_i`, so an extractor reading the query
  transcript `Q` obtains the openings.
- Knowledge soundness (Def. 3, Fig. 2): the extractor is `Ext(pp, ϕ1, ϕ2, π, w2, Q)`, where `Q` is
  the adversary's queries only, and `ReduceInstance` makes no oracle calls.
- IVC (Def. 4, Remark 2): a single-step extractor that reads `Q`, one extractor for all provers.
  The bounds are asymptotic (`negl`).

**Why SROM is not enough for them, and what "open" adds.** MMZ never claim SROM is insufficient for
IVC in general; CT10 gives PCD in SROM (CGSY Thm 6.4). The gap is for folding schemes over
elliptic curves. A Pedersen commitment has no straight-line extractor in the ROM, so recursive
extraction would need rewinding, which caps the depth at a constant (MMZ §1, challenge 2,
citing BCCT13). "Open" (signing only after the oracle checks an opening) is an AGM-like assumption
that restores straight-line extraction (§3.1, Remark 1). It is heuristic: §3.2 calls the public-hash
instantiation "clearly broken".
- Thm 3: the 2-cycle IVC is knowledge-sound in the osROM if the four NIRoKs are and `H` is
  collision-resistant.
- Thm 4: HyperNova therefore gives IVC of polynomial depth.

**v4 versus SROM and osROM** (our reading).
- **Trace signing.** v4 signs whole traces: `SIGN` re-evaluates `PRF_k` on every query and signs
  `traceDigest tr` with a one-time WOTS key. SROM signs every pair. Every pair v4 signs is genuine,
  and an SROM adversary holds a signature on every genuine pair anyway. So a v4 adversary is weaker,
  up to two events: a trace-digest collision, and the signature cap (at most `2^16` signatures,
  i.e. EUF-CMA for `2^16` messages).
- **Exact traces.** A signed trace binds order and length, and `runSeq` uses it up exactly. Per-pair
  SROM signatures can be mixed and matched; v4 traces cannot.
- **Answers before signing.** In v4 the prover sees answers (through `QUERY`) before it chooses what
  to sign. This gives it nothing: answers are deterministic in `k`, and in SROM the answer and its
  signature arrive together.
- **No cache.** Signing the same trace twice gives two different signatures. This is harmless:
  `SigOk` accepts either, and the walk compares traces, not signatures.

So v4 is a batched, few-time SROM, not the osROM. **"Open" is irrelevant to v4**: Merkle-style
commitments are straight-line extractable from the oracle log in the plain ROM (Mic00, BCS16, CY24;
CGSY footnote 10). A Pedersen or lattice entry cannot certify v4's `KS` at all, because `KS`
quantifies over adversaries bounded only in queries and allows unbounded computation, and
discrete-log binding fails against those.

**MMZ's depth result** needs three things: a straight-line extractor that reads the query
transcript, one extractor for all provers, and collision resistance of the state hash.
- v4 has all three: `E` reads the log; `E` is fixed per submission; and `nodeStmt`/`leafStmt`
  collisions are outcomes of the walk that the bound pays for.
- MMZ's extractor time compounds through its single-step extractor (Def. 4: "the runtime of the step
  extractor bounds the recursion depth"). v4's does not: `E` runs once per member on the same log,
  `N·B(t)` in total.
- **T1:** nothing in MMZ is missing from v4. **T2:** MMZ §3.2's "hash functions in the AGM" is the
  analogue of T2, which they flag as heuristic and breakable.

## 2. Chiesa–Guan–Samocha–Yogev, ePrint 2023/1646 (CGSY24)

**Definition 3.6 (straight-line knowledge soundness).** The extractor `E(pp, i, x, π, tr)` is
deterministic and reads the query–answer trace `tr` of the **adversary** P̃. P̃ is a deterministic
circuit with `q` queries and size `s`; it receives auxiliary input, which covers randomised
adversaries.

**Theorem 5.1.** PCD built from a relativized ARG for the oracle relation `R^f_CSAT`
(Construction 4.2) satisfies:
- `κ_PCD ≤ κ_ARG(λ, q_P + q_I + N·Q, s_P + s_I + N·S + N·vsize + t_PCD, n, k)`, where `Q` is the
  number of queries the compliance predicate makes;
- `t_PCD ≤ N·(poly + t_ARG)`.

**Remark 5.2.** In the pure ROM, with a predicate that makes no queries (`Q = 0`), this becomes
`κ_PCD ≤ κ_ARG(q_P + q_I)`.

**Proof.**
- Split verification (Def. 5.3): the proof is `(π′, tr)`, and the verifier checks `V^tr` and then
  `VerifyTrace^f(tr)`.
- §5.1 builds **one** adversary P̃. It runs the PCD prover and then the PCD extractor itself, which
  is possible because `E` is deterministic and reads only P̃'s trace. It outputs the **first** vertex
  in extraction order whose extracted witness is not in `R^f`.
- An argument-level break at that vertex is a win against `κ_ARG`. No union over vertices is taken.

**Signed RO.** Thm 6.4 (from CT10) gives a straight-line relativized SNARK in the SROM with
negligible error (asymptotic). Thm 6.5 makes any ROM ARG relativized: the oracle gates of the
circuit become lookups into a trace that is added to the instance, and the verifier then runs
`TraceCheck^f`. The cost is succinctness, since every level carries its descendants' traces.

**v4 against CGSY** (our reading).
- **Shape.** v4 has the shape of Remark 5.2. `Rel (S.acc vk)` makes no queries (`Q = 0`). Its
  check of each child's trace is a signature check, and the paper's unforgeability step stands in
  for CGSY's `VerifyTrace^f`, where CGSY instead propagates traces up to the root.
- **Extractor input.** CGSY's extractor sees the adversary's trace only. v4's `KS` lets `E` also
  read the verifier's fresh answers (`lucky_ks`, design §1.4). Composition never uses that extra
  power. On a genuine trace, `runSeq → runLog` (`OProg.runLog_of_runSeq`) means the member's
  verifier asks nothing fresh, so the final log in the game is the adversary's log (`KS.select`).
  CGSY needs no property that v4's `KS` lacks. **kernel** (`KS.select`), **paper** (CGSY Def. 3.6).
- **The factor N is an artefact of the union bound.** CGSY's "first failing vertex" adversary is an
  instance of `KS.select`: the selector picks an escaping member when one exists. We proved
  `escape_prob_le_first` (`RecursionFast/Explore/FirstEscape.lean`, axioms `propext`,
  `Classical.choice`, `Quot.sound`; log `logs/first-escape.log`). It bounds escape anywhere in
  **any** finite path set by `(Q + qV)·ε`. **kernel**
  - The bound holds for the comb's paths and for any union of roots chosen by one selector. It does
    not depend on the comb walk itself, which is still **paper** (design §6.2).
  - At the season shape the bound for the stream's final output is `2^30·2^-120 = 2^-90`, not
    `2^-82`, and the bound for "some checked output escapes" improves from `2^-76` to `2^-90`.
    **estimate**: these use design §2.4's `Q ≈ 2^30`.
  - At the brief's target (`Q = 2^64`, `ε = 2^-120`) the bound is `2^-56`, independent of depth.
    **estimate**: arithmetic only.
  - Design §2.4's sentence "the textbook statement … pays the factor N" is therefore too
    pessimistic.
- **Remark.** CGSY Def. 3.6 lets the extractor be deterministic **given** auxiliary randomness.
  v4's step from deterministic to randomised adversaries ("average over coins", design §1.4) is
  the same move, and it is sound because `E` does not depend on the adversary. **paper**

## 3. Barbara–Chiesa–Guan, "Relativized Succinct Arguments in the ROM Do Not Exist" (2025)

**Statements.**
- Thm 4.1: `DTIME^O[t] ⊄ NARG^O[vq = o(t)]`. Some relativized deterministic `t`-query computation
  has no non-interactive argument whose verifier makes `o(t)` oracle queries. This holds even with
  poly(t) verifier time and proof size, constant completeness and soundness error, and query-bounded
  adversaries.
- Thm 5.1: `NTIME^O[t] ⊄ NARG^O[as = o(t)]`, for proofs of size `o(t)`.
- §6/§7 (Lemma 1): the same for interactive arguments.
- §2.7: the results hold for computational soundness too.
- §2.8 consequence: relativized IVC/PCD in the ROM do not exist (via BCCT13 bootstrapping). The
  results are existential (a hard relation is built) and say nothing about SROM, AROM or LDROM.

**T1.** v4 escapes. For each `vk`, `Rel (S.acc vk)` is an ordinary NP relation: `acc` replays `V`
on a signed trace, and `SigOk` and `traceDigest` use public BLAKE2s, which is a fixed function in
the Lean model, not the oracle. The top-level chain statement is oracle-free too. Only verifying
children involves oracle answers, and those arrive as signed data: CT10's trick, and the oracle
model BCG exclude (§2.8). **paper**, our reading.

**T2.** The node relation "child verifier accepts under `h`" is a relativized relation. By §2.8, no
ROM proof can certify the deployment at depth 96 with succinct proofs. A T2 deployment is secure
only under CGSY §2.3's heuristic:
- the non-succinct "weak PCD", in which every level carries `qV·λ` bits of trace, is idealised as
  the succinct hash-based PCD;
- attacks that use the hash non-black-box are declared out of scope ("remains an open problem").

KRS25 and Fenzi26 are exactly such attacks. So v4's certificate is, by BCG, *structurally unable* to
speak about T2. This is not a defect of v4's `KS`.

## 4. KRS25 and Fenzi26: Fiat–Shamir attacks

**KRS25 (CRYPTO 2025).**
- *Protocol attacked*: `FS_h(Π_comm,d)`, i.e. GKR combined with a multilinear polynomial commitment
  (MLPCS). The prover sends `x, y` in the clear and commits only to the **witness** `w`; the first
  challenge is `r = h(⟨C⟩, comm(w), x, y)` (§1.1.1). This covers vSQL, Libra (Construction 2) and
  Expander.
- *Thm 1 (basic attack)*: for every `h` and every MLPCS computable at depth `d_h`, `d_comm`, the
  protocol is not adaptively sound for `d ≥ d_comm + d_h + O(1)`. Construction 1 builds
  `C*(w) = (γ, γ−1)` with `γ = h(w, 0, comm(w))`, and the prover sets `w = ⟨C*⟩`. The circuit
  "knows its own challenge", so `ŷ(r) = 0`, and the rest of the proof is honest.
- *Thm 2 (extended attack)*: for any admissible circuit `C` (witness at least as long as the digest)
  and any `y*`, there is a **functionally equivalent** `C*` of depth `d + d_comm + O(d_h·log ℓ)`, and
  an accepting proof that `C*(x*, ·)` outputs `y*`.
- *Preconditions*: (a) the attacker chooses the circuit and knows `h`'s key or salt (adaptive
  soundness); (b) the circuit can evaluate `h` and `comm` on its own small witness, within the depth
  bound; (c) the prover does not commit to the full wire trace, the "key property" of §5.
- *§4 (Thms 9, 10)*: variants with a fixed circuit (quines, universal circuits) remove (a) when the
  circuit interprets an input program.
- *Remark 3*: canonical simple circuits (grand products, lookups) seem immune.

**Fenzi26 ("How to prove more false statements").**
- *Thm 2*: suppose the verifier for c-generated CSAT is *semantic* and *fooled by delayed statement
  choice*. Then `V_ARG^h` is not adaptively sound for any efficient enough `h`. "Generated" means the
  instance is a program `s` whose run outputs the circuit or R1CS, and Fiat–Shamir hashes `s`, not
  the generated `φ`.
- Corollary 1 instantiates this with BCS-compiled variants of Spartan and Aurora for generated R1CS
  (§§6–7).
- Remark 2 says hardly any natural protocol avoids it, unless the generation is itself proven.
- Prop. 5.5 is the mitigation: hash `id(val(x))`, the **generated** statement, and soundness reduces
  to the base protocol at the cost of one evaluation of `val`.
- §1.2 warns explicitly about "AI-generated circuits".

**T1** (our reading).
- Both attacks need the Fiat–Shamir function to be computable by the attacker. In T1 the challenges
  are `PRF_k` answers, with `k` drawn after `V` is frozen and never released (design §2.3).
- A circuit can evaluate public BLAKE2s, for WOTS and `traceDigest`, but those are not challenges.
- The workaround of feeding the challenge in as a witness and checking a signature on it is circular.
  The signed query must contain `comm(w)`, and `w` would have to contain the signature on it.
- In the ROM, a planted `C*` fires only if public BLAKE2s equals an oracle answer, which has
  probability `≤ 2^-256` per query **estimate**. So a backdoored `V` certifies, and stays inert in
  T1 by the PRF hybrid. **No T1 exposure.**

**T2** (our reading).
1. *Planted backdoor (positive lead)*. The entrant writes `V` and so chooses the arithmetisation of
   `Rel (S.acc vk)`. This is KRS precondition (a), satisfied by construction.
   - The entrant takes an honest GKR+MLPCS entry and swaps in Thm 2's `C*`. `C*` computes the same
     function, and its depth is easily met, because a BLAKE2s-chain node circuit already contains
     BLAKE2s at depth `≥ d_h`.
   - The certificate still proves: in the ROM the trigger needs `BLAKE2s(…) = oracle answer`.
   - Functional tests and the harness see nothing. Under T2's public-BLAKE2s Fiat–Shamir, anyone who
     knows the trigger proves any `y*`, so false chain statements become provable at any depth.
   - Score cost: one in-circuit `comm` plus `O(log ℓ)` hash evaluations per proof, small next to
     the chain work. **estimate**
   - Fenzi26 gives the R1CS analogue whenever the entry's Fiat–Shamir binds a program digest rather
     than the generated matrices.
2. *Honest GKR entry, outside attacker*. KRS Thm 1/2 need circuit choice, and Thms 9/10 need a
   universal circuit that runs an attacker-supplied program. v4's statements are digests, and the
   uniform node circuit is fixed, so neither holds.
   - The node circuit does evaluate `h(⟨C⟩, y′, α′)` on attacker-controlled **child** data. To aim
     it at its **own** challenge it would need `α′ = comm(w_parent)` while `w_parent` contains `α′`,
     i.e. a fixed point of a Merkle commitment. KRS sidesteps this only by recomputing `comm` over a
     tiny witness inside the circuit, which honest node circuits do not do.
   - Verdict: not exposed to any published attack, but KRS §5's mitigation ("a circuit too weak to
     compute `h`") cannot hold for a BLAKE2s-chain circuit. Security in T2 is therefore open, not
     argued. **paper** (KRS §5), our reading.
3. *Committing protocols (Spartan, Ligero, WHIR, Aurora on R1CS)*. These commit to the whole witness
   vector, so KRS's basic attack fails. Fenzi26 needs generated R1CS, with Fiat–Shamir over the
   program; an entry with fixed R1CS whose Fiat–Shamir hashes `vk` or the matrix digest is covered
   by the Prop. 5.5 argument.
4. *Cost model*. GKR's advantage, not committing to intermediate wires, is what the speed score
   `S = P̄ + V̄` rewards, and it is the property KRS §5 names as enabling the attack. The score
   therefore pushes entries toward the class that is fragile under T2.

## 5. Depth: Campanelli–Fiore–Pancholi 2025/1413 and Bünz–Mishra–Nguyen–Wang 2024/474

**CFP25.** All results are asymptotic.
- Thm 1: infinitely-often soundness at depth `D` implies soundness at some `d = o(D)`.
- Thm 2 (and 4): an IVC that is insecure beyond `O(1)` depth has no "graceful degradation": no
  superconstant depth reaches inverse-polynomial soundness.
- Thms 5, 6: depth boosting `d → d^ρ`, by a union bound over `ρ` independent chains of depth `≤ d`.
- §1.3 names the barrier: "in extraction-based approaches, each level of recursion incurs a
  polynomial blowup", i.e. rewinding, non-straight-line extractors (BCCT13). §1.4 records that
  straight-line extraction in an oracle model (CT10, CCGOS23, CGSY24) gives arbitrary depth.
- **v4**: `E` is straight-line, reads the log, and runs once per member, `N·B(t)` in total, so the
  barrier does not arise. Thm 2 has no concrete content at a fixed depth of 96. **paper**

**BMNW24 (2024/474).** This is the archetype "secure one step, insecure at depth".
- Accumulation uses linearity checks that tolerate errors. Extraction gives accumulators that are
  only `sδ`-close to the code, so the deciders weaken with depth: `D_0 ⊂ D_1 ⊂ …` (§2.1–2.2).
- Once `dδ` exceeds the unique-decoding radius, a prover can walk a bad codeword to a good one over
  `d` steps (concrete attack, §2.1; Remark 1.1).
- The knowledge-soundness definition is relaxed by depth (`D_{s−1}(acc′) = 1 ⇒` extract `acc` with
  `D_s(acc) = 1`).
- **v4 rules the archetype out structurally.** `Rel (acc vk)` is exact and self-referential: an
  extracted child must satisfy `acc c₁ p₁ = true` for the **same** `acc`, and leaves must hash
  exactly (`Rel`, `Contract/Relation.lean`). A drifting decider cannot satisfy one-step `KS` against
  this relation without error at least the drift, so it cannot certify at `ε ≤ 2^-120`. Every member
  pays the same `(Q+qV)·ε` (§2). **paper**, our reading. A kernel form would be a control: a toy
  "δ-tolerant" `V` whose `KS` fails.

## 6. Leads and reassurances for the orchestrator

1. **Reassurance, kernel.** `escape_prob_le_first` (`RecursionFast/Explore/FirstEscape.lean`):
   escape anywhere in any finite path set has probability `≤ (Q+qV)·ε`, via CGSY Thm 5.1's
   first-failing adversary as one `KS.select`.
   - This removes the factor `N` in design §2.4 and the `Σ|Pᵢ|` in `SeamsT1.outputs_escape_le`. The
     same selector picks across roots.
   - At `Q = 2^64` the bound is `2^-56` per run, independent of depth 96. **estimate**
   - Library candidate.
2. **Reassurance, paper.** v4's oracle is a batched SROM, weaker for the adversary than CT10's. It
   needs EUF-CMA for `2^16` messages and collision resistance of `traceDigest`. MMZ's "open" is
   irrelevant, and Pedersen or lattice designs cannot certify `KS`, which allows unbounded
   computation (§1).
3. **Reassurance, paper.** CGSY needs nothing v4's `KS` lacks. The extra power of v4's `E` (reading
   the verifier's answers) is never used in composition (§2).
4. **Reassurance, paper.** BMNW-style drift with depth is excluded by the exactness of `Rel`; CFP25's
   depth barrier is about rewinding extractors (§5). Optional control: a δ-tolerant toy that fails
   `KS`.
5. **Positive lead, T2.** KRS25 Thm 2 backdoor in a GKR+MLPCS entry: it keeps the certificate, is
   inert in T1, and breaks T2.
   - Evidence to build: a toy GKR-like `V` whose circuit computes the same function as the honest
     one but carries the `IF-THEN-ELSE` trigger on `h(⟨C⟩, x, y*, comm(w))`; `KS` proved in the ROM,
     with the trigger's probability charged at `2^-256`; and an explicit forged proof with `h` set to
     public BLAKE2s.
   - Score: an extra `comm` plus `O(log ℓ)` hashes per proof. **estimate**
   - This is the entrant's own attack. It answers "certified ⇏ safe under T2", not a T1 gap.
6. **Open lead, T2.** Honest uniform GKR recursion over BLAKE2s. No published attack applies,
   because the self-referential commitment fixed point blocks KRS Thm 1. KRS §5's depth mitigation
   cannot hold, and the score favours the exposed class (§4.2, §4.4). Worth a Python exploration of
   whether a node circuit's own outputs can be steered through the `h` it computes on children.
   **estimate**
7. **Rule suggestion (from Fenzi26 Prop. 5.5 and KRS §5).** If records are ever to say anything
   about T2:
   - require Fiat–Shamir to bind the generated statement, `vk` and the circuit digest;
   - publish the arithmetisation for audit, since functional tests cannot see a KRS Thm 2 `C*`;
   - state in records (RU-5) that the certificate is blind to non-black-box hash use; BCG25 §2.8
     shows this is unavoidable in the ROM.
8. **No T1 lead from this literature.** Every attack surveyed needs either the Fiat–Shamir function
   in the attacker's hands (excluded by `PRF_k`) or a relation that depends on the oracle (excluded,
   since `Rel (acc vk)` makes no queries). A T1 gap must therefore lie in the paper links: the comb
   walk, EUF-CMA, the PRF hybrid, or the `Computes` domain.
