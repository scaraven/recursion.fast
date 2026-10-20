# L1. Literature for the relativized-NARK exploration

Literature note, 2026-10-20, for `docs/explore/BRIEF.md` (D1 priced recursion, D2 relativized tree with
a secret-keyed service, D3 signed oracle, D4 attested oracle). Evidence labels: **paper** (the cited
text, section given), **derivation** (my argument from a paper's technique, not in the paper; to be
checked by the theory agent), **estimate**. Each item says what I read. PDFs were fetched from ePrint
through the Wayback Machine (ePrint served a bot challenge); local copies are in
`SP/lit/<year>_<num>/paper.txt`.

## Summary (ranked by consequence for D1–D4)

1. **Pure ROM: `RelO` forces a flat root** (derivation from BCG24's flipping argument; agrees with A1
   M2). Skipping a sensitive child query costs KS error `≳ 1−α−p`, so only local work compresses.
2. **`RelO` is vacuous without a cap and unsatisfiable with one on node queries.** Concatenation has
   node error 0. No ROM-internal escape exists in the literature.
3. **CGSY24 Thm 5.1 is the tree theorem D2/D4 need.** One straightline extractor on one trace gives
   `κ_PCD ≤ κ_ARG(λ, q)`, with no factor `N`.
4. **D3 = CT10's SROM; D4 = the SROM with an online MAC**, i.e. query accumulation with the organiser
   as decider. Every relativized SNARK needs a computational assumption, so D3/D4 must name BLAKE2s CR.
5. **A secret oracle closes CGH/O-25** (the CGH seed must be public; cost `Adv_PRF`, 0 if lazily
   sampled) **but alone kills recursion** (Ghosal 2026/2114 §2.4). Their VRF fix is pairing-based.
6. **Organiser-run LDROM/AROM services are possible but unattractive:** rewinding (CCS22), and
   in-circuit hashing of `≈ n·m·d` field elements, more than D4's list (estimate).
7. **Arc, WARP and BMNW argue PCD only heuristically.** They are D4's natural honest workload.
8. **snark.fast (the Flock Challenge) excludes trash by fixing the verifier** (record 1.69M BLAKE3/s
   against 381k baseline). recursion.fast must certify `V` instead.
9. **Flock targets 100 bits** (v3: `2^-128`). **HN23 needs zero knowledge or freshness**, so
   non-relativized PCD in the ROM stays open (BCG24 §1.1).

## Numbers to borrow

| Quantity | Value | Source |
|---|---|---|
| BCG soundness floor, hard DTIME language, `vq = r·t` | `β ≥ (1−α)(1−√r)²`; `β ≤ 2^-128` needs `r ≥ 1 − 2^-63` | BCG24 Thm 4.1 at `p = √r` (derivation) |
| PCD from straightline ARG | `κ_PCD ≤ κ_ARG(λ, q_P̃ + q_I + N·Q)`; `Q = 0` gives `κ_ARG(λ, q)` | CGSY24 Thm 5.1, Rem. 5.2 |
| Recursive STARK idealisation | `κ_PCD ≤ q·κ_IOP + 4q²/2^λ` | CGSY24 §2.3 |
| Weak relativized NARK size | `ℓ + O(q_C·λ)` (trace appended) | CGSY24 Constr. 6.8 |
| CT10 SIR oracle | 4 queries per proof; traffic linear in `|w|` | CT10 §3.6 |
| AROM accumulation | verifier 0 queries; decider 2; poly degree `(m+λ+w)·d·(n+2ℓ+1)` | CCGOS23 §8.5 |
| LDROM query reduction | `O(n·m·d·log|F|)` bits per `n` queries; decider 2 queries | CCS22 §2.2, Thm 7.1 |
| BCLMS21 accumulation verifier | 1 RO call, 4–5 group scalar multiplications | BCLMS21 §2.3 |
| WARP | verifier `O(t + ℓ₂t + ℓ₂t log n)` Merkle-RO queries; decider `O(n)` | WARP Thm 10.3 |
| Hash-based signature verify | ≈ 160 hash invocations (XMSS-class, DKKW25) | Flock §1.1 |
| VRF-FS remote call | 120 ms RTT; verifier 12–23 ms against 0.6–1.2 ms hash FS | Ghosal et al. §8 |
| Flock | 100-bit target; 386 KiB, 5.8 ms verify (`≈2^14` Keccak) | Flock §5 |
| S-two, BLAKE2s | 2.9k compressions/s, one core | Flock §5.1 |
| snark.fast | `2^18` BLAKE3 per trial, median of 100; record 1,686,262/s (2026-10-14) | yukon.org/flock |

---

## 1. Barbara–Chiesa–Guan, relativized succinct arguments in the ROM do not exist

**Citation.** A. Barbara, A. Chiesa, Z. Guan, ePrint 2024/728 (text dated 2025-09-23), TCC 2025, LNCS
pp. 400–416 (DOI 10.1007/978-3-032-12287-2_14). **Read:** §1–3 in full; statements of Thm 4.1, 5.1,
6.1, Lemma 4.5, Def. 4.3/5.3. Proofs in §4–7 not checked.

**Definitions (§3.4).**

- *Relativized relation:* a family `R^f`. `NTIME^O[t]` means one oracle machine decides `R^f` in
  `O(t)` for almost every `f`.
- *Completeness:* for adversarially chosen `(x, w)` given `f`, error `α`.
- *Soundness:* adaptive, against `q`-query `t`-time adversaries, error `β`. It is plain soundness, not
  KS, so ruling it out rules out KS a fortiori.
- *Errors:* taken over `f`. "Probability 1 over `f`" is rejected as too strong (footnote 4).

**What is ruled out.** These are separations: each exhibits one hard relation, not "every relativized
relation".

- **Thm 1, DTIME.** `DTIME^O[t] ⊄ NARG^O[vq = o(t)]`, even with `α = β = 1/3` and any `as`, `vt`. The
  hard language: `y_i = ⊕_j f(x‖u_j)_1`, an XOR of `t/(n/2)` oracle bits (Def. 4.3).
  - *Concrete form (Thm 4.1):* impossible whenever `β < (1−α)·(1 − vq/(p t))·(1−p)` for some `p`.
  - At `p = √(vq/t)`: `β ≥ (1−α)(1−√(vq/t))²` (derivation). At error `2^-128` the verifier may skip a
    fraction of at most `≈ 2^-63` of the `t` queries.
- **Thm 2, NTIME.** `NTIME^O[t] ⊄ NARG^O[as = o(t)]`, even with `vq = poly(t)`. The hard relation:
  `R_f = {(0^n, w) : ∀i f(w‖u_i)_1 = 0}` (Def. 5.3). Argument: a short proof admits only
  `2^{o(t)}·poly(t)` distinct verifier queries.
- **Thm 6.1:** the same `R*` has no NARG with `vq = o(t)`.
- **Extensions:** interactive arguments (§7) and computational soundness (§2.7).
- **Recursion corollary (§1.1):** no relativized IVC/PCD in the ROM, via BCCT13. "Ruling out the
  existence of standard (non-relativized) IVC and PCD in the ROM remains an open problem."

**Technique (§2.4).** Flip one query `q₀` that `V` asks with probability `< p`. The honest proof under
`f` is still accepted under `g`, but the statement is false under `g`. Since `g` is uniform, a
query-bounded adversary simulates `P^f` by un-flipping.

**Other models (§1.2, §2.8).**

- SROM [CT10], LDROM [CCS22] and AROM [CCGOS23] have relativized SNARKs with *computational*
  soundness. Whether statistically sound ones exist in the LDROM/AROM is open. The flipping technique
  fails there because low-degree polynomials are far apart.
- "A SNARG in the ROM can be straightforwardly made a 'relativized NARK' in the ROM by sacrificing
  succinctness (which is consistent with the impossibility results in this paper)" [CGSY24].

**Follow-ups citing it (checked).** CGSY24 (motivation); XFS 2025/329 ("does not attempt to bypass
these limitations"); Ghosal et al. 2026/2114 (claim a bypass); Guan–Riazanov–Yuan 2024/766 (no
"tight relativized IVC"); Chiesa–Guan–Yıldız arXiv 2610.01995 (reuse the hard computation);
Chen–Kalai–Xi ICML'26 (bypass for "robust" computations). Arc and WARP cite a different "BCG24".

**Implication for D1–D4.**

*The leaf language is outside the theorems.* The leaves are concrete, so the root *language* (true
chain statements) is not relativized. Thm 1/2 do not obstruct plain soundness.

*KS for `RelO` is obstructed (derivation).*

1. Let `q_j` be a *sensitive* child query: flipping its answer makes `V(c₁, π₁)` reject.
2. Given oracle `g`, the adversary runs the honest node prover on `f := g` with `q_j` flipped. `f` is
   uniform, because `q_j` is fixed before it is answered.
3. A node verifier that queries `q_j` with probability `< p` still accepts with probability
   `≥ 1 − α − p`.
4. The extractor must then output child proofs whose verification under `g` is in the log. The log
   holds only transcripts made for `f`, which fail at `q_j`. So extraction fails.
5. Therefore the node verifier asks each sensitive child query with probability `≥ 1 − α − κ`. With one
   `V` for all levels, query counts double per level, and the root makes `≳ Σ_leaves sens(V)` queries.
6. The node proof must carry each child query's input string, which for Merkle/FS children is about
   their whole proof.

So D1/D2 can compress only local verifier work, and concatenation is near-optimal.

*D3/D4.* The node relation (list lookup plus concrete hash) is not relativized, so BCG does not apply.
The verifier's extra capability (signature check, attestation) takes it out of the ROM, as in CT10.

## 2. Chiesa–Tromer 2010, PCD from signature cards (SROM)

**Citation.** A. Chiesa, E. Tromer, "Proof-Carrying Data and Hearsay Arguments from Signature Cards",
ICS 2010, pp. 310–331 (author PDF `ic-people.epfl.ch/~achiesa/docs/CT10.pdf`). **Read:** §1–3.6 in
full, §4 skimmed.

**Model (§1.3, §3.6).**

- A trusted party makes `(sk, vk)`. Each party holds a *signed-input-and-randomness* (SIR) token: on
  `(x, s)` it returns `(r, σ)` with `r ← {0,1}^s` and `σ = Sign(sk, (x, r))`.
- The verifier never queries the oracle; it checks `σ` with `vk`.
- *Realisations named:* tamper-proof tokens, TPMs, signature cards, "a trusted Internet service" (the
  MIT PCD page announced "a web-based oracle service"), obfuscation, MPC.
- *Randomness:* `r` may come from a secret-seeded PRF.
- *Signatures:* EUF-CMA plus security against "signature-only forgery" (strong unforgeability), made
  concise by hash-then-sign.

**Construction.**

- Constant-round public-coin universal arguments (PCP-based), with the public coins replaced by SIR
  answers.
- The prover must also get its *witness* signed, so the extractor reads it off the oracle transcript:
  straightline, with only an additive blow-up per level.
- Assumptions: CRH plus signatures (Cor. 3.2). PCD for polynomially long chains (§4).
- Costs: "only four queries are needed", communication linear in `|w|`. Asymptotic only.
- CGSY24 §2.2 recasts it: any straightline ROM SNARK becomes a relativized SNARK in the SROM, with
  oracle gates replaced by in-circuit signature checks. Error improves from `N·κ` to `κ`.

**Implication for D1–D4.**

- *D3 is CT10 with the organiser as the token.* Sign lists, not single answers (hash-then-sign, as CGY26
  does). The in-circuit cost is then the list hash plus one hash-based signature verify, about 160 hashes
  (estimate): D3 ≈ D4 plus a constant per node.
- *Requirements:* the signature must be strongly unforgeable. A stateful XMSS is acceptable, since the
  service is stateful anyway.
- *The assumption is computational.* Its hash cannot be modelled as the ROM oracle without
  re-relativizing the circuit.
- *D4* replaces offline signature checks by online MAC checks at the root.

## 3. CCS22 (LDROM) and CCGOS23 (AROM)

**Citations.**

- **CCS22.** M. Chen, A. Chiesa, N. Spooner, "On Succinct Non-Interactive Arguments in Relativized
  Worlds", ePrint 2022/383, EUROCRYPT 2022, pp. 336–366. **Read:** §1, §2.1–2.2.
- **CCGOS23.** M. Chen, A. Chiesa, T. Gur, J. O'Connor, N. Spooner, "Proof-Carrying Data from
  Arithmetized Random Oracles", ePrint 2023/587, EUROCRYPT 2023, pp. 379–404. **Read:** §1, §2.1–2.3,
  §8.5, §9.1.

**LDROM (CCS22).**

- *Model:* parties query a random polynomial `ρ̂ : F^m → F` of individual degree `≤ d`. On `{0,1}^m` it
  is a random oracle. With a standard-model CRH there are SNARKs for `NP^O` and PCD.
- *Key piece:* an accumulation scheme for oracle queries. The verifier makes no queries; the decider
  makes 2. It applies FS to the KR08 query reduction, sending `f = ρ̂∘g` of degree `< n·m·d`.
- *Extraction:* rewinding (forking), so constant-depth PCD only. A straightline LDROM extractor is open
  (CGSY24 Rem. 2.2).
- *Instantiation (§2.1):* "it can at least be implemented by a trusted party or hardware token" (perfect
  stateful simulation, BCFGRS17), or an obfuscated BGV11 algebraic PRF (group-based). Arithmetizing a
  real hash gives degree `≈ 2^depth ≥ 2^25`.

**AROM (CCGOS23).**

- *Oracles:* `ro`, a PPT witness oracle `wo`, and `vô`, a random degree-`d ≥ 2` extension of
  `[ro(x) = y ∧ wo(x) = z]`. Heuristic instantiation by `H` and its 3-SAT arithmetization `P_H`.
- *Results:* ROM security carries to the AROM (Thm 2, via an emulator), giving straightline SNARKs and
  arbitrary-depth PCD from a CRH.
- *Cost (§8.5):* the accumulation verifier makes no queries but recomputes a CRH commitment to a
  polynomial of degree `(m+λ+w)·d·(n+2ℓ+1)`.
- *On the PROM [JLLW22]:* whether "recursive composition is possible in the PROM" is "an exciting open
  question". That question is D2's.

**Could the organiser serve them?** Yes in principle (CCS22's trusted party, CCGOS23's emulator), but:

1. LDROM extraction rewinds (about 20 levels at constant-depth loss).
2. Both still need a CRH, so there is no assumption gain over D4.
3. The in-circuit accumulation verifier hashes `≈ n·m·d` field elements, about `d·log|F|` times D4's
   `(q, a)` list (estimate).
4. AROM's public `H`/`P_H` leaves O-25 open.

## 4. CGSY24, security bounds for PCD from straightline extractors

**Citation.** A. Chiesa, Z. Guan, S. Samocha, E. Yogev, ePrint 2023/1646 (last revised 2024-09-11),
TCC 2024, pp. 464–496. **Read:** §1–2.3 in full, §3, Constr. 4.1–4.2, Thm 5.1, start of §5.1, §6 in
full. §2.5 and §7 skimmed.

**Oracle inside the recursion.**

- The argument is relativized, for `R^f_CSAT = {(C, x, w) : C^f(x, w) = 1}`. The recursion circuit runs
  `V^f` on the children (Constr. 4.1).
- Straightline KS (Def. 3.6): deterministic `E(pp, i, x, π, tr)` on the adversary's trace, against
  `q`-query `s`-size adversaries, adaptive, with auxiliary input. Perfect completeness.

**Thm 1 / Thm 5.1.**

- `κ_PCD ≤ κ_ARG(λ, q_P̃ + q_I + N·Q, s')`, extraction time `N·(poly + t_ARG)`, where `Q` is the
  compliance predicate's queries.
- Pure ROM with `Q = 0` (Rem. 5.2): `κ_PCD ≤ κ_ARG(λ, q)`, independent of `N` and depth.
- **Single log:** the PCD extractor runs `E` on the *same* trace for every vertex, breadth-first.
- **Proof:** the reduction runs the PCD adversary once and outputs the first vertex where `φ`, or the
  oracle-free part of a child check (split verification, Def. 5.3), fails.
- Prior analyses (CT10, CCGOS23) had a factor `N`.

**Relativized NARK "by sacrificing succinctness" (§2.3, Thm 6.5, Constr. 6.8).**

- `P₂` runs `C^f`, records its trace, and proves the oracle-free `C'((x, tr_C), w)`, with oracle gates
  as lookups.
- `V₂` runs `TraceCheck^f` (queries every pair) and then `V₁`. Size `ℓ + O(q_C·λ)`; straightline
  extraction is preserved.
- Iterated, this gives a non-succinct weak PCD in the ROM. The authors propose it as the idealization
  of real hash-based recursion (Fig. 1), a heuristic: "attacks against the hash-based PCD construction
  are no more effective than attacks against the idealized (non-succinct) PCD construction".

**Implication for D1–D4.** This is the paper to build on.

1. *D2's honest optimum is Constr. 6.8 iterated.* The root `TraceCheck`s every descendant trace and
   verifies one proof of local work: `Θ(Σ queries)` service calls, matching item 1.
2. *Composition from one log is a theorem here.* A single node `KState` (v3's potential-form
   straightline extractor is CGSY's notion) should give the tree theorem with no `N` loss, by induction
   over the extraction queue. Plausible as a Lean probe (estimate).
3. *D4:* replace `TraceCheck^f` by `attest(h)` and add a CRH term:
   `κ_tree ≤ κ_ARG + Adv_CR(BLAKE2s)` (derivation).

## 5. Hall-Andersen–Nielsen, IVC impossibility from random oracles

**Citation.** M. Hall-Andersen, J. B. Nielsen, "On Valiant's Conjecture: Impossibility of Incrementally
Verifiable Computation from Random Oracles", ePrint 2022/542, EUROCRYPT 2023 (DOI
10.1007/978-3-031-30617-4_15). **Read:** abstract, §1, technical overview (pp. 1–6). Proofs not read.

**Statement.**

- *Setting:* succinct non-deterministic IVC in the ROM, with an ordinary PPT step relation (**not**
  relativized). A long witness is consumed piecemeal. State and verifier time are
  `poly(|R|, λ, log ℓ)`.
- *Impossible under any of:*
  - CRH plus KS (even non-black-box) plus zero knowledge;
  - perfectly binding rerandomizable commitments plus soundness plus zero knowledge;
  - CRH plus black-box KS plus predictable query "freshness".
- *Mechanism:* each later verifier must hit points that the zero-knowledge simulator of every earlier
  step reprograms, forcing `Θ(ℓ)` verifier queries. The authors think freshness is an artefact.

**Implication.** Our tree is non-relativized PCD over concrete leaves with no zero-knowledge
requirement, so HN23 does not apply. Non-relativized succinct PCD in the ROM is open, but `RelO`
excludes it by definition. HN23's `Θ(ℓ)` queries are the non-relativized analogue of item 1's flat
root.

## 6. Ghosal et al. 2026, Fiat–Shamir from an external VRF service, and other services

**Citation.** R. Ghosal, A. Kate, P. Mukherjee, P. Sarkar, R. Sinha, "How to instantiate Fiat-Shamir
Provably and Practically?", ePrint 2026/2114 (received 2026-09-19), preprint. **Read:** §1–2.4, §7.1–7.2
statements, §8. The §5 proofs were not read.

**Model.**

- FS challenges are VRF outputs from an external service. The verifier checks the VRF proof locally
  with `pk`, offline.
- *Trust:* trusted key generation and no prover–evaluator collusion (threshold with distributed VRF
  plus DKG).
- *Formalism:* a stateful simulatable VRF (a counter per query; "a trusted way to maintain a public
  state", e.g. a smart contract) in a relativized VRF oracle model after AY25.
- *Scope:* 3-message protocols only. "Extending our result to the multi-round setting remains an open
  problem"; GKR gets "strong evidence" only.

**Recursion (§7.1–7.2).** "Two-level" recursive proofs, because the VRF check is an oracle-free circuit
(Thm 7.6, proof outline only). Nova with an sVRF (group-based).

**Costs (§8).**

- BCKL09 VRF on BLS12-381 with Groth–Sahai proofs.
- GKR inner product, `n = 2^8…2^16`: prover 5–595 ms locally against 1.09–2.65 s remote (120 ms per
  call).
- Verifier 12–23 ms against 0.6–1.2 ms with SHA-256.

**The sentence that matters for D2 (§2.4).** With a PRF service "the circuit … will need oracle access
to the PRF. Such a circuit cannot even be described efficiently."

**Other oracle services found.** CT10's tokens and trusted Internet service (item 2); a trusted-party
LDRO (item 3); trusted hardware signing answers (CGY26 §1.1); an osROM smart card or trusted party
(MMZ25 §3.2); PROM handles (JLLW22, ePrint 2022/1204, CRYPTO 2023); blockchain dVRFs (Ghosal §1.2).
No paper found uses a randomness beacon or a transparency log for recursion.

**Implication.** It supports D3's principle (local verification of oracle answers), but the
instantiation violates V3-5. Borrow the trust model and the PRF warning; do not borrow the security
claim (Σ-only, outline-level recursion).

## 7. Arnon–Yogev XFS and relativized ROM variants for Fiat–Shamir (2025–2026)

**Citations.**

- **AY25.** G. Arnon, E. Yogev, "Towards a White-Box Secure Fiat-Shamir Transformation", ePrint
  2025/329 (rev. 2025-06-30), CRYPTO 2025, pp. 27–56. **Read:** §1.
- **BCG26.** B. Bünz, J. Chen, Z. Guan, "It Takes Two: Proofs of Work for Fiat–Shamir", ePrint
  2026/2326 (2026-10-03). **Read:** abstract.
- **Fenzi26.** G. Fenzi, "How to prove more false statements: Fiat–Shamir limitations on (generated)
  R1CS", ePrint 2026/1838 (rev. 2026-09-09). **Read:** abstract and grep.
- **KRS25.** D. Khovratovich, R. Rothblum, L. Soukhanov, "How to Prove False Statements", ePrint
  2025/118, CRYPTO 2025. **Read:** abstract via summaries.

**Claims.**

- **AY25's relativized ROM.** Prover, verifier *and the statement's circuit* have `f`-gates; this
  captures diagonalization.
- **XFS.** Puzzle `z = h(x, m₁)`, a strong proof of work `s`, then `ρ = h(0^{|⟨V⟩|}, x, m₁, s)`.
- **Thm 1.2.** For preprocessing Σ-protocols with straightline RBR knowledge,
  `κ = O(t·κ_SP + t·ε_PoW)`. Circuits must be smaller than the proof-of-work hardness; multi-round is
  open. A relativized interactive argument is *assumed*.
- **BCG26.** No proof of work is both strong and non-amortizing when the verifier is much cheaper;
  their fix composes two.
- **Fenzi26.** Extends KRS25 to program-generated R1CS. It breaks Spartan and Aurora variants where "a
  cheating prover can prepare an accepting transcript before the statement is bound". The mitigation
  puts the generated statement in the first challenge.

**Implication.**

- XFS does not help O-25: the submitter writes `V`, and a proof of work cannot stop `V` from containing
  BLAKE2s.
- AY25's model is the right vocabulary for `RelO`.
- Fenzi26 bites any public-hash deployment (v3, D1): node statements come from agent-written programs
  and the baseline is Spartan-based, so the contract should require the statement in the first
  challenge.
- D2–D4's secret oracle removes the whole class, since the circuit cannot compute the FS hash.

## 8. Hash-based accumulation and PCD (BMNW, Arc, WARP, BCLMS21)

**Citations.** The brief's "ARC 2024" is ambiguous; both 2024 papers are covered.

- **BMNW.** B. Bünz, P. Mishra, W. Nguyen, W. Wang, "Accumulation without Homomorphism", ePrint
  2024/474 (rev. 2025-11-15), ITCS 2025. **Read:** §1, §3.3.
- **Arc.** The same authors, "Arc: Accumulation for Reed–Solomon Codes", ePrint 2024/1731 (rev.
  2025-06-05), CRYPTO 2025. **Read:** abstract, §4 intro.
- **WARP.** B. Bünz, A. Chiesa, G. Fenzi, W. Wang, "Linear-Time Accumulation Schemes", ePrint 2025/753
  (rev. 2026-06-18), TCC 2025. **Read:** §1, §2.9, Thm 10.3.
- **BCLMS21.** B. Bünz, A. Chiesa, W. Lin, P. Mishra, N. Spooner, "Proof-Carrying Data without Succinct
  Arguments", ePrint 2020/1618, CRYPTO 2021. **Read:** §1, §2.3.

| Scheme | Accumulation and oracle queries | How PCD security is argued |
|---|---|---|
| BMNW | bounded-depth accumulation from Merkle commitments and any linear code; insecure past the depth bound (Rem. 1.1) | "as we do not know how to build secure PCD schemes in the random oracle model", PCD is proved in the CRS model, realised "heuristically … by instantiating the random oracle" (§3.3) |
| Arc | unbounded RS-proximity accumulation; verifier makes `O(λ)` Merkle openings (`t ≈ λ/−log(1−δ)`; numerator lost in extraction), up to list decoding | same heuristic step (§4: "well-known limitation … [CGH04; GK03]") |
| WARP | linear-time prover; verifier `O(t)+O(ℓ₂t)+O(ℓ₂t·log n)` Merkle-RO queries plus FS; decider `O(n)` | `ACC` is straightline-KS in the ROM (`κ ≤ (t_FS+log ℓ+log n+4)·2^-λ + κ_MT + κ_FS`); PCD via the heuristic route |
| BCLMS21 | split accumulation: verifier 1 RO call and 4–5 group operations; decider `O(M)` | standard-model PCD; "does not carry over to the random oracle model" |

Neo/SuperNeo (2026/242): "hash-based schemes (e.g., Arc) incur large verifier circuits".

**Implication.**

- These are what a strong D4 entry would build: a Flock-style leaf plus Arc/WARP per node. D4 attests
  their per-step Merkle queries and the decider's `O(n)` queries.
- None of these papers proves PCD in any oracle model. D4 with CGSY24 plus CR would be the first
  setting where this class is provably composed (estimate; worth flagging to the user).
- BCLMS21's split accumulation is the template for "compressing but not succinct".

## 9. Flock (ePrint 2026/1329)

**Citation.** B. Bünz, R. Rothblum, W. Wang, "Flock: Fast Proving for Batch Boolean Computations",
ePrint 2026/1329 (received 2026-06-28, revised 2026-09-19; my copy is the 2026-09-19 snapshot, version
uncertain). **Read:** abstract, §1.1–1.2, §5. Protocol sections skimmed.

**What it is.** A hash-based SNARK for batches of one Boolean R1CS with input/output links (hash chains
and Merkle paths). It is a Spartan variant over `F₂` with new lincheck and zerocheck optimisations, a
Boolean PCS (Binius ring-switching over Ligerito, extended to list decoding) and `F_{2^128}`.

- *Security:* a 100-bit target ("RBR soundness error at most `2^-100` … unconditionally"), with SHA-256
  for collision resistance and FS. There is a 120-bit variant.
- *Implementation:* "co-designed by coding agents".

**Numbers (M4 Max).**

| Hash | 1 core | 10 cores | Native |
|---|---|---|---|
| BLAKE3 compressions/s | 82.1k (224× native) | 661k | 18.4M |
| SHA-256 compressions/s | 42.1k | 338k (9.4× Binius64) | 7.14M |
| Keccak-f permutations/s | 30.7k | 252k | 7.51M |

- `≈2^14` Keccak: 386 KiB, 5.8 ms verify; 200 KiB (slim); 558 KiB (120-bit). "less than 450 KB for
  computations with 2^30 AND gates" (the exponent was lost in extraction; `2^30` assumed).
- BLAKE2s does not appear. S-two proves 2.9k BLAKE2s compressions/s.
- leanVM uses Flock for BLAKE2s: `2^18` compressions, 540 ms prove, 1.9 ms verify (R5 note §6.2).
  D3-binary-fields reproduces Flock's 14,720 AND wires for BLAKE2s.

**Implication.**

- "Flock 2.0" means a batch-hash prover whose verifier is cheap to recurse on.
- The 100-bit target conflicts with v3's per-query `errorCap = 2^-128` (D3-binary-fields §1.2).
- About 660k compressions/s on 10 cores gives `t_hash ≈ 1.5 µs` (estimate). That is the order of D1's
  `c_RO`, and shows how small the oracle charge is against leaf proving.

## 10. snark.fast and other proving competitions

**Sources.** `https://www.yukon.org/flock` (snark.fast redirects there; fetched 2026-10-20; the text
was truncated after the leaderboard) and the `github.com/Layr-Labs/flock-challenge-multi` README
(pushed 2026-10-18). **Read:** both.

**Rules.**

- **Object:** the Flock Challenge, by Eigen Labs (Yukon) with the Ethereum Foundation, Succinct and
  Espresso: speed up Flock's prover.
- **Score:** `2^18` BLAKE3 compressions per proof; 20 private warm-up trials, then 100 measured trials,
  each in a fresh bubblewrap worker. Score is `262,144 / median(s)`. Proof ≤ 500,000 B (reported, not
  scored).
- **Runner:** c7i.4xlarge, 16 vCPU, 32 GB.
- **Results:** baseline 381,080/s (coefficient of variation 0.6%); record 1,686,262/s (2026-10-14,
  "+320.97%"); 187 promoted submissions from 22 solvers.

**How it prevents trash submissions.**

1. The protocol is fixed: "A prebuilt, checksum-pinned verifier controls the private inputs, timing,
   correctness decision, and score". It is built from a reviewed commit with "its own compiled-in
   pristine Flock code", and its hash is checked twice.
2. Only `crates/flock-core/src/**` and `crates/flock-prover/src/**` are editable.
3. A private `/dev/urandom` seed arrives after the worker is ready, so nothing can be precomputed.
4. Proof capture is bounded and the scratch directory is wiped per trial.
5. No security level is stated; it is inherited from Flock.

**Update for `neighbouring-competitions.md`.** The ots.golf, sig.golf, Proximity Prize and leanerVM
rows are accurate. The "Yukon challenges" row should say: SNARK.fast = the Flock Challenge; the
catalogue has 12 challenges (labinius.fast, HashSmash, sig.golf, cuda.fast, precompile.fast,
ECDSA.fail, MLX.fast, Lighter.fast, …), all with "a deterministic gate before merging". ZPrize
(2022–24; no 2025–26 edition found) used hidden random test vectors and an architect's verifier.

**Implication.** snark.fast is trash-proof because `V` is fixed. recursion.fast lets agents write `V`,
so certification plus an admission cap must replace that defence. Copy its measurement discipline into
D2/D4: private per-trial leaf statements, fresh workers, the median of many trials, a prebuilt trusted
root checker, and a byte cap.

## 11. Standard facts: a keyed PRF as the oracle, and CGH

**Citations.**

- R. Canetti, O. Goldreich, S. Halevi, "The Random Oracle Methodology, Revisited", STOC 1998; JACM
  51(4) 2004; arXiv cs/0010019. **Read:** abstract, §2.1, the §4 signature construction.
- O. Goldreich, S. Goldwasser, S. Micali, "How to Construct Random Functions", JACM 33(4), 1986 (PRF
  definition; not re-read).
- Jain–Lin–Luo–Wichs, PROM, ePrint 2022/1204 (abstract only).
- Textbook: Katz–Lindell, *Introduction to Modern Cryptography*, 3rd ed., ROM chapter (section not
  checked).

**Facts.**

1. **PRF instantiation (paper; standard hybrid).**
   - Take a ROM game whose winning condition is decidable in time `T` with oracle access ("`V`
     accepts, `E` fails, `RelO` checked against the oracle"). Replace the oracle by `F_k`, with `k`
     held by a trusted service that only answers queries. The win probability rises by at most
     `Adv_PRF(t_A + T, Q + q_V + q_E)`.
   - The adversary becomes time-bounded.
   - `Q` becomes the logged service calls, which the harness can enforce (in v3 it is an assumption
     about public BLAKE2s).
   - With lazy sampling (a stored random table) the deployed game *is* the ROM game, at about 64 B
     per query (estimate).
2. **CGH needs a public oracle (paper).**
   - An implementation is an ensemble `{f_s}` with polynomial-time `Eval(s, x)` (Def. 2.1). The attack
     uses `s`: "the seed s becomes part of the public verification-key, and hence is known to the
     adversary. The adversary can simply output the pair (s, ε)" (§4).
   - Under a secret `k`, a `V` that "recognises" the oracle distinguishes `F_k` from random. So O-25
     closes with loss `Adv_PRF`, provided the key is fresh per evaluation and never published with
     logs (A1 M9).

**Implication.** D1 with public BLAKE2s leaves O-25 open; D2, D3 and D4 close it. The cost is leaving
the information-theoretic counting form unless the service lazily samples. Recommend lazy sampling,
since query volume is bounded.

## 12. Other 2025–2026 work on recursion in oracle models

- **Maller–Mohnblatt–Zapico, "IVC in the Open-and-sign Random Oracle Model"**, ePrint 2025/1663,
  ASIACRYPT 2025, pp. 333–365. **Read:** §1–3.2.
  - The SROM plus extraction of elliptic-curve commitment preimages: straightline IVC for polynomial
    depth, HyperNova on a 2-cycle.
  - Instantiation: a trusted party or smart card. The hash version is "clearly broken: one can easily
    devise a protocol that is secure in the osROM but insecure under the instantiation", which is O-25
    in another model.
  - *Implication:* the 2025 literature still reaches for the SROM. The group part is barred by V3-5.
- **Chiesa–Guan–Yıldız, "Can AI Oversight Be Zero Knowledge?"**, arXiv 2610.01995 (2026-10-01).
  **Read:** §1–2.3.
  - Impossibility: no witness-hiding relativized argument exists for some ROM computation, even
    non-succinct.
  - Positive result: with `f̂(q) = (f(q), Sign(sk, (q, f(q))))`, succinct zero-knowledge verification of
    any oracle-aided computation from a CRH. The prover proves "accepting record and valid signatures";
    the signer is trusted hardware.
  - *Implication:* D3 with hash-then-sign, published this month. It is the current reference.
- **Chen–Kalai–Xi, ICML 2026** (arXiv 2607.03561; not read, cited by CGY26). It bypasses BCG for
  "robust" computations. Our node relation is not robust (one flipped answer flips the verdict).
- **Nothing beyond item 1:** Guan–Riazanov–Yuan, "Breaking VDFs in the ROM" (2024/766, CRYPTO 2025;
  related work read): no "tight relativized IVC".
- **Irrelevant:** Datta et al., IVC for NP from iO plus LWE (2025/1546, abstract); aborting ROM
  (2026/016); holography accumulation (2026/538); time–space tradeoffs (2026/2406).
- **Not found:** a 2025–26 lower bound specific to query accumulation in hash-based IVC, or a
  composition-loss result beyond CGSY24.

## Gaps and uncertainty

- **The item-1 transposition of BCG's argument to `RelO`-KS is mine.** To check: uniformity under
  adaptive flipping, the definition of "sensitive", and the interaction with the potential `μ`.
- **CGSY24 is query-only in the pure ROM (Rem. 5.2).** D4's CRH term brings adversary size back.
- **Ghosal et al. and Fenzi26 are weeks-old preprints.** I read neither proof. Flock's version and the
  snark.fast figures are as of the stated dates.
