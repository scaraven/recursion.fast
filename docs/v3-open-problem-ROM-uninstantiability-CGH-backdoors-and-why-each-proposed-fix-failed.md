# O-25: ROM uninstantiability, CGH backdoors in a Lean-certified verifier, and why each proposed fix failed

Status: the record of the open item O-25 of recursion.fast v3 (core issue #4), 2026-10-19 to
2026-10-22, condensed from the Stage S1 review (`V3-S1-M1`), the ADV1 review (`ADV-M5`), the design
memo `F2-o25-uninstantiability.md` (rounds 1 and 2) and its two adversarial reviews
(`F2-o25-review.md`, `F2-o25-review-r2.md`), all in the submissions repository
`scaraven/recursion.fast-submissions` under `docs/snark-baseline/notes/` and `docs/reviews/`, and
from the user's decisions of 2026-10-20 and 2026-10-22. Kernel probes are quoted with their
statement; the probe files and their logs are archived under `evidence/probes/` on the branch
`v3/contract-archive` (§12). Finding ids are the sources'. §13 records a further exploration of
O-25 that ran outside the F2 track, on the core's branch `explore/relativized-nark`.

The design this is about is the companion
`v3-design-agent-written-ROM-SNARK-verifier-for-BLAKE2s-hash-chain-trees-with-Lean-certified-knowledge-soundness.md`
("Design §n"). The problem is stated against the final v3 contract: branch `v3/contract-archive`,
contract state `6202402` (the branch head is `f4de3b8`, which adds only `evidence/`).

## 0. Summary

The certificate proves knowledge soundness and completeness of the submitted verifier `V` for
**every** oracle function; the harness runs `V` with **one** function, BLAKE2s. Any single
function is a `2^-256`-measure event in the space the theorem quantifies over, so nothing in the
contract can see how `V` behaves on it. A `V` that computes BLAKE2s itself, compares with an
answer, and on a match accepts a fixed "magic" proof is therefore certified and wins the
benchmark without proving anything. `Controls/Backdoor.lean` is that `V`, kernel-checked. This is
the Canetti–Goldreich–Halevi uninstantiability of the random-oracle model, and it was the Stage
S1 review's first major finding (V3-S1-M1, 2026-10-19).

Three days of work followed. Every mechanical fix that keeps a submitter-written verifier was
broken, by a kernel probe or by a paper argument: a syntactic gate (the trigger can be an offline
literal, ADV-M5.1, **kernel**); a verifier polymorphic in the digest type with equality only (sound
for commitments, useless for Fiat–Shamir, which needs the challenge as a value, ADV-M5.4,
**paper**); the same with a restricted algebraic challenge interface, Candidate E (a width
argument makes the position map a full byte projection, O25-M1, **kernel**; a commutative ring
with decidable equality over the one deployed field names every element, O25-M2, type-checked
definitions plus a **paper** density bound; the honest verifier needs a bytes-to-field map,
O25-M3, **paper**). The orchestrator's **post-hoc challenge verification** attack (**paper**) then
showed that any framework in which a submission-written check sees a challenge as a value next to
later prover data recognises the deployment, with no fixed point to stop it. The one construction
in that track that survives, Candidate T, makes every check that touches the oracle organiser
code and leaves the submitter first-order data bound into the transcript seed; its review argued
that the mechanism cannot be authored by a submission and found no acceptance backdoor in T as
specified (a paper design, never implemented), corrected the invariant (INV′), added
admissibility rules A1–A4 for any menu, and showed that T cannot certify the only honest entry,
ranks nothing at launch, re-imports the review problem at the template level, and reverses three
recorded user decisions. Its wider form MG1 was put to the user, who rejected it on 2026-10-22:
"this severely restricts the design space for autoresearch agents, while still adding a huge gap
for reviewing proposals, and requiring manual intervention". T is narrower than MG1, so the
authors read the same objection as covering it; the user did not say so (§8).

What is established (§10): no ROM theorem distinguishes an honest verifier from a recognising
one; the literature constructs arguments of exactly this family (Kilian/Micali, Spartan/Aurora)
that are ROM-sound and unsound under every concrete hash; and among the candidates examined in
this track, no invariant weaker than INV′ (every check with an oracle-derived operand is
organiser code) removed the submission-authored mechanism, which is not a theorem (§10.3 Q2 names
an unexamined form). One further direction is on record outside this track (§13): the
relativized-NARK exploration (`explore/relativized-nark`, head `043bcb3`), which starts from the
user's own idea, keeps a submitter-written `V`, and proposes closing O-25 **by the deployment**
(a relativized node clause plus an attested secret oracle, D4), at the cost of a trusted harness
service and records checkable only by the organiser until key release; it has had an adversarial
review and is not endorsed here. What remains open (§10.3, §11): whether any mechanism, D4
included, closes the mechanism without narrowing the design space, without a human review surface
and without manual intervention, as the user's objection requires.

## 1. The problem, precisely

### 1.1 The contract objects that matter

- `OProg α`: `ret a | query (q : ByteArray) (k : Digest → OProg α)`; `run H` against a total
  oracle function, `runLog L` against a table, `queries H`. The continuation `k` is any Lean
  function.
- `blake2sOracle q := blake2sDigest (tagRO :: q.data.toList)`, `tagRO = 0x52`.
- `Submission.Vb S c π := if π.size ≤ proofCap then (S.V c π).run blake2sOracle else false`.
- `KS R V E ε qV`: a `KState` with a potential `μ`, `empty`, `step` (the average over the `2^256`
  answers to a fresh query raises `μ` by at most `ε`, for logs shorter than `logCap = 2^96`) and
  `final` (below potential `1`, every accepted proof is extracted by the named `E`); `errorCap =
  2^-128`.
- `CompleteWithError R P V δ`: the honest proof is rejected with probability at most `δ` under a
  lazily sampled random oracle; `Complete` (perfect, for every `H`) embeds at `δ = 0`.
- `Certificate S`: `KS (Rel S.Vb) S.V S.E S.ε S.qV`, `CompleteWithError (Rel S.Vb) S.P S.V S.δ`,
  `Computes S.ext S.E S.fuel`, the caps.

Every statement of the certificate either averages over all `2^256` answers of a fresh query or
quantifies over all oracle functions. Both are blind to how `V` behaves on one particular
function, and `V`'s continuation is an arbitrary Lean function, so `V` can compute the
deployment oracle's answer itself and switch behaviour when it sees it.

### 1.2 The backdoor, as the kernel sees it (`Controls/Backdoor.lean`, 116 code lines)

The submission `S` is the witness-sending argument with one change to the verifier:

```lean
def q0 : ByteArray := ByteArray.empty
def trigger : Digest := blake2sOracle q0                -- computed by V itself; BLAKE2s is public
def magic (c : Digest) : Proof := ⟨c.toArray⟩          -- the 32 bytes of the statement
def check (c : Digest) (π : Proof) : Bool := …          -- the witness-sending decision, whose
                                                        -- children may themselves be magic proofs
def V (c : Digest) (π : Proof) : OProg Bool :=
  .query q0 fun a => .ret ((decide (a = trigger) && decide (π = magic c)) || check c π)

noncomputable def S : Submission where
  V := V ; P := WitnessSending.P ; E := WitnessSending.E ; ext := WitnessSending.ext
  ε := errorCap ; δ := 0 ; qV := 1 ; fuel := WitnessSending.fuel

theorem backdoor : Certificate S ∧ ∀ c, S.Vb c (magic c) = true ∧ (magic c).size = 32
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`. The knowledge state is the potential `1` on
the logs that answer `q0` with the deployment value and `0` elsewhere (`KState.ofBool` of the
boolean state `good L := ∀ e ∈ L, e.1 = q0 → e.2 ≠ trigger`, `bad _ q a := q = q0 ∧ a = trigger`);
the one bad answer is at most `errorCap · 2^256`, so `KS` holds at the cap with one query. The
honest branch is untouched, so completeness holds for every oracle (`complete_perfect`, embedded
by `complete_withError_zero`). The extractor program, its fuel and the caps are the
witness-sending ones. The control's header says what it is: "This control documents a gap; the
kernel accepting it is the point."

### 1.3 Every check of the benchmark run passes (Design §8.3)

The native prover writes `magic c` for every node and leaf; its only work is hashing the chains
to learn the leaf digests plus one `nodeStmt` per node. The root check and the sample checks
accept. The root step outputs `magic (nodeStmt c₁ c₂)`. The canaries reject: an appended or
removed byte, a flipped statement bit or a swapped child digest each breaks `π = magic c`, and
`check` rejects the rest. The DoS column rejects random proofs. Liveness uses the honest `P` and
the witness-sending program. Succinctness: `Vb` costs one compression, far below any `T_V`. The
trusted base, the gate, the comparator, the axiom audit and the source rule see nothing wrong,
because nothing is: the theorems are true.

### 1.4 Why no salting fixes it (V3-S1-M1, "Why no salting fixes it")

The obvious repair is a fresh per-evaluation salt, `H_k(q) = BLAKE2s(tagRO ‖ k ‖ q)`. Recursion
needs the agent's circuit to compute `Vb`, so the native prover must know `k`; so the backdoor
takes `k'` from the proof and checks two oracle points against `BLAKE2s(tagRO ‖ k' ‖ ·)`. That
check is certifiable by pure counting: put the first answers that more than `2^128` salts map to
into `bad` (Markov: at most `2^256/2^128` of them); the second answer is then bad for at most
`2^128` values; both give per-query error at most `2^-128`, with no property of BLAKE2s used.
**Within the ROM, every instantiation known to the prover can be recognised by a certified
verifier.** A public beacon sampled after the entry is frozen helps only against precomputed
proofs (it is already used for fresh chain starts), not against a `V` that recognises the key it
is run with. A secret-keyed oracle is impossible **under v3's node clause**, because that clause
runs the children under concrete BLAKE2s and the recursion circuit therefore evaluates the
oracle. Barbara–Chiesa–Guan (2024/728) is the formal version for that setting: no succinct
argument in the ROM can verify computations that themselves query the oracle, so the recursion
must be non-black-box (BLAKE2s in the circuit) and the instantiation is in the honest data path.
The relativized exploration (§13) removes the premise by changing the node clause: children are
judged on the game's log, nobody arithmetises the oracle, and a secret harness oracle becomes
possible, at the costs §13 records. The keyed-oracle route is dead for v3's relation, not in
general.

### 1.5 The liveness mirror (V3-S2R-H-M4; O25-M6)

Under perfect completeness over every `H`, "the honest proof verifies under BLAKE2s" was a
theorem. Under `CompleteWithError` over a random `H` it is not: a `V` that rejects every honest
proof exactly when the oracle is BLAKE2s is certified (a **paper** observation, V3-S2R-H-M4, the
backdoor's construction with accept and reject swapped; no control at `6202402` builds it). It is
a griefing attack (sabotage of an
entry sharing a library), not a free win, and the harness's concrete checks under BLAKE2s (root,
samples, smoke, liveness) are its only cover. Every mechanism below was also judged against it.

## 2. Why a rule plus review is weak: the disguises (ADV-M5, 2026-10-19)

The design's interim defence was a rule ("`V`'s local computation must not evaluate the oracle's
instantiation", §6.7 of the 2026-10-19 design) and review of `V` at intake. Every variant of the
backdoor is one attack in a disguise: `V` holds a value correlated with the deployment function
that did not reach it through a query, and compares it with something that did. The ROM charges
the comparison at `2^-256` per query; deployment satisfies it always.

1. **Any query, not the empty one.** A fresh, random-looking query per submission.
2. **Recomputed Fiat–Shamir challenges.** `V` recomputes a challenge locally and checks that the
   oracle agrees. It reads as ordinary optimisation code, and v2 was exposed exactly this way.
3. **A literal trigger evades the closure test (kernel-checked).** The S1 review had proposed a
   gate that rejects a `V` whose constant closure contains `blake2sOracle`, `Submission.Vb` or
   `tagRO`, and flags `Blake2s.compress`. The probe `LiteralTrigger.lean` (archived as
   `evidence/probes/LiteralTrigger.lean` with its log; checked against `15e4ae5`) replaces `trigger := blake2sOracle q0` by a 32-byte literal computed offline
   (`hashlib.blake2s(b'R')`): `lit_eq : trigger = lit` by `decide +kernel`, `Vlit_eq : Vlit =
   Controls.Backdoor.V`, and `backdoor_lit : Certificate Slit ∧ ∀ c, Slit.Vb c (magic c) = true`,
   standard axioms. The closure scan:

   | `V` | `blake2sOracle` | `tagRO` | `Submission.Vb` | `blake2s256` | `Blake2s.compress` |
   |---|---|---|---|---|---|
   | `Vlit` (backdoor) | no | no | no | yes | yes |
   | `WitnessSending.V` (honest) | no | no | no | yes | yes |

   The remaining footprint does not separate the backdoor from the honest baseline: both reach
   `blake2s256` through `Rel`'s chain check. The only visible trace is "an oracle answer is
   compared with a 32-byte constant", and an honest preprocessing verifier does the same with its
   verification-key root (ADV-M6).
4. **A trace-check trigger (paper).** `V` legitimately contains the constraint evaluator of its
   own circuit, including the in-circuit `BLAKE2s(tagRO ‖ ·)` gadget it uses for Merkle hashing.
   Add a "debug mode" branch that checks a proof-supplied concrete trace of that gadget whose
   output equals the oracle's answer to `q = c`. That branch recognises the instantiation while
   `V` evaluates no hash; it only checks constraints. The bad set is one answer per query; the
   canaries pass because the magic proof is bound to `c`.
5. **No BLAKE2s in the source at all.** `V` embeds a RISC-V image of BLAKE2s and runs it through
   the contract's own machine (at S1 the vendored Rv64 was in the trusted closure), or calls a
   compression already in the import closure. A grep finds nothing.
6. **Partial recognition.** Accept when the first 128 bits of an answer match a local value: the
   ROM charges `2^-128`, exactly the cap.
7. **Spread recognition.** A few matching bits from each of many answers; no single comparison
   recognises anything. Under the boolean form the charges are summed within the cap; under the
   potential they are priced exactly like a spread challenge (V3-KS), so the amendment does not
   catch it either.
8. **The rule is over-broad.** It bans three things the design wants or tolerates: a
   concatenation node, which verifies child SNARKs locally and so evaluates `BLAKE2s(tagRO ‖ ·)`
   inside `V`; a hard-coded verification key; a "consistency fast path" that skips
   re-verification when the oracle agrees with a locally computed transcript, which is a natural
   optimisation and is exactly the backdoor. The honest entry `spartan-chain` illustrates it: its
   node branch evaluates `blake2sOracle` on the children to decide `Rel` through `Vb`, compares
   no oracle answer, was checked by its final review to contain no CGH-style recognition, and
   would be flagged by any syntactic rule.
9. **The rulebook did not state the rule.** `AGENTS.md` at the pin had no hit for "O-25",
   "recogni" or "magic", while the S1 review called intake review "the binding defence".

What the ROM theorem *does* catch is everything an adversary does **through the oracle**: a
prover that predicts an answer and writes it into the proof is caught, because the ROM adversary
predicts by querying first, the query lands in the log, and `final` demands a witness. The
asymmetry only ever comes from `V`'s private value.

ADV1's recommendations stood until the end as the review-only option: state the rule
semantically ("no branch of `V` may accept because an oracle answer agrees with a value that `V`
did not obtain from the oracle or from the proof"); require `NOTES.md` to list every place where
`V` compares an oracle answer with anything other than another answer or a proof-supplied value
the oracle subsequently hashes; make intake review mandatory with a public challenge period
before a record stands; adopt the indexer (ADV-M6), which removes the one legitimate reason for a
hard-coded 32-byte constant compared with an answer.

## 3. What "recognition" is, and the threat model (F2 §1.3, §2)

**The threat model.** The adversary submits an entire `Submission` (`V`, `P`, `E`, `ext`, `ε`,
`δ`, `qV`, `fuel`). It wins board T if the harness prints `HARNESS: ACCEPT` and its deployed `Vb`
accepts a proof it produced without the knowledge the relation demands, while its certificate is
a genuine kernel-checked `Certificate S` with the three standard axioms, no `sorry`, no
`native_decide`, no code-changing attributes, imports from the allowlist only. The adversary knows
BLAKE2s completely and may hard-code any function of it; may structure queries and split
recognition across many answers and bits; controls `μ` freely (it is the submitter's own
witness); after the completeness change may use `δ`-slack to make honest proofs fail under one
oracle; and will disguise the comparison as ordinary verifier arithmetic. The defender controls
the Lean **type** `V` must inhabit (gate-checked), a small trusted wrapper, the rulebook text, the
review process, and the harness's concrete smoke check on BLAKE2s. The defender cannot see inside
the quantifier `∀ H` with any Lean theorem.

**A recognition site.** A position of `V` where acceptance can depend on the event
`x = f(a₁, …, a_k)`, the `aᵢ` oracle answers, with `x` or `f` encoding information about the
deployed instantiation that `V` did not obtain through queries. In the ROM the event has measure
about `2^-(bits compared)`, charged to `μ`; in deployment it is forced true.

**Two consequences that structure the whole design space.**

- **(R1)** If the only operation `V` has on answers is equality between answers (and against
  proof or statement values that are themselves of the answer type), there is no recognition
  site: any constant `V` could compare against would have to be of that type, which `V` cannot
  name. This is sound for commitment and Merkle verifiers (roots compared with roots), and it is
  the half of the parametric proposal that the probes confirmed (O25-m1).
- **(R2)** The moment `V` can compute any function `answer → observable` whose output `V` can
  also produce *independently of the oracle*, a recognition site reopens. Fiat–Shamir needs
  exactly this: a challenge is a function of an answer, and `V` must use it in arithmetic. If `V`
  can see `g` bits of challenge, it can compare them with `g` bits of a locally recomputed
  BLAKE2s and recognise at error `2^-g` (ADV-M5.4). Grinding is the same shape: "the answer has
  `g` leading zero bits" is a comparison of answer bits with a constant.

So the design problem is not "forbid all answer-dependence" (that kills every SNARK); it is "give
`V` exactly the answer-dependence an honest Fiat–Shamir verifier needs, in a form whose outputs
`V` cannot reproduce oracle-independently *and compare*". Rounds 1 and 2 are the search for such
a form. The conclusion (§6.1) is that for submission-authored code there is none.

## 4. Round 1: Candidate E, a parametric `V` with a restricted challenge interface, and the review that broke it

### 4.1 The proposal (issue #4 §2; F2 §3, §4, §9)

Make the verifier polymorphic in the type of digests, with decidable equality as its only
operation, and hand it everything else it needs on digests as contract-owned, opaquely-valued
operations:

```lean
-- contract-side, trusted (about 30–45 lines)
inductive Tape (D : Type) …                      -- the proof grammar: byte segments ⊕ digest slots
structure DigestOps (D : Type) where            -- D-valued relation hashes, filled with BLAKE2s at D := Digest
  chainStep : D → D ; leafStmt : D → ℕ → D ; nodeStmt : D → D → D
structure ChallengeOps (D F : Type) where       -- the Fiat–Shamir interface (the hard part)
  squeezeF : D → F                              -- a field challenge from a squeeze answer (wrapper: chE)
  idx      : D → ℕ → ℕ → ℕ                      -- a column index from an answer (wrapper: idxOf)
-- the submission
V : ∀ (D F : Type) [DecidableEq D] [CommRing F] [DecidableEq F],
      DigestOps D → ChallengeOps D F → D → Tape D → OProg D Bool
```

Queries are structured, `List (ByteArray ⊕ D)`, serialised by the wrapper (tagged,
length-prefixed, injective: the kernel lemmas `serialise_injective`, `serialise_inl_ne_inr`,
`parse_serialise` were to be trusted controls, because an ambiguous serialiser gives `V` a
byte-equality test on `D` through two queries). The wrapper instantiates `D := Digest`,
`F := EF = GF(2^192)`, parses the proof, runs `V` under `blake2sOracle`, rejects above
`proofCap`. The gate checks the type literally, including that the instance binders are exactly
those three and nothing else (no `Repr`, `Hashable`, `OfNat F _` beyond `0/1`, `Coe _ F`,
`Fintype F`, `ToString`, `F → ByteArray`), and that `Vb` is computable.

**The argument.** A term polymorphic in `D` with only `DecidableEq D` can depend on the
`D`-values it is handed only through their equality pattern (parametricity, a meta-theorem about
Lean terms, not a theorem inside Lean; the three axioms are opaque constants, but
`Classical.choice` yields only an abstract `D`, and a non-computational branch that affects the
result makes `Vb` noncomputable, which the gate rejects). The backdoor needs `decide (a = trigger)`
with `trigger : Digest` a `V`-computed constant; at abstract `D` that constant has type `Digest`,
not `D`, so the comparison does not type-check. For the challenge half, `CommRing F` was meant to
be rich enough for sumcheck identity checks (`evalPoly coeffs (squeezeF a) = …`) and poor enough
that the only `F`-values `V` can build are `0`, `1`, sums and products of those and of `squeezeF`
outputs: polynomials evaluated at challenge points, which collide with a uniform `EF` challenge at
rate `deg/2^192`. Grinding would go through a contract-owned `leadZeros : D → ℕ` compared with a
proof-supplied threshold. The memo's own best attack on itself was recognition through
`evalPoly` with proof-supplied coefficients interpolating a recognition function (F2 §14.1), to be
mitigated by a per-step degree cap; it rated the residual as the generic FS-uninstantiability
every deployed SNARK carries and recommended E together with the rule, review and a public
challenge period.

### 4.2 The review (`F2-o25-review.md`; probes `rf-core-sc/scratch/o25/P1_interface.lean`, `P2_hatches.lean`, Lean v4.34.1, each under `timeout 900 systemd-run --user --scope -p MemoryMax=8G lake env lean`)

**Verdict.** Candidate E as written does **not** close the known CGH mechanism. Its typing closes
the mechanism for the `D` (digest) half only. The `F` (challenge) half and the `ℕ` side channels
give `V` everything the direct backdoor needs. None of the breaks is a parametricity failure;
they are **interface** failures: the interface hands `V` operations whose outputs are
byte-faithful or algebraically complete, and parametricity in `F` buys nothing once `F` is
instantiated at a single known finite field.

- **O25-M1. `idx : D → ℕ → ℕ → ℕ` is a full byte projection; the memo's `2^-ℓ` bound is wrong.**
  The wrapper fills `idx` with the honest entry's `idxOf ℓ a i := natLE a / 2^(i·ℓ) % 2^ℓ`; the
  width `ℓ` is `V`'s own argument. Kernel-checked: `idxOf_full (a : Digest) : idxOf 256 a 0 = natLE a`
  (axioms `propext`, `Classical.choice`, `Quot.sound`; the only `#print axioms` in the probe). So
  `cmpNat ops a loc := decide (ops.idx a 256 0 = loc)` type-checks, parametric in `D` and `F`, with
  `loc := natLE (blake2sOracle q0)` a literal (`cmpNat` is an elaborated **definition**, not a
  theorem); the `KState` is Backdoor's, on paper; accepted. Even at the honest width, `⌈256/ℓ⌉`
  calls on one answer return every bit (`idxOf_all_bits`, **kernel**), so the "spread over
  `t ≈ 190` indices, priced by the potential" argument collapses: one answer, charged once.
- **O25-M2. `CommRing F` plus `DecidableEq F` names every element of `EF`, up to a Galois
  ambiguity of at most 192.** Any prover-supplied `F`-value `β` (a sumcheck message, or
  `squeezeF slot`) generates the field: for a `1 − 2^-96` fraction of elements `{1, β, …, β^191}`
  is an `F₂`-basis (**paper**), so every target `τ`, including `chE(localBlake2s q)`, is `Σ bᵢ βⁱ`
  with bits `V` computes from BLAKE2s (`encodeF`/`cmpF` are type-checked **definitions**, degree 0
  in the challenge, `evalPoly` not used). Or pin `β` against a target by its minimal polynomial
  over `F₂`, coefficients in `{0, 1}` (`pinned`, a definition exercised by
  `#eval pinned (F := ZMod 7) 2 = true`: compiled evaluation, not a kernel proof), degree ≤ 2,
  recognition at rate `≤ 192/2^192` (**paper**). A degree cap does nothing. Root cause: a finite
  field is generated by one element and `CommRing` supplies the generation, `DecidableEq` the
  recogniser.
- **O25-M3. The honest entry needs `ofBytes : bytes → F`, which is the backdoor.** The honest
  verifier decodes **proof** bytes into `F` throughout its non-oracle path (`readEF`, `readF`;
  `EF.ofBytes` is a bijection `Vector UInt8 24 ≃ EF`). Expose it for proof bytes and `V` applies it
  to locally computed BLAKE2s bytes. The alternative, moving all proof-field decoding into the
  trusted wrapper as opaque `F`-slots, makes the wrapper parse the whole Spartan/Ligero proof:
  protocol-specific trusted code, not a 30-line generic serialiser.
- **O25-M4. Grinding (`leadZeros : D → ℕ`) is redundant for the attacker or a channel.** It
  exposes an `ℕ` value (and M1 already gives the full projection); with the threshold from the
  proof, a magic proof supplies `g := 0`; with a contract constant, the honest prover
  rejection-samples in `P` and `V` needs no statistic at all. Fix: a wrapper-enforced
  precondition, no submission code sees it.
- **O25-M5. `evalPoly` with proof coefficients is Turing-rich; the degree cap separates
  nothing.** Pinning already works at degree 2, and a degree-1 `p(x) = x − τ` with `τ` from the
  proof recognises a single target challenge, which is exactly what an honest linear sumcheck step
  looks like.
- **O25-M6. The liveness mirror is not covered on the instances that matter.** The smoke check
  covers only the acceptance the harness can reproduce with the native prover; a `V` that rejects
  on an un-emitted sub-instance evades it; and the memo did not say who picks the ranked
  instances and when. Fix: sample the ranked set after freeze from a beacon; run the smoke on
  every scored instance on the native prover's emitted log.
- **O25-m1.** The `D`-half is sound: `P2_hatches.lean` confirms every Lean-4 escape hatch fails
  as predicted (`Classical.dec (D = Digest)` and `Classical.choice` rejected by the code generator;
  `toString`, `hash`, `default` fail instance synthesis at abstract `D`; `cast rfl : D → Digest` is a
  type mismatch; `Nat.cast : ℕ → F` compiles but gives only `0, 1` in characteristic 2).
- **O25-m2.** Missing citation: Brzuska–Hubáček–Kalsta (PKC 2026) gives simpler counterexamples to
  *extended* Fiat–Shamir, so Arnon–Yogev's XFS, which the memo promoted as the lead for a stronger
  challenge channel, is not a clean escape.
- **O25-m3.** `DecidableEq F` cannot tell an interface-produced `F` from a `V`-constructed one, so
  the rule's `F`-clause is not mechanically checkable; it is review-only, while the memo treated it
  as typed.
- **O25-m4.** The serialiser lemmas guard the `D` byte/slot boundary only; M1–M3 operate after a
  correct parse.

**The repair the review converged on.** `V` must not compute on field or numeric representations
of answers or proof data at all: positions as opaque tokens with widths as contract constants; no
`[CommRing F]` in `V`'s signature, every identity check (sumcheck step, PCS opening, proximity) a
contract-owned operation `V` only invokes; proof field data as opaque slots parsed by the
wrapper; grinding a wrapper precondition; post-freeze instance sampling. "This is not Candidate E
plus a degree cap. It is a contract-owned protocol template: the trusted base contains the
Spartan/Ligero verifier skeleton, and an entry supplies only the opaque data plumbing and the
soundness certificate. That is a coherent and defensible design, but it is a different
competition from 'submit your own `V`'." The honest-entry cost of E was also re-estimated: the
Merkle half ports; the transcript's fiber-count lemmas become wrapper-asserted hypotheses; the
proof-field decode (58 use sites across four modules) and the field arithmetic in `V` are a
redesign of the verifier's core, not a refactor.

## 5. The other candidates of round 1, and why each is dead (F2 §6–§8, R2.3)

- **B. An unknowable deployment oracle (salt, beacon, key).** §1.4: within the ROM every
  instantiation known to the prover can be recognised by a certified verifier, and the prover
  must know it because the recursion circuit evaluates it. B becomes useful only *under*
  parametricity (a salt read as an opaque `D` gives `V` nothing), where it is defence in depth,
  not a fix. The one externally keyed idea that is not dead is the VRF-challenge service of
  Ghosal et al. (2026/2114), which is a standard-model move with an external trusted service that
  the recursion circuit would need; out of scope for a ROM contract. **All of this assumes v3's
  node clause.** The relativized exploration (§13) changes the clause so that no circuit evaluates
  the oracle, and then a secret harness oracle is exactly its proposal (D4); B is dead for v3's
  relation, not for a relativized one.
- **C.1. Knowledge soundness relative to a family of oracles that includes BLAKE2s-like
  functions.** "Efficiently computable" is not a property the potential form can express without
  a complexity model, which the design avoided; a specific finite family including BLAKE2s makes
  the theorem "`V` is sound when `H` = BLAKE2s", which is exactly the heuristic no one can prove;
  the honest entry would then also have to be proved sound at concrete BLAKE2s. C.1 relocates the
  gap.
- **C.2. Digest obfuscation by the wrapper** (run `V` against `H ∘ π` for a fresh secret
  permutation `π` of digests). A keyed oracle in disguise; the recursion circuit must compute the
  unscrambled BLAKE2s, so `π` is undone somewhere the prover can see. It is the semantic shadow of
  the typed approach (why opaque `D` is safe: the wrapper may represent `D` any way it likes), not
  an independent mechanism.
- **D. Standard-model assumptions.** Collision resistance for the Merkle half needs a complexity
  model to state "efficient" and does not touch the challenge channel. Correlation
  intractability for Fiat–Shamir (the CGH98 positive notion; CCHLRR19 and the rest of §9.3) is
  LWE-based and not a property of BLAKE2s; for *arguments* (not proofs) FS can be unsound for
  every hash; encoding CI and LWE in the trusted base is the large, churny addition the design
  rejected (Q6, "ROM-only assumptions"); it changes the hash and breaks the BLAKE2s-only
  recursion. A bespoke "BLAKE2s is a good FS hash for this relation" hypothesis is the honest
  content of what every deployed SNARK assumes; stated as a contract hypothesis rather than a
  disclaimer it would make `ACCEPT` conditional on an unprovable claim.
- **"Run `V` twice, under BLAKE2s and under a secret keyed oracle, and compare verdicts"** (killed
  in round 2). The recursion needs the deployed oracle in the circuit, so the keyed run cannot
  verify nodes; and a backdoor can be made dormant on the smoke instances (O25-M6 again).

**The lesson of round 1, as a principle (F2 R2.0).** Round 1 tried to find an *interface* rich
enough for Fiat–Shamir and poor enough to forbid recognition. There is no such interface *for
submission-authored code*: FS needs the challenge as a field value, and the moment any
submission-authored check sees a challenge as a value, the submission can compare it with
anything it can compute, and over a single known finite field it can compute everything.

## 6. Round 2: the post-hoc attack, Candidate T, and the review that narrowed it

### 6.1 The post-hoc challenge verification attack (the orchestrator, round 2; F2 R2.1)

Let the protocol squeeze a challenge `c₁ = chE(H(absorb(prefix₁)))`. Afterwards the prover sends,
as later messages, (i) the bits of `prefix₁`, (ii) the wires of a BLAKE2s computation of
`H(absorb(prefix₁))`, and (iii) a field element `β` pinned by its minimal polynomial over `F₂`.
`V` checks, with low-degree identities only: the wires are a correct BLAKE2s run; the input bits
equal the earlier messages; and `c₁ = Σᵢ outbitᵢ · βⁱ`. Every check is "normal" verifier
arithmetic. **There is no fixed point**: the data arrives after `c₁`, so the prover does not need
`c₁` to be a function of something that depends on `c₁`. In the ROM the final identity holds with
probability `2^-192` (the real `c₁` is a uniform element independent of the wires); in deployment
it holds always. The `KState` is Backdoor's with the bad event "the squeeze answer's `chE` equals
the BLAKE2s-wire output".

**Why it defeats every interface fix.** It uses only a challenge appearing as a value in a check,
together with later prover data; it needs no `idx`, no `ofBytes`, no equality against a constant
(the comparison is a polynomial identity between the challenge and a prover-supplied linear
form). So it survives contract-owned transcripts that absorb every message, PIOP DSLs,
sumcheck-style identity libraries, normal-form arithmetic circuits, degree caps and opaque
position tokens. **Any framework in which a submission-authored check can mention an earlier
challenge as a value is open.**

**Why honest recursion is not this attack.** A node circuit also verifies BLAKE2s wires of a
transcript and checks `c₁' = Σ outbitᵢ βⁱ`, but on the **child's** transcript, entirely inside the
node's *witness*, which is committed before any of the node's own challenges exist. The node's
own challenges never appear as values in any submission-authored check; they are consumed only
by the fixed sumcheck/PCS protocol over the committed witness.

**The invariant it forces (INV, as first stated).** Let `Chal(π)` be the values derived from the
outer proof's own oracle answers (challenges, positions, transcript states). Every function the
submission authors is applied only to inputs independent of `Chal(π)`; every value in `Chal(π)` is
consumed only by contract-owned (or fixed-template) code whose composition the submission cannot
alter. This is a **data-flow** property, enforced by the shape of the composition: the contract
builds `Vb` from the submission's data, and first-order data cannot be applied to anything.

### 6.2 Candidate T (F2 R2.2): the submission becomes data for a fixed verifier template

```lean
structure UniformR1CS where                        -- T-1: first-order data, no function anywhere
  s m k : ℕ ; A B C : List (ℕ × ℕ × F) ; chain : List (ℕ × ℕ) ; pubSlots : List ℕ ; wf : Bool
structure Params where                             -- T-2: a contract menu
  pcs : PCSChoice ; rate : ℕ ; queries : ℕ ; grind : ℕ
def Params.ok (p : Params) (cs : UniformR1CS) : Bool   -- a contract table: (pcs, rate, queries, size) ⇒ ε ≤ errorCap
structure TSubmission where                        -- T-3
  cs : UniformR1CS ; params : Params
  pub : Digest → ByteArray → Option (List F)       -- the public input from the statement and a
                                                   -- designated pre-challenge segment of the proof
  P : Digest → Wit → OProg Proof ; E : … ; ext : XProg ; ε δ qV fuel
def TSubmission.V (S) (c) (π) : OProg Bool :=      -- T-4: the composition, the whole of O-25's closure
  Template.verify S.params S.cs (S.pub c (preSeg π)) c π   -- organiser library code
def TSubmission.Vb (S) (c) (π) : Bool :=
  S.params.ok S.cs && S.cs.wf && π.size ≤ proofCap && (S.V c π).run blake2sOracle
```

`Template.verify` seeds its transcript with `H(0x10 ‖ c ‖ csDigest S.cs ‖ paramsDigest ‖ x)`, the
statement, **the constraint system**, the parameters and the public input (Fenzi26's
statement-binding rule, §9), then runs the fixed sumchecks, the fixed PCS opening and the fixed
Merkle checks. The certificate (T-5) is discharged by one library theorem `Template.ks`, generic
in `cs`, `params` and `pub`, composed with the submission's standard-model theorem
`cs_implies_rel` (circuit correctness) and `Computes`. The submission proves nothing about the
random oracle; the ROM theorem is the library's, once. Recursion (R2.6): the node constraint
system encodes "the template accepts the child under BLAKE2s" as gadgets over the child's
transcript in the node's witness, and the organiser can ship a verified gadget of its own
template. Round 2 recommended T for ranked entries, tiered with an unranked free-form research
track, and estimated 60–90 contract lines.

### 6.3 The review of T (`F2-o25-review-r2.md`; probe `rf-core-sc/scratch/o25t/T1_pub_sees.lean` against `05fde28`, every theorem with `[propext, Quot.sound]` only)

**What survives.** T is the first proposal that actually removes the CGH98/`Backdoor.lean`
mechanism from submission-authored code, for a structural reason: every check that reads an
oracle answer is organiser code, and every submission-supplied input to such a check is fixed
before the first oracle answer because the seed binds it. A Backdoor-, ADV-M5-, O25-M1…M5- or
post-hoc-style comparison has nowhere to live in a submission. No acceptance backdoor was found
through any `TSubmission` field.

**What is broken.**

- **O25T-M1. INV is false as stated (kernel).** `pub` is authored after `cs` and `params` are
  fixed, so it may hard-code `csDigest cs` and `paramsDigest params`, choose its output `x`, and
  evaluate BLAKE2s locally: `pubTau_eq_challenge : pubTau cs p c (preSeg π) = tmplTau blake2sOracle
  cs p c honestX π := rfl`. In deployment `pub`'s local value **is** the first challenge the
  template consumes; `evil_Vb` is a legal `TSubmission` whose `Vb` rejects when byte 0 of that
  challenge is zero. The same holds for a node witness computing the outer seed answer from its
  own public input. The harm is limited to liveness (§6.3.2 of the review: `x` cannot contain
  `τ(x)`, a BLAKE2s fixed point, and `pub` is a public function the prover could have evaluated
  itself, so acceptance is unaffected), but the stated invariant is the wrong thing to check.
  Repaired as **INV′**: *every check in `Vb` whose operands include an oracle answer, or a value
  computed from one, is organiser code; every submission-authored value that reaches such a check
  (`cs` data, `params`, `x`) is fixed before the seed query and is bound by it; no
  submission-authored function is evaluated on anything the prover writes after the seed.*
  Concretely: the seed query is made by the contract's composition, not the library; `x` is a
  contract-fixed injective map of `(c, header bytes)`, not a submission function; statement checks
  such as `c = leafStmt h n` move into `cs`.
- **O25T-M2. The menu has no admissibility rule; lookups, AIR challenges or multi-phase witnesses
  reopen the post-hoc attack as data (kernel).** `postHoc : List Gate := [⟨.chal, .const 1, .col 0⟩]`
  with `postHoc_iff : holds postHoc w α ↔ α = w 0`: in a constraint language with a challenge term
  and later-phase columns, the last line of the post-hoc attack is data with no function field.
  A library KS theorem generic over such a language either does not exist or certifies the
  backdoor. The rules every menu datatype must satisfy:
  - **(A1)** data-defined functions are evaluated only at verifier challenges and at evaluations
    of oracles committed *before* those challenges and bound by the PCS, with a degree bound fixed
    by the template;
  - **(A2)** no data-defined function or constraint mentions a challenge as a coefficient or
    variable, or constrains a column committed after any challenge (the witness is committed in a
    single phase);
  - **(A3)** every multi-round sub-protocol (lookup, permutation, grand product, GKR, memory
    checking) is a template-authored gadget whose challenge-using constraints are fixed code, and
    the data only names which pre-challenge columns enter it;
  - **(A4)** no datatype is an interpreter: no loop, branch or table whose input is a
    challenge-derived value.

  `UniformR1CS` with single-phase Spartan satisfies A1–A4; halo2-style challenge APIs and AIRs
  with `eval` access to challenges do not. INV′ is a property of the *template's interpretation*
  of the data, not of the data's Lean type.
- **O25T-M3. T-1/T-3 cannot express the honest entry.** `spartan-chain`'s matrices depend on `n`
  and `κ = ⌈log₂ n⌉` (the output check sits at block `n − 1`; non-block rows wire the public
  input), its `Evals` are submission-authored closed forms, and T has no node branch. Padding to
  `k = 20` costs 64× the prover work and a Ligero proof above `proofCap`, so completeness fails;
  one submission per `n` is impossible because the relation is fixed. Fix: a statement-indexed
  family read from fixed slots of `x`, a contract dispatch for nodes, a generic evaluator with an
  `O(nnz(block) + k)` closed form and its correctness theorem, a new generic *knowledge*
  extractor (m4: spartan-chain's proof is soundness with a public witness, not extraction).
- **O25T-M4. The ranked board is empty at launch, and self-verifying recursion with one `cs` is
  an unsolved design problem.** The launch template's leaf exceeds `proofCap` at `n = 2^14`
  (measured), so ranked T needs a WHIR-class template that does not exist in Lean plus full
  recursion; a node circuit must evaluate the MLE of **its own** matrices at the child's
  challenge point, which with a generic sparse evaluator costs at least `nnz(cs)`, so
  `|cs| ≥ |cs| + |rest|`; self-verification closes only with a uniform VM-like block and a
  template-owned memory-checking gadget (multi-phase, so A3 applies) or with preprocessing, which
  the contract forbids (#8 (3)). Under T-only ranking no entrant can be ranked until the organiser
  has built the entire honest recursive SNARK. The dependency chain, without durations: the
  generic evaluator and its theorem; `Template.ks`; a decoder `XProg`; a WHIR-class PCS with Lean
  KS in the unique-decoding regime; a self-verifying node design and gadget with
  circuit-correctness theorems; the template spec, `impl = spec`, and its review. Items 4 and 5
  are each the size of the current honest entry or larger (16,766 lines for a leaf-only
  Spartan+Ligero).
- **O25T-M5. The template-proposal process re-imports the unwinnable review at the template
  level.** A template *is* a verifier on the oracle path; a competitor-proposed template with a
  `LiteralTrigger`-style fast path faces exactly the review the memo rejects for entries, with a
  larger payoff. Fix: each template is a short reference specification plus a kernel theorem
  `impl = spec`, so only the spec is reviewed; an enumerable checklist ((a) every local BLAKE2s
  call site flows only into a query input, a comparison with the statement, or the child
  verification `Rel` defines; (b) every comparison with an oracle-derived operand is one of the
  protocol's fixed identities; (c) no data-dependent control flow selects checks; (d) no
  `implemented_by`/`extern`/`csimp` in the closure; (e) the decision is a conjunction with no
  `||` and no early `true`); a proposer embargo.
- **O25T-M6. T reverses three of Q6's decisions and is narrower than the v2 the user rejected.**
  "No organiser compiler"; "the verifier's circuit and execution trace are the agent's internal
  matter"; "field-agnostic". Under v2 the agent still designed the IOP; under T neither the IOP
  nor the PCS. And v2's shape does not close O-25 either (MG2 below). It must go to the user as
  a reversal, with the options: T as specified, the wider middle ground, or review-only ranking.
- Minors: `wf : Bool` as a structure field is decided by the submitter (m1, probe); T-3 predates
  the S2R contract (m2); hidden hypotheses in `Template.ks` cannot cause unsoundness because the
  entry's own `KS` is still kernel-checked (m3); `csDigest` binding excludes Fenzi's class given
  that the digest covers the expanded instance, blocks KRS's mechanism only heuristically through
  single-phase commitment, and is ROM-invisible (m5); the tier must be type-based, not policy
  (m6); the contract grows by about 100–130 lines to 390–420 of 500, plus 0.5–0.9k template lines
  trusted for meaning and non-recognition (m7); post-freeze sampling is lower-stakes under T
  (m8); grinding must be specified one way (m9).

### 6.4 The middle grounds, judged on one criterion

The post-hoc attack needs a check that the submission defines whose operands are an earlier
challenge and prover data written after it.

| Shape | What the agent chooses | Survives? | Why |
|---|---|---|---|
| **MG2: v2-style agent IOP + organiser BCS** | the IOP, its verifier's decision | **no** | the IOP verifier sees `c₁` and later messages and may check `c₁ = Σ outbitᵢ βⁱ` with BLAKE2s wires as later oracles: IOP-sound, BLAKE2s-unsound |
| **Repaired E, driver style** | the order and subset of contract checks | **no** | a driver that accepts on "all round checks pass" and omits the final opening is certified (bad event: the challenge equals the predicted one) and accepts magic proofs in deployment; each `checkStep`'s `Bool` is a one-bit observable of a challenge |
| **MG3: agent polynomial IOP with an algebraic decision over multi-round oracles** | constraints over oracles from several rounds, with challenges as coefficients | **no** | `postHoc_iff`: `α = w₀` over a phase-2 oracle is data |
| **MG1: admissible menu** | single-phase constraint data in any admissible format (uniform R1CS, CCS, AIR, Plonkish with template-bounded gate degree); a compiler (Spartan-like sumcheck, HyperPlonk-like zerocheck, STARK-AIR quotient); a PCS (Ligero, WHIR, Basefold, FRI); a field (`GF(2^64)`/`EF`, Goldilocks², BabyBear⁴), each a library implementation proved equal to its spec | **yes, under A1–A4** | all data-defined functions are evaluated at challenges and at PCS-bound evaluations of pre-challenge commitments; lookups, permutations and grand products are template gadgets; the composer is contract code over first-order data |
| **T as specified** | `UniformR1CS`, params | yes, with M1's fix | MG1 with one format, one compiler, one PCS, one field |

MG1 restores the arithmetisation format, the PCS (including WHIR, which ranked recursion needs
anyway), the field (Q6's "fields are a large part of the cost") and the compiler family. It still
excludes new IOPs or PCSs that are not yet templates, verifier-side optimisation, and
accumulation; new items enter by core PR under M5's spec-and-embargo process. The review
recommended MG1 to the user, with T's core, INV′, A1–A4, a type-based tier and the organiser
dependency chain recorded.

### 6.5 Strength, stated precisely (review §8)

For T **as specified on paper**: T was never implemented, and the review's one probe
(`T1_pub_sees.lean`) is what found its breaks. The claims below are the review's assessment of a
design sketch, not properties of any contract text.

- **Kernel, unchanged by T:** `KS (Rel S.Vb) S.V S.E ε qV`. It says nothing about the single
  deployed oracle.
- **Structural, definitional in the contract (given INV′'s fixes), if T were implemented as
  specified:** `Vb_S c π = Tmpl(D_S, x(c, hdr π), c, π)`
  under BLAKE2s, with `Tmpl` fixed organiser code and `D_S` first-order data fixed before the seed
  and absorbed into it; no submission-authored function runs on the verification path. Hence no
  check a submission writes compares a locally computed value with an oracle answer. **This needs
  no parametricity meta-theorem.** Round 1's `D`-half is no longer load-bearing.
- **Review, one per template, enumerable with a spec:** that `Tmpl` performs no such comparison,
  and that it interprets `D_S` only as A1–A4 allow.
- **Residual, irreducible:** the template's own Fiat–Shamir heuristic under BLAKE2s for every
  admissible `(cs, x)` (§10); the non-recognition review of each template (the CGH argument
  applied to the organiser); liveness through `pub` if kept; template evolution (one constructor
  with a challenge term reopens the one-line backdoor).

A clever adversary against T with M1–M5 fixed needs either a new FS attack on commit-all-wires
Spartan+Ligero (or WHIR) with the instance bound in the seed (the KRS mechanism then requires a
BLAKE2s fixed point `w ↦ root(w)`; Fenzi's is excluded by binding), delivered through
first-order data, or a subverted template review against a short spec. Against T as written in
the memo: no acceptance workaround was found; one liveness channel; and the large risk that a
future menu item violates A2.

## 7. The "fields as data" variant (suggested after round 2; **unreviewed**)

This was suggested by the orchestrating agent after the round-2 review, as a way to widen MG1's
field menu without one template per field. It has had no adversarial review, no probe and no
sizing, and it does not address the user's objection of §8.

**The idea.** Under T/MG1 the field appears as a type the template computes in (`F = EF` in the
datatype `A B C : List (ℕ × ℕ × F)`), so each field is a separate template with its own library
implementation and `impl = spec` theorem. Instead, let a submission give its field **as
first-order data with proofs**: a characteristic `p` and a defining polynomial `f` (for a prime
field, `p` alone; for a binary tower, the modulus), with kernel-checked irreducibility (CompPoly
already has a Rabin certificate for `BF64`) and a size bound guaranteeing the soundness table's
`|F| ≥ 2^192`-type conditions. The **encoding** of field elements as bytes is contract-owned and
canonical (little-endian coefficients of the residue class), so that the template parses proof
bytes into field elements with no submission code. The submission may supply **arithmetic**
(word-level multiply, inverse) as a program the template calls, but only together with a kernel
theorem that it is extensionally equal to the specification arithmetic of `GF(p)[x]/(f)`, so the
template's soundness proof is against the specification and the submission's code is a
performance twin, as the honest entry's `F`/`EF` are twins of CompPoly's `BF64`/`Ext3`
(`ringEquivBF64`, `ringEquivExt3`).

**Why it might be sound under INV′.** The field is fixed before the seed and bound into
`paramsDigest`; the arithmetic program is submission code, but it is never applied to a value by
a submission-authored *check*: the template applies it, and the extensional-equality theorem
makes the template's behaviour that of the specification arithmetic, which has no recognition
site. The post-hoc attack needs a submission-defined check over a challenge; a multiplication
routine proved equal to the spec defines no check.

**Where it is incomplete.** (i) **Ligero is field-generic** (the proximity lemma is for any
linear code over any field with `MinDist` and `|E| > d`), so a Ligero template takes the field as
a parameter at no cost; **folding PCSs are family-specific** (WHIR/FRI need a smooth
multiplicative subgroup or an additive-NTT basis with its own correlated-agreement theorem per
family), so "fields as data" widens the menu only for the PCS that cannot rank anything
(§6.3, M4). (ii) The extensional-equality theorem must be checked by the comparator for every
entry, which the honest entry showed costs nanoda about 70 s and 2.3 GB for CompPoly's closure
alone. (iii) It does nothing for the format, compiler and PCS dimensions of MG1, so the review
surface of M5 and the narrowing of M6 remain. (iv) Nobody has tried to write the backdoor for it;
the obvious attempt (an arithmetic twin that misbehaves on the one element the deployment
produces) is blocked by the extensional theorem, but a twin that is extensionally equal and
*slow* on one element is a `T_V` channel, and a twin whose equality theorem has a hidden
hypothesis is the "hidden `honest-shaped cs`" risk of O25T-m3 in another place. (v) Two points of
the proposal as it was made (the orchestrator, 2026-10-22) were dropped above and are its main
soundness hazard: the arithmetic must equal the specification **on the whole representation
type, including unreduced encodings** (a twin that agrees only on canonical representatives is a
recognition site through non-canonical bytes), and the **equality test and the challenge
derivation** must be contract-owned, never the submission's twin. (vi) Ring switching, which the
honest entry needs for packing, works only for binary fields, so the variant's field menu is not
as wide as it looks.

It is recorded here so that a next design does not rediscover it, and so that it is not mistaken
for a reviewed option.

## 8. The user's decisions on O-25

- **2026-10-19** (the S1 fix pass). `Controls/Backdoor.lean` is kept as a documented gap, the
  trust statement names it, and O-25 is opened as a **user decision** between the parametric-`V`
  contract stage before S2 and "keep the rule plus review for the first season and record the
  exposure in the records" (#4 §8).
- **2026-10-20.** O-25 **MUST** be closed, on its own track. (The same day: the extractor is a
  Lean program with a proved bound; completeness may have a small error. Both interact with
  O-25: the first removes the vendored RISC-V BLAKE2s from the trusted closure, one of ADV-M5's
  disguises; the second opens the liveness mirror, §1.5.)
- **2026-10-22.** The round-2 review's recommendation, MG1, was put to the user as a reversal of
  Q6 with three options (T as specified, MG1, or review-only ranking). The user rejected MG1, in
  their words:

  > this severely restricts the design space for autoresearch agents, while still adding a huge
  > gap for reviewing proposals, and requiring manual intervention

  The user answered about MG1 only. What follows is **the authors' inference**, not the user's
  words: T is strictly narrower than MG1, so the same objection covers it; and review-only ranking
  does not close O-25 (ADV-M5 shows review cannot separate the backdoor from honest code, §2),
  which the user required on 2026-10-20. On that reading v3 has no closure for O-25 within the F2
  track, and this is the first of the three walls that ended it (Design §15). The relativized
  exploration (§13) was not put to the user with these options.

**What the rejection says, read as requirements (the authors' reading, to be confirmed by the
user).** The three objections, taken up in §11: (1) the design space for agents must not be
narrowed, which the authors read as ruling out any fixed menu of proof systems however it is
extended; (2) there must be no large human review surface, which rules out a per-template
non-recognition review as the security mechanism (and, by ADV-M5, a per-entry one); (3) there
must be no manual intervention, which rules out proposal processes, embargoes and challenge
periods as the mechanism.

## 9. The literature, and what each result implies here

From the user's list (`cgh98_snark_followups.md`), read for its implications; the memo did not
fetch the papers and relied on the list's descriptions and abstracts where it says so.

### 9.1 The source

- **CGH98** (Canetti–Goldreich–Halevi, *The Random Oracle Methodology, Revisited*, ePrint
  1998/011). Two tools: diagonalisation, giving schemes secure with a random oracle and broken by
  every concrete hash; and correlation intractability, the notion a positive answer would need.
  O-25 is an instance of the first; the only known positive route is the second. **CGH TCC'04**
  (2003/150) extends the counterexample to length-restricted signatures: restricting the input
  domain is not a fix, which matches the finding that only restricting `V`'s *operations* bites.

### 9.2 Attacks on Fiat–Shamir with real hash functions

- **Goldwasser–Kalai (FOCS 2003).** A 3-message argument sound in the ROM whose FS version is
  unsound for every hash. Implication: *arguments*, not only pathological schemes, exist that no
  concrete hash instantiates soundly; a `V` encoding such an argument through the challenge
  channel cannot be excluded.
- **Bitansky–Dachman-Soled–Garg–Jain–Kalai–López-Alt–Wichs (TCC 2013, 2012/705)** and
  **Dachman-Soled–Jain–Kalai–López-Alt (2012/706).** FS soundness for some proofs, including
  Micali's CS proofs, cannot be proved by a black-box reduction to any falsifiable assumption.
  Implication: even a standard-model assumption would not give a black-box proof for the
  Micali/Kilian template this competition is; the residual is a non-falsifiable heuristic.
- **Ananth–Bhaskar–Goyal–Rao (TCC 2013, 2012/721).** Fischlin's online-extractable transform is
  also unsound for any hash with a known running-time bound. Implication: changing the transform
  to get online extraction does not escape.
- **Bartusek–Bronfman–Holmgren–Ma–Rothblum (TCC 2019, 2019/997).** The FS version of Kilian's
  argument, the template behind SNARKs and STARKs, can be unsound: a contrived collision-resistant
  hash breaks it for a broad class of PCPs, and an interactive PCP breaks it unconditionally.
  Implication: the construction family is *known* to be FS-uninstantiable in the worst case; the
  saving grace is that the attack needs a contrived hash or PCP, which is the heuristic every
  STARK relies on.
- **Khovratovich–Rothblum–Soukhanov (CRYPTO 2025, 2025/118).** The first attack on a natural,
  deployed protocol: GKR with KZG is FS-unsound under any concrete hash. Implication: the gap is
  not only for contrived schemes; a competitor could in principle submit a `V` in this family.
  Under T, the KRS mechanism is blocked only heuristically by single-phase commitment (a circuit
  computing its own challenges needs a fixed point of `w ↦ root(w)`), not by a proof.
- **Brzuska–Hubáček–Kalsta (PKC 2026).** Simpler counterexamples to FS and its *extended*
  variants. Implication: Arnon–Yogev's XFS is not a clean escape (O25-m2).
- **Fenzi (2026/1838).** Extends KRS25 to statements generated by running a program, covering
  variants of Spartan and Aurora, the honest entry's family; and proves a fix: derive the FS
  challenges from the generated statement rather than from the program. Implication: the residual
  applies to `spartan-chain`'s family specifically; and **statement binding of the transcript
  seed** (the honest entry already seeds with `0x10 ‖ s ‖ enc64 n ‖ h`, `c = leafStmt h n`; T binds
  `c ‖ csDigest ‖ paramsDigest ‖ x`) should be a hard rule in any design, because it excludes
  Fenzi's class by Fenzi's theorem, given that the digest covers the expanded instance. It is not
  a proof against unknown attacks. Dao et al. (2023/691, weak-FS implementation bugs) is the
  practical reminder that not hashing the statement is a real, separate vulnerability.

### 9.3 Defences and the limits of ROM arguments

- **Arnon–Yogev (CRYPTO 2025, 2025/329), XFS.** FS plus a proof of work, secure in a relativised
  ROM where the known diagonalisation attacks have analogues. Weakened as a lead by BHK26.
- **Barbara–Chiesa–Guan (2024/728).** No succinct argument in the ROM can verify computations
  that themselves query the oracle. Implication: the recursion is necessarily non-black-box
  (BLAKE2s in the circuit), composition across levels is a heuristic however the contract is
  written, and the keyed/beacon route (Candidate B) is closed in principle.
- **Chen–Chiesa–Gur–O'Connor–Spooner (EUROCRYPT 2023, 2023/587), PCD from arithmetised random
  oracles.** An oracle model with a non-black-box view, in which recursive proofs can be built.
  Implication: the principled way to make recursion sound is to change the oracle model, not to
  patch `V`; a larger trusted-base change than anything tried, and the literature's answer to the
  recursion heuristic rather than to the acceptance backdoor.
- **Ghosal–Kate–Mukherjee–Sarkar–Sinha (2026/2114).** FS challenges from an external VRF service
  whose key the prover never sees. Implication: the one "unknowable oracle" that works, because
  it is external and standard-model; incompatible with a self-contained BLAKE2s deployment whose
  circuit must evaluate the oracle.

### 9.4 Provably sound FS via correlation intractability

Kalai–Rothblum–Rothblum (2016/303), Canetti–Chen–Reyzin–Rothblum (2018/131), **Canetti–Chen–
Holmgren–Lombardi–Rothblum–Rothblum (STOC 2019, 2018/1004)**, Peikert–Shiehian (2019/158),
Holmgren–Lombardi–Rothblum (2021/286), Jawale–Kalai–Khurana–Zhang (2020/980), Choudhuri–Jain–Jin
(2021/808), Chen–Lombardi–Ma–Quach (2020/915), Guan–Yogev (2025/2328). Common implication: FS can
be made provably sound in the standard model via CI hashes, for **proofs** (not all arguments)
and specific delegation settings, under LWE-type assumptions, with constructions that are not
BLAKE2s. Chen–Lombardi–Ma–Quach is the sharp divider: it identifies settings where a
cryptographic hash is provably needed and settings where simple hashes suffice, so the challenge
channel's security is genuinely assumption-dependent. For this competition it is the expensive
standard-model endgame (a CI hash and LWE in the trusted base, abandoning BLAKE2s-only), not an
option under V3-5.

**Net verdict.** The list confirms, for this exact construction family, that "ROM-secure ⇒
BLAKE2s-secure" is false and unprovable, and that the residual is the generic FS-uninstantiability
of deployed SNARKs. It yields two actionable items for any design: mandate statement binding of
the transcript seed (Fenzi26, Dao), and treat XFS-style proof-of-work as unproven. It confirms B
is dead (Barbara–Chiesa–Guan, Ghosal) and that D is out of scope.

## 10. The impossibility statement, precisely, and what remains open

### 10.1 What no ROM-based rule can achieve

Let the certificate be any statement that quantifies over all oracle functions (or averages
uniformly over answers), as `KS` and `CompleteWithError` do, and let the deployment run the
verifier with one public function `H₀`. Then:

1. **No clause of the certificate can distinguish a verifier that is honest from one whose
   behaviour differs only on a set of oracle functions of measure at most `2^-256` per query.**
   The backdoor is such a verifier (`Backdoor.lean`, kernel-checked); its liveness mirror is the
   same construction on paper (V3-S2R-H-M4), not a control. This is not a weakness of the potential
   form or of the counting form; it is what
   "for every oracle function" means. Adding a clause "and sound at `H₀`" is the statement no one
   can prove for any useful `V`, because it is the BLAKE2s-Fiat–Shamir heuristic itself (C.1).
2. **For submission-authored code, no interface to the oracle's answers is both sufficient for
   Fiat–Shamir and insufficient for recognition.** FS needs a challenge as a field value in a
   check (R2); any such check, together with later prover data, recognises the deployment with
   no fixed point (the post-hoc attack); and over a single known field every element is nameable
   from one prover value (O25-M2). The parametric `D`-half is sound (O25-m1) and insufficient
   (ADV-M5.4).
3. **Among the candidates examined, the only invariant that removed the submission-authored
   mechanism is INV′: every check with an oracle-derived operand is organiser code, and every
   submission value reaching it is first-order data bound into the seed before the first
   answer.** Every weaker candidate examined (a driver choosing which contract checks to require;
   a PIOP DSL; opaque handles with a generic identity check; MG2; MG3) left the submission a lever
   on challenge-dependent values and was one attack from the status quo (review §4, R2.3, R2.9).
   This is not a theorem: §10.3 Q2 names a restricted composition language that was not examined,
   and §13's D4 removes the mechanism by a different route (the deployment, not the verifier's
   code) that this item's framing does not cover.
4. **Even under INV′ the residual is irreducible by any ROM theorem:** the template's own FS
   under `H₀` for every admissible instance (GK03, BBHMR19, KRS25, Fenzi26 are existence results
   over this family; none proves this template instantiable or uninstantiable), and the
   non-recognition of the template itself, which is the CGH argument applied to the organiser
   and is review. Removing the first would need correlation intractability of BLAKE2s for the
   template's bad-challenge relations (unproven, and by BDGJKLW13/DJKL13 unlikely to be provable
   by black-box reduction for every protocol on a menu).

So the precise statement is: **within a ROM contract whose deployed oracle is a public function
the verifier can evaluate, "the submitted verifier cannot recognise the deployment oracle" was
achieved by construction only when the submission authors no check that sees an oracle-derived
value; no weaker form was found among the candidates examined, and none is excluded by a
theorem; and "the deployed verifier is sound" is never a theorem.** If the deployed oracle is
*not* a public function the verifier can evaluate (§13: a secret harness oracle, which v3's node
clause forbids and a relativized clause permits), the first clause is a different problem: the
recognition event is no longer a `2^-256` point the verifier can hit, and the question becomes
what the harness service and the key lifecycle are trusted for.

### 10.2 What is not established

- That T's specific template (Spartan + Ligero, or a WHIR-class one) is uninstantiable: the
  literature gives existence results over the family, not a break of this template.
- That no *potential* exists for a 96-bit-comparison verifier at the 128-bit cap under
  `logCap = 2^96` (V3-S2-KS-m1): the boolean case is kernel-checked, the potential case is a
  paper argument. It is adjacent, not O-25.
- The parametricity meta-theorem for Lean 4 with the three axioms, for the research-track use of
  the `D`-half: probe-confirmed on every hatch tried, not proved.
- Whether any mechanism meets the three criteria of §11. Within the F2 track, none does. The
  relativized exploration's D4 (§13) keeps a submitter-written `V`, has no per-entry review and
  no menu, and claims closure by the deployment; whether it meets the criteria depends on how
  the user weighs a trusted harness service, records checkable only by the organiser until key
  release, and the exploration's own open items (a succinct node is a paper obligation, #7 and #8
  unchanged, #6 (b) untouched). That weighing was not put to the user before v3 stopped.

### 10.3 What remains open, as questions

1. Is there a certificate statement that is neither "for every oracle" nor "at `H₀`" and that a
   submitter can discharge for an honest SNARK but not for the backdoor? Every candidate in the
   F2 track (a family of oracles, an obfuscated digest space, a two-oracle game) either relocates
   the gap or reduces to parametricity (§5). The relativized exploration answers "no, change the
   deployment instead": the relation alone does not close it (kernel, §13), the secret oracle
   does (paper).
2. Is there a way to let a submitter author the *composition* of oracle-facing checks (the thing
   the user wants to keep open) while every check's operands stay organiser-computed and the
   composition cannot turn one-bit outcomes into recognition? R2.3's driver attack says a free
   composition is enough to recognise; whether a *restricted* composition language (for example,
   a conjunction with a mandatory final binding, no disjunction, no data-dependent selection of
   checks) is both expressive and safe was not examined.
3. Can the deployment point be checked mechanically rather than reviewed: an executable
   refutation (a magic proof for a statement the harness knows has no witness) found by the
   harness itself, not by the public? For the benchmark's own leaves the harness holds the
   starts, so "no witness" is decidable for it; what it cannot do is search the proof space.
4. Is there a model between the ROM and the standard model, cheap enough for a 500-line
   trusted base, in which the recognition event is not measure-zero (an arithmetised random
   oracle in the sense of CCGOS23 is the literature's candidate and was not sized)?

## 11. Criteria a satisfying solution must meet

From the user's objections of 2026-10-22, the kernel facts of §1–§6 and the literature of §9. A
proposal that fails any of these is not a solution to O-25 as the user has defined it.

1. **No narrowing of the design space.** A submitter may bring any proof system: a new IOP, a new
   PCS, a new transcript layout, a new field, a verifier-side optimisation. A fixed or extensible
   menu of templates is excluded, however it is grown. (The authors' reading of the objection,
   to be confirmed by the user: a rule may restrict *what the verifier is given*, the type of an
   answer or the shape of a proof, or *how the oracle is deployed*, but not *which proof system
   it may be*.)
2. **No large human review surface.** The mechanism must not be "someone reads the verifier":
   ADV-M5.1 shows a reviewer cannot separate the backdoor from honest code at the entry level,
   and O25T-M5 shows the same at the template level. A finite, enumerable, mechanical check is
   acceptable; a judgement about intent is not.
3. **No manual intervention.** The path from a pull request to a verdict is the harness: no
   proposal process, no embargo, no challenge period as the security mechanism (a challenge
   period may exist as a bounty, D-A/N4 of Design §17, but it is not what makes a record stand).
4. **It must survive the three kernel-checked attacks and the paper one.** The literal trigger
   (`backdoor_lit`), the full byte projection through any `ℕ`-valued interface (`idxOf_full`), the
   field-element naming from one prover value (`encodeF`/`cmpF`, `pinned`), the pre-seed
   computation of transcript values (`pubTau_eq_challenge`), and the post-hoc challenge
   verification attack. A proposal should come with the backdoor written for it and the line that
   stops it.
5. **It must keep the certificate a kernel theorem about the submitted objects** with the three
   axioms, and the trusted base within its budget (Design §16, C12). A meta-theorem about Lean
   terms (parametricity) may be used only where probes have closed every hatch and only for
   something that is not load-bearing for ranked records.
6. **It must state what it guarantees against which adversary**, distinguishing the three
   layers the record established: what is structural in the contract's definitions; what is a
   review of organiser code; what is the irreducible FS residual. "ROM-secure ⇒ BLAKE2s-secure"
   must not be claimed.
7. **It must cover the liveness mirror** at the deployment point for every scored instance, by a
   concrete check on the native prover's emitted log, with post-freeze instance sampling if the
   instance shape is ever secret.
8. **It must keep honest recursion expressible** under the same mechanism: a node verifying a
   child's transcript inside its witness is the honest shape of the post-hoc attack's data flow,
   and the mechanism must distinguish the child's challenges (in the witness, committed before the
   node's seed) from the node's own.
9. **It must mandate statement binding of every transcript seed** (Fenzi26), as the one proved
   positive result for this family.
10. **It must be built against a real entry before it is a rule.** Every one of the findings
    above was invisible in the design text and visible in the first kernel probe or harness run
    (Design §15.4).

## 12. Record

**Finding ids and where they are defined.**

| Id | Where | One line |
|---|---|---|
| V3-S1-M1 | core `docs/reviews/V3-S1-review.md` (Appendix A: `Probe.Backdoor2`) | the backdoor; "why no salting fixes it" |
| V3-S1-A23 | core `docs/DESIGN-AMENDMENTS.md` | `Controls/Backdoor.lean` as the known-gap control |
| ADV-M5 (items 1–5), ADV-M6 | submissions `docs/snark-baseline/notes/ADV1-rules-review.md`; the comment on #4 | the disguises; the indexer |
| F2 §0–§14 (round 1), R2.0–R2.11 (round 2) | submissions `docs/snark-baseline/notes/F2-o25-uninstantiability.md` | Candidates A–E, T; the post-hoc attack; the literature |
| O25-M1 … M6, m1 … m4 | submissions `docs/reviews/F2-o25-review.md` | the break of E |
| O25T-M1 … M6, m1 … m9; INV′; A1–A4; MG1–MG3 | submissions `docs/reviews/F2-o25-review-r2.md` | the review of T |
| CORE-HANDOFF §2.2 | submissions `docs/snark-baseline/CORE-HANDOFF.md` | the settled direction before the user's rejection |
| V3-S2R-H-M4; S2R RESULT §6 | core `docs/reviews/V3-S2R-handoff-review.md`, `docs/stages/V3-S2R-RESULT.md` | the liveness mirror; what S2R assumes about O-25 |

**Kernel probes.** Archived on `v3/contract-archive` under `evidence/probes/` (commits `c198bc3`,
`f4de3b8`; the index `evidence/README.md` says which contract each was checked against; none is
built by `lake build`, and the ones written against `15e4ae5` or `05fde28` do not compile
unchanged at `6202402`). Lean v4.34.1.

| Probe | Archived path (checked against) | What is a theorem, what is not | Axioms |
|---|---|---|---|
| the backdoor | `RecursionFast/Controls/Backdoor.lean` (committed, `6202402`) | `backdoor` (theorem) | `propext`, `Classical.choice`, `Quot.sound` |
| the literal trigger | `evidence/probes/LiteralTrigger.lean`, `.log` (`15e4ae5`) | `lit_eq`, `Vlit_eq`, `backdoor_lit` (theorems) | same |
| E's interface | `evidence/probes/P1_interface.lean` (`05fde28`) | `idxOf_full`, `idxOf_all_bits` (theorems); `cmpNat`, `encodeF`/`cmpF`, `pinned` (type-checked **definitions**, `pinned` with an `#eval` on `ZMod 7`) | `idxOf_full`: the three; the definitions: none |
| Lean-4 escape hatches | `evidence/probes/P2_hatches.lean` (`05fde28`) | H1–H8: each fails or compiles as predicted (build-log evidence, not theorems) | — |
| T's `pub` | `evidence/probes/T1_pub_sees.lean`, `.log` (`05fde28`) | `pubTau_eq_challenge`, `evil_Vb`, `postHoc_iff` (theorems); `csIllFormed.wf = true` (an `example`) | `propext`, `Quot.sound` |

**Nothing was implemented.** The contract at `v3/contract-archive` (contract state `6202402`,
branch head `f4de3b8`) is unchanged with respect to O-25: `Submission.V : Digest → Proof → OProg
Bool`, `Backdoor.lean` certified, the trust statement's item 4 naming the gap, `AGENTS.md` §15
naming #4.

## 13. The relativized-NARK exploration (on record; `explore/relativized-nark`, head `043bcb3`; not endorsed here)

This exploration ran from 2026-10-20 to 2026-10-22 on the core's remote branch
`explore/relativized-nark` (based on `05fde28`; 49 files; `docs/explore/BRIEF.md`,
`docs/explore/REPORT.md`, twelve notes under `docs/explore/notes/` (T1 impossibility, W1
workarounds, W2 attested oracle, A1–A3 attacks, C1 cost, L1 literature, P1–P4 Lean probes), 21
probe modules under `RecursionFast/Explore/`, and an adversarial review with a fix pass,
`docs/reviews/EXPLORE-report-review.md`, M1–M6 and m1–m21 all applied). It was omitted from the
first version of this record (review finding DOC-M1). It is summarised here from its REPORT with
the REPORT's own evidence labels (**kernel**, **paper**, **measured**, **estimate**) kept
exactly; nothing here endorses it, and the user has not been asked to choose it. It is not
merged and not archived elsewhere.

**The user's idea (BRIEF §1, verbatim in the branch).** A verifier knowledge-sound for a
*relativized* recursion relation: the node clause says "both children are accepted by `V` **with
the same oracle**" as the knowledge game, instead of v3's "accepted by `V` with BLAKE2s"; provers
timed on hash chains; a charge for the verifier's oracle calls standing in for the cost of
proving them in a recursion circuit; the user aware of the relativized-SNARG impossibility
results and hoping for a workaround.

**What relativization buys (REPORT §5).**
- *Composition becomes a theorem* (**kernel**): with the node clause read from the log (`RelL`),
  one knowledge state extracts the whole tree from one log, to every depth, with no per-level loss
  (`compose`, `compose_flat`, `paper_tree`: `n·ε` for a game of `n` queries). v3's relation
  cannot give this: `v3_no_compose` exhibits, on a log of potential 0, a node proof that v3's
  certified backdoor verifier accepts but whose children its certified extractor does not open.
- *O-25 closes, but by the deployment, not by the definition.* The relation alone does **not**
  close it (**kernel**, `Relativized/Backdoor.lean`, `backdoor`: the ported backdoor is
  relativized-sound at `errorCap` with one query and accepts the 32-byte magic proof under
  `blake2sOracle`). But nobody has to arithmetise the oracle any more, so it can be a secret
  harness service, and a standard hybrid moves the ROM bound to deployment losing `Adv_PRF`
  (**paper**; BLAKE2s in keyed mode, a key fresh per evaluation held by a separate process;
  the hybrid's fine print: the distinguisher runs the evaluation and the extractor within its
  budget, the step from lazy sampling to a random function is on paper as in v3, the service is
  assumed correct, the deployed whole-tree bound is about `2^-100` at `ε = 2^-128`). Every
  disguise of §2 and the post-hoc check over BLAKE2s wires die, and so does the liveness mirror.
  **The cost:** until the key is released, the competition is designated-verifier (nobody but
  the organiser can check a proof); key reuse across evaluations, or publishing answers before
  release, reinstates CGH; the service is trusted runtime code.

**What it costs in the pure ROM (REPORT §6; D1, D2).**
- *The re-ask law.* A node verifier that judges its children against prover-supplied answers
  without asking the oracle is unsound (**kernel**, `lazy_no_kstate` for the natural extractor at
  any error; `lazy_extractor_collides`: every extractor of such a state must output a `Collides`
  witness, a BLAKE2s collision between distinct inputs when `c₁` is a leaf statement); the honest
  alternative re-asks up to `|Q|` queries per node (`deferState`, `queries_defer`); the general
  deterministic core: if a committed child reads query `q` and the log with `q` erased still has
  potential below 1, the parent must read `q` too (`reask`, `flip_reask`, **kernel**); decoding
  extractors are the only kind a bounded node circuit admits, and for them the parent re-asks
  each child query the child's validity depends on (T1 Thm 2.2, **paper**).
- *Consequences* (**estimate** unless marked): at the ranked shape a deferral root re-asks
  `511·h_V` = 2.6–13.2 M compressions with an 80–850 MB root proof, 0.6–3.2× witness-sending's
  work: **no compression**; counted in queries it compresses about 3×, counted in compressions
  (the unit an unriggable charge must use) it does not; `h_V` is 25.9k for spartan-chain (from its
  5,156 **measured** queries), 9.2k leanVM-class, 5–12k WHIR-class.
- *The requirement is vacuous* (**kernel**): witness-sending (`ws_ksRel`), concatenation
  (`concatState`) and any flat argument with chain starts in the clear, lifted (`lift`,
  `lift_runner_ws`, T1 Thm 4.1) satisfy it; with a succinct flat SNARK the lifted root is succinct
  and nothing recurses (**paper**: the probe's flat instance is not succinct; the lift's
  completeness is paper and fails for an adversarially chosen child with a false clear shape, so
  completeness must move inside the game, "context form", W2 §A.5).
- *The oracle charge is gameable* in every self-measured form and leaves the verifier's local
  work unpriced (A1); a million chains take 89 days at spartan-chain speed (**measured** per leaf).
- Verdict on D1/D2 (A1 M10): the winner would be a BLAKE2s chain prover with any verifier, which
  is snark.fast's board; D2 is unrunnable under v3's caps beyond `r = 2` (its root breaks
  `qV ≤ 2^16` by 40× and `proofCap` by 250×).

**The workaround (REPORT §7): let the harness authenticate oracle answers.**
- **D4, the attested oracle.** The service holds a PRF key and answers `query q`, `certify xs`
  (checks a list of answers and earlier attestations and records its hash) and `attest h`;
  certification is recursive, so the root makes one `attest` call. `Rel` and `Wit` are unchanged;
  only the argument changes from "`V` under BLAKE2s" to "`V` under the log". The knowledge state
  gains a `cert` law, and `final` lets the extractor output a witness **or a BLAKE2s collision as
  data** (the bare proposition is provable by pigeonhole, so the collision must be the output of
  the step-bounded program: `acceptAll_choice` shows a `Classical.choose` extractor certifies
  accept-all at error 0, so D4's knowledge content rests entirely on `Computes`). **Kernel** (P2):
  `attState`, `calls_node` (one `attest` call per node, children judged on the carried list),
  `att_W1`, `compose_all`, `Paper.paper_tree`, `hashList_not_coll`, `encList_inj`; **scope:** the
  probe's node carries its children and the list in the clear, so the kernel shows the call
  count and the laws, not the soundness of a succinct node, which is a **paper** obligation (W2
  §A.4), the same one as issue #7. Why the impossibility does not apply (T1 §6, **paper**): a
  flipped list cannot be certified, and one flipped point moves `attest` on every list containing
  it. Assumptions: PRF security (falsifiable) and collision resistance of BLAKE2s in constructive
  form (the extractor hands over the pair). Cost: about 50 trusted lines over the 288-line
  contract (**estimate**), plus a trusted service process, the first runtime component whose bug
  is accept-all (W2 M8); in-circuit, hashing a child's list costs 1.09× what a real recursion
  spends on those hashes (**estimate**); the defect is traffic, every Merkle hash of every proof
  a service call, `6.7·10^7`–`2.7·10^8` per tree (**measured** service: a batched stream 1.2×
  in-process, unbatched 2.3× spinning and 82× with futex wake-ups, 10–12.5 M calls/s per machine).
  What the records then certify: the *attested* deployment, not a public-hash one; proofs are
  checkable only by the organiser, online, until the key is released after the record is frozen;
  the D4 argument is online and stateful, so proofs are not transferable until key release.
- **W5, the channel split.** Attest only the ≈ 500 Fiat–Shamir answers per proof; Merkle trees
  with public BLAKE2s. The node then pays a real recursion step plus 0.5–2 % (**estimate**), and
  service traffic drops about a thousandfold. The price is an unfalsifiable *extractability*
  heuristic on BLAKE2s (whoever outputs a digest knows a preimage; preimage awareness is defined
  relative to an ideal compression function, and BCPR14 under iO rule out extractable one-way
  functions with arbitrary auxiliary input), weaker than v3's random-oracle heuristic and not
  exploitable by `V`. The model as first written was broken in three places (A2 M1–M3, all
  fixable); **kernel** (P3, a two-leaf Merkle toy): `pubStep` holds with equality
  (`merkleState_pubStep`); W1's "witness or collision" clause fails for the natural extractor at
  every `ε < 1` (`col_no_kstate`; any other extractor must invert, `col_extractor_inverts`); a
  second escape, the late preimage, fixes it (`merkleState` at a tight `ε = 1/2`,
  `honest_extracts`); the backdoor on the public channel is uncertifiable with its natural
  extractor (`bd_no_kstate`) and certified on the secret one (`bdSecW_kstate`); an honest prover
  that hashes late needs a relation-tag exemption (A2 postscript).
- **D4+, the oracle-chain leaf.** The leaf chain through the oracle, certified as an `n`-item
  list; closes #6 (a), the trivial root, **by the certified caps** (`proofCap` and `qV` together;
  a **paper** argument, no Lean theorem) with `qV ≤ 2^13` and the invariant `proofCap < 64·n`;
  does **not** close #6 (b): a relabelled flat proof of a level-`j` subtree fits every cap (A3 M1).
- **D3, the signed oracle**: the same idea with in-circuit hash-based signatures, 145–1,059
  compressions per child and a 150–300-line trusted signature specification; dominated by D4.

**What none of it fixes (REPORT §7.5).** #6 (b) remains a benchmark-shape problem under every
design studied (flattening to `j ≈ 3–4` is certifiable; the honest fix is fewer, longer leaves,
`r = 4`, `n = 2^20`, where recursion costs about 1.17× flat and memory forbids flattening); #7,
node extraction is still decoding; #8, proof sizes are unchanged (D4 adds about 64 B per node).
Without D4+, #6 (a) still needs a CPU-time cap calibrated on the reference machine (raw ratio
6–24× at the ranked shape, 25–95× at the long shape; **estimate**).

**The REPORT's recommendation and the decisions it lists for the user (REPORT §9).** Drop D1/D2
as stated; keep the relativized node relation and pair it with an attested secret oracle as the
O-25 contract stage; deploy all-oracle first, W5 later if the extractability heuristic is
accepted; add D4+ for #6 (a); handle #6 (b) through the shape. Decisions only the user can take:
whether leaving the pure ROM for a trusted harness capability is acceptable (V3-5 says ROM only);
a designated-verifier window; "witness or a collision computed by the extractor" as the knowledge
clause; the shape and a flattening policy; whether records certifying the attested deployment
rather than a public-hash one are what the competition wants, since a real-world recursion built
from a winner still rests on the usual heuristic (CGH plus the impossibility result).

**How it bears on this document.** It falsifies three statements of the first version: "none is
on record" (§0, §10.2); "a secret-keyed oracle is impossible because the recursion evaluates the
oracle" without the qualifier "under v3's node clause" (§1.4, §5, Design §6.7, §13.2); and the
novelty of Design §17.2's N3 (a harness-sampled keyed oracle with the circuit's key separated
from the outer verifier's) and N5 (rank leaves, keep recursion unranked), which overlap D2/D4 and
D1 respectively. Against the criteria of §11 (the authors' reading of the user's objection): D4
keeps an agent-written verifier that may compute anything on answers, needs no per-entry and no
per-template review, and has no manual step in the path from submission to verdict; what it adds
is a trusted service, records that the organiser alone can check online until key release, a
knowledge clause with a collision escape, and the three unchanged issues. Whether that is
"narrowing the design space" or "manual intervention" in the user's sense has not been asked.
