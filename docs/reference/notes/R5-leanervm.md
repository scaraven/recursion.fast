<!-- Copied verbatim from the design workspace CambridgePQ/recursion.fast/notes/R5-leanervm.md (research note of 2026-10-10, written against the pinned checkouts it names). Kept here so the repository is self-contained; see docs/reference/neighbouring-competitions.md for the synthesis. -->

# R5: leanerVM (and leanVM) research note

Task R5 of `PLAN.md`. Author: research subagent, 2026-10-10. Read-only research; nothing in the
referenced repositories was modified.

**Legend.** [V] = verified by reading the cited file/line at the recorded SHA (or by a web fetch,
marked [V-web]). [I] = my inference or recommendation, not stated by the source.

## 0. Provenance (SHAs)

| Source | Path | Revision |
|---|---|---|
| leanerVM working tree (branch `feat/protocol-flock-spec`, clean, = origin) | `/home/devops/Verified-zkEVM/leanerVM` | `8aaf8a0ca385` (2026-10-10 11:44 UTC) |
| leanerVM local `main` / `origin/main` | same | `ad0c5f0617ca` (2026-10-07) / `08dd030ffac8` (2026-10-07, "the opening phase (#81)") |
| leanerVM pins (`upstreams.json`) | | leanVM `a386121f`, ArkLib `7653a901`, CompPoly `572f9973`, Clean `42fe4b26`, VCVio `a4232d08`, Lean/Mathlib `v4.34.1` |
| leanVM (Rust) | `/home/devops/leanEthereum/leanVM` | `a386121f84292f6fa663aaa3e570c15bc0240ea2` (= leanerVM's pin, HEAD) |
| leanerVM talk | `/home/devops/CambridgePQ/leanerVm` | `05cf9fea906d` (+ uncommitted `Slides.lean`, `leanerVm-draft.txt`, dated 2026-10-08) |
| Skills (`lean-spec-authoring`, `adversarial-review`, `human-review-audit`) | `/home/devops/.claude/skills/*/SKILL.md` (user-level, **not** in the repo; the repo's `.claude/` holds only `worktrees/`) | file dates 2026-09-04 .. 10-02 |
| ots.golf-dev (leanISA track, for item 6) | `/home/devops/leanEthereum/ots.golf-dev` | `8b140a99afa5` |
| ArkLib in leanerVM `.lake` | `.lake/packages/Arklib` | `7653a901ed46` |

Line numbers below are at these revisions. Docs on the working branch are the protocol docs as of
the Flock PRs (#86/#88 "on merge"); `docs/architecture.md`, `AGENTS.md` are identical in spirit to
`main`.

## TL;DR

1. leanerVM is a layered (Parameters → Semantics → Arithmetization → Protocol, plus Applications)
   end-to-end formalization of leanVM targeting eight theorems T1–T8. The "two master theorems"
   are **`piop_perfectCompleteness`** and **`piop_rbrKnowledgeSoundness`**: perfect completeness
   and *worst-case-per-prefix round-by-round knowledge soundness with a named, computable
   extractor* (ArkLib's `rbrKnowledgeSoundnessWorstCaseWith`) of the interactive oracle protocol,
   over an **abstract** instance `I : M3Instance`, in the **ideal oracle model** (no shared
   oracle, `[]ₒ`), **conditional on** a bundle of per-phase proofs, at a contract-fixed error
   `piopError I`. They "say nothing of leanVM until the instance and the phases are leanVM's".
2. The non-interactive theorem (`verify_knowledgeSound`, T4) is planned as a ROM statement
   conditional on named *assumed-interface structures* (RBR→state-restoration, BCS/Merkle,
   Fiat–Shamir with proof of work, Johnson-range MCA, Flock security). None is an axiom; each is
   an explicit argument. Not built yet.
3. **Recursion (T6, "Recursive CTE") is declared an open research problem.** Inner SNARK
   knowledge soundness is a ROM statement with a straight-line extractor reading the query log;
   the known outer "recursion topology" argument composes abstract (plain-model) extractors
   through a tree. In recursion the *relation itself queries the random oracle* (the verifier is
   inside the proved computation), and relativized succinct arguments in the ROM do not exist
   [Barbara–Chiesa–Guan, ePrint 2024/728, V-web]. leanerVM forbids a global bridging axiom and
   keeps the end-to-end T7 as a *target schema*.
4. For recursion.fast this means: a batcher theorem stated in the interactive/IOP model as a
   **reduction of knowledge** `R × R → R_acc` (plus a decider), with named computable extractors
   and contract-fixed errors, is honest and composable by ArkLib's sequential composition; it
   must **not** be advertised as security of a deployed recursive SNARK (verifier-in-circuit with
   an instantiated hash). Also: in Lean, knowledge soundness without an extractor-efficiency
   constraint degenerates to soundness on finite witness spaces (Section 7.3) — the contract must
   constrain the extractor's *form*.
5. Directly reusable: ArkLib's RBR-KS definition in the `With` form; leanerVM's
   `Component.{Def,Guarded,Complete,Security}` hole interfaces and `append`; the port of ArkLib
   #615 (KS composition, admitted upstream); the `not_rbr` / `not_perfectCompleteness`
   refutation lemmas (negative controls); `Refinement.knowledge_transport`; the generic sumcheck,
   batching-by-powers, GKR, fingerprint components; the review checklists and 35 "nearby false
   statements"; the axiom-audit script with negative control.

---

## 1. Architecture

### 1.1 Layers and the wall [V]

- Layer DAG (`AGENTS.md:52-57`, `docs/architecture.md:12-18`):
  `Parameters ──→ Semantics ──→ Arithmetization ──→ Protocol`, `Semantics └──→ Applications ──┘`.
  Enforced by `scripts/check-layers.sh` on every validation run (`architecture.md:17-18`).
- Ownership (`architecture.md:20-64`): Parameters = constants/encodings with "an authoritative
  source and exact revision"; Semantics = ISA, memory, interpreter; Arithmetization = tables,
  buses, witness generation, "refinements connecting constraint satisfaction to executions";
  Applications = the recursive XMSS/SPHINCS aggregation guest; Protocol = "only leanVM-specific
  composition of upstream polynomial, oracle, commitment, and proof-system components".
- **The wall** (`architecture.md:59-64`): "every module of the protocol layer is written over an
  abstract instance of the arithmetization and imports nothing from `LeanerVM/Arithmetization/`",
  except an allow-list (fixed columns, adaptor, compiled verifier, base theorems). Purpose: a
  leanISA change touches only those modules.
- Upstream staging (`architecture.md:52-57`, `AGENTS.md:105-108`): generic candidates live in
  `LeanerVM/Protocol/To{ArkLib,CompPoly,VCVio}/`, "written for that library's other consumers ...
  no protocol vocabulary"; deleted when the pin passes the upstream merge.

### 1.2 Libraries and how they are used [V]

`AGENTS.md:98-100`: "CompPoly for computable polynomial algorithms, ArkLib for oracle reductions
and proof systems, VCVio for oracle computations and security carriers, and Clean for generic
circuit/AIR/table infrastructure." Concretely (`protocol-blueprint.md:235-272`):

- **ArkLib** (legacy `OracleReduction` framework; decision 24: "the only one with a knowledge
  notion"): `ProtocolSpec`, `OracleInterface`, `Prover/Verifier/OracleVerifier/OracleReduction`,
  `perfectCompleteness`, `KnowledgeStateFunction`, `Extractor.RoundByRound`,
  `rbrKnowledgeSoundnessWorstCaseWith`, `OracleReduction.append` with guarded completeness,
  Schwartz–Zippel counting, `MvPolynomial.MLE`. ArkLib "carries admitted theorems"; every
  consumed theorem is checked with `#print axioms` (`AGENTS.md:67-69`).
- **VCVio**: `SampleableType`/`$ᵗ` sampling, `ProbComp`, `QueryImpl`; Merkle trees with
  `extractability_rom_bound` as a Layer-11 candidate.
- **CompPoly**: `BF64` (`K = GF(2^64)`), `BF64.Ext3` (`E = GF(2^192)`), computable multilinear
  tables `CMlPolynomialEval`, `CMvPolynomial`, additive NTT.
- **Clean**: `Expression`, `EnsembleWitness`, constraints/interactions of the six opcode tables.
  Clean's own field-summed balance is vacuous over `K` (#16), so leanISA uses `BalancedPair`
  counted in ℕ (`protocol-blueprint.md:271, 350`).

### 1.3 Target ladder T1–T8 and the "target schema" approach [V]

`architecture.md:66-77` (ownership table) and `:169-404` (statements). Summary:

| T | Name | Shape |
|---|---|---|
| T1 | `constraints_iff_isa` | `SatisfiedBy → ∃ trace, Represents ∧ ValidExecution` and converse (`:214-226`), aux columns existential |
| T2 | `witnessGen_correct` | generator output satisfies and represents |
| T3 | `aggregationProgram_correct` | exact guest bytecode execution ⇒ guest postcondition |
| T4 | `baseVerifier_extractsExecution` | ROM, Q-query prover, straight-line extractor reading the query log: `Pr_H[accept ∧ ¬SatisfiedBy (extract log)] ≤ baseError Q` (`:268-288`) |
| T5 | `recursiveVerifier_iff` | verifier-in-circuit ⇔ base verifier decision; deferred claims preserved (`:290-295`) |
| T6 | recursion and CTE | **provisional; open** (`:297-350`) |
| T7 | `finalVerifier_endToEndSound` | **target schema** (`:352-382`) |
| T8 | `finalProver_complete` | liveness of the real pipeline (`:384-389`) |

Two sentences worth copying into recursion.fast's own methodology:

- `architecture.md:280-281`: "`Accepts … → except with probability …` is not a statement:
  acceptance of fixed values has no randomness in it." (Security must be stated as a game over
  the adversary and the oracle/coins, not as an implication from a fixed accepting proof.)
- `architecture.md:285-286`: "Instantiating `H` by the deployed hash is the one non-formal step:
  an assumption of the deployment, named, never a hypothesis of a theorem."

"Target schema" (`architecture.md:352-382`, `README.md:35-38`): the end-to-end statement is
written down in full as the goal, but "Until the T6 bridge is resolved, this is a target schema. A
conditional theorem may instantiate it from a clearly named recursion/extraction hypothesis, but
it is not the final concrete security theorem." The capstone must expose "its total error bound,
cryptographic assumptions, fixed program identity, public-input interpretation ... and trusted
compiler or implementation bridges" (`:516-519`). Also the statement-binding point
(`:204-206`): `FinalVerifier.AcceptsExpected` "must rule out acceptance for a different
prover-selected statement" — the bare `AggregateSignature::verify` validates "the statement
carried by the object".

### 1.4 The two master theorems, exactly [V]

Blueprint summary (`protocol-blueprint.md:11-25`):

```text
piop_perfectCompleteness (I : M3Instance) (P : Phases I) (C : P.Complete) :
  M3Holds I input q → the honest prover makes leanVmVerifier P accept with probability 1
piop_rbrKnowledgeSoundness (I : M3Instance) (P : Phases I) (S : P.Security) :
  leanVmVerifier P is round-by-round knowledge sound for M3Holds I, with the named extractor
  piopExtractor P S (it reads the stack q off the commitment), at the error piopError I
```

Lean (`LeanerVM/Protocol/Spine/Compose.lean:211-227`):

```lean
theorem piop_perfectCompleteness (P : Phases I) (C : P.Complete) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmPiop P).perfectCompleteness init impl (M3Rel I) (Seam.done I) :=
  C.toDef.complete init impl

theorem piop_rbrKnowledgeSoundness (P : Phases I) (S : P.Security) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmVerifier P).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl (M3Rel I)
      (Seam.done I) S.extraction.witMid (piopExtractor P S) (S.extraction.kSF init impl)
      (piopError I) :=
  S.toDef.rbr init impl
```

What they say, precisely:

- **Relation in**: `M3Rel I = {((input, ∅), q) | M3Holds I input q}` where the witness is the
  committed stack `q : Column I.μ` (`blueprint:461-464`):
  `M3Holds I input q := ConstraintsVanish ∧ Balanced (List.Perm) ∧ CountsNonzero ∧
  PublicLinesHold input ∧ aux` (aux = Flock R1CS on the BLAKE2s region).
- **Relation out**: `Seam.done I` = `True` ("ends with nothing left to check",
  `Compose.lean:31-32`). The protocol is a reduction `M3Rel → ⊤`, i.e. a proof system.
- **Model**: shared oracle spec `[]ₒ` — ideal/information-theoretic IOP; "the stack `q` is an
  oracle answering inner products `⟨W, q⟩`, and the challenges are uniform" (`blueprint:24-25`).
- **RBR KS semantics** (ArkLib `RoundByRound.lean:557-568` at `7653a901`): for every input
  statement, every challenge round `i`, every fixed transcript prefix,
  `Pr_{c ← $ᵗ}[∃ witMid, ¬kSF(i) s tr (extractMid i s (tr‖c) witMid) ∧ kSF(i+1) s (tr‖c) witMid]
  ≤ ε i`. The `KnowledgeStateFunction` (`RoundByRound.lean:165-191`) must satisfy `toFun_empty`
  (state at round 0 ⇔ input relation), `toFun_next` (prover messages cannot make the state
  true; extraction backward), `toFun_full` (if the verifier can output something in `relOut` the
  final state is true).
- **Error**: `piopError I : ChallengeIdx → ℝ≥0`, a concatenation of slot errors fixed by the spine
  as closed forms of the instance's sizes — "no phase declares its own, since a declared error of 1
  makes the knowledge theorem hold of a phase that checks nothing (decision 20)"
  (`blueprint:311`). `piopError_le`: `Σ piopError I < 2^{-159}` at admissible sizes
  (acceptance test 23, `blueprint:1377-1380`).
- **Conditionality**: hypotheses `C : P.Complete`, `S : P.Security` are the per-phase proofs. Status
  (`protocol-status.md:43-53`): proved with only `propext, Classical.choice, Quot.sound`; the bus,
  table-sumcheck, public-input and opening phases are built; Flock on branches (#86/#88).
- **Extractor**: named (`piopExtractor`), computable, and `piopExtractedStack_eq`
  (`Compose.lean:197-199`) proves the extracted stack *is the committed first message* on every
  transcript.
- **Plain KS is not claimed**: "Its plain reading ... is ArkLib's
  `rbrKnowledgeSoundness_implies_knowledgeSoundness`, admitted at the pinned revision"
  (`Compose.lean:33-36`). [V] It is `by sorry` at `7653a901`
  (`ArkLib/OracleReduction/Security/Implications.lean:193-198`) and still `sorry` at ArkLib HEAD
  `db7005f84`. `rbrSoundness_implies_soundness` is also `sorry` there (`:79-83`).
- **The instance is trusted data**: "the master theorems hold of instances whose relation is empty"
  (`blueprint:322, 401-402`); "a verifier that omits a check *together with* an instance that
  omits the matching clause ... satisfies them. What catches it is the adaptor's soundness theorem,
  whose conclusion `SatisfiedBy` does not weaken with the instance" (`blueprint:115-121`).

### 1.5 The relation ladder and the adaptor [V]

`blueprint:346-359`: Clean `Ensemble.Statement` (unusable, vacuous balance) → leanISA
`SatisfiedBy prog input w` (T1's relation) → spine `M3Holds I input q` (protocol relation, witness in
`Type 0`) → `ValidExecution prog input t` (never the protocol's relation). Rationale
(`blueprint:109-113`): "a knowledge extractor recovers column data, never an execution; a protocol
stated against `ValidExecution` would demand of the extractor what it cannot produce". The adaptor
transports knowledge along a validity-preserving witness map at the same error
(`Refinement.knowledge_transport`, `ToArkLib/Refinement.lean:82-…`; `blueprint:529-533`), and T4 =
`verify_knowledgeSound ∘ knowledge_transport satisfiedBy_witnessOf ∘ constraintSoundness`
(`blueprint:390`).

### 1.6 Trust policy [V]

- `AGENTS.md:67-71`: "a leanerVM declaration must not depend on [an admitted ArkLib theorem] (the
  kernel axiom audit rejects `sorryAx`)"; "Do not add `axiom`, `sorry`, `admit`, `unsafe`, or
  `native_decide` to accepted first-party Lean code."
- `AGENTS.md:81-83`: "Treat T6 recursion extraction and unconditional T7 soundness as open research
  targets. Keep inner ROM knowledge soundness separate from the conditional outer topology theorem,
  name every heuristic bridge explicitly, and do not introduce a global axiom to connect them."
- `blueprint:322` (*Trusted surface*): "Every trusted definition fits on one screen, cites its
  source line ...; assumed interfaces are structures whose docstring names the owner and the witness
  obligation, never `variable`-block hypotheses or `axiom`s." `blueprint:323` (*Unproved targets*):
  "a block comment at its place ... Never `sorry`." `blueprint:1491-1498`: the assumed interfaces
  "a reviewer must know are exactly" FlockSpec + Flock Security, `McaJohnson`,
  `RbrToStateRestoration`, `BcsSecurity`, `ChainFiatShamirSecurity`, and the `Phases` fields;
  "none is an axiom, none has an inhabitant in the repository until it is proved, and every theorem
  that uses one takes it as an argument."
- Two source categories (`blueprint:189-196`; skill `lean-spec-authoring` §5): **Category A**
  (specification of intent: accept condition, relations, security statements) is "written from the
  specification first and then diffed against the Rust"; **Category B** (transcribed artifacts:
  tags, encodings, layouts, constants) "are wrong if they deviate". Decision 22 (`:1556`): model
  the deployed checks; an auditable variant only "if it accepts no more and its relation to the
  deployed one is a theorem".
- Author's audit-size claim (talk, `CambridgePQ/leanerVm/Slides.lean` "What do I audit?"):
  leanISA spec ≈250 lines, SNARK input relation 141 lines, security definitions ≈500 lines,
  verifier/prover specification ≈1,200 lines each (≈1,000 shared), plus upstream library
  definitions. "Everything else is checked by the Lean kernel."

---

## 2. The recursion / "Recursive CTE" open problem

### 2.1 Where it is discussed [V]

- `README.md:35-38`: "Recursive CTE is an open research problem: the intended knowledge-soundness
  arguments for the concrete inner SNARKs live in the random-oracle model, while the known outer
  recursion-topology argument requires an extraction interface that is not presently justified by
  such inner results. The architecture keeps the desired final theorem as a target schema and does
  not claim that this bridge has been solved."
- `docs/architecture.md:297-350` (T6), `:352-382` (T7 schema), `:481-500` (Recursion section),
  `:126-138` (the "extract: CTE / topology bridge (provisional)" arrow).
- `AGENTS.md:81-83`; skill `adversarial-review` ground rule ("T6 and unconditional T7 are open
  research targets"); skill `lean-spec-authoring` §6 ("No global bridging axiom").
- `docs/leanvm-target.md:86-94` (deferred claims; no decreasing depth measure), `:246, :249,
  :268-272`.
- `docs/roadmap/protocol-blueprint.md:99-100` ("What is not attempted: recursion (T5, T6) ..."),
  `:160-162` (out of scope), `:1524-1527` (Boundaries with recursion: `settleFixedClaims` is the T5
  seam; `execution_of_extracted` "hands recursion the extracted witness").
- `docs/roadmap/leanth-reuse.md:277-282` (tree extraction in the private predecessor "assumes
  transparent recursion"), `:300, :318-331` (product extraction `multi_isKnowledgeSound` with
  counterexamples; "An independent product theorem does not establish arbitrary shared-oracle
  composition or recursive T6").
- Talk notes (`Slides.lean`, "Open Problems"): "Recursive CTE: the inner SNARKs' knowledge soundness
  is in the ROM, but the known recursion-topology argument needs an extraction interface those
  results don't currently justify." Draft (`leanerVm-draft.txt:52-56`): "How do we model the running
  time/complexity of the extractor (or any algorithm) in Lean 4?", "Recursive Proofs in a zkVM are
  secure".

### 2.2 The problem, self-contained

Setup. A recursive aggregation tree: each node runs a guest program that (i) verifies `n_rec`
child proofs with the *same* verifier `V^H` (H = BLAKE2s modelled as a random oracle), (ii) checks
raw signatures, (iii) publishes a statement. The node's proof attests "this guest execution is
valid", and the guest execution contains `V^H` computations — so **the proved relation itself
depends on `H`**: `R^H = {(x, w) : guest^H(x, w) halts}`.

Two results one can state cleanly (`architecture.md:301-305`) [V]:

- **Inner theorem**: knowledge soundness of the concrete non-recursive SNARK in the ROM, with a
  straight-line extractor reading the adversary's oracle query log (T4's shape:
  `Pr_H[accept ∧ ¬R(x, Ext(log))] ≤ ε(Q)`). Here the relation `R` is fixed, independent of `H`.
- **Outer topology theorem**: given *abstract* extractors for each proof relation, compose them
  through the tree into a global witness (an execution tree whose edges are consistent and whose
  leaves contain signature witnesses), the provisional `Recursion.ValidExecutionTree`
  (`architecture.md:307-321`). Following "the game-based insight that CTE is knowledge soundness
  for a full-trace relation" (`:323-324`).

The gap (`architecture.md:324-329`) [V]: "Recursive verification makes the relation itself query
the random oracle, so connecting ROM knowledge soundness of the inner SNARKs to the outer theorem
would require a suitable relativized notion. Relativized SNARKs do not exist in the ROM in general
[ePrint 2024/728]. Plain-model straight-line knowledge soundness is also incompatible with
succinctness in general."

Explanation [I, standard]: to apply the outer theorem at depth 2, one needs: from a root prover
`P*^H`, extract an accepting *child proof* `π_c` and then apply the inner extractor to `π_c` to
get the child's witness. But the inner extractor's guarantee is about an adversary *interacting
with H* and reads *that adversary's* query log; the child proof was never "produced by a
query-logged adversary" — it was extracted from the root's witness, and checking it requires
evaluating `H` inside `R^H`. A relativized SNARK (knowledge soundness for relations that may
themselves query the oracle) is what would close this; Barbara–Chiesa–Guan prove such succinct
arguments do not exist in the ROM [V-web: "succinct arguments in the random oracle model, which can
verify computations that query the random oracle, cannot exist, even if the argument is
interactive and its soundness is only computational"; this "rule[s] out that approach for IVC and
PCD in the random oracle model"]. Practical systems (PCD/IVC from hash-based SNARKs) therefore rest
on a *heuristic*: instantiate the oracle by a concrete hash and assume the resulting
plain-model SNARK is knowledge sound (straight-line, or with bounded-depth rewinding).

Candidate bridges, all named as heuristics with different claims (`architecture.md:331-343`) [V]:
"plain-model or relativized extraction assumptions, a NARK carrying outer queries, or rewinding with
a bounded depth". Rules: no global ROM→plain-model axiom; an idealized outer theorem "must expose
its extraction assumption and must not be presented as concrete security of the instantiated
recursive system"; a non-straight-line extractor "needs a meaningful recursion-depth bound and a
justified rewinding model"; "any candidate needs an explicit advantage sum, extractor runtime,
oracle model, and well-foundedness argument. A bound on child arity alone does not bound depth."

Well-foundedness finding about leanVM (`leanvm-target.md:90-94`) [V]: "No public decreasing
recursion-depth measure was found ... `MAX_RECURSIONS` bounds child arity, not depth, and the
published signer claim need not strictly grow from child to parent." (`MAX_RECURSIONS = 16`,
`crates/rec_aggregation/src/aggregation.rs:78`.)

What the extracted object must be (`architecture.md:345-350`) [V]: "ordered `pc`/`fp` steps and the
full memory image ...; table openings, bus digests, or a final commitment alone are not a correct
trace."

Outer-topology prior art [V-web, github.com/b-wagn/lean-vanillavm, README]: CTE is
`∃ E : Stmt → Proof → PrivInput × (ℕ → State), ∀ x p, verify x p → TraceValid x (E x p).1 (E x p).2`
— "our extractor is a plain function, with no probabilities or running times" (v1). I.e. the outer
theorem is in a *deterministic, plain* model; that is exactly the interface the inner ROM theorem
does not supply.

leanth predecessor (`leanth-reuse.md:277-282, 318-331`) [V]: tree extraction
(`stochasticExtractTree_failure_le`, `isKnowledgeSound_of_core`) "assumes transparent recursion
(child proofs read off the root proof)"; RBR knowledge soundness of the forwarding sumcheck "is an
assumed field, not proved". Product extraction `multi_isKnowledgeSound` (k independent proofs at
once, errors summed) comes with two negative controls: `multi_isKnowledgeSound_counterexample`
and `..._refinement_insufficient` ("neither the maps nor component security can be omitted"); its
extractor depends on the prover (a `CoupledExtractor`), which ArkLib's current
`Extractor.Straightline` (statement, witness, transcript, query logs; no prover code) does not
allow.

### 2.3 leanVM's actual recursion design: deferred claims (accumulation) [V]

`leanVM/doc/leanvm/body/09-recursive-aggregation.tex:9-20`: three fixed multilinears (the bytecode
and Flock matrices `A_0, B_0`, "28-variable multilinears with ≈89M nonzero Boolean entries") would
"dwarf the entire remaining verifier" in-circuit. "The aggregation guest therefore does not evaluate
these fixed polynomials. It verifies every surrounding reduction and exports only the resulting
points and claimed values." "Each child contributes two claims on each ... so a node batches
`2 n_rec` per polynomial and a statement stays one size however deep the tree." "Only the root pays
those evaluations: every other node's claims are discharged by its parent's batch." The node's
public input (`:30-42`) hashes the environment digest, signer-set digest and the deferred
points/values.

[I] This is an *accumulation scheme* for evaluation claims on fixed polynomials: inner verifier ≠
final verifier (final = inner + native "decider" `settleFixedClaims`); the accumulator is part of
the statement and has constant size. This is precisely the brief's "#1: the verifier specification
may change compared to the final layer verifier and inner SNARK verifiers". leanerVM's T5 owes "that
batching preserves the three deferred fixed-polynomial claims ... and that native root discharge
closes every claim carried through the tree" (`architecture.md:293-295`, `:498-500`).

---

## 3. The proof-system specification on ArkLib

### 3.1 The protocol and its components [V]

Overview (`blueprint:3-9`): commit the six M3 tables as one multilinear "stack" `q`; then bus
(GKR grand product), one batched table sumcheck, two-cell public input, Flock (BLAKE2s R1CS) with ring
switching, one WHIR opening; Fiat–Shamir over BLAKE2s. Fields: `K = GF(2^64)`, challenges in
`E = GF(2^192)` (`blueprint:127-128, 267`). Oracle: one committed stack with an inner-product
interface — a query is a weight `W`, the answer `⟨W, q⟩` (`blueprint:52-61, 307`; decision 19).

Composition: `commit ⟫ bus ⟫ table ⟫ pub ⟫ flock ⟫ opening` (`Compose.lean:17`). Each phase is an
ArkLib reduction between **seams** (`Seam.commit = M3Holds`, `Seam.bus`, `Seam.table`, `Seam.pub`,
`Seam.flock`, `Seam.done = True`); "The output relation of a phase is the input relation of the next,
by definition (`Seam.*`), never by a bridge lemma" (`blueprint:328`).

| Component (file) | Reduction | Per-challenge error (spine-fixed) | Status |
|---|---|---|---|
| commit (`Spine/Compose.lean`, `ToArkLib/SendOracle.lean`) | send the stack as oracle; extractor reads it | 0 | built |
| sumcheck plain / normalized (`ToArkLib/Sumcheck.lean`, `SumcheckRound.lean`) | virtual polynomial (formula of tables), last message = table values; normalized = Gruen cofactor round | `d/|F|` per round (`d_c/|F|`) | built (#75/#76) |
| `Sumcheck.transport` (`ToArkLib/TranscriptMap.lean`) | wire drops one coefficient; RBR KS preserved under injective decoding | same | built |
| batching by powers `Component.batch` (`ToArkLib/Batch.lean`) | random linear combination of `k` claims by powers of one challenge | `(k−1)/|F|` | built (#77) |
| fingerprint + collision (`Fingerprint.lean`, `ToArkLib/GrandProductPoly.lean`) | Lemma 5.2 (product polynomial determines multiset), Thm 5.1 | `4·2^μ/|E|` | built (#39/#78) |
| grand-product GKR (`ToArkLib/GrandProduct*.lean`) | radix-4 layers, normalized sumchecks, "riders" (tables that must vanish at the final point) | `(nside−1)/|E|` per combiner, `4/|E|` per radix-4 round, `1/|E|` per combination challenge | built (#62/#70) |
| bus phase (`Bus.lean`, `BusSecurity.lean`) | `(α,β)` then GKR then boundary evals; checks `R_c ≠ 0`; zerocheck carried by the state function | `4·2^{μ_bus}/|E|` + `gkrError` | built (#79/#80) |
| table sumcheck (`TableSumcheck.lean`) | `ξ` batch + plain sumcheck on `τ_max` vars | `(B+2)/|E|` on ξ, `3/|E|` per round | built (#85/#87) |
| public input (`PublicInput.lean`) | one challenge on the line through cells 0,1 | `1/|E|` | built (#60/#72) |
| Flock (`Flock.lean`, `ToArkLib/Flock/`) | zerocheck + lincheck on Boolean R1CS blocks, ring switching | `flockError` | branches #86/#88 |
| opening (`Opening.lean`, `ToArkLib/QueryCheck.lean`) | batch by `λ` then one weighted oracle query | `(J−1)/|E|` | built (#81) |
| WHIR, Merkle, FS chain, `verify` (Layers 11–13) | IOPP (RBR *soundness* for the list relation); list-binding compilation; BCS; FS with 17-bit grinding | `niError Q` | not built |

Hole interfaces (`blueprint:327`, `:492-501`): each component is
`Component.Def` (the reduction, computable, no error) / `Guarded` (prover output pure; verifier =
guard then verdict) / `Complete` (perfect completeness) / `Security` (extractor, knowledge state
function, `rbrKnowledgeSoundnessWorstCaseWith` at the spine's error), "so that knowledge soundness
does not presuppose completeness (decision 23)". `Component.Security.append` composes; the
knowledge-soundness composition that ArkLib admits is ported from ArkLib PR #615
(`ToArkLib/KnowledgeAppend.lean`, 582 lines; "Deleted when some ArkLib framework proves a
guarded-first append", `blueprint:281`).

### 3.2 Security statements targeted [V]

- Interactive: perfect completeness + **worst-case RBR KS with named computable extractor** per
  component (decisions 10, 11, 23); error per challenge, `ℝ≥0`, spine-fixed closed forms.
- WHIR: "round-by-round soundness for the list relation, not knowledge soundness: the commitment
  is list binding" (`blueprint:1145-1148`); "every oracle-protocol challenge pays the list size
  `L_0`" (110 to 648 at deployed parameters, `:1219-1225`; acceptance test 11).
- Non-interactive (`blueprint:1190-1203`): `verify_knowledgeSound (rs bcs fs mca flock) (Q) (A :
  Adversary H Q) : Pr_H[verify^H prog input proof ∧ ¬M3Holds … (extract … log)] ≤ niError Q`, with
  `niError Q = (Q + rounds)·max_i ε_i + c·Q²/2^256 + …` (`:1227-1231`). "At the deployed parameters
  the maximum is the query rounds' `2^{−128}`, which holds only with the proof-of-work factor, an
  assumption of `ChainFiatShamirSecurity` that no published theorem covers; without it the statement
  certifies about 111 bits" (`:1231-1234`).
- Out of scope (`blueprint:151-173`): adaptive statement choice (statement quantified outside the
  probability), ZK, quantum adversaries, the Johnson-range proximity-gap theorem (consumed as
  `McaJohnson`, "a preprint whose proof is sketched"), FS/BCS theory, prover performance.
- Completeness after compilation is *not* perfect: "the honest prover's grinding is a search with
  no proved bound, so `prove` takes fuel" (`blueprint:1291-1292`).

### 3.3 Lessons from the adversarial reviews (generic, reusable)

Each item: source, then the generic lesson [I = my generalization].

1. **Seam over-generality makes completeness vacuous** (`reviews/protocol-spine.md:70-108`, A1,
   high). `Seam.bus` admitted true claims of any degree; the next phase's completeness ranges over
   all of them, so "`Phases.Complete` has no inhabitant whose `table` field is the intended phase,
   and `piop_perfectCompleteness` is vacuous for the real protocol". Lesson: an intermediate
   relation must be no larger than what the honest previous phase emits *and* what the next phase
   can serve; put bounds (degree) in the type.
2. **Under-determined auxiliary predicate breaks one direction either way** (A2, high,
   `:110-148`): weak reading ("limbs compress") makes Flock completeness false (wires committed
   before; cannot be fixed); strong reading ("R1CS holds") moves obligations to the adaptor.
   Lesson: when a relation crosses a module boundary, decide the exact predicate and write down
   which side owes which lemma.
3. **Existential extractor = soundness only** (A3, `:150-191`; blueprint acceptance test 24,
   `:1381-1386`): "ArkLib lets an extractor be any function, so a theorem that merely asserts some
   extractor exists is satisfied by one that picks a witness by classical choice and carries no
   knowledge" (`blueprint:69-71`). Fix: the `With` form, extractor a computable `def`, and a test
   that it returns the honest witness. Related: GKR review M1 (`protocol-gkr-security.md:75-97`):
   every `Security` was `noncomputable`, so the extractor could not be run.
4. **Unprovable-as-stated adaptor theorem** (A5, `:220-238`): caps were outside the relation, so
   `M3Holds → SatisfiedBy` is false for oversize parameters. Lesson: every size cap the verifier
   checks must be either in the relation or an explicit hypothesis discharged by the verifier.
5. **Declared errors** (decision 20; test 32, `blueprint:1410-1412`): "Five phases that draw a
   challenge, check nothing and declare error 1 satisfy knowledge soundness at their declared
   error." Lesson: the contract, not the submitter, fixes (or upper-bounds) the error.
6. **Load-bearing checks need refutations** (`blueprint:321`; reviews bus #1, sumcheck #4,
   opening #3): every verifier check comes with a theorem that removing it destroys RBR KS (`1 ≤ ε`)
   "whatever the extractor". "A check is load-bearing only if the verifier commits to what it
   checked: a claim pooled from a prover's message pools the value *sent*"; "A public-input
   verifier that pools the values it computes is knowledge sound with no check at all" (test 31).
   Public-input review ran the tautology test against five wrong verifiers
   (`reviews/public-input-phase.md:109-133`).
7. **Tightness witnesses** (fingerprint #1, opening #2): show the error bound cannot be lowered
   (e.g. `{0}` and `{e₁₅}` collide at > `3·|E|⁴` challenges). Lesson: bound claims ("attained")
   need a witness.
8. **Quantifier order in security hypotheses** (`reviews/protocol-batch.md:70-80`): choosing the
   distinguishing vector *after* the witness forced a `[Subsingleton W]` hypothesis (counterexample
   over `ZMod 5`); choosing it before removed the hypothesis. Lesson: a component's security
   hypothesis can silently restrict which witnesses/consumers it applies to.
9. **Context not carried through a component** (`protocol-sumcheck-security.md:74-115`): a
   generic sumcheck's state function could not carry untouched conjuncts of the outer relation, so
   the phase could not reach its seam. Lesson: generic components need a "frame rule"
   (`Security.conj`) to be composable.
10. **Characteristic-2 traps** (spine review clean pass `:257-260`; acceptance test 7): a balance
    summed in the field accepts a tuple pushed twice and never pulled; copying padding multiplies by
    `2^k = 0`. Lesson: multiset equalities stated as `List.Perm`/ℕ counts, never field sums.
11. **"Nearby false statements"** catalogue (`blueprint:1295-1423`, 35 entries): each names a
    reading that compiles and is wrong, and the witness rejecting it. A model for the contract's
    own "attack catalogue".
12. **Audit surface** (`protocol-spine.md:428-449`; `protocol-spine-revision.md:229-271`): spine =
    1,314 lines, ≈306 statement lines + ≈100 meaning-carrying bodies vs 212 proof lines; the whole
    protocol layer had 532 declarations, 510 public; reviewers routinely make proof-only lemmas
    `private` to shrink what a human must read.

---

## 4. Spec-authoring discipline (skills)

Location: `/home/devops/.claude/skills/{lean-spec-authoring,adversarial-review,human-review-audit}`
(user-level; referenced by the repo but not committed in it) [V].

**`lean-spec-authoring`** (`SKILL.md`, 355 lines) [V]:
- Governing rule (`:20-29`): "The statement is the deliverable. The proof is an implementation
  detail." ... "If the proof is hard, the statement does not move."
- Forbidden moves (`:91-100`): strengthening a hypothesis, weakening the conclusion (`↔` to `→`,
  `=` to `≤`), specialising a variable, adding side conditions, redefining the object.
- Non-vacuity (`:138-147`): "instantiate the hypotheses with a concrete witness ... Pin the witness
  as a guard theorem checked into `tests/`." Non-tautology via the **substitution test**: "would the
  statement still be provable, by the same proof, if the object it is about were replaced by a
  different one of the same shape?"
- Load-bearing vs proof-help lemmas (`:149-181`): proof helpers `private`; "delete every proof-help
  lemma ... A reviewer reading only what remains should still know exactly what has been proved."
- Category A vs B sources (`:195-234`): write Category A "expectation-first" before reading the
  implementation; Category B "copy, do not paraphrase".
- Visible gap vs invisible assumption (`:236-274`): "A hypothesis or assumed interface looks like
  rigour and may be vacuous ... and *no tool detects this*"; every assumed interface carries a
  **witness obligation**.
- `references/vacuity-and-tautology.md`: sources of vacuity (conjoined exclusive flags, assuming
  what is asserted, resource hypotheses that swallow the theorem, contradictory numeric side
  conditions, char-2 degeneracies); coverage (one clause per admissible case; both directions);
  trust closure (`:171-209`) — "`./scripts/audit-lean.sh` is a **lexical** gate" and "does not
  inspect the kernel's axiom closure" (that text predates CI enabling the kernel audit, see §5).

**`adversarial-review`** (`SKILL.md`, 177 lines) [V]: three passes — A specification (non-vacuity,
semantic not tautological), B fidelity (against the pinned source), C hygiene — "Pass A and Pass B
must be run independently" (`:32-35`); B-before-A only for Category B; for Category A "a
specification that matches `cpu/verify.rs` line for line is evidence of confirmation bias"
(`:46-53`). "Do not report a suspected defect you could have checked" (`:128-143`). Findings ranked
with "the concrete failure — the input, flag setting, or prover deviation the defect admits"
(`:163-166`). After review, the author implements every fix and fills a disposition table
(`:145-159`). Its `references/specifications.md` A4 lists what tooling cannot catch: assumed
interfaces, bridging assumptions.

**`human-review-audit`** (`SKILL.md`, 314 lines) [V]: deliverable for a domain expert who does not
read Lean: header/map, vocabulary ("Domain word first, Lean name after"), a oneline index of every
load-bearing definition and theorem, close reading with a plain-language equivalent, and "the
trusted surface, every hypothesis and external fact the reader has to accept".

[I] Relevance to recursion.fast: these give a ready-made *contract audit protocol*: (a) every
trusted definition gets a guard (inhabited) theorem and a negative control in the verification
repo; (b) a published "nearby false statements" list; (c) a human-readable audit document of the
trusted contract in `human-review-audit` format; (d) adversarial review of submissions' *statement
use* is unnecessary if the contract fixes the statements (sig.golf/ots.golf style), but the review
discipline applies to the contract itself.

---

## 5. CI and trust closure

[V] `docs/ci.md:6-15`: required checks `CI` (build, Lake tests, "audit production and test axiom
dependencies with a negative control", test root with warnings as errors), `Repository policy`
(lexical trust markers + planted violations), `Imports and layers`, `Documentation integrity`;
informational `Build timing`, `PR summary`/`PR review` (LLM via OpenRouter; summary uses
`pull_request_target` "without checking out or executing pull-request code"), `Upstream drift`.

Three independent trust gates [V]:
1. **Lexical** `scripts/audit-lean.sh:7-10`: `rg '\b(axiom|sorry|admit|unsafe|native_decide)\b'`
   over `LeanerVM LeanerVM.lean tests`, plus `check-lean-options.py` (no local option overrides).
2. **Kernel, production**: `.github/workflows/ci.yml` uses `leanprover/lean-action@v1.6.0` with
   `axiom-audit: true`, `axiom-audit-root: LeanerVM` ("no declaration under `LeanerVM` may depend on
   an axiom outside `propext`, `Classical.choice`, `Quot.sound`").
3. **Kernel, production + tests**: `scripts/audit-axioms.lean:17-28` iterates `env.constants`,
   for names prefixed `LeanerVM` or `LeanerVMTests` runs `collectAxioms`, rejects anything outside
   the three; `scripts/test-axiom-audit.py` adds a negative control "check[ing] transitive rejection
   through production and test declarations in a temporary fixture" (`docs/development.md:28-38`).
   Spine review reports "the axiom audit reports 2757 declarations and no unexpected axiom"
   (`reviews/protocol-spine.md:25-26`).

Timing [V]: `Build timing` workflow measures clean build, warm build, `lake test`
(`.github/workflows/build-timing.yml`); "Do not make timing a merge gate" (`ci.md:17-21`). CI job
timeout 30 min (with Mathlib cache). No aggregate build time is documented. Recorded data points:
`decide +kernel` order checks 18–36 s; table files 10–21 s each; `Statement.lean` test 2 min 15 s
(`leanisa-status.md:1006-1039`); table-sumcheck test 327 s of interpretation reduced to 1.3 min
(`reviews/protocol-table-sumcheck.md:16, 102-103`); "an `E` multiplication costs about 2 ms in the
interpreter and an inversion about 1 s" (`protocol-status.md:482`), so honest-prover runs are only
feasible on tiny toy instances.

[I] Gaps relevant to an adversarial setting: the lexical/`collectAxioms` gates do not catch
`implemented_by`/`@[extern]` (affects `#eval`/compiled code, not kernel proofs), statement drift
(handled in ots/sig.golf by comparing exported statements against the trusted ones), or semantic
vacuity — leanerVM relies on review for the last; recursion.fast cannot.

---

## 6. leanISA and leanVM recursion cost

### 6.1 The ISA [V]

`LeanerVM/Semantics/Instruction.lean:57-72`: six opcodes over `K = GF(2^64)` addresses and
`E = GF(2^192)` cells: `xor` (`[o_C] = [o_A] + [o_B]` in `E`; ADD is XOR in char 2),
`mulNative` (product in `E`), `setConstant`, `deref` (three modes), `jump` (conditional, to
`([o_d],[o_f])`), `blake2s` (compression of four message cells). Addresses are powers of a
generator `g` (instruction `i` at `g^i`). Memory is a **write-once image committed by the prover**;
the Semantics directory is 1,523 lines incl. executable carriers; the talk claims ≈250 lines of
audited ISA spec. Reference semantics `step`/`run`/`ValidExecution` are noncomputable; a computable
checker is proved equal (`checkTrace_eq_true_iff`, `docs/leanisa-checker.md:11-30`): "its bodies
may hold speedups and are not audited, only the equivalence statements are" — [I] a useful pattern
for recursion.fast's cost harness (trusted noncomputable semantics, untrusted fast carrier with a
proved equivalence).

ots.golf's leanISA track (`ots.golf-dev/AGENTS.md:167-201`, `docs/AUDIT.md:119-150`) [V]: semantics
taken as a Lake dependency on leanerVM `8563b05b`, BLAKE2S replaced by the shared random oracle;
cost 1 cycle per instruction, 10 per `BLAKE2S`, +120-cycle surcharge for the statement re-derivation;
"leanVM's memory is committed by an untrusted prover and no instruction writes, so the machine has
no accept/reject output" — a certificate proves `Faithful` (honest image reproduces the verifier's
decision) and `Sound` (no committed image at any admissible `κ ∈ [16,32]` completes on a rejected
input). `maxProgramLogSize = 18` is "load-bearing, not hygiene: `Program.code` is a function, so
`κ_bc ≤ 32` alone would admit a free constant-time lookup table". Seeded+finalized rows
`< 2^20`. [I] For recursion.fast a leanISA track would make the cost model "rows of the
recursion circuit" directly, with native `E` multiply and hash — much closer to "cost of 2→1
recursion" than RV64IM cycles — but the verifier is a relation, not a program with an output, which
changes the faithfulness theorem's shape (two directions, quantifying over prover images).

### 6.2 leanVM numbers [V] (`leanVM/README.md`, Mac M4 Max, at `a386121f`)

| Workload | VM steps | Proof size | Prove | Verify (native) |
|---|---|---|---|---|
| 900 XMSS aggregation (rate 1/2) | 1,571,001 (2^20.58) | 296.1 KiB | 0.818 s | 16.8 ms |
| 245 SPHINCS (rate 1/2) | 2,629,855 (2^21.33) | 320.8 KiB | 1.082 s | 15.5 ms |
| **2→1 recursion**, leaves of 900 XMSS, `--log-inv-rate 2` (`README.md:74-79`) | **686,085 (2^19.39)**; MUL 31.4 %, DEREF 31.0 %, XOR 25.1 %, SET 5.9 %, JUMP 4.0 %, BLAKE2S 2.7 % (2^14.17 ≈ 18.4k compressions); MEMORY 2^19.68; TOTAL_COMMITTED 2^24.66 | 206.3 KiB | 0.394 s | 14.6 ms |
| Flock batch, 2^18 BLAKE2s compressions | — | — | 540 ms | 1.9 ms |

Security claim: "128-bit (LDR Johnson, no proximity gaps conjecture)" (`README.md:120-122`); PCS
WHIR; binary tower of 192 bits; Flock for BLAKE2s; ring switching, M3 (Binius lineage).
[I] So one in-circuit child verification + node bookkeeping (statement rebuild, coverage of 1,800
signer slots, deferred-claim batching) costs ≈343k leanISA steps; the guest bytecode size is printed
by the benchmark (`crates/rec_aggregation/src/benchmark.rs:169-174`) but not documented. The guest
is `crates/rec_aggregation/guests/aggregate.py` (3,538 lines of zkDSL). These numbers are a useful
reference point for "what an optimized hash-based recursion step costs", but they are leanISA steps
with native GF(2^192) multiply and BLAKE2s, not RISC-V cycles.

---

## 7. Implications for recursion.fast

### 7.1 Directly reusable [V for existence; I for recommendation]

- **Security definitions**: ArkLib's `perfectCompleteness` and
  `rbrKnowledgeSoundnessWorstCaseWith` (named `WitMid`, extractor, `KnowledgeStateFunction`,
  per-challenge error `ChallengeIdx → ℝ≥0`). Prefer the `With` form; the existential form proves
  soundness only. Note that the RBR→plain KS implication is `sorry` in ArkLib at both `7653a901` and
  `db7005f84`; target RBR KS directly (which is also what BCS/FS needs) and do not depend on the
  implication.
- **Composition machinery**: `Component.{Def,Guarded,Complete,Security}` + `append`
  (`ToArkLib/Component.lean`, 318 lines) and the #615 port (`ToArkLib/KnowledgeAppend.lean`); the
  spine pattern "the contract fixes seams and slot errors; submissions fill holes".
- **Components** (all ArkLib candidates, generic over the field): `Sumcheck.plain/normalized` with
  `d/|F|`, `Sumcheck.transport` (wire-compressed round messages), `Component.batch` (`(k−1)/|F|`),
  GKR grand product, fingerprint/collision, `queryCheck`, pass-through, send-oracle. A baseline
  R1CS verifier (Spartan-like: zerocheck sumcheck + batched evaluation claims + opening) could be
  assembled largely from these, but they are in a binary-field, inner-product-oracle setting and
  pinned to Lean v4.34.1/ArkLib `7653a901`.
- **Negative controls**: `Verifier.not_rbr`, `not_rbr_zero`, `not_rbr_of_escape`,
  `Reduction.not_perfectCompleteness_of_reject` (`ToArkLib/Refutation.lean:107-163, 242-300`), with
  the accept-all/reject-all examples (`:326-375`). These can be contract-side guard theorems that
  prove the contract's definitions are not vacuous.
- `Refinement.knowledge_transport` (move KS along a witness map at the same error) — needed to
  transport from an "internal" relation (e.g. committed polynomial) to the R1CS relation.
- **Policy/process**: three-gate axiom audit with negative control; "nearby false statements"
  catalogue; disposition-table reviews; Category A/B discipline; `human-review-audit` for the
  contract's audit document.

### 7.2 What the recursion open problem implies for the batcher definition [I]

1. **"V accepts π1 and π2 ⇒ V accepts π′" is completeness only.** The load-bearing direction is
   knowledge: from a prover convincing the batched check one must extract witnesses for *both*
   input instances. leanth's `multi_isKnowledgeSound` controls show that product extraction
   needs both component security and relation maps.
2. **Model the batcher as an interactive reduction of knowledge, not as a program over proofs.**
   In the IOP/interactive model (which the brief already prefers), there is no "verifier inside the
   proved relation" and no random oracle inside the relation: a 2-to-1 batch step is an ArkLib
   `OracleReduction` from `R_acc × R_acc` (two accumulated instances, witnesses with the prover,
   commitments as oracle statements) to `R_acc`, plus an embedding reduction `R1CS → R_acc` and a
   decider `R_acc → ⊤`. RBR KS composes sequentially with additive per-challenge errors and a
   composed straight-line extractor (leanerVM's ported append), so a tree of depth `d` / `N−1`
   batch steps has an explicit error sum. This is exactly the leanVM deferred-claims design
   (§2.3): accumulator = pending evaluation claims, decider = root discharge.
3. **What it can honestly claim**: "in the ideal oracle (information-theoretic) model, any prover
   that makes the composed verifier (embed ⟫ batch-tree ⟫ decide) accept with probability above
   `Σ ε` yields, by the named straight-line extractor, R1CS witnesses for every leaf instance". What
   it cannot claim: security of the deployed recursive SNARK where the batch verifier is compiled
   (BCS/FS with a concrete hash) and itself proved inside the next proof — that is leanerVM's T6,
   which has no known ROM proof (2024/728). The report must name this as a deployment heuristic,
   never as a theorem hypothesis or axiom.
4. **Constant-size accumulator is a contract requirement**: otherwise "batching" by concatenation
   (`R × R → R × R`) is trivially sound and complete. Fix the statement type of `R_acc` to be the
   same at input and output (type-level), and/or charge its size in the cost; leanVM: "a statement
   stays one size however deep the tree".
5. **Depth and error accounting**: state the tree theorem for a fixed shape (or depth `d`) with
   error `Σ` over all batch reductions; "A bound on child arity alone does not bound depth"
   (`architecture.md:343`).
6. **Inner vs final verifier**: allow `V_batch ≠ V_final` via the decider; score the per-step
   batch verifier (the recursion cost) and the decider separately.
7. **Errors fixed by the contract**: the submitter must not choose the error function; either the
   contract demands `Σ ε ≤ 2^{−λ}` over a fixed challenge-space size, or it fixes per-round budgets
   (decision 20 lesson).

### 7.3 A critical caveat: knowledge soundness without extractor efficiency [I, argued, not machine-checked]

leanerVM states "Knowledge soundness of `verify` is claimed in the information-theoretic sense
(Lean does not measure running time)" (`blueprint:329`), and the talk lists extractor running time
as an open problem. Consequence for an adversarial competition: if the witness type is finite with
decidable relation (R1CS over a finite field with fixed sizes), a computable *brute-force*
extractor exists. With `kSF.toFun m s tr w := (s, w) ∈ R` for all `m` and `extractMid`/`extractOut`
returning a brute-force witness whenever one exists, `toFun_empty/next/full` hold and the bad event
is empty for statements in the language. So "RBR KS with a computable extractor" collapses to (RBR)
soundness for statements with a witness, and an accept-all verifier passes on any relation whose
language is everything (e.g. a hash-preimage relation whose statement space is the hash range).
leanerVM's refutation lemmas require `hin : ∀ w, (s, w) ∉ relIn`, i.e. they only bite on false
statements. Recommendations: (a) require the extractor to have a fixed structural form, e.g.
leanerVM's `piopExtractedStack_eq` pattern — the extracted witness is a contract-fixed decoding of
the committed first oracle message — so efficiency is by construction; (b) state soundness for the
general R1CS relation over arbitrary (including unsatisfiable) instances, where soundness is
meaningful; (c) add a contract guard theorem showing the accept-all verifier fails the contract.
This should be probed in Lean (P2 / A2).

### 7.4 Suggested phrasing (sketch) [I]

```lean
/-- Trusted. A 2-to-1 batch step: an oracle reduction from two accumulated instances to one,
over the contract's accumulator relation `Racc` (same statement type in and out). -/
structure Batcher (Racc : Set ((Acc × ∀ i, AccO i) × AccW)) where
  red : OracleReduction []ₒ (Acc × Acc) (fun i => …) (AccW × AccW) Acc AccO AccW pSpec
  ext : Extractor.RoundByRound … -- must be of the contract's fixed form (7.3)

/-- Trusted requirement on a submission. -/
def Batcher.Secure (B) (ε : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  B.red.perfectCompleteness init impl (Racc.pair Racc) Racc ∧
  ∃ kSF, B.red.verifier.toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
           (Racc.pair Racc) Racc WitMid B.ext kSF ε
```

plus contract theorems (proved once, by the organizers): the tree composition
`embed ⟫ batchTree d ⟫ decide` is complete and RBR-KS from `R1CS^(2^d)` to `⊤` at the summed error,
with a named extractor; and the guard/negative-control theorems of §7.1. The report text: "The
batcher theorem certifies the information-theoretic interactive batching reduction. It does not
certify the security of a recursive SNARK obtained by compiling the batch verifier with a hash
function and proving it inside the next proof; that step is the open recursive-extraction problem
(leanerVM T6; Barbara–Chiesa–Guan 2024) and is a named deployment assumption."

### 7.5 Other implications [I]

- Use leanerVM's toolchain/pins (Lean v4.34.1, ArkLib `7653a901`) if reusing its `ToArkLib`
  components; ArkLib HEAD is v4.34.0 (PLAN §0), so a pin decision is needed (P1).
- Lean-interpreted honest provers are slow (≈2 ms per `E` mult, ≈1 s per inversion), so
  completeness should be proved, not evaluated; fixtures only on toy sizes.
- leanVM's 2→1 recursion (≈686k leanISA steps per node with two children) is a realistic target
  scale for a "recursion circuit" cost; a RISC-V verifier on generic R1CS will be far more
  expensive per step; comparisons across ISAs need the non-hash instruction count (ots.golf lesson).
