# Exploration brief: a relativized-NARK design for recursion.fast

Shared context for every agent on branch `explore/relativized-nark` (worktree
`/home/devops/Verified-zkEVM/recursion.fast-relativized`, based on `05fde28`, the committed head of
`v3/rules-handoff`). Read this whole file before starting. The orchestrator wrote it on 2026-10-20.

## 0. Ground rules for agents

- Write only inside this worktree, and only the files your task names. Never edit
  `/home/devops/Verified-zkEVM/recursion.fast` (main), `/home/devops/Verified-zkEVM/recursion.fast-rules`
  (the user's live rewrite, which has uncommitted work), the submissions repository or
  `/home/devops/CambridgePQ/`. Read them freely.
- Do not commit. The orchestrator commits.
- Every Lean build or probe gets a `timeout` (for example `timeout 900 lake build RecursionFast.Explore.Foo`
  or `timeout 600 lake env lean file.lean`). If a single module takes more than a few minutes, find
  out why (`ps -eo pid,etime,cmd | grep lean`), do not wait. `.lake/packages` is a symlink to a
  prebuilt shared tree: never run `lake update`, never rebuild Mathlib.
- Mark every claim with its evidence: **kernel** (a Lean theorem, file and name), **paper** (an
  argument; cite page/section), **measured** (a log), **estimate**. Do not present an estimate as a fact.
- Audience of the final report: world-class cryptographers and zkVM engineers, plus formal-methods
  readers who know less cryptography. Write notes concisely: the conclusion first, then the argument.
  No filler, no restating this brief.
- The user is not available. Resolve ambiguity yourself, say how you resolved it, and move on.

## 1. The user's idea, verbatim

> autoresearch agents can submit a Lean 4 verifier function (or RISCV bytecode) which we prove to be
> knowledge sound and imperfect complete (with very small error) in the ROM for a relation
> R = {(x, w) where x = H(w) } and H is a concrete hash function such as Blake2s. We allow the
> autoresearch agent to produce a prover (in rust or lean) which is executable and then force it to
> prove a million hash chains which we measure the geomean/average/median wall-time of as the cost
> model. In order to ensure that the verifier is amenable to recursion, we force it to be knowledge
> sound in NP^H (i.e. a reletavized NARK), where the relation is 2->1 or 1->1 recursion which also
> allows random oracle queries. We add a extra term (addition, multiplication, whatever) by
> measuring the cost of proving a random oracle call from the previous wall-time measurement. Note
> that impossibility results for reletavized SNARKs exist for certain relations, so you should be
> constantly aware that it may be impossible to write a verifier which satifies these security
> definitions. I'm hoping to find a workaround this impossiblity result by having you generate a
> baseline which is compressing (but not necessarily succint), or our relation happens to be
> provable for our reletavized relation.

The user's goal for the competition (their words): a "big brother" to snark.fast that pushes agents
to design "a Flock 2.0" (Flock = ePrint 2026/1329, leanVM's BLAKE2s-proving protocol): verifier
architectures that are recursion-friendly and extremely fast at proving hash functions, while
**constraining agents from making adversarial or trash submissions**. The motivating defect of v3 is
O-25: a verifier certified in the ROM that recognises the deployed hash (BLAKE2s) and accepts a magic
proof (Canetti–Goldreich–Halevi uninstantiability).

## 2. What v3 is (read the sources, these are pointers)

- Design: `docs/DESIGN-v3.md` in the rules worktree `/home/devops/Verified-zkEVM/recursion.fast-rules`
  (newer than this worktree's copy; includes uncommitted amendments V3-S2R-A1…A7).
- Contract: `RecursionFast/Contract/{Oracle,Relation,Security,Certificate}.lean` (this worktree has the
  committed potential-form `KState`; the rules worktree adds `OProg.bind`, `failProb`,
  `CompleteWithError`, the step-counting extractor machine).
  - `Rel Vb` (Relation.lean): leaf = `n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n` with **concrete**
    BLAKE2s; node = `c = nodeStmt c₁ c₂ ∧ Vb c₁ π₁ ∧ Vb c₂ π₂` where `Vb` is `V` run with the
    **concrete** oracle `blake2sOracle q = BLAKE2s(0x52 ‖ q)`.
  - `KState R V E ε` (Security.lean): potential `μ : Log → ℝ≥0`, `empty`, `step` (average rise ≤ ε per
    fresh query, within `logCap = 2^96`), `final` (`μ L < 1` and `V.runLog L c π = some true` ⇒ `E`
    extracts `w` with `R c w`). Paper theorem: advantage ≤ `(Q + qV)·ε`.
  - `KS` = a `KState` exists ∧ `V` asks ≤ `qV` queries. `errorCap = 2^-128`.
- The heuristics v3 does not claim (DESIGN §5.4): composition across tree levels; BLAKE2s is a random
  oracle; O-25 (a certified `V` may recognise the deployed oracle; `Controls/Backdoor.lean` is a
  kernel-checked certified backdoor).
- Open issues on GitHub `scaraven/recursion.fast` (#4 O-25, #5 KS unsatisfiable (fixed by the
  potential), #6 `T_V` does not exclude witness-sending and board T does not reward recursion, #7 node
  extraction is decoding, #8 honest recursion under the caps). Local copies:
  `SP/issues/issue-<n>.md`.
- Prior O-25 work (do not re-propose what it rejected without saying why the new setting differs):
  `/home/devops/Verified-zkEVM/recursion.fast-submissions/docs/snark-baseline/notes/F2-o25-uninstantiability.md`
  (candidates A parametric-V, B salt/beacon/keyed oracle "dead because the recursion evaluates the
  oracle", C oracle families, D standard-model, E typed interface + review) and its review
  `.../docs/reviews/F2-o25-review.md` (E broken). F2's key sentence: "the only way to make the
  instantiation unknowable is to make it external, which recursion forbids." **The relativized idea
  changes exactly this premise**: if the node relation is relativized, nobody arithmetises the oracle,
  so the oracle can be external and secret.
- A real certified leaf SNARK exists: `spartan-chain` (submissions repo,
  `docs/stages/V3-S2b-RESULT.md`): Spartan + Ligero over GF(2^64), BLAKE2s R1CS. At `n = 2^14`:
  proof 1,464,107 B, 5,156 oracle queries, Rust prove 7.4–8.0 s (32 vCPU VM), native verify 0.8 s.
  Witness-sending root check for the ranked tree (r = 8, n = 2^14): 21 s reference Lean, 37–43 ms
  unrolled + threads (issue #6).
- Designs v1/v2 and the user's decisions: `/home/devops/CambridgePQ/recursion.fast/DISCUSSION.md`
  (Q1–Q6), `design/`. v3 decisions V3-1…V3-12 in DESIGN-v3 §1.2 (notably V3-5: ROM only, no groups,
  pairings, lattices).
- The impossibility paper: Barbara, Chiesa, Guan, "Relativized Succinct Arguments in the ROM Do Not
  Exist" (ePrint 2024/728, version of 2025-09-23). Text: `SP/paper/paper.txt`; PDF
  `/tmp/reletavized-snark-in-rom-do-not-exist.pdf`. Main results: `DTIME^O[t] ⊄ NARG^O[vq = o(t)]`,
  `NTIME^O[t] ⊄ NARG^O[as = o(t)]`, also for interactive and computationally sound arguments. Its
  §1.2 notes that relativized SNARKs exist in other oracle models (SROM [CT10], LDROM [CCS22], AROM
  [CCGOS23]) and that a ROM SNARG becomes a relativized NARK "by sacrificing succinctness" [CGSY24].

`SP` = `/tmp/claude-1000/-home-devops-Verified-zkEVM-recursion-fast/def0cdd4-333d-4119-a8bb-365ff3790edf/scratchpad`.

## 3. The orchestrator's reading of the idea, and the variants under study

The prompt is ambiguous in places; the orchestrator resolved it as follows. Agents may argue for a
different resolution in their notes.

- **`H` is overloaded.** In "R = {(x, w) : x = H(w)}, H concrete" the leaf hash is concrete BLAKE2s.
  In "NP^H" the superscript is the random oracle. We keep the leaf relation **concrete** (as in v3),
  because a leaf relation over the oracle itself (`x = O^n(w)`) is exactly the hard relation family of
  the paper: its verifier would need Ω(n) oracle queries and no argument could compress it.
- **The relativized node relation.** `RelO`, the oracle relation of the knowledge game:
  `RelO^O c (node c₁ c₂ π₁ π₂) := c = nodeStmt c₁ c₂ ∧ V^O c₁ π₁ ∧ V^O c₂ π₂`, the *same* oracle `O`
  the adversary and the verifier query (v3 uses concrete `Vb` here instead). In the potential form the
  natural statement reads the child verdicts from the log: `final : μ L < 1 → V.runLog L c π = some true →
  ∃ w, E c π L = some w ∧ RelL L c w` with the node clause `V.runLog L cᵢ πᵢ = some true`. 1→1 (IVC) is
  the case of one child.
- **Variants.**
  - **D1, priced recursion, not run (closest to the prompt).** Certify `KS` for `RelO` and completeness
    with error. Benchmark: prove many independent leaves (chains); score = a statistic of leaf wall time
    plus (or times) a charge `c_RO` for the verifier's oracle calls, priced at `t_hash` = measured cost
    of proving one hash, taken from the leaf measurement (for example `T_leaf / n`). The recursion is
    never executed.
  - **D2, relativized tree in the pure ROM.** v3's whole-tree benchmark with `RelO`; the oracle at
    deployment is a harness service (secret-keyed PRF), never arithmetised; score = `T_tree` plus a
    charge per verifier oracle call. Root check runs `V` online against the service.
  - **D4, attested oracle (orchestrator's candidate workaround, to be attacked).** As D2, plus the
    service offers `certify(list)`: it checks that every `(q, a)` in `list` is a genuine answer, stores
    `h = BLAKE2s(enc list)` and later answers `attest(h)`. A node proves in-circuit that each child is
    accepted by `V` answering from a list whose hash it computes, and the hashes are attested (flat:
    the root proof carries one hash per inner proof and the root verifier attests each; recursive:
    `certify` also accepts previously attested hashes, so the root verifier makes one `attest` call).
    The in-circuit cost of a child's oracle calls is hashing their `(q, a)` list with concrete BLAKE2s,
    about the cost of computing those hashes in a real public-hash recursion. Claimed properties, to be
    checked: CGH closed (the oracle is secret, nothing arithmetises it), composition across the whole
    tree provable from one log, root verification compressing (not necessarily succinct), no proxy
    term needed. This leaves the pure ROM: it is an SROM-like model with the harness as the
    "signature card" and online verification at the root.
  - **D3, signed oracle (SROM proper).** As D4 but the service signs lists with a hash-based signature
    that the circuit verifies; no online attestation.
  - **v3** as the comparison point.

## 4. Questions the exploration must answer

1. Is the user's design (D1, and its tree form D2) well defined, non-vacuous and tight? What does the
   relativized requirement actually force?
2. What exactly does the impossibility result rule out for this relation, and what does it leave
   open (a compressing but non-succinct baseline; a relation for which relativized arguments exist)?
3. Does it close O-25? Under what deployment of the oracle?
4. Incentives: what wins under each variant (recursion, concatenation, witness-sending, flat SNARK)?
   Cost model: what to measure, how the oracle charge is gamed, which statistic.
5. Is there a workaround (another oracle model, a harness capability) that gives real recursion,
   closes O-25, and keeps the trusted base small? What does it cost?
6. Which of these can be checked in Lean now (probes), which are paper arguments, which are open?
