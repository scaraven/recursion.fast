# recursion.fast: the design record (v3, and the v4 proposal)

**State of play (2026-10-26).** **v4, the signed-random-oracle (SROM) rules, is the proposal now
implemented on the branch `v4/srom-rules`**, not yet adopted by the user: v3's certificate kept,
O-25 closed by the oracle's deployment (a secret-keyed BLAKE2s service that signs the answers each
proof used, checked by one trusted predicate `acc`), x86-64 assembly provers timed on GitHub-hosted
runners with attested results, and (since V4-A11, 2026-10-28) one pure-IVC stream scored
`S = P̄ + V̄` with no proof cap (the score was `S = T_tree + K·t_link` before). Its normative design is
[`DESIGN-v4-srom.md`](DESIGN-v4-srom.md); its build record (the brief, the design attack, the stage
results) is under [`v4/`](v4/). On 2026-10-26 the user trimmed it (V4-A9, design §4.4: 30-minute
jobs, one run each of the tree and the stream, the organiser's checks in the core CI only,
`errorCap = 2^-120`, `completenessCap = 2^-40`). On 2026-10-27 the user made the certificate state
textbook single-output knowledge soundness, the potential becoming a library route to it (V4-A10,
design §1.4, §2.4: the tree then composes by a union bound, about `2^-81` against `2^-90`). The
next paragraph is the record v4 starts from.

**v3.** The third iteration of the competition, v3 (a non-interactive argument in the
random-oracle model over a digest relation, scored by whole-tree wall time), was
built as far as a trusted contract, a certified witness-sending entry, a certified honest leaf
SNARK entry (Spartan over GF(2^64) with a Ligero commitment, `HARNESS: ACCEPT`), and a rules stage
that amended the security definitions. It then hit a wall: among the designs examined in the
O-25 design track, the random-oracle uninstantiability gap could be closed only by taking the
verifier away from the submitter, which the user rejected as too narrow for an autoresearch
competition (a separate exploration, the relativized node relation with an attested secret
oracle, proposes closing it by the deployment instead and was not put to the user); and, by
paper estimate, only a WHIR-class commitment fits the caps at node size, "yes, barely", with no
Lean proof behind it, while every other way to make room changes the trusted base (the honest
entry measured only that a Ligero leaf does not fit). The user decided to go back to ideation.
The code was archived and the trusted core's `main` stripped to a skeleton; everything learned
lives in the three v3 documents below, which also incorporate and close the GitHub issues #1, #4,
#5, #6, #7, #8, #9 and #10.

## The documents

| File | What it is |
|---|---|
| [`DESIGN-v4-srom.md`](DESIGN-v4-srom.md) | **The v4 design (SROM), a proposal implemented on `v4/srom-rules`.** The relation with signed children and the one acceptance predicate `acc`; the contract-fixed hash-based signature; why no certified verifier can trust a signature; the deployment argument that closes O-25; textbook single-output knowledge soundness (V4-A10); composition across the tree (kernel walk and union bound, paper reductions); the signature's EUF-CMA statement; the trust statement; the service, the sandbox, the assembly prover, CI as the attested trusted machine, the measurements and the season-1 score; incentives, the consequences that bite, the trusted base, and every decision taken in the user's absence. Its checks against C1–C15, the O-25 criteria and the earlier proposals' decisions are [`v4/CHECKS.md`](v4/CHECKS.md). |
| [`v3-design-agent-written-ROM-SNARK-verifier-for-BLAKE2s-hash-chain-trees-with-Lean-certified-knowledge-soundness.md`](v3-design-agent-written-ROM-SNARK-verifier-for-BLAKE2s-hash-chain-trees-with-Lean-certified-knowledge-soundness.md) | **The design.** v3 as it finally stood, self-contained: the pitch, the relation, the submission, the security definitions as amended (potential-form knowledge soundness with `logCap`, completeness with error `2^-128`, the step-counted extractor language with a proved bound), scoring, the trusted base, the harness and the two-repository model. Then the record: the issues incorporated, the user's decisions, the open problems, the constraints any next design must satisfy, and the design space for the next iteration. |
| [`v3-lessons-from-building-a-witness-sending-entry-and-an-honest-Spartan-Ligero-SNARK-entry.md`](v3-lessons-from-building-a-witness-sending-entry-and-an-honest-Spartan-Ligero-SNARK-entry.md) | **The iterations and the measurements.** Stages S1, S2a, S2-KS, S2b and S2R, what each review found, the cost by component (lines, theorems, build and check times), proof sizes, prover and verifier times, the second-kernel finding, the proof-size analysis, what reuse cost, and process lessons for agent-driven development. Every number names its log, its kernel theorem, or (for a handful of figures that exist only as text in the stage reports) says so. |
| [`v3-open-problem-ROM-uninstantiability-CGH-backdoors-and-why-each-proposed-fix-failed.md`](v3-open-problem-ROM-uninstantiability-CGH-backdoors-and-why-each-proposed-fix-failed.md) | **The open problem O-25**, condensed but complete: the kernel-checked backdoor, its disguises, the two design rounds (Candidate E, Candidate T) and the reviews that broke or narrowed them, the post-hoc challenge verification attack, the "fields as data" variant, the user's rejection, the literature, the precise impossibility statement, the criteria a satisfying solution must meet, and (§13) the relativized-NARK exploration that proposes closing O-25 by the deployment. |
| [`DESIGN-relativized-recursion.md`](DESIGN-relativized-recursion.md) | **A design proposal, not in force** (PR #14): the relativized node relation with an attested secret-keyed oracle (D4), compiled from the `explore/relativized-nark` exploration, with its decisions, costs, incentives, trust statement, build order and the user's open decisions. |
| [`CGH-circumvention-guide-secret-keyed-signed-and-attested-random-oracles-with-reading-list.md`](CGH-circumvention-guide-secret-keyed-signed-and-attested-random-oracles-with-reading-list.md) | **A guide to closing O-25 by the oracle's deployment**: why a secret key removes the CGH trigger, why it alone breaks recursion, the signed (SROM, D3) and attested (D4) fixes, what an evaluation would check and cost, D4 against the O-25 criteria, a reading list with links, and a map of where everything is. The on-ramp to the D4 proposal. |
| [`DESIGN-cost-incentive-model.md`](DESIGN-cost-incentive-model.md) | **A scoring proposal, not in force**: `S = T_tree + K · t_link`, whole-tree wall time at the long shape (`r = 4`, `n = 2^20`) as the chain term plus a weighted recursion term measured on a stream of short chains, each added to a running proof by a fresh prover process on the clock; why one wall time cannot weight recursion, the measurement protocol, the calibration of `K` from the leading entry, incentives, residual risks and the user's decisions CM-1 … CM-8. Answers v3's #6 (b) and C7 and the D4 proposal's RU-4. Its review is [`reviews/DESIGN-cost-incentive-model-review.md`](reviews/DESIGN-cost-incentive-model-review.md). |
| [`reference/`](reference/) | The research notes behind the design: `neighbouring-competitions.md` (ots.golf, sig.golf, the Proximity Prize, leanerVM; what was taken from each and what to re-check when a rule changes; its §5 table is as of the 2026-10-19 design and says so), `notes/` (R1 ots.golf, R2 sig.golf, R3 Proximity Prize, R5 leanerVM), and `papers/` (redistributable copies of papers the designs rely on, with licence and version; now CGSY24). |

For v4, read [`DESIGN-v4-srom.md`](DESIGN-v4-srom.md) §0 first. For the record, read the v3
design; its §1 is the one-page summary. The other two v3 documents are its
companions and are cited from it; the D4 proposal and the CGH guide came after v3 stopped. A
reader-only path: Design §1, then §15–§17; O-25 §0, §10, §11 and §13; Lessons §5 and §8.4; for the
next direction, the CGH guide's §0 and the D4 proposal's §1; the rest as needed.

## Where the code went

- **The v3 trusted core** (contract, library, controls, harness tools, stage records, reviews,
  the design and its amendments ledger) is on the branch `v3/contract-archive` of
  https://github.com/scaraven/recursion.fast, head `f4de3b8`; its contract state is `6202402`.
  Its history: `15e4ae5` (`main` before PR #11: stage S1 plus the removal of the v2 tree) →
  `ecdcbd5`, `c3f6380`, `05fde28` (the knowledge-soundness amendment, PR #11, merged into `main`
  as `059812f` on 2026-10-22) → `4b3356a` (stage V3-S2R, the rules) → `ef7349a` (its review) →
  `6202402` (its fix pass and golf) → `c198bc3`, `f4de3b8` (the `evidence/` folder: the kernel
  probes the documents cite, with their logs, and the two interim harness series as patches;
  `evidence/README.md` is the index). The branch is the reference whenever a document below
  cites a file under `RecursionFast/`, `scripts/`, `docs/` or `evidence/` of the core.
- **The relativized-NARK exploration** is on the branch `explore/relativized-nark` of the same
  repository, head `043bcb3` (2026-10-20 to 22; based on `05fde28`): the user's relativized node
  relation, its impossibility analysis, the attested-oracle workaround D4 with the W5 and D4+
  variants, 21 untrusted Lean probe modules, and an adversarial review. Not merged, not archived
  elsewhere, not put to the user; summarised in the O-25 document §13 and listed as direction
  D-L in the design's §17.1.
- **The v2 tree** (chips + CCS relation, the organiser's Merkle plus Fiat–Shamir compiler, the
  RISC-V extractor machine, the v2 harness and baseline) is at the core's tag `v2-archive`
  (`git show v2-archive:docs/DESIGN.md`).
- **The submissions repository** https://github.com/scaraven/recursion.fast-submissions is not
  changed by this PR. It holds the two entries (`submissions/baseline/`, the witness-sending
  argument; `submissions/spartan-chain/`, the honest leaf SNARK), the rulebook `AGENTS.md`, the
  honest-baseline plan, blueprint, notes, reports and reviews under `docs/snark-baseline/`,
  `docs/reviews/` and `docs/stages/`, and a `.contract` submodule pinned at `15e4ae5`. Neither
  entry is certified against the archived contract: S2a is certified at `15e4ae5` and the honest
  entry at `05fde28`, both with the interim harness. Its guidance (`CLAUDE.md`, `AGENTS.md`,
  `docs/README.md`) still describes DESIGN-v3 as the design in force and stage S2 as the task in
  front of it; that guidance is frozen as of 2026-10-22. Its branch `v4/flock-baseline` moves the
  pin to this branch (`81e1ebf`), replaces the guidance with the v4 rulebook and adds the first
  certified v4 entry, `spartan-srom`.
- **Logs** (`logs/` in both repositories) are gitignored and local to the development VM; the
  lessons document (§9) says which log each number comes from and which probes were archived.
- The core's `main` was stripped to a skeleton when v3 stopped (this `docs/` folder, a stub Lean
  root, and the build, licence and guidance files). The branch `v4/srom-rules` adds the v4
  contract, library and controls (`RecursionFast/`), the service, runner and workflows, and the
  v4 build record (`docs/v4/`); the v3 code stays on the archive branch above.
