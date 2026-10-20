# V3-S2R review: the rules stage (extractor program, completeness with error, gate rule 4, library)

## Scope, method and runs

Reviewed 2026-10-20 by an agent independent of the implementation. Object: commit `4b3356a` on
branch `v3/rules-handoff` (worktree `/home/devops/Verified-zkEVM/recursion.fast-rules`), that is
`git diff 05fde28 4b3356a`, plus the KS amendment `15e4ae5..05fde28` where the stage depends on it.
Inputs: the handoff (`recursion.fast-submissions/docs/snark-baseline/CORE-HANDOFF.md`, cited "handoff
§n"), the implementer's pre-review `docs/reviews/V3-S2R-handoff-review.md` (cited "H-M<i>",
"H-m<i>"), `docs/stages/V3-S2R-RESULT.md`, `docs/DESIGN-AMENDMENTS.md` (V3-KS-A8, V3-S2R-A1 … A7),
and the user's decisions of 2026-10-20 as the task states them: (a) the extractor is a computable Lean
function with a **proved** step-count bound; (b) completeness with error `δ` over a random oracle,
cap `2^-128`; (c) O-25 is out of scope.

Findings are numbered `V3-S2R-M<i>` (major: must fix) and `V3-S2R-m<i>` (minor: fix or argue).

**Runs (this review's own, all under `timeout` and a memory cgroup).**

| Run | Result | Log |
|---|---|---|
| `scripts/ci.sh` (hygiene, source-rule fixtures, build of contract/library/controls/gate/axiomaudit, axiom audit, line budget) | **CI passed**, 14 s warm; 1272 jobs; audit PASS, 98 theorems with no axiom; trusted code lines **288 / 500** | `logs/review/ci.log`, `logs/ci/` |
| `python3 scripts/loc.py` on the contract, the changed library and control files | every count in RESULT §1 matches | (this review's terminal) |
| Review probes, `lake env lean logs/review/probes/Review.lean` | all four probes check; axioms `propext`, `Classical.choice`, `Quot.sound` only (`mem_le`: no `Classical.choice`) | `logs/review/probes/Review.log` |

The probe file (gitignored, not part of the stage) proves:

* **P1** `budget_edge : 2 ^ 80 < extractorBudget (2 ^ 64)`.
* **P2** `mem_le : (∀ t, f t ≤ extractorBudget t) → Computes p E f → p.mem ≤ 2 ^ 48 + 2 ^ 16 * 6`.
  A certified program's memory is one constant, at most about `2^48` words, whatever the tape.
* **P3** `choice_certificate : Certificate Schoice`, where `Schoice` is the witness-sending
  submission with `E` replaced by the witness-sending extractor on tapes of at most `2^64` words and
  by `Classical.choose` of a witness beyond them.
* **P4** `big_certified_and_rejects_all : Certificate Sbig ∧ ∀ c π, Sbig.Vb c π = false`. `Sbig`'s
  `V` accepts only proofs longer than `proofCap` (a `2^20 + 1`-byte pad, then a leaf's
  witness-sending proof), `P` pads, `E` decodes after the pad, and `ext` is the one-statement
  `haltProg`. It is fully certified (`KS` at `ε = 0`, `CompleteWithError` at `δ = 0`, `Computes`, the
  caps), and its instantiated verifier `Vb` accepts nothing.

The Lean kernel accepted every review probe. Nothing in the stage was edited.

## Major findings

### V3-S2R-M1. Memory is one up-front constant, so the budget's derivation does not run in the machine, and every leaf run pays node-sized memory

**Evidence.** `Contract/Machine.lean:94-123`: `XProg.mem : Nat` is a constant of the program, and
`XProg.run` allocates and charges `Array.replicate p.mem 0` before the first statement, on every
input. Probe **P2** (`mem_le`) proves that a program computing any extractor within any fuel `≤ B`
has `p.mem ≤ 2^48 + 2^16·6`, because `Computes` includes the 6-word tape of the empty proof and
log. The budget's derivation, which RESULT §7 question 2 asks the user to confirm, says otherwise:
`Contract/Extractor.lean:40-41` and `DESIGN-v3.md:395-397` give the linear term `2^16·t` as "indexing
the log by sorting it (`t · log t` comparisons of 4-word digests)". Sorting a log needs `Θ(t)`
words of working memory. The input tape is read-only, and memory cannot grow with `t`. So for tapes
above about `2^48` words the stated algorithm cannot be written in the language, while `Computes`
demands extraction up to `2^64` words.

**Failure scenarios.**
1. *The derivation the user is asked to approve is not an algorithm of the machine.* The budget is
   being confirmed against a cost argument that the contract's own language excludes on most of
   the domain. An honest node extractor may still fit, but by a different algorithm: keep the set of
   needed digests (about `2^29` words for the node word) sorted in memory and stream the tape once
   per Merkle level, binary-searching each entry's answer. That costs about `2^8` statements per
   entry per level, roughly `2^13·t` over 30 levels. Nothing in the stage states or checks this,
   and no positive control indexes a log at all (M2).
2. *Leaf liveness allocates the node extractor's memory.* There is one `ext` for leaves and nodes,
   and DESIGN §6.3 step 8 (`DESIGN-v3.md:512-521`) says "a leaf is always run". A node-capable
   extractor must declare its decoder's working memory (the `2^29`-symbol word and its scratch,
   plausibly `2^30`–`2^31` words). Every leaf run then zero-fills `2^31` `BitVec 64` cells in the
   compiled interpreter, about 16 GB at 8 bytes per cell (not measured), before reading a word of
   input. The liveness cap of H-M3 (`2^36` steps) does not catch this, because `2^31 < 2^36`.
3. *The fixed term is spent on allocation.* Memory is charged at the full declared size on every
   input, including a 6-word tape. A program needing `2^47` words for its largest inputs spends
   half of `2^48` on its smallest ones.

**Smallest fix.** Either:
- (contract, recommended, a few lines) make memory proportional to the input as data, not a
  function: `mem : ℕ × ℕ` read as `mem.1 + mem.2 · t`, charged up front against `fuel t`, so that
  `steps ≥ memory` still holds. A function-typed `mem` would reopen H-M1, since its value is
  observable through in-bounds probing. An equivalent is memory that grows on a write past its end,
  charging the extension;
- or (text only) correct the derivation in `Extractor.lean`'s header and DESIGN §4.4 to an algorithm
  the machine can run (the streaming one above, with its memory bound). State the constant-memory
  constraint and its liveness consequence in §6.3 step 8, and put both to the user with RESULT §7
  question 2.

Either way, add the log-indexing positive control of M2, so that the linear term is checked rather
than estimated.

### V3-S2R-M2. The handoff's positive controls for the new language are missing, and no deviation records it

**Evidence.** Handoff §2.5 "Controls (each kernel-checked)" requires these positive controls:
"R1's parsing leaf extractor ported; **a log-indexing extractor (find an entry by answer) within
the linear term**; **a toy decoder (for example Berlekamp–Welch on a tiny code) within a stated
bound**". Its acceptance criterion is "the new statement is in the contract, with the controls
above". `Controls/Extractor.lean` and `Controls/Machine.lean` contain the witness-sending copy loop,
`haltProg`, straight-line and counting programs, and negatives. No program in the tree reads the
log part of the tape: `ext` copies the proof's words, and no control parses a log entry or compares
a digest. RESULT §5 lists 13 deviations, and this omission is not among them. RESULT §7
question 11 moves R1's port to entry work, which is reasonable. The other two have no counterpart.

**Failure scenario.** The positive side of the new language is checked only on programs that never
touch the log. This stage exists to make recursive entries certifiable (#7). Whether the language
and `B` admit the extractors such entries need is what these controls would show:
- the variable-length entry layout, which forces arithmetic on `⌈|q|/8⌉` to skip queries;
- 4-word digest comparison;
- memory limits (M1).

As things stand, the budget value (RESULT §7 question 2) and the claim "this unblocks #7" rest on
paper estimates. CLAUDE.md says "a claim in a RESULT is a kernel-checked theorem or a measurement".
A language or budget defect that blocks every SNARK entry would surface only at entry porting time,
after the pin moves.

**Smallest fix.** Add one log-reading positive control. It takes a digest `d` given in the proof and
scans the log for the entry whose answer is `d`, outputting its query's words or a tagged `none`.
Prove that it computes that specification within `c·t` steps for an explicit small `c` (one pass:
header skip, a per-entry length computation and a 4-word compare). If the toy decoder is dropped,
record it as a deviation with its reason and the user's agreement.

## Minor findings

### V3-S2R-m1. A certified submission's instantiated verifier `Vb` may reject every proof

**Evidence.** Probe **P4** (`big_certified_and_rejects_all`). `Certificate.complete` is
`CompleteWithError (Rel S.Vb) S.P S.V S.δ`, which is about `V`, not `Vb`
(`Contract/Certificate.lean:71`). A `V` that accepts only proofs above `proofCap`, with a prover that
pads, is complete at `δ = 0`. Its `Rel S.Vb` has only leaf witnesses, so `KS` holds, and `Vb ≡ false`.
DESIGN §4.3 says completeness is about `V` (`DESIGN-v3.md:353-356`), so this is by design and
pre-dates the stage: S1's `Complete ∀ H` had the same shape. The stage's rewritten text overclaims,
though:
- `DESIGN-v3.md:349-351` says "Completeness is required … because knowledge soundness alone is
  satisfied by a verifier that rejects everything (`rejectAll_not_complete`)";
- the threat table at `DESIGN-v3.md:612` says "A verifier that rejects everything | `KS` holds,
  `Complete` fails" (`Complete` is also the old name).

Both hold for `V ≡ false` and fail for `Vb ≡ false`. `rejectAll_no_certificate` likewise speaks only
of `S.V`.

**Scenario.** No security consequence: the harness's root check rejects such an entry, as it would
under H-M4. But a reader of the certificate is told that it excludes the reject-all verifier at
deployment, and it does not.

**Fix.** Text: say in §4.3, in the threat table and in `Certificate.lean`'s header that the
certificate does not exclude a `Vb` that accepts nothing, and that the harness does. Keep P4 as a
control in `Controls/Certificate.lean`. Optional contract change, satisfiable by every current
argument: require completeness through the size cap on **leaf** witnesses,
`if π.size ≤ proofCap then V c π else .ret false`. Witness-sending leaf proofs are 48 bytes, and the
non-succinctness argument of `DESIGN-v3.md:356` concerns nodes only.

### V3-S2R-m2. Beyond `2^64` tape words the named extractor may be non-constructive, and the Security header does not say so

**Evidence.** Probe **P3** (`choice_certificate`). The witness-sending submission stays certified
when `E` is `Classical.choose` of a witness on tapes above `2^64` words, because `Computes` ranges
over `(extractorInput c π L).length ≤ 2 ^ 64` (`Contract/Extractor.lean:109`), while
`KState.final` covers logs up to `logCap = 2^96`. DESIGN §4.5 (`DESIGN-v3.md:407-409`) and the
ledger (A6, H-m3) record that efficient extraction stops at about `2^61` entries. The contract's own
statement of the paper theorem, `Contract/Security.lean:24-31`, does not: it speaks of a proof "the
extractor cannot open" for every `Q + qV ≤ logCap`.

**Scenario.** For `Q` in `(2^61, 2^96]` the certified statement degenerates to "a witness exists".
Through `acceptAll_kstate_iff` that is a soundness-type claim, not knowledge. A reader of the trusted
file would take the `2^-32`-at-`2^96` figure as a knowledge bound.

**Fix.** Add one sentence to `Security.lean`'s paper-theorem paragraph: "the extractor is efficient
(`Computes`) only for tapes of at most `2^64` words, about `2^61` entries". Keep P3 as a control.
RESULT §7 question 3 should present the alternative, `logCap ≤ 2^58`, which makes the two domains
agree.

### V3-S2R-m3. "Within the domain `B t ≤ 2^80`" is false

**Evidence.** Probe **P1**: `2^80 < extractorBudget (2^64) = 2^80 + 2^48`. The claim is in
`Contract/Extractor.lean:41` (trusted header) and `DESIGN-v3.md:397`. **Fix.** Write "`B t < 2^81`"
(the argument against `2^128` enumeration is unchanged).

### V3-S2R-m4. Gate rule 4's fixtures are not in the tree

**Evidence.** RESULT §1.4 and §4 ("Gate rule 4 is done, with fixtures") and ledger A3 cite three
fixtures. They live only in `logs/s2r/gate/` (`GateNeg.lean`, `gate-*.log`, a local manifest),
which is gitignored. `git ls-files` lists no gate fixture, and `scripts/ci.sh` has no gate step.
**Scenario.** A later change to `badgeFields` (for example O-25's parametric `V`) can drop `ext`
from the list with CI green. **Fix.** Commit `GateNeg.lean` and the two positive invocations under
`tests/gate/`, and run them in `ci.sh` against a manifest generated in CI. If that is S3's job, say
so in A4 and change "done, with fixtures" to "checked by hand".

### V3-S2R-m5. Stale or false text left by the removal

- `DESIGN-v3.md:702` ("the trusted core: contract, **vendored machine**, library, …") and `:719`
  ("A protected-file list covers the contract, **the vendored machine**, …").
- `RecursionFast/Controls/Security.lean:33`: "the named extractor with its **image** and budget".
- `scripts/tools.env:3-4`: "sourced by `scripts/ci.sh` and `scripts/harness.sh` (so
  `HARNESS=1 submissions/baseline/scripts/check.sh` and CI agree)". `ci.sh` does not source it, and
  `harness.sh` and that path are v2's. Line 1's provenance note says S3 owns `harness.sh`, but the
  claim about `ci.sh` is false now.
- `scripts/ci.sh:13`: the usage line reads `scripts/ci.sh       (the vendor check of the RISC-V
  model left with the model, V3-S2R-A1)`, a garbled leftover of the argument's removal.
- `DESIGN-v3.md:612`: `Complete` (see m1).
- Outside this repository, for the orchestrator: the submissions repository's `CLAUDE.md` still
  documents `scripts/ci.sh /home/devops/Verified-zkEVM/riscv-zkvm`. The argument is now ignored.

No dangling code reference was found. `git grep` for `RiscvZkvm`, `ImageComputes`, `imageCap`,
`check-vendor` and `tests/asm` outside `docs/` and the ledger finds only historical comments, and the
build, gate and olean manifest no longer name the vendored library. **Fix.** Edit the five lines.

### V3-S2R-m6. Decision (a) was reinterpreted, and the user is not asked about it

**Evidence.** The task and the ledger record decision (a) as "the extractor is a computable Lean
function with a proved step bound". The handoff (§2.5, requirement 6) has "`E` (the program) is on
the badge path: gate rule 4 lists `E`". The stage makes `E` a **specification that may be
noncomputable**, adds a separate field `ext : XProg` (data in a contract language), and lists `ext`,
not `E`, in rule 4 (RESULT §5 items 1 and 6; H-M1, H-m6). The reasons are sound: H-M1's probe shows
that any shallow Lean function or monad hides work. But this changes what the user decided, not just
how it is implemented, and RESULT §7 does not ask. Question 9 asks only about Q1's wording in
`DISCUSSION.md`.

**Fix.** Add to RESULT §7: "Decision (a) is implemented as a deep program `ext` plus a specification
`E`, not as a computable Lean `E` (H-M1). Confirm." Note it in A1.

## Attacks that found nothing

**1. Uncharged work in the machine (handoff requirement 1, which the handoff asks the review to
attack).** No loophole was found.
- `XStmt` has no function-typed field. Every constructor's arguments are `Nat` indices, one `Word`
  or sub-statements, so a program cannot run Lean code of its own.
- `XStmt.exec` (`Machine.lean:103-116`) consumes one unit of fuel for every statement it pops,
  including `seq`, `ite` and each `loop` test. Each arm does constant word-RAM work: one `XOp.eval`
  (all 15 are fixed-width; `clmul` is a 64-iteration fold), one `getD`/`setIfInBounds`, one `push`,
  or pushing at most two stack entries.
- A loop needs at least two steps per iteration (`count_short`), and there is no empty body.
- Fuel exhaustion returns `none` (`exec`'s second clause), and `Computes` needs `some`.
- Memory is charged before the first statement (`mem_charged`).
- Out-of-range reads give `0` and out-of-range writes are lost, so a 64-bit address cannot reach
  unallocated memory.
- The `Nat` operand indices reveal only "in bounds or not", and constants are 64 bits per
  statement, so the advice is at most `progCap` words. The program is fixed, and against a random
  oracle that advice is useless (H-m11).
- The output's `toList` at halt is bounded by `outCap`.
- `enum_no_computes` is correct and general over `E` and `fuel`.

**2. Can a certified `E` brute-force?** No, on the domain. On the domain, `Computes` pins `E` to
`decodeWit` of the run's output. Within the domain, steps are at most `B t < 2^81` (m3), and `Rel`
has no secret shorter than 256 bits. Off the domain `E` is free (m2, P3; and for proofs above
`proofCap`, which `Vb` rejects anyway).

**3. The link between `ext` and what the harness runs.** The harness compiles the submission's own
term `S.ext` and runs the contract's `XProg.run`, the same term the certificate is about.
- Divergence between compiled and kernel semantics needs `implemented_by`, `extern`, `csimp` and
  the like, which gate rule 3 and the source rule reject.
- A noncomputable `ext` is rejected by rule 4 (`logs/s2r/gate/gate-neg.log`).
- Computing the term at start-up is input-independent advice (point 1).

**4. Completeness with error.**
- `failProb` is a lazily sampled uniform oracle: a fresh query averages over all `2^256` answers
  through the `noncomputable` `Fintype Digest`, which lists each digest once.
- A repeated query is answered from the table by first match, as `runLog` does.
- `OProg.bind` threads one table through `P` and then `V`, so the verifier sees the prover's
  answers.
- `failProb_eq_prob` identifies it with `PaperTheorem.prob`.
- `δ ≤ 2^-128` is a cap, so no declared `δ` trivialises the statement. `delta_one_no_certificate`
  and `rejectAll_not_complete` at every `δ < 1` hold for `V` (for `Vb`, see m1).
- `grind_exact` is exact, with the fallback to an already-tried nonce (H-m1).
- `fixed_not_complete` quantifies over all provers, so it is not a statement about one bad `P`.
- `complete_withError_zero` holds for the right reason: every table has a consistent oracle
  (`exists_consistent`), and `Complete ∀ H` applies to it.
- `Rel S.Vb` always has leaf witnesses, so completeness is never vacuous for want of witnesses.
- The KS laws, `paper` and `Controls/Potential.lean` are untouched by the stage, and the build that
  checks them is green.

**5. The removal.**
- No code, lakefile, gate, olean-manifest or source-rule reference to `RiscvZkvm`, the image,
  `ImageComputes`, `imageCap`, `check-vendor.sh` or `tests/asm` remains (m5 lists the stale prose).
- `ci.sh` lost its vendor step outright rather than keeping a step that now passes trivially.
- `olean-manifest.py`'s `DEFAULT_PREFIXES` and the gate's trusted list no longer name the vendored
  library, so nothing outside the contract is trusted by hash under its name.
- `PINNED_PKGS` drops Clean.

**6. Hygiene.**
- Axiom audit PASS.
- `check-hygiene.sh` clean; a manual grep finds no `sorry`, `native_decide`, `partial`, `unsafe`,
  `opaque` or forbidden attribute under `RecursionFast/`.
- 288 trusted code lines.
- Every new contract definition (`Word`, `clmul`, `XOp`, `XOp.eval`, `XStmt` and its constructors,
  `XStmt.size`, `XProg`, `XStmt.exec`, `XProg.run`, `progCap`, `Computes`, `OProg.bind`,
  `failProb`, `CompleteWithError`, `completenessCap`, and the `Submission`, `Declared` and
  `Certificate` fields) has a docstring that states its meaning.
- RESULT's line counts match `loc.py`, and its build, CI, gate and nanoda claims have logs under
  `logs/s2r/`.

**7. O-25 forward compatibility (for the separate track).** Nothing in the stage makes O-25 harder:
- `Computes` is independent of `V`'s type.
- `CompleteWithError` can be restated at `D := Digest` after a parametric `V` is instantiated
  (RESULT §6).
- Two things the O-25 track must keep in view:
  - completeness over a random oracle constrains nothing about `V`'s behaviour under BLAKE2s (H-M4,
    and m1 here), so an O-25 fix cannot lean on completeness to pin `V` at deployment;
  - `badgeFields` names `V` by field, so a type change of `V` needs rule 4 and its fixture (m4)
    updated in the same change.

## The implementer's open questions

RESULT §7, question by question. Two contain errors rather than open choices. The others are
genuine decisions.

1. `completenessCap`: a decision. The implementation matches the recommendation.
2. **The budget value is presented on a flawed derivation** (M1). Its log-indexing term assumes
   sorting in memory proportional to `t`, which the machine does not allow beyond about `2^48`
   words. Fix the derivation, or the machine, before asking.
3. **`logCap` versus `2^61` is an inconsistency, not only a question.** The trusted
   `Security.lean` header states the paper theorem without the efficiency restriction (m2, P3).
   Present `logCap ≤ 2^58` as the option that removes it.
4. Liveness cap: a decision. Add M1's point that "a leaf is always run" allocates the program's full
   memory.
5. A decision.
6. A decision.
7. Interpreter speed: correctly marked unmeasured. The `2^36` liveness cap cannot be sized without
   it.
8. Primitive set: the argument that an extractor never hashes is right (it reads preimages from the
   log). M2's log-indexing control would show the remaining primitives suffice for log work.
9. Add m6: decision (a) itself was reinterpreted, not only Q1's wording.
10. A decision (GitHub writes).
11. Correct and important: S2a and R1 do not build against this commit. The submissions pin must not
    move before they are ported.
12. A decision.

## Verdict

**Not ready to commit as is; ready after the fix pass.**

The core of the stage is sound:
- The deep three-address machine has no uncharged-work channel I could find. Its step bound is a
  theorem, and its controls separate.
- `CompleteWithError` is the right probability space, with exact grinding controls and a correct
  embedding of perfect completeness.
- The removal of the RISC-V model left no dangling code reference.
- CI, the axiom audit and the trusted budget (288/500) are green.

Two major findings must be fixed before the commit:
- **M1**: memory is a per-program constant (at most about `2^48` words, P2). The budget derivation the
  user is asked to confirm uses an algorithm the machine cannot run on most of the domain, and every
  leaf liveness run pays node-sized memory. Make memory affine in `t`, or correct the derivation and
  state the constraint.
- **M2**: the handoff's log-indexing positive control (and the toy decoder) is missing without a
  recorded deviation. No program in the tree reads the log.

The minors are text and test hygiene (m3, m4, m5), two true-but-understated certificate properties
with kernel-checked witnesses (m1: `Vb ≡ false` is certifiable, P4; m2: extraction beyond `2^64`
words is existence-only, P3), and one decision to put back to the user (m6). Probes:
`logs/review/probes/Review.lean`, log `logs/review/probes/Review.log`. CI log: `logs/review/ci.log`.
