# Stage E-ks (V4-A10, textbook knowledge soundness): adversarial review

Reviewed: commit `a283ff8` on `v4/ks-standard` against its base `15dac52`, in the read-only
worktree `/home/devops/Verified-zkEVM/recursion.fast-v4-ks-review`. Read in full: every changed
Lean file (`Contract/Security.lean`, `Contract/Oracle.lean`, `Contract/Certificate.lean`,
`Library/{Prob,KS,PaperTheorem,Compose,Security,Completeness,Oracle,SigTrust}.lean`,
`Controls/{Security,Completeness,Potential,Certificate,Backdoor,Compose}.lean`), the documents'
diff, and `docs/v4/stages/E-ks-RESULT.md`. Out of scope as instructed: paired record comparison,
FB-5, Q11, Q5, nothing ran on GitHub, no season-shape entry.

**Reproduced here** (logs under `logs/`, gitignored):

| Check | Outcome | Log |
|---|---|---|
| `timeout 1800 lake build` | green, 1,266 jobs, 0 warnings | `logs/review-lake-build.log` |
| axiom audit (`lake env lean --run scripts/AxiomAudit.lean`) | PASS: every declaration within `propext`, `Classical.choice`, `Quot.sound`; 157 theorems use none | `logs/review-axiom-audit.log` |
| line budget (`loc.py`, the files `ci.yml` names) | **350** code lines (`Security.lean` 28) ≤ 500 | inline |
| token sweep for `sorry`, `native_decide`, `implemented_by`, `extern`, `export`, `init`, `csimp`, `cpass`, `computed_field`, `unsafe`, `partial`, `opaque`, `admit`, `axiom` over `RecursionFast/` | prose hits only (the words "admits", "partial table") | inline |
| review probe `LuckyVerifier.lean` (M-1) | compiles against the built library: `KS (Rel acc) Vlucky Elucky 0 1` is kernel-checked | `logs/review-probe-lucky.log` |

The probe's source is outside the repository:
`/tmp/claude-1000/-home-devops-Verified-zkEVM-recursion-fast/deb0fda2-5afe-4ae8-816d-bf1a4a32e03f/scratchpad/ks-probe/LuckyVerifier.lean`.

## Major

### M-1. `KS` gives the extractor the verifier's own fresh answers; the textbook game gives it the adversary's trace only

**Where.** `RecursionFast/Contract/Security.lean:129-134` (`KS`), its docstring (`:124-128`), the
header (`:17-23`, "the extractor `E`, given `c`, `π` and that log"), `docs/DESIGN-v4-srom.md`
§1.4 (`:260-298`) and `docs/v4/BRIEF.md` §5c (`:226`), which all say the extractor reads the
**final** query log.

**What the Lean says.** The game is `A.bind fun x => (V x.1 x.2).bind fun _ => .ret x`, and the
event is on the log `L` at the end of that game, so `E x.1 x.2 L` reads a log that contains the
verifier's queries and their answers, including those the adversary never asked (fresh at `V`'s
time, uniformly sampled and appended by `prob`). In the textbook single-output definition
(Chiesa–Yogev, *Building Cryptographic Proofs from Hash Functions*, the knowledge-soundness
definition for NARGs in the ROM; CGSY24, which `Library/Compose.lean` cites) the extractor
receives `(x, π, tr)` with `tr` the **adversary's** query trace, and the verifier is run on the
same oracle afterwards; `E` does not see `V`'s fresh answers (and has no oracle access). The two
differ exactly on verifiers whose acceptance is decided by an answer the adversary did not ask
for.

**Concrete failure.** A verifier that asks the proof itself as a query and accepts when the
oracle's answer, with 144 bits masked to zero, is the leaf start of the statement; an extractor
that reads that answer from the log:

```lean
def mask (a : Digest) : Digest := Vector.ofFn fun i => if i.val < 18 then 0 else a[i]
def Vlucky (c : Digest) (π : Proof) : OProg Bool :=
  .query π fun a => .ret (decide (c = leafStmt (chainEnd (mask a) 0) 0))
def Elucky (_ : Digest) (π : Proof) (L : Log) : Option Wit :=
  (L.find? fun e => e.1 = π).map fun e => .leaf (mask e.2) 0
theorem lucky_ks (acc : Digest → Signed → Bool) : KS (Rel acc) Vlucky Elucky 0 1   -- kernel-checked
```

`KS` holds at **error `0`** with `qV = 1`, for the relation of every `acc` (`KS.of_extracts`:
whenever `V` accepts on the final log, that log answers `π`, and the masked answer is a witness).
`Elucky` is one log lookup, so it is also computable within any reasonable `Computes` budget. In
the textbook game the adversary that asks nothing and outputs `(leafStmt (chainEnd s 0) 0, π)` for
an `s` with 144 zero bits wins with probability `2^-112` (the verifier's fresh answer masks to `s`),
and an efficient extractor seeing only `(c, π)` and an empty trace must invert two BLAKE2s
evaluations on a 112-bit space; so textbook knowledge error about `2^-112 > errorCap = 2^-120`
(paper, standard preimage hardness), against `KS` at `0`. The prover does not "know" the witness;
the oracle produced it and the contract's `E` reads it off the verifier's own answer.

**Why it is not worse than it looks, and why it is still a finding.** (i) v3's `KState.final` read
the same log, so this is inherited, not a regression (the same `Vlucky` has `KState.zero`). (ii) In
the SROM deployment every answer the verifier uses is in the signed trace the prover submits, so
`V`'s answers are always queries the prover made; and in `Compose.compose_prob` the per-member
verifier asks nothing fresh (`KS.select`), so the composition is unaffected. (iii) But the stage's
and the user's claim is "exactly the textbook notion"; the Lean is the textbook notion **with the
extractor additionally given the verifier's fresh answers**, which is weaker on single-level
statements, and nothing in `Security.lean`'s header, the design or the brief says so. The header
even lists what the file "does not exclude" (`:57-66`) and omits this one.

**Fix, one of two (the user's call, since it is the content of V4-A10).**

*(a) Statement.* Give `E` the adversary's log. The game must return the adversary's log beside its
output: a contract-level `withLog` (as `Library/Prob.lean:203`, about 5 lines) and the game
`(withLog A []).bind fun y => (V y.1.1 y.1.2).bind fun _ => .ret y`, the event
`fun y L => (V y.1.1 y.1.2).runLog L = some true ∧ ¬ ∃ w, E y.1.1 y.1.2 y.2 = some w ∧ R y.1.1 w`
(acceptance still on the final log; extraction on `y.2`, the adversary's log). About six trusted
lines (356). Cost downstream: the bridge `KState.ks` no longer goes through as stated, because
`final` extracts on the log `V` accepts on, which is the final one; a potential-form entry would
need `final` restated on the adversary's log for every continuation `V` may append (or an extra
hypothesis that `E` ignores entries after the adversary's), so `Library/Security.lean`,
`PaperTheorem.lean`, `Controls/Potential.lean` and `Backdoor.lean` change. `Compose.compose_prob`
survives: the member's adversary is `withLog A` and `V` asks nothing fresh on an accepted member,
so the two logs coincide.

*(b) Documentation, if the user keeps the final log* (defensible for SROM: the prover submits the
trace, so there is no "verifier's own answer" in the deployment). Then `Security.lean`'s header,
`KS`'s docstring, design §1.4 and BRIEF §5c must say that `E` reads the final log, that the textbook
gives it the adversary's trace only, that the difference is the verifier's fresh answers, that it
admits a verifier such as `Vlucky` at error `0`, and why that is harmless here (the deployment's
trace and `KS.select`). The probe should become a control, "what `KS` does not exclude", in
`Controls/Security.lean` beside `acceptAll_ks_above_logCap`, with the paper figure `2^-112`.

Whichever is chosen, the word "exactly" (RESULT §2 "It is the starting design of the brief,
unchanged") should carry the caveat.

## Minor

### m-1. `KS` is vacuous for `qV > logCap` (the implementer's open question 3)

**Where.** `Contract/Security.lean:132` (`Q + qV ≤ logCap →`), `Controls/Security.lean:125`
(`acceptAll_ks_above_logCap`). **Evidence.** The control proves `KS (fun _ _ => False) acceptAll E ε
(logCap + 1)` for every `ε`, with `fun _ _ _ hQ => absurd hQ (by omega)`. The old `KS` was not
vacuous there (`acceptAll_no_kstate_empty` holds at every `ε`). **Why minor.** `Certificate.cap`
gives `qV ≤ 2^16`, and the header (`:41-42`) and design §2.7 say so. **Suggested fix.** Either add
`qV ≤ logCap` as a conjunct (one trusted line; then `KS` is non-vacuous on its own, the natural
reading of a definition that has its own query bound), or keep it and leave the control and the
header as they are. State the choice in the RESULT.

### m-2. A tactic block inside a trusted definition

**Where.** `Contract/Security.lean:118`: `| .ret x, L => by classical exact if B x L then 1 else 0`.
**Why.** A reader of the trusted base sees a `by` block in a definition; the term it produces is
`@ite _ (B x L) (Classical.propDecidable _) 1 0`, which is fine, but the project's reviewability rule
is that trusted definitions are terms. v3's `failProb` had `if b then 0 else 1` with no tactic.
**Fix.** `open Classical in` before `noncomputable def prob`, and `if B x L then 1 else 0` in the
clause (the same term; `Library/Prob.lean:61` `ind` can do the same). Line count unchanged.

### m-3. No kernel fact that the event's acceptance is the verifier's verdict in the game

**Where.** `Contract/Security.lean:133` reads acceptance as `(V x.1 x.2).runLog L = some true` on
the final log, after the game ran `V` and discarded its result (`fun _ => .ret x`). **Why it
matters.** The textbook event is "`V^f(x, π) = 1`", the verdict of the run. Here the verdict is
re-read from the final table; the two agree because the table is consistent with the run (first
match, `prob`'s lazy sampling), but nothing kernel-checked says so. `prob_bind_of_runLog`
(`Library/Prob.lean:195`) covers only the case where the table already answers `V`.
**Suggested fix (library, no trusted change).** A theorem in `Library/Prob.lean` or `KS.lean`:
for every `A`, `prob (fun x L => (V x.1 x.2).runLog L = some true ∧ P x L) (A.bind fun x => (V x.1
x.2).bind fun _ => .ret x) [] = prob (fun y L => y.2 = true ∧ P y.1 L) (A.bind fun x => (V x.1
x.2).bind fun b => .ret (x, b)) []` (by induction on `V`'s run with `expect_withLog`-style
bookkeeping). Cite it from `KS`'s docstring. This also makes M-1's option (a) easier to state.

### m-4. Dead library code and a layout nit

- `Library/KS.lean:85` `KS.mono` has no user (`grep` finds only its docstring mention; every
  `.mono` in the tree is `KState.mono`, `Bounded.mono` or `CompleteWithError.mono`). Either use it
  (e.g. `Controls/Security.lean` `mono_control` could be restated as `KS` at the cap through it)
  or drop it.
- `Library/Compose.lean:259-260`: two consecutive blank lines.

### m-5. Documents: stale number, self-contradictory brief paragraph, and the caveat of M-1

- `docs/v4/BRIEF.md:216` (amendment table, item 10): "keeps the whole-run bound negligible
  (about `2^-90` at `2^30` queries)" is pre-V4-A10; design §6.2 and §4.4's twin were updated
  (`DESIGN-v4-srom.md:1167`), this row was not.
- `docs/v4/BRIEF.md:39-43` §2 reads "The submitter proves, in the random-oracle model with v3's
  potential `KState` (since V4-A10: the textbook single-output statement, the potential a library
  route), one-level knowledge soundness" and `:72` "`final` extracts children whose signed traces
  are genuine again": the brief is annotated rather than rewritten, so its §2 states the rule and
  its negation in one sentence. Either rewrite §2 for V4-A10 or mark §2 and §3 "as of 2026-10-22,
  superseded by §5c" at the top of §2, as §5c already says of V4-1.
- The caveat of M-1 is absent from every document (design §1.4, §2.4 table row "one member's bound
  `(Q + qV)·ε`", §2.7 item 2; BRIEF §5c; `Security.lean` header); see M-1 (b).
- Otherwise the documents agree with the Lean: `KS` quoted verbatim in §1.4; the trusted line count
  350 in design §0, §5 (`:1203`, `:1208`), CHECKS C12 and criteria 2 and 5, CLAUDE.md and README;
  §2.4's table says exactly what is kernel (`walk`, `compose`, `Escape.wins`, `KS.select`,
  `KS.union`, `compose_prob`, `compose_of_kstate`, `prob_potential_ge_one`) and what is paper (lazy
  sampling vs a random function, randomised adversaries, the forgery/collision split, the PRF
  hybrid, the stream's walk); no live text calls the potential a rule (the remaining mentions are
  the library route, history in `docs/README.md:37` and BRIEF `:12`, and `final` in §2.4's lossless
  paragraph, correctly about `compose_of_kstate`).

### m-6. "The whole run" is bounded per composed output (the implementer's open question 1)

**Where.** `DESIGN-v4-srom.md` §0 (`:69`, "the first term about `2^-81`"), §2.4 "The error"
(`:495-504`), §2.7 item 4 ("Knowledge soundness of the whole tree from one log"), §6.2 (`:1334-1336`).
**What is right.** `513 · 2^30 · 2^-120 = 2^-80.997`, `127 · 2^30 · 2^-120 = 2^-83.01`, and
`Σ_{i≤256} (2i+1) = 257² ≈ 2^16.01`, so about `2^-74` for every stream output at once; the per-output
figures quoted are correct, and the kernel theorem is per root (`compose_prob` on one `A` output).
**What to fix.** §2.4 should say in one sentence which event `2^-81` bounds (the stream's final
output's extraction tree) and give the all-outputs figure (`2^-74` at `2^30` queries, a union over
the 257 outputs' trees), since the harness scores every stream output (`t_link` is measured per
link) and a reader of "the whole run" will take the smaller number. Also note that the balanced tree
`compose_prob` covers is the season tree only; the stream's comb needs the paper walk (already
stated in the table, not in "The error").

## Checks that found nothing

**Pass A, the trusted definitions (beyond M-1, m-1, m-2).** `prob` is the lazily sampled oracle:
fresh answers uniform over `Digest` (`(2^256)⁻¹ * ∑`, with `Fintype Digest` listing each digest
once) and recorded by `L ++ [(q, a)]`, repeats read by `L.find?` first match, the same reading as
`runLog` (`Oracle.lean:45-47`), so the game sees one function (`Controls/Completeness.lean`
`prob_askTwice`). The game runs `V` on the adversary's output on the same oracle, so the final log
holds `V`'s answers and `runLog` on it is `V`'s verdict (m-3 asks for the lemma). The statement is
chosen after the queries (`A : OProg (Digest × Proof)` outputs it at its leaves). The budget
`∀ H, (A.queries H).length ≤ Q` is sound for lazy sampling: every path is consistent with some
function (`exists_consistent`, `consistent_append`), so no path asks more than `Q`; repeated queries
are counted, which only charges the adversary more (a de-duplicating adversary has the same output
and log distribution with a smaller `Q`), so no strength is lost; branching on answers is covered
since `queries H` follows each `H`'s path. Deterministic adversaries suffice because the bound is
uniform in `A` for fixed `Q` and `E` does not depend on `A` (header, paper; correct). The guard
`Q + qV ≤ logCap` is what `paper` needs and what V3-KS-A6 argued; vacuity above it is m-1.
`(Q + qV) * ε` elaborates in `ℝ≥0` as stated.

**Pass A, completeness.** `CompleteWithError` reads `prob (fun b _ => b = false)` where it read
`failProb`; `failProb_eq_prob` (`Library/Completeness.lean:36`) is by structural induction with the
same two clauses, and `completeWithError_iff` is `simp only [CompleteWithError, failProb_eq_prob]`:
the statement is v3's word for word. `failProb` and `KState` moved out of trust; nothing moved in
besides `prob`. The four completeness controls and `rejectAll_not_complete` are the old statements
through the iff.

**Pass A, the bridge and `paper`.** `KState.ks k hq : KS R V E ε qV` has no hypothesis beyond the
knowledge state and the verifier's functional bound; its proof bounds the game's queries by `Q + qV`
under every `H` (`queries_bind` twice) and applies `paper`, generalised from `DepthLE` to
`∀ H, (G.queries H).length ≤ n` through `bound_found`/`bound_fresh`/`bound_zero`, which carry
`Consistent H L` so that the count under consistent functions bounds the lazily sampled run. The
docstrings say what they prove. `prob_potential_ge_one` is the same argument with `hB := id`.

**Pass A, composition.** `compose_prob`'s event is `acc` accepting the root and `walk` returning
its fourth outcome `escape`, i.e. none of the leaf starts, a collision or a forgery; `Escape` is
"accepted, trace in the log, `E` returns no witness", and `Escape.wins` turns it into the `KS`
event at `(c, p.π)` on a functional log via `runLog_of_runSeq` (every lazily sampled log is
functional: `functional_append` through `prob_mono_of_inv`). `KS.select`: the member's adversary is
`withLog A []` followed by `memberAt` (a Lean function; the adversary is unbounded), asks at most
`Q` (`queries_withLog_le`), and `V` run after it on an accepted member asks nothing fresh
(`prob_bind_of_runLog` on `hw.1`), so each member costs `(Q + qV)·ε` from `KS` directly; the union
over `paths r` (`card_paths`: `2^(r+1) − 1`) is `prob_exists_le` through linearity. The bound
`N·(Q + qV)·ε` is justified and sharper than the brief's `N·(Q + d·qV)·ε`. `compose_of_kstate` is a
corollary of `compose` with `Escape.not_of_kstate`. The stream's walk is paper and the design says
so (§2.4 table). Numbers: m-6.

**Pass A, controls.** Every new trusted definition has both signs, each non-vacuous:
`prob`: `prob_askGood = 2⁻¹` (positive, exact) and `prob_askTwice = 0` (negative, where fresh
sampling would give `1 − 2^-256`). `KS`: positives `queryThenAccept_ks_one` (direct, `ε = 1`),
`twoLucky_ks_exact` (through the bridge at the exact error `2^-192`), `ws_ks`, `rejectAll_ks`,
`Backdoor.certified`; negatives `acceptAll_wins`/`acceptAll_not_ks` (probability exactly `1`),
`acceptAll_not_ks_none`, `queryThenAccept_wins`/`queryThenAccept_ks_ge_one` (the verifier's query
is charged; without it the definition would hold at `ε = 0` for a verifier that draws its own
challenge), `oneQuery_not_KS` (the first conjunct), `sigTrust_no_certificate` (the adversary holding
`sk`, probability `1`, against `qV·ε < 1` from the caps), `noExt_not_ks`/`noExt_escape_prob`
(the composition's event is certain for an extractor that returns nothing). Statements compared
against `15dac52`: `acceptAll_no_certificate`, `sigTrust_no_certificate`,
`sigTrust_certificate_opens`, `choice_certificate`, `big_secure`, `certified`, `twoLucky_ks`,
`collision_ks`, `v24_ks`, `ws_ks`, `rejectAll_ks`, the completeness controls, `walk_one_leaf`,
`walk_two_leaves`, `forgery_trivial`, `compose_exists_free` keep their statements (the proofs
change to the bridge or the iff); `twoLucky_ks_exact`, `acceptAll_ks_above_logCap`,
`ws_compose_prob`, `noExt_*`, `prob_ask*` are new. Nothing was weakened.

**Pass B (fidelity)** does not apply: no transcribed artifact changed (the RESULT's "No Python,
Rust, workflow or harness file changed" is confirmed by the diff stat).

**Pass C, hygiene.** Axioms: PASS (above). No `sorry`, `native_decide`, code-changing attribute,
`unsafe`, `partial` or `opaque` in `RecursionFast/`. Trusted docstrings say what, not how (`prob`,
`KS`, `CompleteWithError`, `logCap`). Headers are long but in the project's established style and
every paragraph is load-bearing. Dead code: m-4. Naming consistent (`Wins`, `Escape`, `Escaped`,
`escape_prob_le`, `compose_prob`).

## Verdict

**One major, six minors.** The Lean is kernel-checked, green and within budget; completeness is
provably unchanged; the bridge and the union-bound composition prove what their docstrings say;
every new trusted definition has non-vacuous controls of both signs and no control statement was
weakened. The one defect is at the statement level of the user's decision: `KS` is the textbook
single-output notion **except** that the extractor reads the final log, so it also sees the
verifier's fresh answers, which the textbook extractor does not; a kernel-checked probe shows a
verifier certified at error `0` whose textbook knowledge error is about `2^-112`. It is inherited
from v3, harmless for the SROM deployment and for the composition, and either fixable in about six
trusted lines (at a cost to the potential bridge) or to be stated as a deliberate deviation in the
header, the design and the brief. **Not mergeable as "textbook" until M-1 is resolved one way or
the other; mergeable after that with the minors applied.**
