# Review of `docs/explore/REPORT.md` (relativized recursion exploration)

Reviewer: final adversarial pass, 2026-10-22. Checked against `BRIEF.md`, `00-prompt-review.md`,
notes L1/T1/A1/A2/A3/C1/W1/W2/P1–P4, every `.lean` file under `RecursionFast/Explore/`, the audit
files under `docs/explore/probes/audit/`, the C1 service logs, and the paper text
(`SP/paper/paper.txt`). `M<i>` must be fixed; `m<i>` are answered or fixed at the author's choice.
Quotes are from the report; "Lean" cites file and declaration in `RecursionFast/Explore/`.

## Major findings

**M1. `pure_no_kstate` is overclaimed as "no knowledge state exists at all".**
Quote (§7.2): *"If `V` hashes privately, without reading its BLAKE2s values from the log, no
knowledge state exists at all (`pure_no_kstate`)."*
Wrong: the theorem is for the natural extractor and errors below 1 only. Lean
`TwoChannel/Merkle.lean`, `pure_no_kstate (mode) {ε} (hε : ε < 1) : ¬ Nonempty (KState2W mode MRel
Vpure (E mode) ε)`; the "any extractor" half is `pure_extractor_inverts` (every certifying
extractor returns a Merkle preimage of every good root from one leaf and a squeeze-only log).
P3 §Conclusions 4 states it correctly. The same qualifiers are missing from *"W1's 'witness or
collision' clause is unsatisfiable (`col_no_kstate`)"*: Lean `col_no_kstate … (hε : ε < 1) :
¬ Nonempty (KState2W .col MRel V (E .col) ε)`, natural extractor, plus `col_extractor_inverts`.
Corrected text: "If `V` hashes privately …, the natural extractor has no knowledge state at any
error below 1 (`pure_no_kstate`), and every other extractor must invert the Merkle root map from a
log holding only the squeeze (`pure_extractor_inverts`)." And for W1's clause: "is unsatisfiable
for the natural extractor at every `ε < 1` (`col_no_kstate`); any other extractor must invert
(`col_extractor_inverts`)."

**M2. The D4 "escape" kernel result is for a node with children and list in the clear; the
succinct (SNARK) node is paper, and the report does not say so.**
Quote (§1): *"In the kernel, one `attest` call per node replaces re-asking."* Quote (§7.1):
*"`attState` and `calls_node`: a node verifier that makes one `attest` call and judges its children
on the carried list has a knowledge state with the child's potential and error."*
Wrong by omission: `attV` (Lean `Attested/Escape.lean`) decodes a frame `(c₁, c₂, π₁, π₂, xs)`
with the child proofs in the clear and runs them itself with `runItems xs`; nothing is committed
or decoded. P2 "What the probes do not show": *"Succinctness or a SNARK node. Children are in the
clear. That a SNARK node proving `runItems xs cᵢ πᵢ = some true ∧ hashList xs = hᵢ` in-circuit is
sound is W2 §A.4, paper (issue #7's decoding is unchanged)."* The §7.1 "Relation" paragraph
describes the SNARK node, and the kernel bullets follow without the distinction, so a
formal-methods reader will take the succinct node as kernel-checked. Corrected text, after the
`attState` bullet: "The probe's node carries its children and the list in the clear, so the kernel
shows the oracle-call count and the composition laws, not the soundness of a succinct node; that
a SNARK node that decodes `(πᵢ, xsᵢ)` from its committed witness satisfies `final` is the paper
obligation W2 §A.4, exactly issue #7's." Summary item 3: "In the kernel (for a node with children
in the clear), one `attest` call per node replaces re-asking."

**M3. Completeness in the relativized setting is never discussed, and the lift is presented as an
entry although its completeness is unproved.**
Quote (§6.4): *"It lifts to a relativized knowledge-sound verifier with `V₀`'s own potential,
error and query bound. … With a succinct flat SNARK, its root is succinct and nothing recurses."*
Quote (§6.4): *"So 'knowledge-sound for the relativized recursion relation' does not mean
'amenable to recursion'."*
Missing caveat: P4 "What this does not show": completeness of the lift for `RelO` is *"paper,
sketched"*, fails for *"an adversarially chosen child that `V₀` accepted with a false clear
shape"*, so perfect completeness over every oracle is not implied and *"any completeness clause
for `RelO` in D1/D2 must be adaptive and probabilistic, as in [BCG] Def. 3.12, or the lift is not
an entry."* Also A1 m2: `CompleteWithError` is ill-typed for an oracle-dependent relation; W2 M10:
node completeness from an arbitrary starting log is unsatisfiable for every Fiat–Shamir design,
hence the context form of W2 §A.5. The report's only trace is the bare item "completeness in
context form" in §9.2. The vacuity conclusion survives (witness-sending and concatenation are
perfectly complete: `concatV_node_run`, `Backdoor.complete`), but the "succinct root" instance
of vacuity rests on the lift, and the §9 recommendation cannot be implemented without restating
completeness. Corrected text: add to §6.4 "The lift's knowledge soundness is kernel; its
completeness is paper and only against children whose clear statement is true (P4), so under a
perfect-completeness clause it is not an entry, and under the contract's `CompleteWithError` the
clause itself must be restated for an oracle-dependent relation (A1 m2, W2 M10, context form
W2 §A.5)". Add a one-line §4 remark that `RelL`'s node clause makes the relation depend on the
log, so completeness must be stated inside the game.

**M4. `lazy_extractor_collides` does not conclude "a BLAKE2s collision".**
Quote (§6.2): *"`lazy_extractor_collides`: every extractor of such a state must output a BLAKE2s
collision."*
Lean `Relativized/Lazy.lean`: the conclusion is `Collides C c₁ c₂ w`: a leaf witness with
`nodeStmt c₁ c₂ = leafStmt …`, or a node witness `(d₁, d₂)` with `nodeStmt d₁ d₂ = nodeStmt c₁ c₂`
whose children are lazy node statements. That is a BLAKE2s collision between distinct inputs only
when `c₁` is a leaf statement (then `d₁ = c₁` is a cross-tag collision and `d₁ ≠ c₁` a second
preimage); the reading is the file's docstring and P1's table, not a theorem. Corrected text:
"every extractor of such a state must output, on the empty log, a `Collides` witness: a preimage
of `nodeStmt c₁ c₂` under the leaf tag, or a second node preimage whose children are themselves
lazy nodes; when `c₁` is a leaf statement (as in the `W1` instance) each case is a BLAKE2s
collision between distinct inputs."

**M5. The axiom-audit claim does not match the evidence table.**
Quote (§10): *"All 27 headline theorems above depend only on `propext`, `Classical.choice` and
`Quot.sound` (`docs/explore/probes/audit/audit-orchestrator.log` …)."*
The table above it names 34 declarations. The cited log has 27 lines; `queries_defer`,
`Paper.paper_tree`, `merkleState_pubStep`, `honest_extracts`, `col_extractor_inverts`,
`bd_extractor_inverts` and `liftState_μ` are not in it (they are audited only in the per-note logs
under `logs/`, which is gitignored; P2 §axioms, P3 §axioms, P4 §axioms). Fix: extend
`Audit.lean` to every name in the table and re-run, or say "the 27 in the log; the other seven in
P2–P4's logs". Either way the count must match the table.

**M6. §6.3 says the ranked-shape deferral root both compresses about 3× and does not compress.**
Quote (§6.3 table): *"re-ask `511·h_V` = 2.6–13.2 M compressions … 0.6–3.2× WS's `2^22` hashes:
no compression."* Quote (§6.3 text): *"'Compressing but not succinct' holds exactly when
`n > qV_leaf` (T1 §3): about 3× at `n = 2^14`."*
Both are in the notes but in different units: T1 §3.3 counts *queries* (5,156 < 16,384, ratio
3.2), C1 row 4 counts 64-byte *compressions* (`h_V` = 25.9k > 16,384, so 0.6–3.2× more work than
WS). Since the honest in-circuit cost and A1 M3's unriggable charge are per compression, the
reader must be told which unit carries the verdict. Corrected text: "In queries the root compresses
about 3× at `n = 2^14` (T1 §3); in 64-byte compressions, the unit the charge must use (A1 M3), it
does 0.6–3.2× WS's work and does not compress (C1 row 4). The two agree at `chainCap`."

## Minor findings

**m1.** Quote (§6.2): *"`queries_defer` shows it asks as many oracle queries as running the
children would."* Lean `queries_defer : … ≤ Q.length` is an upper bound; the "exactly `|Q|` on
acceptance" reading comes from `checkAll`'s structure, and "as many as the children" assumes an
honest `Q`. Say: "asks at most the `|Q|` queries of the carried list, all of them when it accepts;
for an honest list that is the children's query count."

**m2.** Quote (§6.2): *"If a committed child reads query `q` and the log has potential below 1,
the parent must read `q` too."* Lean `Lift/Deferral.lean`, `reask`: the hypothesis is
`k.μ (eraseKey L q) < 1`, the potential of the log *without* `q` (P4 item 4 says so). Correct the
clause.

**m3.** Quote (§5.1): *"a node proof that v3's certified backdoor verifier accepts but whose
children cannot be extracted."* Lean `Relativized/Compose.lean`, `v3_no_compose`: the conclusion is
`¬ TreeOK WitnessSending.E L₀ 2 …`, i.e. the control's own certified extractor returns nothing for
a child. Say "whose children its certified extractor does not open".

**m4.** §7.2 P3 details: *"then evaluates only the opened leaf"*: `lateTail` evaluates the opened
leaf's hash *and the root* (Lean `Merkle.lean` 471–473). *"Honest proofs are extracted, not
escaped (`honest_extracts`)"*: under the side condition that neither leaf hash equals the root,
checked in the kernel for two concrete leaves (`honest_extracts_blake2s`). *"the natural extractor
works: `merkleState` certifies the toy at a tight `ε = 1/2` (`merkle_eps_ge`)"*: tight for the
natural extractor (`merkle_eps_ge` quantifies over its states only).

**m5.** Quote (§6.3): *"5,156 queries and about 25.9k compressions for spartan-chain …, and
10k–26k for WHIR or leanVM-class verifiers."* C1 §2.1: WHIR-class 5.1k–12k, leanVM-class 9.2k,
spartan-chain 25.9k; "10k–26k" is C1 row 2's range for a real recursion root. Write "5–12k for
WHIR-class, 9.2k for leanVM-class, 25.9k for spartan-chain".

**m6.** Quote (§7.5): *"A one-core CPU-time cap separates the two by only 2–2.5× at the ranked
shape. At `r = 4, n = 2^20` the margin grows to 25–95× (C1)."* The first number is C1 row 6's
*margin per side* of a cap window; the second is C1 row 7's *raw ratio* WS/real. Like for like:
raw ratio 6–24× (ranked, C1 row 3) vs 25–95× (long); cap margin per side ≈ 2–2.5× vs ≈ 5× (C1
§2.3). The recommendation still follows; the sentence should give both pairs.

**m7.** Quote (§6.5): *"Ligero's ≈ 4 M field operations"* (A1 M4, estimate). C1 §1 and §3.4 put
spartan-chain's verifier field work at `3.1·10^7` `K`-multiplications (0.54 s at 17.5 ns). The
notes disagree; cite C1's figure or flag the spread.

**m8.** Quote (§5.2): *"The harness serves `PRF_k(q) = BLAKE2s(k ‖ q)`."* A1 m6 and A2 m11 both
say: use BLAKE2s's keyed mode, not `k ‖ q` (length-extension hygiene; under W5 the concatenation
makes every secret answer a public-channel value at release, complicating `pubOrdered`). State the
keyed mode here and in §9.2.

**m9.** Quote (§1, §7.1, §8, §9): *"PRF security and BLAKE2s collision resistance, both
falsifiable."* Collision resistance of a fixed unkeyed function is not an assumption in Naor's
sense (no challenger; Rogaway's "human ignorance"); the report's own mechanism, the collision as
an output of the budgeted extractor, is precisely the constructive form that makes it meaningful.
Say "PRF security (falsifiable) and collision resistance of BLAKE2s in constructive form (the
extractor hands over the pair)". The contrast with W5's heuristic stands.

**m10.** Quote (§6.2): *"The paper's concrete bound lets a verifier skip at most a `2^-63` fraction
of the sensitive queries at error `2^-128` (L1)."* L1 tags this "derivation" (Thm 4.1 at
`p = √(vq/t)`) and it is about the paper's hard DTIME language, not this relation's sensitive
queries; the transfer to our setting is T1 Thm 2.2 with its `(Q + qV)·ε` per-query bound. Attribute
it so.

**m11.** Quote (§7.2): *"Bitansky–Canetti–Paneth–Rosen rule out a standard-model version."* A2 M4:
BCPR14 rule out extractable one-way functions with arbitrary auxiliary input *assuming
indistinguishability obfuscation*. Add the condition.

**m12.** Quote (§1): *"Witness-sending, concatenation and a flat SNARK with chain starts in the
clear all satisfy it (kernel)."* The lift theorem is kernel for any `V₀`, but the only Lean
instance is the non-succinct `flatV` (`flatState`); that a succinct `V₀` exists is paper (P4,
"That a succinct `V₀` exists"). §6.4 says this; the summary's tag should read "(kernel; the
succinct instance is paper)".

**m13.** Quote (§10): *"The whole probe library, about 5,200 lines, builds in under 20 s from cold
contract oleans."* No note measures a whole-library build. P2: 26 s for the seven Attested
modules after an edit to `Model`; P3: 37 s for three TwoChannel modules, `Merkle` alone 21.3 s to
check; P4: 17.0 s; P1: 9–13 s. Replace with the per-note figures, or measure and log it. "5,200
lines" is `wc -l` (5,174), not `scripts/loc.py` code lines (P2 ≈ 860, P3 1,006); say which.

**m14.** §7.2 and §9.4 recommend the late-preimage *escape*. A2's postscript notes the escape
form "shares the statement-digest problem": an honest prover that recomputes `leafStmt`/`nodeStmt`
late (column R's node mode is handed child digests) makes the escape valid on the honest log, so a
relation-tag exemption (A2 M2) or a liveness rule rejecting escape outputs on honest proofs is
still needed. Add this to §7.2's "price" bullet and to the R1 stage row.

**m15.** The PRF hybrid's requirements are understated. Quote (§5.2): *"Every winning condition
the theorem bounds can be decided in polynomial time with oracle access … losing only
`Adv_PRF`."* The distinguisher runs the whole evaluation and the extractor within its budget
`B t = 2^48 + 2^16·t` (W2 A.7: hours, `≤ 2^28` queries), so `Adv_PRF` is taken at that cost; the
step from lazily sampled answers to a random function and to randomised adversaries remains paper
(P2, W2 A.7, "as v3"); the service's correctness is assumed (W2 M8); and the deployed whole-tree
bound is about `2^-100` at `ε = 2^-128` because `Q` counts every query of the evaluation (W2
§A.6). State the four in §5.2 or §7.1.

**m16.** Quote (§1, §9.5): D4+ *"closes the trivial-root half (#6(a)) by the theorem"*. There is no
Lean theorem; A3 §3 is a paper information bound from the certified caps (`proofCap`, `qV`), and
A3 M2 says the mechanism is both caps, with `qV ≤ 2^13` and `proofCap < 64·n` as invariants. §7.4
tags it "(A3, paper)"; the summary and §9 should say "by the certified caps (paper), not by a
measurement".

**m17.** Terms a cryptographer or zkVM engineer meets undefined: `#6(a)`/`#6(b)` (first explained
in §7.5 headers, used from §1), `T_V`, "board T", `qV`, `proofCap`, `chainCap`, `O-18`, "the
§6.7 recognition rule", `V3-5`, spartan-chain, Flock, WHIR, leanVM, `Computes`, "decoding
extractor", "straight-line", `runLog` (appears first inside Lean in §4), "potential" (never
defined as a function from logs to `[0, ∞)` whose value below 1 licenses extraction). "Escape" is
used in three senses: escape from the impossibility (§1), the attestation escape from re-asking
(§7.1 header), and an extractor output in place of a witness (§7.2). A ten-line glossary after §3
and one sense per word would fix all of these.

**m18.** §9 decision 5 (*"the competition's records then certify the attested deployment and not
a public-hash deployment"*) is the caveat a cryptographer raises first against "closes O-25 by
construction"; it belongs in the summary verdict, not only in the decision list. Same for the
designated-verifier window and the fact that the D4 argument is online and stateful, so proofs
are not transferable until key release (T1 §6.3 item 3: "not a NARG").

**m19.** Trusted-line bases differ: §7.1 "288 → ≈ 340" uses the rules worktree's 288, §7.2
"≈ 370–450" uses both 288 and this worktree's 328 (CLAUDE.md, W1 §0). Name the base once.

**m20.** Quote (§7): *"Our variant is CCS22/CCGOS23's 'accumulation of oracle queries', with the
organiser as the trusted decider (L1)."* L1's literal match is "the SROM with an online MAC" (L1
summary 4); the LDROM/AROM accumulators rewind or need algebra (L1 §3), which D4 does not share.
Keep the analogy but say it is one.

**m21.** Quote (§8 table): *"Trusted lines added … D3 +150–300"* against §7.3's *"100–200-line
trusted signature specification"*. Both are W1 §4 (spec 100–200 plus the signing-oracle model);
say "+150–300 including the signing-oracle model".

## Checks that passed

Statements read against the files and found as described: `compose`, `compose_flat`,
`paper_tree`, `ws_ksRel`, `concatState`, `Backdoor.backdoor` (`KSRel V E errorCap 1` and the
32-byte magic proof under `blake2sOracle`), `lazy_no_kstate` (natural extractor, any error),
`deferState`, `attState`, `calls_node` (exactly `[attest (hashList xs)]`), `att_W1` (`KSA … 0 1`),
`compose_all`, `Paper.paper_tree` (`nq·ε`, `nq + nc ≤ logCap`), `acceptAll_choice`,
`hashList_not_coll`, `encList_inj`, `merkleState`, `merkleState_pubStep` (equality),
`merkle_eps_ge`, `bd_no_kstate`, `bd_extractor_inverts`, `bdSecW_kstate`, `lift`,
`lift_runner_ws` (`d ≤ 14`), `liftState_μ` (`rfl`), `reask`, `flip_reask`. Numbers checked
against C1 (rows 1–15, the service table against `svc.log`/`svc-multi.log`: 1.22×, 2.3×, 82×,
10.3–12.5 Mcalls/s), A1 (2.6 M, 250 MB, 40×, 250×, 89 days), A2 (+0.5%, 476 RTTs, 1.4–52%,
+80–120 lines), A3 (1.16×, 2.3–7.5×, 524 KB, 17 ms–0.61 s, `qV ≤ 2^13`), W2 (+50 lines,
`6.7·10^7–2.7·10^8` calls). Literature: the paper's §1.2 names the SROM/LDROM/AROM and the
"relativized NARK by sacrificing succinctness" remark (paper lines 212–229); its theorems, the
interactive and computational extensions, and §2.8's "far from one another" are as cited; CT10's
"trusted Internet service", CGSY24 Thm 5.1, CGH §4, DRS09, snark.fast's fixed verifier agree with
L1. W1 §11.2 and A2 §2 support the disguise list in §5.2.

## Verdict

The report's main line is correct and, with the fixes above, fairly stated:

1. **Relativization diagnoses O-25 correctly, and the relation alone does not close it.** Kernel
   (`Backdoor.backdoor`) and paper (A1 M8, T1 §6.4) agree; the secret deployment closes it modulo
   PRF security, with the designated-verifier and key-hygiene costs the report lists.
2. **In the pure ROM the requirement is vacuous or non-compressing.** Vacuity is kernel for
   witness-sending, concatenation and the abstract lift; non-compression is the deterministic core
   (`lazy_no_kstate`, `reask`/`flip_reask`) plus T1 Thm 2.2 on paper and C1's numbers. M3
   (completeness) and M6 (units) are the caveats that must be added; neither reverses the
   conclusion.
3. **An attested oracle is the workaround.** The model's laws, the one-call escape, composition
   and the collision disjunct are kernel for a node with children in the clear (M2); the succinct
   node, the PRF hybrid and the service's correctness are paper, as the report mostly says. The
   W5 split and its late-preimage escape are correctly reported as trading two constructive
   assumptions for one unfalsifiable heuristic, with the kernel evidence for the laws (M1 fixes
   the one overclaim).
4. **#6(b) is not fixed by any theorem studied.** A3 M1's relabelled flat proof is correctly
   carried into §7.4, §7.5, §8 and §9.6; D4+'s #6(a) closure is a paper cap argument and should be
   labelled as such (m16).

The recommendation (drop D1/D2, adopt the log-relative relation with an attested secret oracle,
W5 as an option, D4+ for #6(a), shape for #6(b)) follows from the evidence. Required before the
report is used for a design decision: M1–M6; strongly advised: m8, m9, m14, m15, m17, m18.

## Fix pass (orchestrator, 2026-10-22)

All six majors and all 21 minors are applied in `docs/explore/REPORT.md`.

- **M1, M4, m1–m4.** Every negative Lean result now states its extractor and error range
  (`pure_no_kstate`, `col_no_kstate`, `lazy_extractor_collides`). `queries_defer` is an upper bound.
  `reask`'s hypothesis is on the erased log. `v3_no_compose` is about the control's extractor. The
  toy's side conditions are stated.
- **M2.** The summary, §7.1 and the evidence table say the attested node in the kernel carries
  children in the clear; the succinct node is a paper obligation (W2 §A.4, issue #7).
- **M3.** §4 has a completeness paragraph (context form; A1 m2, W2 M10). §6.4 adds the lift's
  completeness caveat. R1 in §9 includes completeness.
- **M5.** `docs/explore/probes/audit/Audit.lean` now covers all 36 declarations the table names.
  The log was re-run. The build figure is a measured cold rebuild (43.5 s, logged), and the line
  count is from `scripts/loc.py`.
- **M6.** §6.3 states both units and which one carries the verdict.
- **m5–m21.**
  - `h_V` figures per class.
  - Raw ratio against margin per side.
  - C1's field-work figure.
  - Keyed-mode BLAKE2s.
  - Constructive collision resistance in place of "both falsifiable".
  - L1's `2^-63` attributed as its derivation for the paper's language.
  - BCPR14's iO condition.
  - The succinct lift instance tagged paper.
  - The late-hashing exemption (A2 postscript) in §7.2, §9 and R4.
  - The PRF hybrid's fine print in §5.2.
  - D4+ "by the certified caps (paper)" throughout.
  - A glossary after §3, with "escape" in one sense only.
  - What the records certify and the designated-verifier window in the summary.
  - One trusted-line base.
  - The analogy wording for CCS22/CCGOS23.
  - D3's line counts reconciled.
