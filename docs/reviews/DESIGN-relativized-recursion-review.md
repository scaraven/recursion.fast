# Review of `docs/DESIGN-relativized-recursion.md` (proposal, 1,080 lines, uncommitted)

Adversarial reviewer, 2026-10-22. Checked against the exploration worktree (`REPORT.md` as the
ground truth, `EXPLORE-report-review.md` and its fix pass, notes W1, W2, A1–A3, T1, C1, L1, P1–P4,
every `.lean` file under `RecursionFast/Explore/`, the C1 service logs, the audit log) and the rules
rewrite (`DESIGN-v3.md`, `Contract/{Security,Extractor,Certificate}.lean`, `DESIGN-AMENDMENTS.md`
V3-S2R-A9, `scripts/loc.py` = 292). Quotes are from the design document; "Lean" cites file and
declaration under `RecursionFast/Explore/`. Line numbers are the document's.

## What passed

Every Lean theorem the document names was read against its statement. Scope qualifiers are carried
correctly: `lazy_no_kstate` (the natural extractor `dE`, any `ε`), `lazy_extractor_collides`
(`Collides`, a BLAKE2s collision only for a leaf `c₁`), `kstate_of_leaf_surjective`, `queries_defer`
(`≤ Q.length`), `reask` (`k.μ (eraseKey L q) < 1`), `v3_no_compose` (the control's own extractor),
`attState`/`calls_node`/`att_W1` (children and list in the clear; `calls = [attest (hashList xs)]`),
`attV_complete` and `runLog_append_of_clean` (one node; `Clean`), `compose`/`compose_all`/
`compose_blake2s`, `Paper.paper`/`paper_tree` (`nq·ε`, `nq + nc ≤ logCap`), `acceptAll_iff`/
`acceptAll_choice`/`final_prop_vacuous`/`exists_isColl`, `encList_inj`/`encList_not_inj`/
`hashList_not_coll`/`Item.enc_append_inj`/`IsColl.blake2s`, `KStateA.ofRel` (`μ ∘ ansLog`),
`gμ_*`, `ws_ksa`, `KState2` (`pubStep` on `pubConsistent (L ++ [.pub m a])`, `secCount`),
`ofHist_pub`, `merkleState` (`ε = 1/2`), `merkle_eps_ge` (natural-extractor states only),
`honest_extracts` (good leaves, neither hash equal to the root), `honest_extracts_blake2s`,
`col_no_kstate`/`pure_no_kstate` (`ε < 1`, natural extractor), `*_extractor_inverts` (every
extractor), `bd_no_kstate` (any `ε`), `bdSecW_kstate` (`errorCap`), `lift`/`liftState_μ` (`rfl`)/
`flatState`/`lift_free`/`lift_runner_ws` (`d ≤ 14`), `Backdoor.backdoor` (`KSRel V E errorCap 1`,
32-byte magic proof). Numbers checked against their sources: C1 rows 1–15 and §2.1–§6 (25.9k/9.2k/
5–12k, 2.6–13.2 M, 80–850 MB, 0.6–3.2×, 6–24×/25–95×, 2–2.5×/5×, 2.5–12.6×/1.17×/0.18/<15%,
1.09×/28.3k/0.79–1.56×, 4.7–14.5 M, 262,614/278 MB/6.7·10^7–2.7·10^8, 82×/2.3×/1.22×/10–12.5 M
calls/s against `svc.log` and `svc-multi.log`, 71 GB/17–69 GB/62 GB, +0.3–1.2%/+30–110%, 89 days/
9.4 h/14–62/8–41%, 93–99.6%/69–75%/≈10%/<1%, 3.1·10^7), A1 (40×, 250×, 2.6 M, 250 MB), A2 (+0.5%/
+0.1%, 476, 1.4–52%/13%, 13 + 100 items, +80–120 lines), A3 (1.16×/0.5×, 2^15 + qV, 2^-7, 524,320 B,
64 B over, 2^13/2^12, `proofCap < 64·n`, 17 ms–0.61 s, 1.09–39 s, 0.25 µs/4 ms/30 ms, 2.3–7.5×,
77.6/33.6 MB, 2^22/17×/0.4 s, +6 lines), W2 (+28/+1/+16/+6/±0 = +50, 16,352 B/511 calls, 300–400
lines of Rust, `2^33–2^35`, `Q ≈ 2^26–2^28`, `2^-100`), the audit (36 `#print axioms`, 36 lines
in the log, 21 modules = 20 files + `Explore.lean`, 5,196/3,008 lines, 43.5 s), the rules rewrite
(292 code lines; `Computes` with `e.1.size < 2^64`, `outCap = 2^24`, `B t`; V3-4 … V3-8 as
summarised; trust items 2, 4, 5, 6, 8, 9 changed, 1, 3, 7 unchanged). All six review majors and the
21 minors survive in the document (keyed mode, constructive CR, units, 36 declarations, `d ≤ 14`,
the lift's completeness caveat, "by the certified caps (paper)", not a NARG, one line base, iO
condition, the late-hashing exemption, the hybrid's fine print). The §9 ledger covers A1 M1–M10,
m2, m6, m8; W2 M1–M11, m1–m8; A2 M1–M5, m2, m6–m11; A3 M1–M4, m1, m4, m6–m8; T1 §0, §5.2, §6.3;
the report review. Missing from it: A3 m5 (folded into M3 below).

## Major findings

**M1. RO-2 is right, and as written §4.5 excludes every `δ > 0` design; RR-6 and the §4 "normative"
label do not carry the caveat.** Quote (L427): `def CompleteWithError (R) (P) (V) (δ : ℝ≥0) : Prop :=
∀ ctx, failCtx R P V ctx [] ≤ δ`. Quote (L83–88, RR-6): *"Completeness in context form (§4.5). |
`CompleteWithError` takes the relation outside the game: ill-typed for a log-dependent relation."*
A context is an arbitrary `OProg`. It can simulate `P c w` for candidate statements by making `P`'s
queries itself (lazy sampling answers a repeated query from the record, `failProb`'s `find?` case,
rules `Security.lean`), observe which candidate the real run would fail on, and return it; the real
`P c w` then sees the same answers and fails. For a design whose honest failure is `δ' > 0` per
statement (the case V3-S2R-A2 was decided for: *"This admits grinding and challenge-dependent
exceptional cases"*, rules `Security.lean` header; V3-4 in `DESIGN-v3.md` L82), a context trying `N`
candidates fails with probability `≈ min(1, N·δ')`, so only `δ' = 0` designs satisfy any `δ ≤
2^-128`. W2 §A.5's *"receives the same random answers the prover would, so `δ` is unaffected"* is
consistency, not selection, as the document itself says (L447–448). This contradicts the base the
document declares (L14, `CompleteWithError` with `δ ≤ 2^-128`), the §8 row *"Grinding | yes (see
RO-2)"* and the honest provers the competition targets (A1 m8: proof-of-work boosting, leanVM-style).
The decision RR-6 is therefore not decidable as stated. Fix to state (two alternatives, R1 picks one):
(a) **honest contexts only**: an inductive `Honest P : OProg (Digest × Wit) → Prop` (a `ret (c, w)`
with `w` a leaf witness; a node context that runs two honest sub-contexts, then `P` on each, and
returns the node statement with the two proofs), and `CompleteWithError R P V δ := ∀ ctx, Honest P
ctx → failCtx R P V ctx [] ≤ δ`; about six trusted lines; the harness's `tree` mode and column R's
node mode are honest contexts, selection is impossible, and the Library lemma "clean node
completeness ⇒ tree completeness" (RO-3) becomes the submitter's route to the certificate; `δ` is
then per tree, so either `completenessCap` is read per tree or the clause divides by the number of
`P` runs (A1 m8: `511·δ' ≤ 2^-119`). (b) **a per-query completeness charge**, mirroring `ε`:
`∀ ctx nq, DepthLE ctx nq → failCtx R P V ctx [] ≤ (nq + 1)·δ`; keeps the full context form (a
context can test at most one candidate per prover-run's worth of queries) but changes what the cap
means. Corrected RR-6 row: *"Completeness over honest contexts (§4.5; RO-2 fixed by (a) or (b)). |
`CompleteWithError` takes the relation outside the game; an unrestricted context can search for a
failing statement."* Add the same caveat to §4 L269–272 ("normative … except the quantifier of
§4.5, RO-2").

**M2. RO-4 is right: with §4.2's `Valid`, the honest extractor cannot satisfy `Computes`, because a
certified list has no size bound and `.coll` outputs must fit `outCap`.** Quote (L308–309):
*"`def Valid (L : Log) (xs : List Item) : Prop -- ans q a: q.size < 2^64 ∧ L.answer q = some a; att
h: L.attested h`"*. Quote (L987): *"either `Valid` carries the service's list caps … or the stage
shows why outputs fit"*. `Computes` (rules `Extractor.lean`) requires `o.length ≤ outCap = 2^24`
words on every log in the domain (tape ≤ `2^64` words). The honest node extractor returns
`.coll (tagList ‖ enc xs) (tagList ‖ enc ys)` with `ys` the certified list found in `L` (W2 §A.4,
Lean `attE`); in the model nothing bounds `|ys|` below the tape, so on a well-formed log with a
`2^30`-byte certified list the output exceeds `outCap` and `final` cannot be discharged through
`Computes`. The stage cannot "show why outputs fit" without a bound in the model. Fix: put the
service's caps into `Valid`, the same move §4.3 makes for `2^64`:
```lean
def Valid (L : Log) (xs : List Item) : Prop :=
  xs.length ≤ listItemCap ∧ (encList xs).length ≤ listByteCap ∧ ∀ x ∈ xs, x.OK L
-- OK (ans q a) := q.size ≤ queryCap ∧ L.answer q = some a      (2^20; implies V3-S2R-A9's 2^64)
-- listItemCap = 2^16, listByteCap = 2^24 (the §4.8 table, now contract constants: +3 lines)
```
Then every certified list of a `WF` log is capped, the two `.coll` strings are at most `2 · (1 +
2^24)` bytes ≈ `2^22` words, the carried list is bounded by `V`'s circuit, and the tree walk's
collisions are 65- and 41-byte preimages. This also closes W2 m1's "fails at deployment only" gap
(the model then accepts exactly what the service accepts; the `2^64` tape bound stays in `Computes`
for uncertified queries). Update §4.7's `Oracle.lean` delta to +31 and §4.3's last sentence.

**M3. `qV ≤ 2^13` (RR-12) is tight at the long shape RU-4 recommends, and the document gives only
the ranked-shape number.** Quote (L794–795): *"**Fix: `qV ≤ 2^13`** (`2^12` under W5), which fits
spartan-chain's 5,156 queries plus attests and excludes the hybrid everywhere"*. Quote (L75): *"What
does not change. … `qV ≤ 2^16`"*. A3 m5 (**measured**, also C1 §3.2 row 1): spartan-chain makes
7,774 queries at `n = 2^20`, 418 under `2^13`; the certificate has one `qV` for every `n ≤
chainCap`, so a re-querying leaf branch is incomplete for `n > qV` and the cap is a design
constraint on the leaf verifier at `n = 2^20`. Choosing RU-4 (long shape) and RU-6 (R3) together
therefore puts the certified baseline leaf 5% under the cap, which the user should see before
deciding either. Corrected §6.3 text: *"`qV ≤ 2^13` fits spartan-chain at the ranked shape (5,156
queries) and at the long shape (7,774 at `n = 2^20`, A3 m5, 418 to spare for attests); a `V` whose
only leaf branch re-queries the chain is incomplete for `n > qV` (A3 m5), so leaves are SNARKs or
compact lists."* Add the A3 m5 row to §9. Corrected L75: *"`qV ≤ 2^16` (R1–R2; `2^13` under R3)"*.

## Minor findings

**m1.** Attest calls per node are stated three ways: RR-3 (L85) *"a node makes one `attest`
call"*; §4.7 (L514) *"`V` attests `h₁ h₂`"*; §4.8 (L541) *"Recursive, it makes one or two calls"*;
§8 (L876) *"one `attest` per node"*. Lean `calls_node` is one call for the probe's node, which
certifies the *concatenation* of both children's lists (`attV_complete`, `xs₁ ++ xs₂`). Say once:
"two calls, or one when the node prover certifies `[att h₁, att h₂]` (W2 §A.1); `qV` counts them".

**m2.** L339–342 attributes `wrong_not_wf`, `unasked_not_wf`, `shadowed_not_wf`, `unattested_not_wf`
to `Attested/Model.lean`; they are in `Attested/Controls.lean` (§13.1 has it right).

**m3.** §13.1 scope column (L1039–1040) says *"negatives for the natural extractor"* for a row that
includes `col_extractor_inverts` and `pure_extractor_inverts`, and *"natural extractor"* for
`bd_extractor_inverts` and `bdSecW_kstate`. The `_inverts` theorems quantify over every extractor
`E'` (Lean `Merkle.lean` L570–575, L641–645; `Backdoor.lean` L132–135); `bdSecW_kstate` is a
positive. Write "natural extractor (`*_no_kstate`); every extractor (`*_inverts`)".

**m4.** L472–476 cites *"Hidden conditions ([T1] §5.2)"* for the tape being the whole evaluation's
log; T1 §5.2 lists depth, length guard, cycles, collisions and `Q` growth; the tape point is W2 M6.
And L61–62 *"kernel for toys, paper for a succinct node"* undersells `compose_all`/`paper_tree`,
which are kernel for every `KStateA` (Lean `Compose.lean`, `Paper.lean`, no toy hypothesis); what is
toy is the *node state* (`attState` with children in the clear). Say "composition is kernel for any
attested state; the succinct node's state is paper".

**m5.** L592–593: *"`D` runs the evaluation and the extractor within `2^48 + 2^16·t` steps, hours
and at most about `2^28` queries"*. At ranked size the tape is about `2^33` words (71 GB of
queries, C1 §5.3), so one extraction is budgeted at `≈ 2^49` steps and `treeExtract`'s 511 of them at
`≈ 2^58`: days per extraction on the contract machine, not hours. Nothing changes (far below any
keyed-BLAKE2s margin), but say "polynomial, about `2^58` steps at ranked size, and at most `2^28`
queries".

**m6.** §9 T1 row (L920): *"an oracle leaf is hopeless | … concrete leaf"* contradicts §6, which
makes the leaf an oracle chain. Write "hopeless in the pure ROM ([T1] §4.4); concrete leaf under
R1–R2, attested oracle chain under R3 (§6)".

**m7.** §11 R1 (L968): *"the interim harness may still run `V` on public BLAKE2s"*. After R1
`Certificate.secure` is `KS S.RelL …` and `V` may `attest`; `OProg.run H` has no attest case and
`Vb` is only deleted at R2. The R1 row must name the interim semantics (an in-process stub service
answering `attest` from a local set, or `attest ↦ false`), or move the `Vb` deletion into R1.

**m8.** §5.1's block (L666) concludes `Valid R c L o`, the same name as §4.2's list validity
`Valid L xs`; Lean has `Valid mode R c L o`. Rename (`SoundW`) and say the block drops `mode`.

**m9.** L320–323: *"a `V` that accepts because a hash is unattested accepts on the empty log for
every statement"*. Only a `V` that accepts on `false` *alone* does; W2 m3's content is that `false`
is forced by any adversary (a random `h`), so the branch adds nothing a certified `V` can use. Say
that.

**m10.** L229–230 *"the lift covers up to `2^14` leaves (`lift_runner_ws`, `d ≤ 14`)"* is right; P4
§"What this does not show" adds that the halves must fit too, `d ≤ 13` on paper. Add "(`d ≤ 13`
with the halves, paper)" or drop the number.

**m11.** L1053 *"The 36 declarations of [REPORT] §10's table"*: the table in the document's own
§13.1 lists more names than 36 (`gμ_*`, `*_not_wf`, `attV_complete`, `runLog_append_of_clean`,
`compose_blake2s`, `KStateA.ofRel`, `exists_isColl`, `toA_runLog`, `flatState`, `lift_free` are not
in `Audit.lean`). They are audited in the per-note logs only (P2–P4). Say "36 in `Audit.lean`; the
rest in P1–P4's own `#print axioms` output".

**m12.** L17 *"the section numbers cited are the same in both"* (main's `DESIGN-v3.md` and the
rewrite's): not checkable from the rewrite alone; either cite the rewrite only (the document's base,
L13) or verify once and drop the sentence.

## Cuts

The document repeats itself in five places (a decision's "why", its body section, §8's row, §9's row
and §12's item). Concrete passages, with savings (≈ 150 lines, to ≈ 930; the 900 target needs the
last item too):

1. L55–67, §1 "What changes, and why" (13 lines): the RR-* "Why" column says the same. Keep a
   three-line pointer. −10.
2. L68–77, "What it costs" / "What does not change": the first duplicates §10 and §12.2; keep the
   second as three lines (with M3's correction). −6.
3. L97–103, §1.2: verbatim in §12.2. One line: "Six decisions are the user's, §12.2." −5.
4. L119–123 (the F2 memo) and L245–251 (digest-parametric `V`): one sentence each; the rest is
   history a design reader does not need. −9.
5. L132–146, the impossibility paragraph: keep "the theorems do not apply verbatim (Prop. 1.4);
   knowledge forces re-asking (§3.2); the SROM is where relativized SNARKs exist; the technique fails
   in D4 at both steps ([T1] §6.1)". −9.
6. L152–177, §3.1 D1 (table and percentages): a rejected design (RR-10); eight lines suffice (the
   charge is gameable in every self-measured form, local work is unpriced, the statistic is wrong,
   the winner is a chain prover). −18.
7. L204–210, the §3.2 shape table: duplicates §7.3 and §8 for a rejected design; one sentence with
   the ranked and long rows. −5.
8. L238–265, §3.4: one line per direction, three for D3 (RU-2 cites it). −16.
9. L339–342, L411–418, L479–486, the three "Evidence" paragraphs: every name and scope is in
   §13.1; one sentence each pointing there. −12.
10. L559–567, "Transport": §7.3's "D4 traffic" row has the numbers; keep the measured sentence and
    the fix. −5.
11. L598–609, "The other channels" / "What it kills": the disguise list is §8's backdoor row and §2;
    five lines. −7.
12. L674–692 and L694–707: the "Kernel:" sentences of §5.2 repeat §5.3; keep the names in §5.3 only.
    −8.
13. L737–741, §5.4 "Cost": §7.3 rows "W5 node" and "W5 traffic". −4.
14. L778–785, "Not #6(b)": §7.2, §8 "Proof of parent" and §9 A3 M1 say it; three lines here. −5.
15. L827–840, §7.1: §8's witness-sending row and §6.2 carry it; six lines. −8.
16. L866–893, §8: drop the rows "Deferral; lazy parent", "Collision laundering", "Session mixing",
    "Precomputed proofs", "Service as co-processor" (each is one sentence of §3.2, §4.4, §4.8,
    §4.10). −6.
17. L897–924, §9: drop the T1 and Review rows (the report review is cited in §13) and shorten the
    "Problem" column to the finding's id and a noun phrase. −6.
18. L1012–1019, the §13 index paragraph: repeats the provenance paragraph. −5.
19. L32–44, terms: fold "ranked, long shape", `h_V`, spartan-chain and Flock into two rows. −4.
20. L630–632, §4.10 "Rejected": report material. −2.
21. To reach 900: §3.2–§3.3's kernel bullets (L185–202, L220–236) can be reduced to the theorem
    names with §13.1 pointers, since the design decision they support is RR-10 and the lift's
    caveat is restated in §4.5. −30.

## Verdict

**Fidelity.** The document compiles the exploration faithfully: every number and tag I checked
matches the report, the review's fixes survive, the kernel qualifiers (natural extractor, `ε < 1`,
children in the clear, two-leaf toy, `d ≤ 14`) are carried into the body and §13.1, the corrected
values (keyed mode, `qV ≤ 2^13`, D4+ by the certified caps, 1.16×) are used throughout, and the §9
ledger is complete but for A3 m5. The decisions table, stages, trust statement and open items are
consistent with the body except for the attest count (m1), the `qV` line (M3) and the R1 harness
row (m7).

**The specification.** §4.2–§4.4, §4.6–§4.9 are precise and correct as a contract shape: the
`KState` laws are the probes' (`KStateA`), `Out`/`Sound` under `Computes` is the right form and the
document shows why, the encoding and its bound are kernel-backed, `runLog`'s semantics (`false` on a
miss, `none` on `certify`, the final log) are the service's, and the lifecycle and failure semantics
are W2 §B's fixes. Two parts do not work as written: the completeness quantifier (M1: unrestricted
contexts collapse the clause to perfect completeness over reachable logs) and `Valid` without the
list caps (M2: the honest extractor's `.coll` output cannot be shown to fit `outCap`). Both are
flagged by the author as RO-2 and RO-4, both are real, and both have a few-line fix stated above.
With M1–M3 applied (M1 and M2 change normative text; M3 adds a number and a caveat), §4–§6 are
precise and correct enough to start stage R1 from. Strongly advised before the user decides RU-1 …
RU-6: m1, m5, m7; the cuts are at the user's discretion.

## Fix pass

Author's fix pass, 2026-10-22, on `docs/DESIGN-relativized-recursion.md`. Line count: **1,080 before,
920 after** (`wc -l`). Every remaining evidence tag, Lean name, number and scope qualifier was kept.

**Majors**

- **M1 fixed, with fix (a), honest contexts.** §4.5 now defines `Honest P` (fixed leaf witnesses; a
  node runs two honest contexts, `P` on each, and returns the node statement) and states
  `CompleteWithError R P V δ := ∀ ctx, Honest P ctx → failCtx R P V ctx [] ≤ δ`; `δ` bounds each honest
  prover run (a 511-run tree fails with probability at most `511·δ ≤ 2^-119`, A1 m8); what it gives up
  (node witnesses with children `P` did not produce, used only by the lift's caveat) is stated. Chosen
  over (b) because it keeps `completenessCap`'s per-run meaning from V3-S2R, makes selection
  impossible by construction, matches what the harness's `tree` mode and column R run, and leaves the
  submitter the Library route "node completeness ⇒ completeness over honest contexts" (RO-3), whereas
  (b) changes the cap's meaning and asks every submitter for an adaptive completeness proof; (b) is
  recorded in §4.5 as the rejected alternative. Also updated: RR-6, RO-2 (resolved), §8 grinding row,
  §4.7 (`δ` per honest prover run), §10 item 5, §11 R1, §3.3 (the lift is an entry under honest
  contexts), §6.1 and §6.4 (`Honest`'s chain leaf under R3).
- **M2 fixed.** `Valid` carries `queryCap = 2^20`, `listItemCap = 2^16`, `listByteCap = 2^24` (§4.2);
  §4.3 and §4.4 say why (certified lists bounded; a list collision is about `2^22` words, inside
  `outCap`); §4.8's table takes its caps from `Valid`; the `Oracle.lean` delta is +31, the total +53
  (about 345 of 500) in §1, §4.7 and §10; RR-4 updated; RO-4 resolved. The W2 m1 gap closes for
  certified lists; a verifier's direct query above `2^20` bytes still fails only at deployment, as a
  reject, which §4.2 states.
- **M3 fixed.** §6.3 gives 7,774 queries at `n = 2^20` beside 5,156 (A3 m5, **measured**), the
  418-query margin under `qV ≤ 2^13`, the one-`qV`-for-every-`n` point and the incompleteness of a
  re-querying leaf; the terms table, §7.2 and §4.7's `cap` comment carry the number or the `2^13`; §1
  now reads `qV ≤ 2^16 (R1–R2; 2^13 under R3)` and the header lists v3 §2.2; §12.2 records the RU-4 ×
  RU-6 interaction; §9 has an A3 m5 row.

**Minors**

- **m1 fixed:** RR-3 states the count once ("two calls, or one when the node prover certifies
  `[att h₁, att h₂]`; `qV` counts them"); §4.7, §4.8 and §8 refer to it; §13.1 notes that
  `calls_node` is for the concatenated list.
- **m2 fixed:** §4.2 names `Attested/Controls.lean` for the `*_not_wf` controls; §13.1 lists them there.
- **m3 fixed:** §13.1's scope column separates natural extractor (`*_no_kstate`), every extractor
  (`*_inverts`) and the positive `bdSecW_kstate`.
- **m4 fixed:** §4.6 cites the tape point to W2 M6 and keeps T1 §5.2 for depth and collisions; §1 and
  §4.6 say composition is kernel for any attested knowledge state, paper only for the succinct node's.
- **m5 fixed:** §4.9 fine print (1): polynomial, about `2^58` steps at ranked size (a `2^33`-word tape,
  511 extractions), at most about `2^28` queries.
- **m6 fixed:** §9's T1 row: hopeless in the pure ROM; concrete leaf under R1–R2, attested chain under R3.
- **m7 fixed:** §11 R1 deletes `Submission.Vb` (no `attest` case in `OProg.run`) and names the interim
  harness, an in-process stub service (`query` by public `blake2sOracle`, `certify`/`attest` from a
  local set with `Valid`'s checks); R2 replaces the stub and deletes `blake2sOracle` and `tagRO` as a
  relation constant; RR-7 points to §11.
- **m8 fixed:** §5.1 writes `SoundW` and says the mode argument is dropped.
- **m9 fixed:** §4.2's first bullet: `false` is forced by any adversary, so the branch adds nothing; a
  `V` accepting on `false` alone is the accept-all obligation.
- **m10 fixed:** §3.3 and §13.1 add "`d ≤ 13` once the halves must fit, paper".
- **m11 fixed:** §13.2: 36 declarations in `Audit.lean`; the other names in P1–P4's own `#print axioms`.
- **m12 fixed:** the sentence is dropped; the header now says `v3 §n` cites the rewrite's
  `DESIGN-v3.md` and that `main`'s predates it (the two files' section numbering was also checked and
  is the same).

**Cuts.** 1–16 and 18–21 applied (21 as theorem names with §13.1 pointers, one sentence per result, so
the §3.2–§3.3 argument still reads). 17 applied in part: the problem column is shortened and rows are
merged, but the T1 and report-review rows are **kept** (compressed), because the document's brief
requires the ledger to cover T1's corrections and the report review that changed the design.

**Also.** The A3 m5 row is in §9, and a `DREVIEW M1, M2` row records this pass. The provenance cites
this review by URL on the exploration branch ([DREVIEW]). W5's trusted-line estimate now says
explicitly that A2's +80–120 is over v3 with D4's shared machinery included (about 372–412 of 500).
