# V3-S1 review: the v3 contract (Relation, Oracle, Security, Extractor, Tree, Certificate) and its controls

Adversarial review of Stage V3-S1 on branch `v3/s1-contract` (uncommitted working tree), 2026-10-19.

## Scope and method

**Read.**
- `CLAUDE.md` and `docs/DESIGN-v3.md` §1–§8, §11 and §12.
- `docs/stages/V3-S1-RESULT.md` and the V3-S1 section of `docs/DESIGN-AMENDMENTS.md` (A1–A18).

**Read in full.**
- `RecursionFast/Contract.lean`.
- `Contract/{Hash/Blake2s,Relation,Oracle,Security,Machine,Extractor,Tree,Certificate}.lean`.
- `Controls/*.lean`.
- `Library/{Oracle,Security,Words,WitnessSending,Machine}.lean`.
- `legacy/v2/README.md`, `lakefile.toml`, `scripts/{ci.sh,check-hygiene.sh,AxiomAudit.lean}` and the
  `git diff HEAD` of `Machine.lean` and `CLAUDE.md`.

**Isolation.**
- A golf agent was editing proofs in the main tree, so the LSP reported its imports as out of date.
- Every Lean check therefore ran in a snapshot copy of the working tree taken at 11:25:
  `/tmp/v3s1-review/snap`, with the shared `.lake/packages` and `ext/Clean` symlinked.
- At the time of writing, the contract and the controls are byte-identical to the snapshot. Only
  `Library/{WitnessSending,Words}.lean` have changed since (golf).
- This review edits nothing except this file.

**Builds and checks.**
- `lake build RecursionFastContract RecursionFastLibrary RecursionFastControls` on the snapshot:
  green, 2 min 32 s cold (`/tmp/v3s1-review/build.log`).
- `scripts/loc.py` over the trusted files: **320** code lines.
- The hashlib known answers were rerun with `python3 -I` and match.
- The axioms were printed with `#print axioms`.
- Five contract mutations were rebuilt against the controls (table under Probes).
- Two submissions were kernel-checked as probes: a backdoor (V3-S1-M1) and a step-law control
  (V3-S1-M2).
- Probe sources are in `/tmp/v3s1-review/probe/`. The two load-bearing ones are reproduced in the
  Appendix so that the fix pass can turn them into controls.

**Ordering.**
- This is Category-A work (security definitions, relation, certificate), so the expectation was
  formed from DESIGN-v3 §2–§5 and from the standard ROM knowledge-soundness definitions before
  reading the Lean.
- No upstream implementation is authoritative here.

## Verdict

**ACCEPT after fixes.** There are 4 majors and 12 minors. V3-S1-M1 is a design hole that the fix
pass cannot close alone: it needs a recorded user decision (a new open item) before board T ranks
anything.

**What is right.**
- The contract says what DESIGN-v3 says, up to recorded and sound amendments.
- 320 code lines, no field, Mathlib imports limited to three modules.
- Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).
- No `sorry`, `native_decide`, `implemented_by`, `extern` or `csimp` in Contract, Library or Controls.
- Every definition has a docstring.
- No closed term in our modules is expensive to initialise.
- The witness-sending certificate inhabits every clause of `Certificate`.

**What is wrong.**
- **M1.** The contract cannot see a verifier that recognises its own deployment oracle. A certified
  submission (kernel-checked) has an instantiated verifier that accepts a 32-byte "magic" proof of
  every statement. Every check of §6.3 then passes with no proving at all. §6.7's row "a verifier
  that accepts a magic proof … the kernel refuses the certificate" is false.
- **M2.** No control exercises the `step` law. A contract whose `step` is vacuous builds green with
  every control passing.
- **M3.** Efficient extraction (`ImageComputes`) is required only for logs of at most `2^24`
  entries. §4.5 and §8 quote `2^64`-query adversaries.
- **M4.** The committed state would list lake targets that do not build, a failing axiom-audit tool
  and a v2 CI script.

## Findings

### V3-S1-M1 (major, design): a certified verifier can recognise the instantiated oracle and accept magic proofs; nothing in the contract or the run excludes it

**Where.**
- `Contract/Certificate.lean:143-149` (`blake2sOracle`, `Submission.Vb`).
- `Contract/Security.lean:61-69` (`KS`, `Complete` quantify over every oracle function).
- DESIGN-v3 §3.4, §5.4, §6.7 (row "A verifier that accepts a magic proof") and §8 item 4.

**The attack.** Every statement of the certificate either:
- counts bad answers over all `2^256` answers of a fresh query (`KS`), or
- quantifies over all oracle functions (`Complete`).

Both are blind to how `V` behaves on one particular function. `V`'s continuation is an arbitrary
Lean function, and `blake2sOracle` is public, so `V` can compute the deployment oracle's answer
itself and switch behaviour when it sees it. This is the Canetti–Goldreich–Halevi counterexample
to the random-oracle methodology. Here it costs about 15 lines, and an agent optimising the score
has every reason to find it.

**The probe.** `Probe.Backdoor2` (Appendix A) is kernel-checked, with axioms `propext`,
`Classical.choice` and `Quot.sound`.

The verifier:
- `V c π := query ε (a ↦ ret ((a = blake2sOracle ε ∧ π = magic c) ∨ check c π))`.
- `magic c` is the 32 bytes of `c`.
- `check` is the witness-sending decision, whose children may themselves be magic proofs.

The rest of the submission:
- `P`, `E`, `img` and `fuel` are the witness-sending ones.
- `ε = errorCap`, `qV = 1`.

The knowledge state:
- `good L` says the log does not answer `ε` with the deployment value.
- `bad L q a := q = ε ∧ a = blake2sOracle ε`, one answer in `2^256`, so `Bounded errorCap`.
- On good logs `V` is the honest `check`, so `final` holds with the witness-sending extractor.
- `Complete` holds because the honest branch accepts the honest proof under every `H`, including
  the deployment oracle.

The theorem:

```lean
theorem backdoor : Certificate S ∧ ∀ c, S.Vb c (magic c) = true ∧ (magic c).size = 32
```

**Every check of the run passes** (DESIGN-v3 §6.3).
- **Tree.** The native prover writes `magic c` for every node and leaf. Its only work is hashing
  the chains to learn the leaf digests, plus one `nodeStmt` per node; nothing is proved.
- **Root check and sample checks.** They accept.
- **Root step.** It outputs `magic (nodeStmt c₁ c₂)`.
- **Canaries.** They reject: an appended or removed byte, a flipped statement bit or a swapped child
  digest each breaks `π = magic c`, and `check` rejects the rest.
- **DoS column.** Random proofs are rejected.
- **Liveness.** It uses the honest `P` and the witness-sending image.
- **Succinctness.** `Vb` costs one compression, far below `T_V`.

**Why no salting fixes it.** The obvious repair is a fresh per-evaluation salt in the oracle,
`BLAKE2s(tagRO ‖ k ‖ q)`. It does not work:
- Recursion needs the agent's circuit to compute `Vb`, so the native prover must know `k`.
- So the backdoor takes `k'` from the proof and checks two oracle points against
  `BLAKE2s(tagRO ‖ k' ‖ ·)`.
- That check is certifiable by pure counting. Put the first answers that more than `2^128` salts
  map to into `bad` (Markov's inequality: at most `2^256 / 2^128` of them). The second answer is
  then bad for at most `2^128` values. Both give per-query error at most `2^-128`, with no
  property of BLAKE2s used.
- Within the ROM, every instantiation known to the prover can be recognised by a certified
  verifier.

**Fix.** There is no contract-level fix inside the ROM. The fix pass and the design should do the
following.
1. **Pin the gap.** Add `Probe.Backdoor2` as a documented known-gap control in
   `Controls/Certificate.lean`, so nobody reads `Certificate` as excluding it.
2. **Correct the claims.** Correct §6.7's "magic proof" row. Correct §3.4, §5.4 and §8 item 4: the
   heuristic is applied to a `V` chosen by an adversary, and the CGH-type `V` is certified. Correct
   the `Certificate.lean` and `Security.lean` headers, which state the paper theorem as if the
   instantiation were covered.
3. **Open an item for the user (O-25).** The defence is a rule plus review:
   - **Rule.** "`V` must be oracle-oblivious: it must not evaluate BLAKE2s on the oracle's domain or
     otherwise recognise the instantiated oracle; violating entries are disqualified."
   - **Review.** An intake review of `V`'s source (stage S7) is mandatory before an entry is ranked.
   - **Gate speed bump (S3).**
     - Reject a `V` whose kernel-term closure contains `blake2sOracle`, `Submission.Vb` or
       `tagRO`.
     - Flag for review a `V` whose closure contains `Blake2s.compress`. The witness-sending `V`
       legitimately reaches it through `leafStmt` and `chainEnd`.
   - **Canary additions (S3).** `Vb` must reject the empty proof, the statement's own bytes and a
     short constant proof. These catch only lazy versions.

### V3-S1-M2 (major): the `step` law is never exercised; a vacuous `step` passes the whole build

**Where.**
- `Contract/Security.lean:48` (`step`).
- `Controls/Security.lean`, all of it.

**The gap.** Every negative control of the counting form fails at the empty log:
- `acceptAll_no_kstate_*` and `acceptAll_kstate_iff` use `final [] … k.empty`.
- `bounded_ge_one` and `badAll_not_capped` test `Bounded` alone.
- `rejectAll_ks` and `ws_ks` use `good := True`.

No control has a verifier that queries the oracle and accepts on a fresh answer. So nothing checks
that the counting form charges answers, or that `final` binds on a non-empty log.

**Mutation.** Replace the conclusion of `step` by `good L`. This makes the law vacuous: then
`good := (· = [])` certifies any verifier whose acceptance needs one query. Result:
`lake build RecursionFastContract RecursionFastLibrary RecursionFastControls` is **green**
(`/tmp/v3s1-review/mut-step.log`).

**Fix.** Add `Probe.StepControl` (Appendix B, kernel-checked) to `Controls/Security.lean`:
- **`queryThenAccept`.** It asks one query and accepts. For the empty relation, every
  `Bounded ε` knowledge state has `1 ≤ ε`.
- **`ks1`.** Such a state exists, so it is the bound that fails, not the laws.

Against the step mutation, the control fails to elaborate (checked). Optionally add the
counting variant "accept iff the answer's first byte is 0 ⇒ `ε ≥ 2^-8`". It shows the bound
scales with the density of lucky answers.

### V3-S1-M3 (major): efficient extraction is required only for logs of at most `2^24` entries; §4.5 and §8 quote `2^64`-query adversaries

**Where.**
- `Contract/Extractor.lean:101` (`L.length ≤ 2 ^ 24 →` in `ImageComputes`).
- DESIGN-v3 §4.4, which has the same bound, against §4.5 ("an adversary with `2^64` queries has
  advantage `≤ 2^-64 + 2^-112`").

**The gap.** V3-S1-A13 establishes that `KState` alone constrains only the existence of a witness.
Heuristically every digest has one: `nodeStmt` is onto. So the whole knowledge content of the
certificate is `ImageComputes`.

Outside its domain the extractor `E` is an arbitrary Lean function, for example
`Classical.choose`. For an adversary whose log has more than `2^24` entries, about 16.7 million
oracle calls (seconds of work), the certificate says only that "some Lean function returns a
witness".

The paper theorem of §4.5 needs `E` to be the efficient extractor on the final log, which has
`Q + qV` entries. The certificate therefore gives the §4.5 bound only for `Q + qV ≤ 2^24`.

A concrete cheating protocol is not easy to build: `final` must still be proved on large logs,
which requires provable witness existence. But the claim as written is not what the definition
gives.

**Fix.** Drop the conjunct `L.length ≤ 2 ^ 24 →`. This costs nothing:
- The `2^60`-word tape conjunct remains, and implies at most `2^58` entries.
- The budget grows with `l`, and with (d) with the log's size.
- In the mutation run (`mut-nobound.log`), the only fallout was `WitnessSending.computes`'s
  `intro c π L hπ _ _`, which needs one `_` fewer. The four `ImageComputes` controls also pass one
  `(by decide)` fewer.

Then restate §4.5 for `Q + qV ≤ 2^58`. The alternative is to keep the bound and restate §4.5 and §8
for `Q + qV ≤ 2^24`, which is a weak statement.

### V3-S1-M4 (major): the committed state must build every target it lists and say what is deferred

**Where.** `lakefile.toml`, `scripts/AxiomAudit.lean:41`, `scripts/ci.sh`,
`scripts/olean-manifest.sha256`, `RecursionFast/{Bridge,Clean}/`, `legacy/v2/README.md`, `CLAUDE.md`.

**The state.**
- **Lake targets.** Eight targets fail on an import of a deleted or moved module:
  `RecursionFastBridge`, `RecursionFastClean`, `RecursionFastCandidate`, `RecursionFastHarness`,
  `harness-linkcheck`, `RecursionFastSmoke`, `smoke-verify`, `smoke-index`
  (`logs/V3-S1/deferred-targets.log`).
- **Axiom audit.** `lake exe axiomaudit` builds but fails at run time, because its module list
  includes `RecursionFast.Bridge`. The RESULT's PASS comes from a private copy (`AxiomAuditV3.lean`).
- **CI.** `scripts/ci.sh` is the v2 pipeline:
  - Step 2's organiser build includes Bridge and the harness, so it fails.
  - Step 3's manifest predates the trusted change. `CLAUDE.md` requires regenerating it after any
    trusted edit.
  - Step 4's `loc.py` call omits `Hash/Blake2s.lean`.

**Fix (for an honest pull request).**
1. `git mv RecursionFast/Bridge{,.lean} RecursionFast/Clean{,.lean} legacy/v2/RecursionFast/`.
2. In `lakefile.toml`, comment out the eight targets above, each with "deferred to S2/S3/S4 (V3-S1)".
   Replace the v2 header comment. Keep or drop the `Clean` require as an explicit decision; if
   kept, say why.
3. Drop `RecursionFast.Bridge` from `scripts/AxiomAudit.lean`'s module list, so that
   `lake exe axiomaudit` is the binding audit again.
4. Make `ci.sh` v3-valid for steps 1–4. Source checks; default build; axiom audit; `loc.py` with
   `Hash/Blake2s.lean`. Gate the rest behind "S3". For the manifest, either regenerate it from a v3
   organiser build (`org-build.sh` adapted) or state in the PR body that CI step 3 is owed by S3.
5. Update `legacy/v2/README.md` (Bridge and Clean moved).
6. Fix `CLAUDE.md`:
   - It still says "The design is `docs/DESIGN.md`. It is authoritative." That contradicts the new
     v3 line.
   - The Library row and the build-time lines describe v2.

The criterion: every target named in `lakefile.toml` builds, and the PR body lists every harness
artefact that is still v2: challenge stubs, gate allowlist, manifest, renderer (V3-S1-A16).

### Minor findings

**V3-S1-m1. Rel's node clause has a negative control for the second child only.**
- `second_child_rejected` targets the third conjunct.
- Two mutations, dropping `c = nodeStmt c₁ c₂` and dropping `Vb c₁ π₁ = true`, were caught only by
  the anonymous-constructor shape of `WitnessSending`'s proofs (`mut-nodestmt.log`,
  `mut-child1.log`), not by any control. A golfed proof could stop catching them.
- Add two controls with accepted children:
  - a statement mismatch, `¬ Rel Vb (leafStmt …) (.node …)`;
  - a rejected first child.

**V3-S1-m2. `oneQuery_not_qV0` restates the formula instead of using `KS`.**
- It never mentions `KS`. Dropping `KS`'s query conjunct was caught only by proof breakage
  (`mut-qv.log`).
- State it as `¬ KS R oneQuery E ε 0` for every `R`, `E` and `ε`.

**V3-S1-m3. No known answer for `blake2sOracle`.**
- The instantiation that the runner, the native prover and the liveness wrapper must reproduce is
  never tested against an independent BLAKE2s. The witness-sending verifier makes no query.
- Add a KAT, for example on `q = 01 02 03`:
  `python3 -c "import hashlib; print(hashlib.blake2s(b'R'+bytes([1,2,3])).hexdigest())"`
  gives `5d32eaa721251d8e473bc410cf953591949de810e935f6e06caa3f8d5ae9cf84`. Computed here.

**V3-S1-m4. No known answer for the tape and output formats.**
- `extractorInput` is exercised only on the empty log (`tape0`).
- `decodeWit` is exercised only by the library round trip.
- The Python twins of S3 need test vectors. Add a KAT of `extractorInput` on a non-empty log with a
  9-byte query (padding) and a KAT of `decodeWit` on a node with two short proofs.

**V3-S1-m5. `decodeWit` denotes proofs longer than its output.**
- Missing words read as 0, and a child length is any 64-bit word. A 10-word output can therefore
  denote a `2^63`-byte proof.
- This is harmless for the contract, because `Rel` needs both children within `proofCap`. It is,
  however, a memory-exhaustion vector for the Python decoder that A16 makes normative.
- Return `none` when a child length exceeds `proofCap`. This costs nothing: no witness of `Rel` is
  lost, and an `E` that is in `Rel` on good logs never needs larger children.

**V3-S1-m6. Two cap conjuncts have no negative control.**
- `Certificate.cap`'s image cap and its `fuel ≤ extractorBudget` conjunct have none.
- Add an image of `2^18 + 1` code words that fails `cap.2.2.2`. Add a constant fuel of `2^41` that
  fails `cap.2.2.1 0 0`.

**V3-S1-m7. Two separation claims stay false after (c); `tags_separate` is not a separation control.**
- **The claim.** §3.4 says "the proof system never queries a string the relation hashes". The
  `Relation.lean` header says that distinct first bytes separate statements from queries. After
  decision (c), both still fail in one place: the node clause evaluates `Vb`, which hashes
  `tagRO ‖ q` (the recursion, §5.4).
  - Reword: "no chain, leaf or node preimage is an oracle input; the oracle's own inputs are hashed
    by the relation only inside `Vb`".
- **The control.** `tags_separate` proves that BLAKE2s differs on two particular inputs, which is a
  fact about the hash, not about the definition.
  - Replace it with a structural lemma: the head byte of every chain, leaf and node preimage is in
    `{tagChain, tagLeaf, tagNode}`, the head byte of every oracle input is `tagRO`, and the four
    tags are pairwise distinct.

**V3-S1-m8. Stale text in trusted files and around them.**
- **`Hash/Blake2s.lean` header.** It still lists the v2 roles ("`D`, the digest of a verification
  key … `aggOK` … `compile`").
- **`Machine.lean` header.** It says "In v2 it runs only the bounded extractor (… DESIGN §4 item 3)".
- **`nodeStmt_kat` docstring.** It elides the hex (`0582…93d1`), so the command cannot be run as
  written.
- **`lakefile.toml` header.** It still describes the v2 contract.

Trusted-file text changes need the manifest regenerated anyway (M4).

**V3-S1-m9. `CertificateR` puts no bound on the declared fuel.**
- `D.fuel` may exceed the budget, and the liveness check runs with `D.fuel` (A10).
- **Fix.** Either add `∀ p l, D.fuel p l ≤ extractorBudget p l` to `CertificateR`, or have S3 run
  with the minimum of the two.
- **The name changed meaning.** In v2, `CertificateR` was the recursion-board certificate; in v3 it
  is "against the rendered claim". The gate, the renderer and the stubs (S3) must not carry over
  the v2 meaning.

**V3-S1-m10. Without a counted-error form, two design rows are inoperative.**
- V3-S1-A9 leaves no counted-error completeness form in the contract.
- So §6.6's `δ ≤ 2^-64` row and §6.7's "Grinding / proof of work: allowed" row describe nothing
  that can be certified. Mark both "after O-23".

**V3-S1-m11. Over-strong but harmless.**
- `KState.final` quantifies over proofs above `proofCap`, which `Vb` rejects anyway.
- Optionally restrict it with `π.size ≤ proofCap →`. This is a free simplification for submitters
  and changes nothing the paper theorem uses. Not required.

**V3-S1-m12. Style.**
- Six lines exceed 100 characters: `Extractor.lean:70,82`, `Machine.lean:52,120,165`,
  `Controls/Relation.lean:60`.

## The four orchestrator decisions

### (a) V3-S1-A13: replace the accept-everything control by the exact iff plus the certificate-level negative, and reword §4.2

**Right, but insufficient.**

**What is right.**
- `acceptAll_kstate_iff` is the exact and correct statement.
- The design's sentence is worse than unprovable: it is heuristically **false**. Under the
  accept-all verifier, every image digest of `nodeStmt` has a node witness. `nodeStmt` is
  `2^512 → 2^256`, so almost certainly onto, and the choice extractor then gives a `KState`.

**What the rewording must also say.**
1. `KState` alone is (heuristically) satisfiable by every verifier. Knowledge is exactly
   `ImageComputes` with its budget. So the domain of `ImageComputes` is load-bearing (M3).
2. Two rows of §6.7 that rely on "KS on a false statement" must go: the magic-proof row and the
   random-proof-DoS justification. There is no provably false statement (A13), and magic proofs are
   certifiable (M1).
3. The vacuity controls must reach past the empty log (M2).

**A stronger certificate-level negative.** `acceptAll_no_certificate` fixes `E := none`, which is
narrow. A stronger negative is provable for every extractor that ignores the statement
(`∀ c c', E c = E c'`):
- At the empty log, two statements would share one witness.
- A leaf or node witness pins its statement digest, so this is impossible.

This is optional.

### (b) V3-S1-A14: bound `n ≤ 2^20` in `Rel`'s leaf clause

**Right.**
- It removes the fallback cascade that A14 describes: an agent's leaf circuit need not handle
  unbounded `n`.
- `enc64` becomes injective on the range.
- `norm`, `rel_norm`, the A7 remark and the `n < 2^64` side conditions (`Wit.Fits` for leaves,
  `node_of_two_leaves`) disappear.

**How to write it.** Use a named, documented constant:

```lean
/-- The longest chain a leaf statement may commit to: `2^20` steps. -/
def chainCap : ℕ := 2 ^ 20
…
| c, .leaf s n => n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n
```

Put `n ≤ chainCap` first, so the decidable size check precedes the hash. Add one positive control
and one negative control:
- **Positive:** `n = chainCap` passes the size conjunct.
- **Negative:** `¬ Rel Vb (leafStmt (chainEnd s (chainCap+1)) (chainCap+1)) (.leaf s (chainCap+1))`.

**What not to add.**
- A lower bound `2^4 ≤ n` is unnecessary: `n = 0` is a valid, trivial leaf.
- Pinning `n` to the season's single value would make the relation season-dependent. Do not.

**Note.** No digest becomes provably witnessless: it may still be a node statement. A13 stands.

### (c) V3-S1-A6: tag the chain step

**Right.**

**Arithmetic, checked against `Hash/Blake2s.lean`.** `compressInput h 0 d ((|d| − 1) / 64)` makes
`(33 − 1)/64 = 0` non-final blocks. So a 33-byte input is **one compression**, with counter 33 and
the last-block flag. That is the same cost as today's 32-byte step. Leaf preimages (41 bytes) stay
at one compression and node preimages (65 bytes) at two.

**Which strings can coincide.**
- With `tagChain = 0x43` ('C'), the chain, leaf and node preimages begin with 0x43, 0x4C and 0x4E.
  Every oracle input begins with `tagRO = 0x52`. No preimage the relation itself forms can equal an
  oracle input, whatever the lengths.
- This covers `leafStmt` and `nodeStmt` preimages, whose first bytes already differed, and closes
  the 31-byte query versus chain-step collision of A6.

**What it does not cover.** The relation still hashes `tagRO`-prefixed strings through `Vb` in the
node clause. That is the recursion and cannot be tagged away; see m7 for the wording.

**Follow-ups.**
- `chain{1,2,16}_kat` and their python commands become `b'C'+d`.
- `node_of_two_leaves`, the runner's chain and the witness-sending verifier follow automatically.
- Add `tagChain` to `tags_distinct`.

### (d) V3-S1-A12: make the budget's `l` the serialised log size in words

**Right in direction.** Two refinements.
1. **Charge the whole tape.** Prefer `B t = 2^40 + 2^8 · t` with
   `t = (extractorInput c π L).length`, and a declared `fuel : ℕ → ℕ` of the tape length.
   - This removes the mixed units (proof bytes plus log words).
   - It charges the statement and the length words as well.
   - It gives the runner one number to compute.
   - Keeping `(p, l)` with `l` in words is also sound, at the cost of a second number the Python
     twin must reproduce.
2. **Drop the `2^24`-entry domain bound** (M3). With the budget proportional to the input it has no
   remaining purpose.

**Effect on honest extractors.** None loses budget: a log entry is at least 5 words, so the
per-entry allowance grows at least fivefold.

## Spec tightness against DESIGN-v3 (Pass A)

**§2.1 `Rel`, `chainEnd`, `leafStmt`, `nodeStmt`, `Wit`.** Status: as designed, up to A3, A4 and A5.
- `Rel` matches clause by clause.
- `Vector UInt8 32` is justified by measurement (A4).
- `Nat.card Digest = 2^256` is proved in the library (`card_digest`).
- Open: A14 (b) and A6 (c).

**§2.2 `proofCap`.** Status: as designed.
- `Vb` rejects `> 2^20`. Controls: `Vb_over_cap` and `deep_accepted_but_capped`.

**§3.1 `OProg`, `run`, `runLog`, `queries`.** Status: as designed.
- `runLog` takes the first match (`List.find?`) and returns `none` on a miss.
- `queries` lists every query of the run, repeats included, under `H`.

**§3.2 `Submission`, `Vb`, `Certificate`, `Declared`, `CertificateR`.** Status: as designed, up to
A10 and A11.
- `Vb` prepends `tagRO` (`blake2sOracle`) and rejects above `proofCap`.
- `cap` has the design's three conjuncts plus the image cap (A11).
- `CertificateR` binds the image by equality and the numbers as bounds (A10). See m9.

**§4.2 `KState`, `Bounded`, `KS`, `errorCap`.** Status: as designed.
- `final` reads `V` from the log, so the verifier's own queries are charged by `step` and `Bounded`.
- `Library/Oracle.lean`'s `runLog_eq_run` is the right link to the real run: a log consistent with
  `H` that contains every query of the run answers it as `H` does.
- `bad` depends only on the history, the query and the answer, which is exactly what the union
  bound needs.
- See M2 and M3.

**§4.3 `Complete`.** Status: as designed.
- It is perfect completeness over every `H`, for `V` rather than `Vb` (A18: a prover may exceed
  `proofCap` and score nothing).
- A prover that queries nothing is complete, as intended.

**§4.4 `ImageComputes`, `B`.** Status: deviates (A7, A11, A12).
- **A7, decoding.** The image's output must decode to `E`'s result rather than equal one
  serialisation of it. The deviation is sound:
  - Non-canonical outputs exist: nonzero padding bits, trailing words, and outputs truncated where
    zero-reads supply the rest. They do not matter, because nothing hashes or compares the raw
    output.
  - The Python decoder must replicate `decodeWit` exactly (m5).
- **The output cap `2^24` words.** It is a conclusion of `ImageComputes`, a cap on the image, not
  an assumption, and it is not vacuity-inducing. A `Rel` witness needs at most
  `11 + 2·⌈2^20/8⌉ = 262,155` words.
- **The `2^24`-entry input bound.** It weakens the claim (M3).

**§5.1 `treeRoot`.** Status: as designed, up to A8. `2^r` leaves give the design's tree; the odd
case and the empty case are conventions only.

**§1.1 and §8 trust statement.** Status: overclaims. See M1 (§6.7 and the instantiation heuristic)
and M3 (`2^64`).

The other amendments are sound and recorded: A1 (order), A2 (only `clResult` references changed,
per the diff), A3, A5, A8, A9 (see m10), A15, A16, A17 (see M4), A18.

## Trust policy and hygiene (Pass C)

**Imports.**
- `Contract/` imports only:
  - Lean core;
  - the vendored `RiscvZkvm.Rv64.Execution` and `RiscvZkvm.Interpreter.Decode`;
  - three Mathlib modules: `Mathlib.Logic.Function.Iterate`, `Mathlib.Basic.NNReal.Defs` and
    `Mathlib.SetTheory.Cardinal.Finite`.
- No ArkLib, VCVio, CompPoly, Clean or PolyFun.
- The import closure of `RecursionFast.Contract` is 2,608 modules, 849 of them Mathlib (computed
  with `importModules`). Contract, Library and Controls together reach 2,718 modules, all with
  prebuilt objects.
- `Nat.card` is the right choice over `Fintype.card`. A computable `Fintype Digest` instance would
  be a closed `2^256`-element `Finset`: exactly the S6b-A5 start-up trap.

**Start-up (S6b-A5).**
- The closed computable constants of every `RecursionFast.*` module are:
  - **Contract:** `proofCap`, the three tags, `outCap`, `imageCap`, `CODE_BASE`, `TAPE_BASE`,
    `Blake2s.iv`, `Blake2s.sigma`.
  - **Library:** `digestEquiv`, `WitnessSending.{img,kstate,submission}`.
  - **Controls:** small images, lists and digests (`s0`, `tape0`, `q₁`, `prog`, `declared`,
    `flipped`).
- None hashes or enumerates. `errorCap` is `noncomputable`.
- `harness-linkcheck`, the executable check, is deferred with the harness. It should be rerun when
  S3 revives it.

**Forbidden tokens.** There is no `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`,
`csimp`, `unsafe`, `axiom` or local `set_option` in Contract, Library or Controls. Checked by grep;
`scripts/check-hygiene.sh` is OK.

**Axioms.** Printed for:
- `Certificate`, `CertificateR`, `KS`, `KState`, `KState.Bounded`, `Complete`, `ImageComputes`,
  `Rel`, `treeRoot`, `Submission.Vb`, `decodeWit`, `errorCap`;
- `WitnessSending.certificate`, `ws_certificateR`, `acceptAll_kstate_iff`, `chain16_kat`,
  `deep_accepted_but_capped`, `toolong_not_computes`, `treeRoot_kat`, `runLog_reads_log`,
  `card_digest`, `runLog_eq_run`.

All are a subset of `[propext, Classical.choice, Quot.sound]`.

**Docstrings.** Every trusted `def`, `abbrev`, `structure` and `inductive` has one, and they say
what, not how. Exceptions:
- the stale headers (m8);
- the fields of the v2 `Image` (`code`, `data`) and the `WordOp` constructors, which have none
  (unchanged v2).

**Line budget.** 320 code lines out of the 500 allowed (`loc.py`):
`Contract.lean` 8, `Blake2s` 68, `Relation` 22, `Oracle` 19, `Security` 23, `Machine` 110,
`Extractor` 33, `Tree` 7, `Certificate` 30. That leaves room for `chainCap`, `tagChain` and the
`decodeWit` cap.

## Trusted definition → positive control → negative control

**Hash, relation and oracle.**

| Trusted definition | Positive | Negative | Note |
|---|---|---|---|
| `blake2s`, `blake2s256` | 12 KATs, `iv_spec`, `sigma_perm` (`Controls/Blake2s`) | `flip_neg`, `key_neg`, `nn_neg` | v2, unchanged |
| `blake2sDigest`, `chainEnd` | `chain1_kat`, `chain2_kat`, `chain16_kat` | `wrong_end`, `start_ne_end` | change to `b'C'+d` with (c) |
| `enc64`, `leafStmt` | `leafStmt_kat` | `wrong_end`, `tags_separate` | m7 |
| `nodeStmt` | `nodeStmt_kat`, `treeRoot_two` | `treeRoot_order` | |
| tags | the KATs (`b'L'`, `b'N'`) | `tags_distinct` | add `tagChain` (c) |
| `Rel`, leaf clause | ws `complete`, `node_of_two_leaves` | `wrong_end` | add `n ≤ chainCap` controls (b) |
| `Rel`, node clause | `node_of_two_leaves` | `second_child_rejected` only | **m1** |
| `proofCap`, `Vb` | `Vb_eq`, `node_of_two_leaves` | `Vb_over_cap`, `deep_accepted_but_capped` | |
| `blake2sOracle` | none | none | **m3** |
| `OProg`, `run`, `queries` | `prog_queries`, `prog_run` | `oneQuery_not_qV0` | |
| `Log`, `runLog` | `prog_runLog`, `prog_runLog'`, `prog_runLog_first` | `prog_runLog_miss`, `runLog_reads_log` | |

**Security and certificate.**

| Trusted definition | Positive | Negative | Note |
|---|---|---|---|
| `errorCap` | `errorCap_lt_one` | `badAll_not_capped`, `error_one_no_certificate` | |
| `KState` (`empty`, `final`) | `ws_kstate_trivial`, `rejectAll_ks` | `acceptAll_kstate_iff`, `acceptAll_no_kstate_empty`, `acceptAll_no_kstate_none` | empty log only |
| `KState.step` | (trivial states only) | **none** | **M2**: add `queryThenAccept_ge_one` |
| `KState.Bounded` | `bounded_of_not_bad` | `bounded_ge_one`, `badAll_not_capped` | |
| `KS`, query conjunct | `ws_ks` | `oneQuery_not_qV0` (formula, not `KS`) | **m2** |
| `Complete` | `ws_complete` | `rejectAll_not_complete` | |
| `Certificate` | `ws_certificate` | `rejectAll_no_certificate`, `acceptAll_no_certificate`, `error_one_no_certificate` | plus the M1 known-gap control |
| `cap`: fuel budget and image cap | ws `cap` | none | **m6** |
| `Declared`, `CertificateR` | `ws_certificateR` | `flipped_image`, `fuel_7_claim` | m9 |

**Machine, extractor and tree.**

| Trusted definition | Positive | Negative | Note |
|---|---|---|---|
| `Machine.run`, the decoder, `clmul` | `wzbc_run`, `tape_below_ok`, `halt_reads` | `tape_readonly`, `halt_misaligned`, `ecall_trap`, `spin_run_100`, `spin_run` | v2 |
| `packBytes`, `bytesWords`, `extractorInput` | `ws_computes`, `ws_run_8` (empty log) | none | **m4** |
| `decodeWit`, `digestAt`, `bytesAt` | `decodeWit_witWords` (library) | `halt_not_ws` | m4, m5 |
| `outCap` | `ws_computes` | `toolong_not_computes` | |
| `ImageComputes` | `ws_computes`, `halt_computes` | `halt_not_ws`, `ws_fuel_7`, `noCode_computes_nothing`, `toolong_not_computes` | |
| `treeLevel`, `treeRoot` | `treeRoot_{nil,one,two,three,four,eight}`, `treeRoot_kat` | `treeRoot_order` | |

**Known answers, reproduced.**
- These five match, run with `python3 -I`: `chain1_kat`, `chain2_kat`, `chain16_kat`,
  `leafStmt_kat`, and `nodeStmt_kat` with the full hex.
- `treeRoot_kat` also matches: `818de831…10c4`.

**Vacuity by universe or instance accident.** None found. Each negative uses the definition it
names, except `oneQuery_not_qV0` (m2) and `tags_separate` (m7).

## Probes

**Mutation table.** Each mutation edits the snapshot's contract, then rebuilds Contract, Library
and Controls.

| Mutation | Result | Caught by |
|---|---|---|
| `step` concludes `good L` (vacuous) | **build green** | nothing (M2); the proposed control fails |
| `Rel` node clause without `c = nodeStmt c₁ c₂` | build fails | `WitnessSending` proof shape only (m1) |
| `Rel` node clause without `Vb c₁ π₁` | build fails | `WitnessSending` proof shape only (m1) |
| `KS` without the query conjunct | build fails | `WitnessSending.ks` proof shape only (m2) |
| `ImageComputes` without `L.length ≤ 2^24` | build fails at one `intro` | `WitnessSending.computes`'s intro arity (M3: the fix is free) |

**Kernel-checked probes.**
- `Probe.Backdoor` (accepts the empty proof) and `Probe.Backdoor2` (accepts the magic proof,
  canary-resistant): `Certificate S` plus acceptance. Axioms standard.
- `Probe.StepControl`: compiles against the contract, fails against the `step` mutation.

## Lean4 review summary (`lean4:review`, read-only)

- **Scope.** Contract, Controls, `Library/{Oracle,Security}`.
- **Layer 2.** Advisory (`repository_kind = other-lean`).
- **Build.** Green on the snapshot.
- **Sorries and axioms.** No sorry; standard axioms only.
- **Style.** See m12. The proofs are short and direct. Golf is out of scope here: the golf agent
  owns it.

## Appendix A: `Probe.Backdoor2` (V3-S1-M1, kernel-checked against the snapshot)

```lean
import RecursionFast.Library.WitnessSending
open RecursionFast
open scoped NNReal

namespace Probe.Backdoor2
open RecursionFast.WitnessSending (decode encode norm size_encode size_eq_length)

def q0 : ByteArray := ByteArray.empty
def trigger : Digest := blake2sOracle q0
/-- The magic proof of `c`: its own 32 bytes. -/
def magic (c : Digest) : Proof := ⟨c.toArray⟩

/-- Witness-sending decision whose children may also be magic proofs. -/
def check (c : Digest) (π : Proof) : Bool :=
  match decode π with
  | some (.leaf s n) => decide (c = leafStmt (chainEnd s n) n)
  | some (.node c₁ c₂ π₁ π₂) =>
    if _h : encode (.node c₁ c₂ π₁ π₂) = π then
      decide (c = nodeStmt c₁ c₂) &&
        (decide (π₁.size ≤ proofCap) && (decide (π₁ = magic c₁) || check c₁ π₁)) &&
        (decide (π₂.size ≤ proofCap) && (decide (π₂ = magic c₂) || check c₂ π₂))
    else false
  | none => false
termination_by π.size
decreasing_by
  all_goals
    rw [← _h, size_encode]
    simp only [witWords, bytesWords, List.length_cons, List.length_append, packBytes_length,
      ← size_eq_length]
    omega

/-- Under the deployment oracle a magic proof is accepted; otherwise the honest decision. -/
def V (c : Digest) (π : Proof) : OProg Bool :=
  .query q0 fun a => .ret ((decide (a = trigger) && decide (π = magic c)) || check c π)

noncomputable def S : Submission where
  V := V
  P := WitnessSending.P
  E := WitnessSending.E
  img := WitnessSending.img
  ε := errorCap
  qV := 1
  fuel := WitnessSending.fuel

theorem Vb_eq (c : Digest) (π : Proof) :
    S.Vb c π = (decide (π.size ≤ proofCap) && (decide (π = magic c) || check c π)) := by
  unfold Submission.Vb
  split <;> simp_all [S, V, OProg.run, trigger]

theorem check_sound {c : Digest} {π : Proof} (h : check c π = true) :
    ∃ w, decode π = some w ∧ Rel S.Vb c w := by
  unfold check at h
  split at h
  next s n hd => exact ⟨.leaf s n, hd, show c = _ from of_decide_eq_true h⟩
  next c₁ c₂ π₁ π₂ hd =>
    split at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      refine ⟨.node c₁ c₂ π₁ π₂, hd, h.1.1, ?_, ?_⟩ <;> rw [Vb_eq] <;> simp [h]
    · cases h
  · cases h

def kstate : KState (Rel S.Vb) V WitnessSending.E where
  good L := ∀ e ∈ L, e.1 = q0 → e.2 ≠ trigger
  bad _ q a := q = q0 ∧ a = trigger
  empty := by simp
  step L q a hL _ hb := by
    intro e he h1
    rcases List.mem_append.mp he with he | he
    · exact hL e he h1
    · simp at he; subst he; exact fun h2 => hb ⟨h1, h2⟩
  final L c π hL hacc := by
    simp only [V, OProg.runLog] at hacc
    cases hf : L.find? (fun e => decide (e.1 = q0)) with
    | none => simp [hf] at hacc
    | some e =>
      have hm := List.mem_of_find?_eq_some hf
      have hq : e.1 = q0 := by simpa using List.find?_some hf
      have hne := hL e hm hq
      simp [hf, hne] at hacc
      exact check_sound hacc

theorem bounded : kstate.Bounded errorCap := by
  intro L q
  have : Subsingleton {a // kstate.bad L q a} :=
    ⟨fun ⟨a, _, ha⟩ ⟨b, _, hb⟩ => Subtype.ext (ha.trans hb.symm)⟩
  have h1 : Nat.card {a // kstate.bad L q a} ≤ 1 :=
    (Nat.card_le_card_of_injective (fun _ => ()) (fun x y _ => Subsingleton.elim x y)).trans (by simp)
  have h2 : (1 : ℝ≥0) ≤ errorCap * Nat.card Digest := by
    rw [card_digest, errorCap]; norm_num
  exact le_trans (by exact_mod_cast h1) h2

theorem check_encode {c : Digest} {w : Wit} (hR : Rel S.Vb c w) (hf : w.Fits) :
    check c (encode w) = true := by
  unfold check
  rw [WitnessSending.decode_encode w hf]
  cases w with
  | leaf s n => exact decide_eq_true hR
  | node c₁ c₂ π₁ π₂ =>
    obtain ⟨hc, h₁, h₂⟩ := hR
    rw [Vb_eq] at h₁ h₂
    simp_all

theorem size_le {c : Digest} {π : Proof} (h : S.Vb c π = true) : π.size ≤ proofCap := by
  rw [Vb_eq, Bool.and_eq_true] at h; exact of_decide_eq_true h.1

theorem fits_norm {c : Digest} {w : Wit} (hR : Rel S.Vb c w) : (norm w).Fits := by
  cases w with
  | leaf s n => exact Nat.mod_lt _ (by positivity)
  | node c₁ c₂ π₁ π₂ =>
    exact ⟨(size_le hR.2.1).trans_lt (by decide), (size_le hR.2.2).trans_lt (by decide)⟩

theorem complete : Complete (Rel S.Vb) S.P V := by
  intro H c w hR
  simp only [S, WitnessSending.P, OProg.run, V]
  rw [check_encode (WitnessSending.rel_norm hR) (fits_norm hR)]
  simp

theorem certified : Certificate S where
  secure := ⟨⟨kstate, bounded⟩, fun H c π => by simp [S, V, OProg.queries]⟩
  complete := complete
  computes := WitnessSending.computes
  cap := ⟨le_rfl, by decide, fun p l => by simp [S, WitnessSending.fuel, extractorBudget]; omega,
    by decide⟩

/-- Certified, and the deployed verifier accepts a 32-byte proof of every statement that the
prover computes without any witness. -/
theorem backdoor :
    Certificate S ∧ ∀ c, S.Vb c (magic c) = true ∧ (magic c).size = 32 := by
  refine ⟨certified, fun c => ⟨?_, ?_⟩⟩
  · rw [Vb_eq]; simp [magic, proofCap, ByteArray.size]
  · simp [magic, ByteArray.size]

end Probe.Backdoor2
```

## Appendix B: `Probe.StepControl` (V3-S1-M2; passes on the contract, fails on the `step` mutation)

```lean
import RecursionFast.Library.Security
open RecursionFast
open scoped NNReal

namespace Probe.StepControl

/-- Ask one query, then accept. -/
def queryThenAccept (_ : Digest) (_ : Proof) : OProg Bool := .query ByteArray.empty fun _ => .ret true

/-- Every answer to the verifier's own (fresh) query is bad, so the error is at least 1: the
`step` law charges the verifier's query. -/
theorem queryThenAccept_ge_one (E : Digest → Proof → Log → Option Wit)
    (k : KState (fun _ _ => False) queryThenAccept E) {ε : ℝ≥0} (h : k.Bounded ε) : 1 ≤ ε := by
  refine k.one_le_of_bounded h [] ByteArray.empty fun a => ?_
  by_contra hb
  have hg := k.step [] ByteArray.empty a k.empty (by simp) hb
  obtain ⟨w, -, hw⟩ := k.final _ (Vector.replicate 32 0) ByteArray.empty hg (by
    simp [queryThenAccept, OProg.runLog])
  exact hw

/-- And the knowledge state exists (so the bound is what fails, not the laws). -/
def ks1 (E : Digest → Proof → Log → Option Wit) : KState (fun _ _ => False) queryThenAccept E where
  good L := L = []
  bad _ _ _ := True
  empty := rfl
  step _ _ _ _ _ h := absurd trivial h
  final L c π hL h := by subst hL; simp [queryThenAccept, OProg.runLog] at h

end Probe.StepControl
```

## Notes for other stages (not V3-S1 findings)

- **S3, the extractor log.** The liveness log must contain `V`'s queries (A16), deduplicated, in
  query order.
- **S3, the Python twins.** They must reproduce `extractorInput`, `decodeWit` (including zero-reads,
  with the m5 cap), `blake2sOracle` and `treeRoot`. Use the KATs of m3 and m4.
- **S3, the gate.** Rule 4's fields become `V`, `P`, `E` and `img`. Add the M1 speed bump and
  canaries.
- **S7, intake.** The review of `V` for oracle recognition is the binding defence of M1.
- **O-21.** It should also fix the budget's argument, following (d).
