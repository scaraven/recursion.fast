# Lessons from v3: building a witness-sending entry and an honest Spartan + Ligero SNARK entry against a Lean contract

Status: the measured record of recursion.fast v3, 2026-10-19 to 2026-10-22. It covers the five
stages that were built (S1 the contract, S2a the witness-sending entry, S2-KS the knowledge-
soundness amendment, S2b the honest entry, S2R the rules), what each review found, what each
component cost, and what the measurements say about proof sizes, prover and verifier times and the
harness. The design itself is the companion
`v3-design-agent-written-ROM-SNARK-verifier-for-BLAKE2s-hash-chain-trees-with-Lean-certified-knowledge-soundness.md`
("Design §n"); the O-25 exploration is
`v3-open-problem-ROM-uninstantiability-CGH-backdoors-and-why-each-proposed-fix-failed.md`.

**How to read the numbers.** Every number below is one of two things, and says which: a
**kernel** fact (a theorem checked by Lean's kernel with only `propext`, `Classical.choice` and
`Quot.sound`, named by its Lean name and module) or a **measurement** (a timing, a size or a
count, with the path of its log). Logs live under `logs/` of the core worktrees and of the
submissions repository; `logs/` is gitignored in both, so **the logs are local to the development
VM** (`leanervm-dev`: a QEMU virtual CPU, 32 vCPUs, 62 GB, AVX2, **no `pclmulqdq`, `vpclmulqdq`
or `gfni`**, shared by up to about ten agents at a time). It is not the reference machine of the
design (O-6), which was never procured; every time is an upper bound and every `T_V` margin would
have to be re-measured. Paper estimates are marked **estimate**. There are no time estimates of
human or agent work anywhere in this document.

Line counts are code lines by the core's `scripts/loc.py` at `v3/contract-archive` (blanks and
comments excluded; the script is not on the stripped `main`) unless marked `wc -l`. The decisive
kernel probes cited below were copied from local folders into `evidence/probes/` on
`v3/contract-archive` (head `f4de3b8`; `evidence/README.md` is the index); §9 says which are
archived and which remain local.

## 1. The iterations

v3 ran five stages in four days, each under the same protocol (implement; adversarial review and
golf in parallel; fix; commit), and one design track without code. The order below is the order
they were built in; the contract changed under the entries twice.

| Stage | Dates | Where | What it produced | Record |
|---|---|---|---|---|
| **S1, the contract** | 2026-10-19 | core, branch `v3/s1-contract`, PR #2 merged `069b1a6`; the v2 tree removed in PR #3, `15e4ae5` | 9 trusted files, 328 code lines after the fix pass; the witness-sending argument with a full certificate in the library; 111 control theorems; `Controls/Backdoor.lean` | `V3-S1-RESULT.md`, `V3-S1-review.md` (4 majors, 12 minors, ACCEPT after fixes), `V3-S1-golf.md` |
| **S2a, the witness-sending entry** | 2026-10-19 | submissions, `submissions/baseline/`, against the pin `15e4ae5` | 310 Lean code lines, 38 theorems; `CertificateR` kernel-checked; `HARNESS: ACCEPT` with interim organiser tooling; the root-check calibration | `V3-S2a-RESULT.md`, `V3-S2a-review.md` (2 majors, 9 minors), `V3-S2a-golf.md` |
| **S2-KS, the amendment** | 2026-10-19/20 | core, branch `v3/ks-potential` (`ecdcbd5`, `c3f6380`, `05fde28`), PR #11, merged 2026-10-22 as `059812f` | the potential-form `KState` with `logCap`; the paper theorem in the library; `Controls/Potential.lean`; `Security.lean` 23 → 26 lines | `V3-S2-KS-RESULT.md`, `V3-S2-KS-review.md` (1 major, 6 minors, "sound; fix M1 before merge") |
| **S2b, the honest entry `spartan-chain`** | 2026-10-19/20 | submissions, `submissions/spartan-chain/`, against `05fde28` (not the pin) | 61 modules, 16,766 code lines, 1,561 theorems; 3,315 lines of Rust; `Challenge.certified` kernel-checked with no hypothesis; `HARNESS: ACCEPT` (commits `3171790` certified, `0358ec5` accept, `781d98c` golf, `1f59b38` final runs) | `BLUEPRINT-R1.md` with two reviews (4 + 3 majors), `V3-S2b-midreview.md` (5 majors, 12 minors), `V3-S2b-review.md` (2 majors, 7 minors), `V3-S2b-golf.md`, `V3-S2b-RESULT.md`, `REPORT.md`, fourteen component reports |
| **S2R, the rules** | 2026-10-20 | core, branch `v3/rules-handoff` on `05fde28`: `4b3356a` (stage), `ef7349a` (review), `6202402` (fix and golf); archived as `v3/contract-archive` | the step-counting extractor language; `CompleteWithError`; gate rule 4; the strict linear library verifier; the contract 331 → 288 → 292 lines | `V3-S2R-handoff-review.md` (4 majors, 17 minors, before any code), `V3-S2R-RESULT.md`, `V3-S2R-review.md` (2 majors, 6 minors), `V3-S2R-golf.md` |
| **O-25 design track** | 2026-10-20/22 | submissions, `notes/F2-o25-uninstantiability.md` | two rounds; nothing built | `F2-o25-review.md` (6 majors, 4 minors), `F2-o25-review-r2.md` (6 majors, 9 minors) |
| **The relativized exploration** | 2026-10-20/22 | core, branch `explore/relativized-nark`, head `043bcb3` (based on `05fde28`; not merged) | 12 notes, 21 untrusted Lean probe modules (3,008 code lines; a cold rebuild against built contract oleans 43.5 s, **measured**, `docs/explore/probes/audit/explore-cold-build.log` on that branch), an oracle-service microbenchmark; nothing in the contract | `docs/explore/REPORT.md`, `docs/reviews/EXPLORE-report-review.md` (6 majors, 21 minors, all applied); O-25 document §13 |

Two things in this table are unusual. The amendment S2-KS was requested by the entry work and
built in a scratch clone of the core because the honest entry could not start without it (PLAN
D-2); the entry was then certified against a branch that was not on the core's `main` for three
days, and the submissions pin never moved. And S2R was a rules stage requested by the issues the
entries filed; it changed the extractor and completeness clauses under the two certified
entries, so both would have needed porting (S2R RESULT Q11), which never happened: **neither
entry is certified against the archived contract** (S2a at `15e4ae5`, `spartan-chain` at
`05fde28`, both with the interim harness now archived under `evidence/interim-harness/`). A note
on decision ids: `PLAN.md` numbers its decisions D-1 … D-12 with no D-7, and `BLUEPRINT-R1.md`
numbers its own **[D-7] … [D-11]** "continuing PLAN", which collides with PLAN's D-8 … D-11; this
record cites PLAN's D-9 and D-11 (the `Fintype` fix, the nanoda finding) and BLUEPRINT's D-7
(ring switching), and says which.

The exploration notes that fed the design decisions were written in parallel on 2026-10-19
(E1 leanerVM, E2 ArkLib/VCVio/CompPoly, E3 leanVM/Spartan/Rust, E4 Clean/RISC-V tooling/harness),
together with F1 (the knowledge-soundness feasibility memo, verdicts H1–H3) and ADV1 (an
independent review of the rules with kernel probes, ADV-M1 … M8, m1 … m7). The issues #5–#10 and
the comment on #4 were filed from these on the same day (PLAN D-6).

## 2. What the contract cost

The trusted base stayed small and its build stayed fast; what grew was the library and the
controls, and what the stages learned about the contract came from the controls that could not
be proved as the design stated them.

### 2.1 Trusted lines by stage (`scripts/loc.py`)

| File | S1 | S1 fix | KS fix | S2R | S2R fix (final) |
|---|---:|---:|---:|---:|---:|
| `Contract.lean` | 8 | 8 | 8 | 8 | 8 |
| `Hash/Blake2s.lean` | 68 | 68 | 68 | 68 | 68 |
| `Relation.lean` | 22 | 25 | 25 | 25 | 25 |
| `Oracle.lean` | 19 | 19 | 19 | 22 | 22 |
| `Security.lean` | 23 | 23 | 26 | 33 | 33 |
| `Machine.lean` | 110 (RISC-V) | 113 | 113 | 59 (word language) | 62 |
| `Extractor.lean` | 33 | 34 | 34 | 34 | 35 |
| `Tree.lean` | 7 | 8 | 8 | 8 | 8 |
| `Certificate.lean` | 30 | 30 | 30 | 31 | 31 |
| **total** | **320** | **328** | **331** | **288** | **292** |

Logs: `logs/V3-S1/loc-*.log`, `fix-loc-contract.log`; `logs/ks-amendment/fix/loc-*.log`
(submissions); `logs/s2r/loc-contract.log`, `logs/s2r/fix/loc-contract.log` (core). The design
estimated "about 400" and the budget is 500. The vendored RISC-V model (205 declarations) left
the trusted closure with S2R.

### 2.2 Library and controls

| Stage | Library (code lines, theorems) | Controls (code lines, theorems) |
|---|---|---|
| S1 | 563, 70 | 387, 86 |
| S1 fix | 511, 81 (normalisation deleted) | 544, 111 (`Backdoor.lean` added) |
| KS fix | `Security.lean` 166, `PaperTheorem.lean` 113 new | `Potential.lean` 448 new, `Security.lean` 96 |
| S2R | `Machine.lean` 105 (rewritten), `Completeness.lean` 63 new, `Words.lean` 196, `WitnessSending.lean` 236 | `Machine` 105, `Extractor` 97, `Completeness` 120, `WitnessSending` 49 (all new or rewritten) |
| S2R fix and golf | twelve library and control modules 1,561 → 1,552 | `LogScan.lean` 298 new, `Certificate.lean` 141 |

### 2.3 Build and check times of the core (development VM)

| What | Time | Peak RSS | Log |
|---|---|---|---|
| S1 `lake build` cold (own build products removed; packages prebuilt), 1,249 jobs | 2 min 02.5 s | 4.17 GB | `logs/V3-S1/build-cold.{log,time}` |
| S1 warm | 3.1 s | | `build-warm.time` |
| S1 slowest modules: `Controls.Blake2s` 48 s (v2 known answers), `Controls.Relation` 46 s, `Controls.Tree` 15 s; all others ≤ 5 s | | | `build-cold.log` |
| S1 fix pass cold | 2 min 09.7 s | 4.2 GB | `logs/V3-S1/fix-build-cold.*` |
| S1 fix `lake exe axiomaudit` | PASS, 24 modules, 661 declarations | | `axiomaudit-exe-fix.log` |
| KS amendment cold; unamended `15e4ae5` in the same clone, first build | 2 min 07 s; 2 min 36 s | 4.15 GB | `logs/ks-amendment/build-*.log` (submissions) |
| KS fix cold / warm | 2 min 00 s / 2.8 s | 4.16 GB | `logs/ks-amendment/fix/build-cold.log`, `build-warm.log` |
| KS fix new modules: `Contract.Security` 2.0 s, `Library.Security` 4.0 s, `Library.PaperTheorem` 4.1 s, `Controls.Potential` 5.4 s | | | same |
| S2R: cold build before the stage at `05fde28` / after | 2:31.85 / 1:47.86 | 4.16 GB | `logs/s2r/build-baseline.log`, `build-cold.log` (core) |
| S2R warm | 2.77 s | 0.91 GB | `build-cold.log` |
| S2R `scripts/ci.sh` (hygiene, source-rule fixtures, build, audit, line budget) | 76.97 s, CI passed | 4.18 GB | `logs/s2r/ci3.log` |
| S2R fix: `ci.sh` warm (now with the gate fixtures, 13 s of it) | 47 s | | `logs/s2r/fix/ci-final.log` |
| S2R fix cold build of the five targets | 1:41.84 | 4.18 GB | `logs/s2r/fix/build-cold.log` |
| S2R fix axiom audit | PASS; 110 theorems use no axiom | | `logs/s2r/fix/axiomaudit.log` |
| S2R fix second kernel (nanoda `3a24072`) on 50 target declarations (55.6 MB export, 7,860 theorems) | 5.09 s, accepted | 263 MB | `logs/s2r/fix/nanoda/` |
| S2R golf per-module times: `Controls/Relation` 50.2 → 50.5 s (BLAKE2s known answers by `decide +kernel`, about 2.5 s per compression), everything else 5–9 s; import floor about 2.5 s | within noise | | `logs/s2r/golf/time-{before,after}.log` |

**Kernel evaluation of BLAKE2s costs about 2.4 s per compression** (one 32-byte message 2.43 s,
`logs/V3-S1/digest-probe/kernel-vector-ofFn.lean`). It is why the relation controls evaluate 16 +
2 + 1 chain steps and a handful of statements and no more, why the honest entry's transcript
known-answer module is its slowest (68.6 s, §4.3), and why no kernel run of a tampered full leaf
proof exists.

**Two S1 probes that decided trusted definitions.** A function-typed digest (`Fin 32 → UInt8`) is
re-evaluated per byte read by compiled code: 600 ms for 2 chain steps and 15.5 s for 3 in the
interpreter (`32^n`), against 428 ms for 1,000 steps with `Vector UInt8 32`; the vector is also
faster in the kernel (a 16-step chain 28.7 s against 35.5 s) (`logs/V3-S1/digest-probe/`,
V3-S1-A4). And the `2^18 + 1`-instruction image-size negative control had to be proved
symbolically: a concrete size check made the kernel build the list in 35 s (V3-S1-m6).

## 3. The witness-sending entry (S2a)

The baseline exists to exercise the whole pipeline with the simplest certified argument. It did,
and it found two defects in the organiser's own library, one false claim about its own
complexity, and the calibration number that broke the succinctness rule.

**What it is.** `submissions/baseline/`, flat: `BaselineV3.lean` 158 code lines (the linear
codec twins `packFast`, `bytesAtF`, `decodeWitF`, `decodeF`, `witWordsF`, `encodeF` with their
equalities to the library's functions; the strict `check`, `V`, `submission`; `check_eq`,
`Vb_eq`, `check_canonical`, `check_sound`, `fits_of_rel`, `check_encode`, `Vb_iff`; `kstate`,
`ks`, `complete`, `certificate`), `BaselineV3Controls.lean` 78, `BaselineV3Solution.lean` 21
(generated), `BaselineV3Run.lean` 53 (the local runner); 310 code lines, 38 theorems
(`logs/V3-S2/fix/check/loc.log`). A 94-line Python native prover, `smoke.py` 219 lines,
`check.sh` 136 lines, the 8-instruction RISC-V image from the core. It imports the library's
`encode`, `decode`, `P`, `E`, `img`, `fuel`, `computes` and proves only the strict check.

**Kernel.** `RecursionFast.Challenge.certified : CertificateR declared submission` against the
organiser-side v3 stub rendered from `claim.json`; 64 public declarations with the three axioms
(`logs/V3-S2/fix/check/axioms.log`); the controls `encode_leaf_kat`, `encode_node_kat`,
`decode_leaf_kat`, the four canaries `leaf_appended_rejected` … `node_truncated_rejected`,
`bad_tag_rejected`, `leaf_over_chainCap`, `stmt_unique` (a proof is accepted under at most one
statement), `node_children_capped`, `leaf_zero_accepted` (no hash evaluated), `certificateR`,
`flipped_image`, `fuel_7_claim`, `fuel_over_budget_claim`, and the four `lib_*` theorems that
convict the library.

**Measured** (`logs/V3-S2/fix/`, the end-to-end run after the fix pass and the golf):

| What | Time | Log |
|---|---|---|
| scratch core clone of the interim branch plus the entry, `gate`, `axiomaudit`, `entry-run`, from a fresh clone | 151.5 s, 2.2 GB | `check/setup-core.log` |
| clean organiser clone (for the manifest and allowlist) | 164.7 s, 4.2 GB | `check/setup-org.log` |
| clean rebuild of the entry (4 modules and the executable) | 15.8 s, 2.2 GB | `check/build-entry.log` |
| `leanchecker BaselineV3Solution` | 24.5 s, 1.7 GB | `check/leanchecker.log` |
| smoke tree `r = 2`, `n = 16` (canaries, node mode, Lean `P` = native prover, DoS sample) | 8.7 s | `check-run.log` |
| comparator, both kernels | 72.7 s, 1.0 GB | `check/harness-work/comparator.log` |
| `harness-local.sh` (render, stages 0–2) | 122.9 s | `check-run.log` |
| `HARNESS=1 check.sh` from fresh scratch clones, both core builds included | 530.8 s | `check-run.log` |
| **root check at `r = 8`, `n = 2^14`** (the calibration) | **20.69 / 21.11 / 20.93 s**, about 5.0 µs per compiled compression | `calibration-r8-n16384.log` (the first run, 20.87 / 21.23 / 21.16 s, is `logs/V3-S2/calibration-r8-n16384.log`) |
| native prover, whole ranked tree | 0.52 s | same |
| random 1 MiB proofs rejected; adversarially shaped 1 MiB proofs | ≤ 0.28 s; ≤ 1.25 s | `check/smoke.log` |
| the first verifier (strict `check` over the library's quadratic codec) rejecting a random 1 MiB proof | **563.26 s**, 128 MB | `logs/V3-S2/dos-unfiltered/run.log` |
| valid caterpillar proofs (each node a deeper left child and a zero-step leaf): depth 250 / 500 / 1,000 / 2,000 (272,048 B) | 2.68 / 11.63 / 49.56 / **212.64 s** | `logs/V3-S2/review/caterpillar.log` |
| S2a re-checked on 2026-10-20 against the pin: comparator 69.5 s, `HARNESS: ACCEPT`, whole run | 225.7 s | `logs/V3-S2/recheck-20261020.log` |

**What it found.** (1) The library's `WitnessSending.check` required canonicity only for nodes,
so a leaf proof with a byte appended or removed was accepted: the organiser's reference argument
failed two of the canaries of Design §8.3 step 7 (#10; fixed in S2R). (2) The contract's `packBytes`/`bytesAt` compile to
quadratic code (#10; linear twins now in the library). (3) The verifier is per level linear and
overall `O(|π| · depth)` because each node decodes, re-encodes and compares its whole subproof
(V3-S2a-M2); the RESULT and README had claimed "linear". (4) Organiser material (the stub, the
renderer, the local harness) had been put in the entry root, so a submitter following the worked
example could have edited the statement it was certified against (V3-S2a-M1; moved to the
interim branch `v3/s2-interim-harness`, and the harness now renders the challenge itself and
refuses a foreign comparator configuration). (5) Gate rule 4 still listed v2's fields and passed
only because `ε := 0` made `submission` computable as a whole (#9 item 4). (6) The calibration
number itself: 20.9 s is above `5 · T_V`, as designed, and also 500× above what a threaded
unrolled implementation of the same certified function takes (design §8.5; issue #6).

## 4. The honest entry `spartan-chain` (S2b, "R1")

The honest entry is the one measurement of what a real hash-based SNARK costs to certify against
this kind of contract. It was built by several agents in parallel from a normative blueprint,
reviewed six times, and it is the source of most numbers in this record.

### 4.1 What it is (PLAN D-3, D-4, D-5; BLUEPRINT-R1 D-7)

- **Leaves**: a real SNARK of `chainEnd s n = h` with `(s, n)` in the clear. The BLAKE2s chain as
  a uniform repeated-block R1CS over `K = GF(2^64)` (leanerVM's circuit, 14,720 gates + 256 output
  rows per compression, `rowsDigest = 4056851438423586957`, leanerVM's own `#guard` value);
  Spartan-style outer and inner sumchecks over `E = GF(2^192)` with a closed-form evaluation of the
  matrices' multilinear extensions (no SPARK, no preprocessing); 64 bits packed per `K` element
  with Frobenius ring switching (leanVM Annex A), which shrank the committed object 64× and was
  what made the smoke root fit `proofCap`; a Ligero tensor commitment with `t = 260` opened
  columns under unique decoding (`e < d/3`); a Merkle tree and Fiat–Shamir over the contract's
  oracle, the transcript seeded with the statement. Knowledge error `2^-129` proved, `2^-128`
  declared; `qV = 2^14` (7,774 queries at `n = 2^20`).
- **Nodes**: witness-sending, S2a's format and strict check, decided locally. **Not recursive.**
- **Extractor**: the library's parsing extractor (the witness is in the clear); the knowledge
  content is in `Rel`'s `chainEnd s n = h`, which only the SNARK's soundness delivers; the final
  review checked that a verifier skipping the SNARK would make `final` false.
- **Native prover**: a dependency-free Rust crate (BLAKE2s, the thread pool and the additive FFT
  written in it), whose bytes the compiled Lean `P` reproduces exactly.

### 4.2 Lean, by component (final `measure.sh` run on the golfed tree `781d98c`, `reports/measurements.md`, `logs/spartan-chain/measure/20261020-025203/`; theorem counts from `V3-S2b-RESULT.md` §1)

| Component | Modules | Code lines | Theorems | Copied | Check time, sum (s) | Peak RSS, max (MiB) |
|---|---:|---:|---:|---:|---:|---:|
| field: word-level `F`, `EF`, proved equal to CompPoly's `BF64`/`Ext3` | 5 | 1,031 | 128 | 0 | 43.6 | 2,790 |
| BLAKE2s circuit, chain R1CS, matrix-MLE closed form, prover tables | 15 | 4,622 | 390 | 1,543 | 131.5 | 2,714 |
| algebra: MLE, sumcheck, ring switching | 4 | 936 | 95 | 90 | 26.8 | 2,569 |
| RS code, proximity (AHIV22-style), PCS parameters | 3 | 696 | 66 | 0 | 21.8 | 2,657 |
| oracle, Merkle, transcript | 3 | 993 | 98 | 0 | 19.6 | 2,607 |
| protocol: Ligero, Spartan, leaf verifier, prover, decoder, node branch | 6 | 1,917 | 102 | 247 | 47.2 | 2,724 |
| knowledge soundness: log forest, PCS, Spartan rounds, chain, potential, `step`, `final` | 11 | 5,481 | 468 | 0 | 115.8 | 3,048 |
| submission, final instantiation, solution, runner, controls, known-answer tests | 14 | 1,090 | 214 | 0 | 156.0 | 4,068 |
| **total** | **61** | **16,766** | **1,561** | **1,880** | **562.3** | **4,068** |

The copied count is `loc.py`'s rule on provenance headers (three whole leanerVM files, the
`RingSwitch` sections, the whole of `Decode`); the stricter count is 1,687. The soundness proof is
a third of the entry; the BLAKE2s circuit with its chain R1CS is another third. **The theorem
column is approximate per row:** the rows are `measure.sh`'s component groups, while the theorem
counts come from the S2b RESULT §1, which groups modules differently (its protocol row is 4
modules and 1,284 lines with 102 theorems; its field row has 6 modules); only the total, 1,561, is
exact. The mismatch is inherited from REPORT §3.1.

### 4.3 Build, check and harness times (shared VM, load average 1.6–7.1 during the measurement run)

| What | Time | Memory | Log |
|---|---|---|---|
| cold full build of the entry (`lake build SpartanChain`, default `-j`, core libraries prebuilt), 61 modules | **130.4 s** | 4,061 MiB (largest process) | `measure/20261020-025203/full.time` |
| warm-up of the core libraries the entry imports | 93.2 s | | `core.time` |
| sum of per-module check times, imports prebuilt; floor 5.3 s of `.olean` loading per module | 562.3 s (golf: 682.5 → 621.5 s on a busier machine) | | `modules/`; `logs/spartan-chain/golf/{before,after}/times.txt` |
| slowest module, `TranscriptControls` (the kernel's BLAKE2s known-answer tests) | 68.6 s | 4,068 MiB | `measure/…/modules` |
| next: `SoundnessKSBase` 35.1 s / 3,048 MiB; `FieldBaseCorrect` 14.4 s; `Blake2sCompress` 12.4 s; `SoundnessChain` 11.1 s; every other module ≤ 11.5 s; every module under 2 min | | | same |
| warm `lake build SpartanChain` (2,288 jobs) | 1 min 58 s | | `reports/fix-pass.md` |
| `check.sh` build of the entry, `gate`, `axiomaudit` and the runner in a fresh scratch core | 189.3 s (118.5 s in the final run) | 3.2 GB | `harness-final3/check/build.log` |
| comparator, both kernels | 465 s; 401.7 s in the final run | 3.67 GB | `harness-final3/`, `harness-final4/check/harness-work/` |
| nanoda alone, after the fix of §4.5 | about 70 s | 2.41–2.47 GB | `harness-final3/nanoda-rss.log` |
| `harness-local.sh` (render, manifest, source rule, comparator, rebuild, gate) | 720 s; 596.1 s | | `harness-final3/check-run.log` |
| `HARNESS=1 check.sh` end to end, `HARNESS: ACCEPT` both times | 1,105 s; 794.6 s | 6.3 GB max | `harness-final3/check-run.log`, `harness-final4/check-run.log` |
| Rust crate clean build (`cargo build --release --offline`) | 22.7 s | | `logs/spartan-chain/rust/build.log` |

The gate on the final tree: `PASS`; rule 4 finds compiled code for `V`, `P`, `E`, `img`; 28
pinned (CompPoly) and 3,727 trusted modules; the closure of `certified` has 32,999 constants with
the three axioms (`harness-final4`). The source rule: 61 files, 0 findings.

### 4.4 Prover, verifier and field runtimes, and proof sizes

**Rust prover** (`reports/rust-prover.md`, `logs/spartan-chain/rust/leaf-n*.log`; 3 runs each,
all 32 threads, about 2,200 % CPU at `n = 2^14`):

| `n` | Proof size | Prove wall | Peak RSS | Native verify | Oracle queries |
|---:|---:|---|---:|---|---:|
| 16 | 143,711 B | 0.18 / 0.19 / 0.18 s | 8 MB | 0.084–0.103 s | 3,533 |
| 1,024 | 457,843 B | 0.71 / 0.71 / 0.70 s | 255 MB | 0.39–0.42 s | 4,414 |
| 16,384 (the ranked leaf) | **1,464,107 B (above `proofCap`)** | 7.61 / 7.43 / 7.98 s | 3.95 GB | 0.81–0.84 s (`check-leaf`, which skips the cap) | 5,156 |

Where the time goes at `n = 2^14`: outer sumcheck 4.4 s, inner 1.5 s, encode 0.5 s, witness 0.4 s,
ring switching 0.4 s, Merkle 0.1 s. Native verify is single-threaded and dominated at `n ≥ 1,024`
by the two column equations at 260 columns (`7k` `K`-products per column). The smoke tree
(`r = 2`, `n = 16`): 0.66–0.79 s for the whole tree, root 575,112 B, native root verify 0.17–0.20 s.
For comparison, leanVM's own Flock on this VM proves `2^14` compressions in 14.25 s and verifies
in 477 ms (`logs/probes/flock-2e14.log`; its README reports 485,033 compressions/s on an M4 Max),
and one native chain of `2^14` steps hashes in 2.1 ms (`logs/probes/fieldbench.log`).

**Compiled Lean verifier** (`Run.verifyProof`, `rfl`-equal to the certified `Submission.Vb`):

| Proof | Bytes | Lean `Vb` | Log |
|---|---:|---|---|
| leaf `n = 1` | 95,719 | 138–153 ms | `leaf-snark/verify-leaves.log` |
| leaf `n = 16` | 143,711 | 0.21–0.30 s | `leaf-snark/verify-tree.log` |
| level-1 node (two leaves) | 287,512 | 0.47 s (1.01–1.06 s before the byte-offset node codec) | `fix-m2/after-root.log` |
| smoke root (four leaves) | 575,112 | **0.99–1.71 s over nine runs** (`logs/spartan-chain/fix-m2/after-root*.log`, which includes a 1.707 s run); 1.06–1.45 s through `Run.verifyProof`; 1.22–1.26 s in the two harness smoke runs; before the byte-offset node codec 2.25–2.51 s (midreview S2b-M2, `fix-m2/before-root.log`) and 2.25–2.8 s as REPORT §3.3 quotes it | `fix-m2/`, `harness-final3/check/smoke.log` |

So the smoke root is under `T_V = 2 s` with a margin as small as 0.29 s on this loaded VM. All 28
canaries are rejected on every proof; 16 random 1 MiB proofs are rejected in at most 0.094–0.11 s
(Lean) and 0.013 s (native). **Valid caterpillar proofs** (`logs/s2b-final-review-probes/caterpillar/`):
6.8 s at depth 1,000 (168,080 B), 64.0 s at 3,000, **275.0 s at depth 6,000** (1,008,080 B), about
80 ns per byte re-processed per level.

**The Lean prover**: `n = 16` in 34.9 s after the table builders were rewritten (word-array forms
and a transposed sparse walk; 1,783 s before, with 16,384-bit `Nat` shifts), byte-identical to
Rust at `n = 1, 2, 16` (`infra/harness-final/prove-kat-n16.log`). The Ligero commit computes
`N·k·(m+1)` `K`-products (about 19 M at `n = 16`, about `9·10^9` at `n = 1,024`), so the Lean `P`
is practical for small `n` only; the Rust prover uses the additive NTT. The known-answer test
(`kat.py`, nine dumps, all `SAME`) runs in 21 s compiled; through the interpreter `walk` had taken
462 s and `leaf` 690 s.

**The field** (`FIELD.md`, `logs/field/bench-20261019-185727.log`, `logs/probes/e2/bfbench.log`,
`logs/probes/fieldbench.log`):

| Operation | Compiled Lean, word-level | CompPoly compiled | Rust (this VM, no `pclmulqdq`) |
|---|---:|---:|---:|
| `K`/`F` multiply | 87 ns | 30,300 ns (29.7 µs mul+add) | 17.5 ns (leanVM's naive loop 22–25 ns) |
| `E`/`EF` multiply | 535 ns | 466,000 ns (415 µs mul+add) | 66 ns |
| `F` inverse | 1,506 ns | 1.72 ms | |
| `EF` inverse | 2,217 ns | | |
| BLAKE2s, one oracle call on 33 bytes (Lean) | 5.9–7.3 µs | | 124 ns serial, 46 ns with SIMD `hash_many` |
| Merkle build over 4,096 columns (8,191 oracle calls); 260 openings | 65–77 ms; 25–28 ms | | |

The equality of the word-level field with CompPoly's is a kernel-checked ring isomorphism
(`ringEquivBF64`, `ringEquivExt3`), so CompPoly stays the specification.

### 4.5 The second kernel: 52 GB on one ordinary lemma (D-11; V3-S2b-M1)

The comparator checks the certificate with two kernels. On the certified entry, Lean's kernel
accepted; nanoda's memory grew about 2 GB per minute and the global OOM killer stopped it at
**52.0 GB** after 23 min on a quiet machine (`logs/spartan-chain/infra/harness-final2/nanoda/nanoda-run.log`;
a second run inside a 50 GB scope was killed at 51.3 GB; the review's sampler saw 53.5 GB; the
sources quote different runs). The export was 236 MB: 22,745 theorems, 7,978 definitions, 662
inductives, 4.27 M expression nodes; lean4export took 25 s and 3.0 GB. The harness printed
`HARNESS: REJECT` and the comparator run took 1,797 s.

**Bisection** (`harness-final2/nanoda/bisect/`: `modules.log`, `compoly.log`, `suspects.log`,
`spread-nanoda.log`; nanoda on each module's export closure under a 4 GB cap and a 300 s timeout):
every closure containing `SpartanChainFieldBaseCorrect` fails, every closure without it checks in
at most 8 s, and CompPoly's `BF64` closures check in about 70 s and 2.3 GB (`cp-Impl` 74.73 s /
2,292,144 KB; `cp-Ext3` 69.95 s). Narrowed inside the module to one **private** lemma,
`SpartanChain.F.spread_getLsbD`, proved by a 64-way `interval_cases j <;> simp` over `BitVec`
positions: its closure alone (3,441 declarations, 20.5 MB of export) took nanoda to **41.9 GB**
before the cgroup killed it (`logs/field/nanoda.log`). It is load-bearing: it feeds `P_spread`,
`toBF64_sq`, `sq_eq_mul`, `frob_eq_pow`, `toBF64_inv`, hence `instField`.

**After the rewrite** as five mask-and-shift stage lemmas with `omega`, statement unchanged: the
lemma checks in **0.76 s / 33 MB**; the whole solution checks under nanoda in **70 s, peak
2,412,072 KB** (`harness-final3/nanoda-rss.log`), and `HARNESS: ACCEPT` followed. The orchestrator
also replaced `SoundnessPCS.x_pow_word`'s `decide +kernel` (it had passed nanoda in 23 s / 614 MB
for a 1,032-declaration closure). For comparison S2a's comparator took 71 s and 0.98 GB with both
kernels; v0.3's nanoda had been OOM-killed at 60 GB on a diverging declaration (E4 §3).

**Why it matters.** A tactic proof that elaborates in seconds, passes Lean's kernel and is
semantically innocuous can be uncheckable by the harness's second kernel, and the submitter finds
out only at intake. The cost is the size of the export, not the difficulty of the mathematics:
case splits over concrete words produce proof terms whose unfolding the second kernel does not
share with the elaborator. The design caps the harness at 2 h and the build at 48 GB but sets no
memory or time cap per kernel; the proposed cap (16 GB / 30 min for the whole comparator run under
a cgroup, with a fixture of the old lemma rejected as "nanoda budget exceeded") and a
pre-submission check with the pinned kernels (`tools.env` was restored for this) are S3 work that
never happened.

### 4.6 What is kernel-checked, what is measured, what is claimed (V3-S2b-RESULT §2)

- **Kernel**: `Challenge.certified : CertificateR declared submission` from the closed theorem
  `SpartanChainFinal.facts`, no hypothesis; `KS.kstate : KState (Rel (vb LV)) (V LV)
  WitnessSending.E (2^-129)` and `KS.ks` with `qV = 2^14`: the potential `μ` of blueprint §9.3,
  `mu_empty`, the `step` law (`mu_step_chain` from `doom_absorb`, `doom_mid`, `esc_single_le`,
  `round_r0_le`, `round_r7_le` and the generic `muG_step`), the `final` law (`final_law` from
  `runLog_chain`, `accept_not_doomed`, `doom_of_not_esc`); `chainEvals_ok`; perfect completeness
  for every oracle (`complete`, `snark_complete`, `chainHonest`); the query bound `queries_le`; the
  components (the field isomorphisms; the MLE/sumcheck/ring-switching counting lemmas; the RS
  code's distance and the proximity lemma `far_bad_le` with the sharper `(e+1)` form; the numeric
  R0/R7 bounds at the protocol's parameters, `r7_far : (4/5)·2^-129` in exact `ℕ` arithmetic, the
  kernel-decided `pow17_le : 17^260·2^129·5 ≤ 24^260·4` and its negative `pow17_259`; the BLAKE2s
  chain block against the contract's own `blake2s` in both directions; the chain R1CS
  `chain_sound`, `chain_complete`; the closed-form matrix evaluation `chainMats_eq`; Merkle
  completeness and binding on the log; the transcript forest); that the compiled verifier and
  prover are the certified objects (`Run.verifyProof_eq`, `Run.proveLeafBytes_eq`, by `rfl`); the
  negative claims (image bit, fuel 7, `qV − 1`, declared `ε = 2^-130`); every positive and
  negative control of `reports/controls.md`, including that booleanity is load-bearing for the
  packing (`and_gadget_bool` / `and_gadget_nonbool`).
- **Measured**: everything in §4.3–§4.5.
- **Claimed, not proved**: the Rust prover's correctness (checked by the compiled `Vb` and the
  byte-identity KAT only); `T_V` and DoS behaviour on the reference machine; and, as for every
  entry, the BLAKE2s-as-random-oracle heuristic and composition across levels.

### 4.7 Scope: what R1 is not

Not recursive (the node branch runs the instantiated `Vb` on embedded children, which is
literally what `Rel`'s node clause states; no node circuit, no in-circuit BLAKE2s verification, no
decoder). Not rankable (§7.3 of the design). Certified only against the amended contract, with
interim organiser tooling (the v3 stub and renderer, the CompPoly-pinned allowlist and manifest,
gate rule 4 over the v3 fields, all on the local branch `v3/ks-interim-harness`). A DoS property
on prover-chosen statements (275 s). Its node branch evaluates `blake2sOracle` on the children to
decide `Rel` and compares no oracle answer, which an O-25 intake review must be told. R2 (recursive
nodes, semi-uniform circuits, a WHIR- or FRI-class PCS, a circuit DSL with `toProg`/`toR1CS` and a
correctness theorem, a decoding node extractor) was designed (F1 §5.3) and blocked on #7 and #8;
not started.

## 5. Proof-size analysis

A Ligero proof is √-size: it opens `t` whole columns of a `m × k` matrix and sends two combined
rows, so it cannot fit `proofCap` at the ranked leaf however the matrix is shaped. Folding
schemes are polylogarithmic but need a proximity theorem the provable regime does not yet give
in Lean. This section puts the numbers next to each other.

### 5.1 The honest entry's leaf, measured and decomposed

The leaf proof at `n = 2^14` is **1,464,107 B** (measured, §4.4; above `proofCap = 1,048,576 B`).
The byte layout (BLUEPRINT-R1 §7, `leafSize`, at `k = 2^14`, `m = 256`, `ℓ_N = 17`; the shares
computed from the blueprint's formula, the total measured):

| Part | Bytes | Share |
|---|---:|---:|
| the two combined rows `ū`, `v` (`48k`) | 786,432 | about 54 % |
| the 260 opened columns (`260 · 8m`) | 532,480 | about 36 % |
| their Merkle paths (`260 · 31 · ℓ_N`) | 137,020 | about 9 % |

The split minimises `48k + 2080m` subject to `k·m = M'`, the packed witness size (blueprint §5.2),
so both leading terms scale as `√M'`; leaves fit `proofCap` up to `n = 4,096` (457,843 B at
`n = 1,024`, 143,711 B at `n = 16`). Packing 64 bits per `K` element (ring switching) already
shrank the committed object 64× against an unpacked bit witness, which at `n = 16` would have been
about 450 KiB with the best shape (blueprint §0, computed). The ranked leaf's witness is about
`2^28` R1CS constraints; its committed word and codeword are 2–4 GiB (F1 §5.2).

### 5.2 Sizing the alternatives for recursion (F1 §5.2, from WHIR Table 5 UD column and ZCF24; all **estimates** except the measured rows)

The node circuit verifies two children: with BLAKE2s in R1CS at about `2^14` constraints per
compression (measured, leanerVM's circuit) and 10k–14k compressions to verify one UD-provable
128-bit PCS proof at `2^24`–`2^28`, the node circuit is about `2^28.3` constraints. The ranked leaf
is the same order (`2^14` compressions). leanVM measures a 2→1 step at about 18,400 compressions
and one compression at 15.9k Boolean constraints (E3 §4).

| PCS (with Spartan) | Proof at `2^24` / `2^28`, 128-bit UD | Fits `proofCap` for the node circuit? | Lean proof content |
|---|---|---|---|
| WHIR-class | 621 KiB / 770 KiB | yes, barely | out-of-domain samples, shift queries, mutual correlated agreement in the UD regime, folding: the largest |
| FRI, arity 8, rate 1/16 | about 1 MiB / above | no at node size | folding in the UD regime (BCIKS20 correlated agreement for lines), the query phase |
| Basefold, arity 2 | 7.95 MiB at `2^24` (ZCF24, λ = 100) | no | the smallest: one folding lemma in the UD regime; ArkLib #383 has it over binary fields |
| Ligero/Brakedown tensor | `≥ 25 MiB` at `2^27`; **1,464,107 B measured at `2^28`-constraint leaf** | no at any useful size | the simplest: the interleaved proximity lemma, row decoding |

With a plonkish/AIR arithmetisation of BLAKE2s (`2^10`–`2^11` cells per compression) the node
circuit is about `2^24` and every row but Ligero fits (F1-4). The tensor layout also makes node
extraction cheap (`2^35`–`2^41` steps for short rows) but fails `proofCap`, which is the trade
F1 §3.3 records.

### 5.3 Unique decoding against the Johnson regime

The provable regime under V3-5 (no named conjecture) is unique decoding: the interleaved
proximity lemma the entry proved is AHIV22's, with `e < d/3` (`far_bad_le`: if `U` is not
`e`-close then at most `d · |E|^{m−1}` coefficient vectors make the combination close; the entry's
sharper form has `(e+1)` in place of `d` and is tight on a toy, `tight_toy`). It gains at most one
bit per opened position, so 128 bits need `t ≥ 128` positions; the entry's `t = 260` with
`(4/5)·2^-129` escape probability for the far case (`far_miss`, kernel) is what the 36 % column
share pays for. The user's direction of 2026-10-20 (CORE-HANDOFF §2.14): an R1′ with WHIR- or
Ligerito-style folding in the unique-decoding regime, using **BCHKS25's half-distance mutual
correlated agreement** in place of AHIV22's `d/3`, is the route under `proofCap`; the **Johnson
regime** (BCIKS20, BCHKS25's list-decoding results, `1 − √ρ`) comes later and would roughly halve
the queries, but its theorems were judged out of reach for a baseline proof (F1 §5.1). Proved
proximity-gap theorems formalised by an entry or the library are admissible; named conjectures
are not (V3-5).

### 5.4 Grinding

Grinding trades prover work for queries: a proof-of-work of `g` bits on designated answers lets
the soundness analysis charge `2^-g` per attempt and reduces the query count accordingly
(leanerVM plans 17 bits per WHIR level, E1). It was impossible under perfect completeness over
every oracle (an adversarial `H` defeats any bounded nonce search) and is admitted by
`CompleteWithError`: `89·2^g` attempts for `δ = 2^-128`, `67·2^g` for `2^-96`, with the same
expected `2^g` (design §6.4). No entry used it, and the O-25 record shows that a `V` which reads
the leading-zero count of an answer is a recognition channel (O25-M4), so grinding must be
checked by code the submitter does not author.

### 5.5 What the sizing says about the benchmark shape

At `r = 8`, `n = 2^14`, a witness-sending root carries 256 leaves, so any SNARK leaf above 4 KiB
cannot be concatenated into a rankable root, and a Ligero leaf cannot fit even alone; a recursive
entry needs a WHIR-class PCS, a decoding extractor and a self-verifying node circuit, none of
which existed in Lean. Fewer and longer leaves (`r = 4`, `n = 2^20`) were proposed for the `T_V`
calibration (#6) and would also shift the balance from nodes to leaves. The shape was never
re-decided; a next design should size it together with the caps (design §16, C5).

## 6. What reuse cost

The entry imports only Mathlib, the contract, the library and CompPoly's `BF64`/`Ext3` closure;
everything else had to be copied with a provenance line or written fresh. This is what each
candidate library turned out to be worth (E1–E4, REPORT §3.5).

| Source | Reused how | What it gave | What it cost |
|---|---|---|---|
| **leanerVM** (`532ebb4`; WHIR and Merkle on unmerged branches `review/whir-67`, `review/whir-103`) | **copied**, 1,543 code lines with modifications: `Flock/{Circuit,Builder,Words}.lean`, `Blake2sCircuit.lean`, plus 90 lines of the Frobenius map; Apache-2.0, licence in the root | the only existing proved BLAKE2s R1CS, bridged to the contract's `compress` by one lemma; the circuit matches leanVM's row for row (`rowsDigest`) | cannot be imported: it imports ArkLib and CompPoly modules outside the allowlist, uses the module system (`module`, `public import`, `@[expose]`) and `#guard` tests, which the source rule refuses; copies had to drop the module keywords and the tests. Its sumcheck and lincheck security is ArkLib-framework code; only its mathematics informed the design. Its own planned KS bound has a `Q²` term and a grinding-backed query round, which confirmed #5 independently (E1 §4). |
| **leanVM** (`a386121f`, Rust) | architecture and conventions | the design itself: `GF(2^64)`/cubic extension, Flock = Spartan over binary fields, ring switching (Annex A), the one-compression Merkle framing; the Rust prover follows its field conventions (`R64 = 0x1B`, limb order, Karatsuba), FFT structure and stage order; `hash_chain.rs` proves exactly the leaf shape | its fast path is `pclmulqdq`, which this VM lacks, so its `GF(2^64)` falls back to a 22–25 ns loop; its one-compression framing breaks under the oracle's one-byte tag (E3 §0.4) |
| **CompPoly** (`572f997`) | **imported** as the specification field (28 modules, allowlisted and pinned by the interim tooling) | `BF64`, `Ext3`, the Rabin irreducibility certificate, byte serialisation; the Gao and Guruswami–Sudan decoders as future specifications | too slow compiled (29.7 µs / 415 µs per multiply; `BitVec` compiles to `Nat`), so the entry wrote a word-level twin proved equal (D-5, 1,031 lines); its one `@[csimp]` lemma (`Fields.Extension.Arithmetic`) made the gate reject until CompPoly was pinned; its closure costs nanoda about 70 s and 2.3 GB per entry; its `Multilinear.Basic` is a 3-module closure (cheap to admit), its `Univariate` core and `Multivariate` are built in the shared tree, its decoders are not allowlisted |
| **ArkLib** (`7653a90`) | guide only | the AHIV22 proximity lemma's statement (re-proved fresh with a row-by-row induction instead of the maximal-support argument), `card_badChallenge_le`'s shape | not allowlisted; the AHIV22 lemma pulls a 102-module, 24.7k-line closure through VCVio and PolyFun; its Spartan, BCS/FS, FRI, Binius and ring-switching files carry `sorry` or are definitions only (E2 §7); its probability layer was rewritten twice in a month |
| **VCVio** (`a4232d0`) | not used | Merkle extractability in the ROM (51 files, sorry-free) | 107–158 modules; the contract's `OProg`/`Log` is a different formalism; the ROM union-bound lemma is one commit past the pin (O-20) |
| **Clean** (`42fe4b26`) | not used | a circuit DSL with soundness and completeness notions | never on the badge path; not required at the pin; imports `Lean`, so any copy must be stripped of its tactics and `circuit_norm` sets (E4 §1) |
| **The S2a entry** | copied (54 lines of `Decode`) and the library's `E`, `img`, `fuel`, `computes` imported | the extractor side of the certificate cost nothing | — |
| **Mathlib** | imported | `Polynomial.card_roots'`, double counting (`Finset.card_mul_le_card_mul`), `InformationTheory.Hamming`, the RS distance, `LinearAlgebra.Basis`, `MvPolynomial.schwartz_zippel_*` | no `Fintype` instance for core `Vector` (#9 item 7); the `Fintype Digest` instance had to be the contract's |
| **The v2 harness** (tag `v2-archive`) | re-implemented locally (`harness-local.sh`, `render-challenge.py` cut down) | the comparator order, the manifest, the gate, the source rule, the sandbox | the v3 stub, renderer, allowlist and manifest did not exist at the pin (E4 §3); the two entries ran on scratch branches |

**The net.** Of 16,766 lines, 1,687–1,880 were copied and 14,886 written fresh; the parts a
submitter should never have had to write (the field, the BLAKE2s gadget, Merkle and transcript
on the log, the generic potential, the proximity lemma, the sumcheck counting lemmas, the codec)
are about 10,500 lines and are the organiser library the design's §11.2 names. A next design
should decide the allowlist policy for ArkLib and CompPoly's decoders (re-prove, copy a
Mathlib-only closure, or extend the allowlist) before entries start (#9 item 8), and should
budget the second kernel's cost of every admitted closure.

## 7. What the reviews found

Fifteen review and golf passes ran in four days. The pattern across them: the statement-level
errors were in the *definitions* of the security argument (what is bad, when is a chain doomed,
what is the invariant), not in the protocol, the bytes or the parameters; and three of the most
consequential findings were invisible until the harness ran on a real entry.

| Review | Majors / minors | Verdict | What the majors were |
|---|---|---|---|
| `V3-S1-review` (the contract) | 4 / 12 | ACCEPT after fixes | **M1** a certified verifier can recognise the deployment oracle (O-25; the probe became `Backdoor.lean`); **M2** no control exercised the `step` law (a vacuous `step` built green); **M3** efficient extraction required only for logs of `≤ 2^24` entries while §4.5 quoted `2^64`; **M4** the committed state listed targets that did not build |
| `V3-S1-golf` | — | 451 declarations with identical type and value hashes before and after | eight private helpers added; six compiler-generated equation lemmas no longer generated |
| `V3-S2-KS-review` (the amendment) | 1 / 6 | sound; fix M1 before merge | **M1** `logCap = 2^64` was justified by a false sentence and certified a 96-bit verifier at the 128-bit cap (`Probe.v24_ks`); the paper theorem kernel-checked by the reviewer (`Probe.paper`, adopted); the `Fintype` elaboration snag (m2); two redundant hypotheses (m3) |
| `V3-S2a-review` (the witness-sending entry) | 2 / 9 | changes required | **M1** organiser material in the entry root (a submitter could edit the statement); **M2** the "linear" claim false on lopsided proofs (212.6 s measured) |
| `V3-S2a-golf` | — | 289 → 277 code lines | two proof bodies |
| `BLUEPRINT-R1-review` (the protocol and its §9) | 4 / 14 | sound in substance; §9 does not hold as written | **M1** a partially built Merkle tree was "doomed forever", making `final` false; **M2** `Bad` omitted hits on Fiat–Shamir states, so chains could be assembled out of order; **M3** `bounded_chainBlock` false as specified; **M4** the quadratic decoder on the node path |
| `BLUEPRINT-R1-S9-review` (§9 rewritten) | 3 / 4 | not ready to formalise | **M1** `Doom_T` ignored failed verifier checks, so a sumcheck round escaped with probability 1 and `step` was false; **M2** `μ` double-counted prefixes of a partial round; **M3** two lemma statements false (L-M4, L-K7); three further false statements found by the Merkle implementer |
| `V3-S2b-midreview` (the entry, mid-stage) | 5 / 12 | faithful and honest; not certifiable yet | **M1** `Facts.queries` false with no bound on `n`, so the certificate was vacuous (kernel-checked uninhabited); **M2** the smoke root over `T_V` (2.25–2.51 s); **M3** the `step` law only generic; **M4** `chain_sound` without a consumer; **M5** the final instantiation missing |
| `V3-S2b-review` (the certified entry, code frozen) | 2 / 7 | the mathematics is sound and the statement is the contract's; the stage is not done | **M1** nanoda out of memory, `HARNESS: REJECT` (§4.5); **M2** the interim gate rejecting for two organiser-side reasons (CompPoly unpinned; rule 4's v2 fields); a false "memcpy cost" claim (275 s caterpillar); the KAT run on a pre-change copy of the tables; no kernel negative for the declared `ε` (added) |
| `V3-S2b-golf` | — | 682.5 → 621.5 s summed check time, 284 → 28 warnings, −4 lines, statements byte-identical under `pp.all` | two 37 s elaborations fixed by naming dot-constructors; a 31 s `congr 1` replaced by explicit congruences; 218 unused simp arguments removed |
| `V3-S2R-handoff-review` (the rules, before any code) | 4 / 17 | the stage implements the handoff as amended | **H-M1** a step monad with Lean continuations charges nothing for the continuation (kernel probe `bruteForce_steps = 1`); **H-M2** expression trees evaluated in one step hide a `progCap`-fold factor; **H-M3** node liveness cannot run at node size; **H-M4** a `δ` statement over random `H` loses the theorem that honest proofs verify under BLAKE2s |
| `V3-S2R-review` (the rules stage) | 2 / 6 | fix M1, M2 | **M1** memory was one up-front constant, so the budget's derivation did not run in the machine and every leaf run paid node-sized memory (probe `mem_le`); **M2** the handoff's positive controls for the new language were missing (no program read the log); also `vb_rejects_all_certified` (m1) and `choice_certificate` (m2) as probes |
| `V3-S2R-golf` | — | 1,561 → 1,552 lines over twelve modules; times within noise | two helper lemmas; the contract not golfed |
| `F2-o25-review` (Candidate E) | 6 / 4 | does not close the mechanism | O-25 document §4 |
| `F2-o25-review-r2` (Candidate T) | 6 / 9 | adopt the core, not as specified | O-25 document §6 |

**Three lessons for the organiser's documentation** (REPORT §3.4). The definitions of the
potential are where the errors were, and a blueprint reviewed on paper twice still had `step`
false before the formaliser touched it: the paper cannot be trusted until the Lean exists. Three
findings (the `Fintype` start-up bug, the nanoda budget, the gate's field list) were invisible
until the harness was run on a real entry: rules written without an entry built against them
will be wrong in the same way. And every review that mattered ran kernel probes rather than
arguing: the S1 review's backdoor, the KS review's `v24_ks`, the midreview's `facts_uninhabited`,
the S2R reviews' `bruteForce_steps` and `mem_le`, the O-25 reviews' `idxOf_full` and
`pubTau_eq_challenge`.

## 8. Process lessons for agent-driven development

v3 was built by agents under an orchestrator, about ten at a time on one 62 GB machine, with
the user reachable only part of the time. What follows is what the record shows about that way
of working, separated into build-time traps (each a measurement), the shared-machine rules
(from `IMPLEMENTERS.md` and the repositories' `CLAUDE.md`), and the orchestration lessons (from
the stage records and the orchestrator's own session notes; those last have no log and are
marked so).

### 8.1 Build-time traps, each of which decided whether an entry could be certified or accepted

| Trap | What happened | Measured | Rule it produced |
|---|---|---|---|
| **A computable closed term in the trusted base** | the KS amendment's `instance : Fintype Digest` was a computable closed term; every compiled binary that imported the contract enumerated `256^32` functions at start-up; `verify` and `prove-lean` never started; the interpreter was unaffected, which is why the review did not see it | a hello-world reached 22.9 GB in 20 s without printing (`logs/spartan-chain/oracle-merkle-transcript/init-blowup.log`); the "6.8 GB in 7 s" and the post-fix "0.20 s and 86 MB" figures appear only as text in REPORT §2.6, PLAN D-9 and CORE-HANDOFF §2.1 (no log); V3-KS-A8 | `noncomputable` on any closed term only proofs use; never `irreducible` in the trusted base (an attribute); the literal `2^256` in trusted statements |
| **Function-typed data** | `Digest := Fin 32 → UInt8` was a closure re-evaluated per byte read | `32^n` hashes per chain (`logs/V3-S1/digest-probe/`) | data is `Vector`/`Array`/`ByteArray`, never `Fin n → α` |
| **Failing unification unfolding an instance** | proofs that mismatched a goal containing `Fintype.card Digest` failed with "maximum recursion depth" or heartbeat timeouts instead of a type mismatch | deterministic, 5.6 s for the probe file (`logs/ks-review-probes/Snag.lean`); `whnf` timeouts on `split.symm` in the `V24` proof | rewrite with `fintype_card_digest` first; avoid `positivity`, `gcongr`, `rfl`/`decide` on the term; keep bounds abstract until the end |
| **`decide +kernel` on concrete data** | deciding a 117-entry honest transcript in the kernel | 7 min 45 s and 5.3 GB, killed in parallel runs; the symbolic proof of the same control 7.5 s (REPORT §3.1) | never let the kernel or `decide` evaluate the `2^14`-row block or BLAKE2s on concrete data; reason about the generic definitions |
| **Case splits over concrete words and the second kernel** | a 64-way `interval_cases j <;> simp` over `BitVec` positions | nanoda killed at 41.9–52 GB; 0.76 s / 33 MB after a structural rewrite (§4.5) | a per-kernel budget and a pre-submission nanoda check; no `interval_cases`/`decide` over concrete words in anything the comparator exports |
| **`binop%` elaboration of long `++` chains with bare dot-constructors** | two definitions took 37 s each to elaborate | 0.4 s once the constructors were named (`SoundnessLog.shape`, `KS.pre8`; golf) | name constructors in list literals and `replicate` arguments |
| **`congr 1` unfolding `compress`** | `isDefEq` on two applications of `compress` unfolded it and `Vector.ofFn` | 31 s → under 0.5 s with explicit congruences; the proof hit the heartbeat limit under the profiler (golf) | explicit `congrArg` where the heads are expensive |
| **Large closed circuit terms** | `blake2sCircuit`, `chainBlock` (`2^14` rows) | had to be `@[irreducible] noncomputable`: a compiled closed term is evaluated at program start, and the kernel must never unfold it (REPORT §3.1) | computable builders (`@[never_extract] chainBlockAt`) beside noncomputable closed terms |
| **`BitVec`/`Nat` in compiled hot paths** | CompPoly's field, the Lean prover's table builders with 16,384-bit `Nat` shifts | 29.7 µs per multiply; 1,783 s for one 16-step leaf, 34.9 s after word-array forms (§4.4) | word-level twins proved equal to the specification; the specification never runs |
| **List codecs on the verifier path** | the contract's `packBytes`/`bytesAt` | 563 s to reject 1 MiB; per-level re-encoding, 275 s on a lopsided proof | linear twins with `_eq` theorems; byte-offset parsing; canonicity on the bytes |
| **Kernel BLAKE2s** | known-answer tests | 2.4 s per compression | few compressions per control; the module that does them is the slowest in the entry (68.6 s, 4 GB) |

### 8.2 The shared-machine budget (`IMPLEMENTERS.md`, the `CLAUDE.md` files)

- About ten agents build concurrently on one 62 GB VM. Each module should check in under about
  2 minutes and 4 GB; a module that needs more is a build-time defect, and build time was a
  stated priority. Probes run under `systemd-run --user --scope -p MemoryMax=8G timeout 900 …`;
  reviews ran their builds in snapshot copies (`/tmp/v3s1-review/snap`) because a golf agent was
  editing the main tree at the same time.
- **Never kill processes you did not start**: no `pkill lean`, `killall lake` or other name-based
  kill; kill only by the PID of your own process, or use `timeout`. Every Lean or cargo command
  gets a `timeout`. If a build runs much longer than expected, inspect it with `ps` (a lock, a
  package being rebuilt from scratch) rather than waiting.
- The shared package tree (`/home/devops/CambridgePQ/recursion.fast/contract/.lake/packages`) is
  prebuilt and read-only: never `lake update` or `lake exe cache get` against it; new clones
  symlink it. The shared development clone (`rf-core-sc`) needed `./refresh-roots.sh` after every
  new module (lake roots) and another agent's `lake build` sometimes removed a module's `.olean`
  mid-edit (`ligero.md` note 5).
- Cold builds were not re-measured after golf because measuring one would mean deleting build
  products in the shared clone (`V3-S2b-golf.md`). Every reported time is therefore an upper
  bound with the load average recorded next to it.

### 8.3 Orchestration lessons

From the stage records:

- **Reviews in parallel with golf, on a frozen tree.** The S1 review had to snapshot the tree
  because golf was editing it; the S2a review's line numbers are post-golf; the S2b entry was
  code-frozen at 22:00 on 2026-10-19 before its final review. A review of a moving tree is
  wasted.
- **Probes over arguments.** Every review that changed a decision did so with a kernel-checked
  probe (§7). The orchestrator should ask for the probe file and its `#print axioms` line, not
  the argument.
- **A blueprint is not a specification until it is Lean.** Two paper reviews of BLUEPRINT-R1 §9
  found seven majors, and the formaliser still found three more false statements. The decision
  that paid off was to put the implemented Lean, not the design text, as "the reference" in every
  ledger entry.
- **Sources disagree; status lines go stale within hours.** REPORT, PLAN, the S2b RESULT and the
  #5 comment all said the amendment branch "was not pushed"; it had been pushed and PR #11 opened
  by the time CORE-HANDOFF was written (its §0.1 records the disagreement and the `git ls-remote`
  that settled it). Two root-check triples (20.87/21.23/21.16 and 20.69/21.11/20.93 s) are
  different runs; nanoda's peak is 52.0, 51.3 or 53.5 GB by run and sampler. Every record should
  name its run and the handoff should re-check `git` and `gh` before trusting a status line.
- **GitHub writes and pushes were not permitted to agents**, by rule (`CLAUDE.md`: no pushing, no
  PRs, no issue edits without the user). Consequences: the amendment sat unpushed until the user
  pushed it; issue #1 stayed stale; D-11 (the nanoda budget) was never filed; the pin never moved.
  A workflow that depends on a human for every remote write needs that human in the loop at the
  stage boundaries, or the records drift.
- **"No estimates" and "every claim is a theorem or a measurement with a log"** were the two
  rules that kept the RESULTs honest; the paper sizings (the node circuit, the decoder step
  counts, the WHIR/FRI/Basefold proof sizes, the `2^48` budget, the 65 ms best-linear-verifier
  figure) are the places where a next design still has nothing but estimates.
- **The ledger with ids** (V3-S1-A*, V3-KS-A*, V3-S2R-A*; each code comment and design passage
  naming its entry) is what made this record writable after the ledger file was deleted.
- **A parallel exploration can go unrecorded.** The relativized-NARK exploration (§1) ran on a
  remote branch of the core while the O-25 design track ran in the submissions repository; the
  first version of this record missed it entirely, and an independent review found it
  (`V3-ideation-docs-review.md`, DOC-M1). Any record of a multi-agent iteration should start from
  `git branch -r` on every remote, not from the documents one track wrote.

From the orchestrator's session notes (no log; recorded here so they are not lost):

- **Agents hit output-token limits on long documents.** An earlier attempt at this design record
  failed by putting a whole memo into one response; the fix was to create each file with its
  headings first and fill one section per write. The same limit shows in the stage records: the
  longest documents (`F2-o25-uninstantiability.md`, 1,617 lines; `CORE-HANDOFF.md`, 1,287;
  `BLUEPRINT-R1.md`, 1,459) were written in rounds, and reviewers were told to read specific
  sections.
- **Self-matching wait loops.** An agent waiting for a build with `pgrep -f <pattern>` matched
  its own shell (the pattern appears in its own command line) and waited forever; the rule became
  to wait on the PID of the process one started, under `timeout`, and to inspect a job that runs
  longer than expected rather than poll it (the user's `CLAUDE.md`, "Long-running builds").
- **The user's hard rules were written as prohibitions with reasons**, and the ones that held
  were the ones agents could check mechanically (the source rule, the axiom audit, the line
  budget, `loc.py`); "a proof never changes the statement it proves" held because reviewers
  diffed declaration signatures (`V3-S1-golf`'s hash dump, `V3-S2b-golf`'s `pp.all`).

### 8.4 What to do differently next time, in one list

1. Build the first honest entry **before** fixing the rules, and treat its reviews as the rules'
   reviews; three of the decisive findings came only from a real entry under the real harness.
2. Put every rule that bites a submitter in a mechanical check with a fixture, including the
   second kernel's budget and the compiled start-up time of the badge executables.
3. Keep the trusted definitions' positive controls one step ahead of the entries: `twoLucky` and
   `Vcol` should have existed before any Merkle verifier was attempted (design §16, C3).
4. Measure compiled speed of every organiser object on the verifier path (field, codec, hash)
   before setting any cap, on the machine the cap is for.
5. Keep the ledger, the ids and the "measurement with a log or kernel theorem" rule; they are
   the reason this record could be written.

## 9. Index of the logs and probes cited

**Logs** are gitignored and local to the development VM `leanervm-dev`, in three places:
`/home/devops/Verified-zkEVM/recursion.fast/logs/` (the main core checkout, where the S1 logs
were written), `/home/devops/Verified-zkEVM/recursion.fast-rules/logs/` (the S2R worktree) and
`/home/devops/Verified-zkEVM/recursion.fast-submissions/logs/` (the KS amendment, the entries, the
reviews). Paths below are relative to those roots.

| Directory | Root | What |
|---|---|---|
| `logs/V3-S1/` | main core checkout | S1 build, loc, axiom audit, hygiene, vendor, `digest-probe/`, `fix-*` |
| `logs/V3-S1-golf/` | main core checkout | signature dumps, timings, diffs of the S1 golf |
| `logs/ks-amendment/`, `logs/ks-amendment/fix/` | submissions | the KS amendment's builds, loc, CI |
| `logs/ks-review-probes/` | submissions | `PaperTheorem.lean` (adopted into the library), `Truncated.lean`, `Redundant.lean`, `Snag.lean` and their logs (local only) |
| `logs/adv-probes/` | submissions | `CountingForm.lean`, `LiteralTrigger.lean`, `TaskRfl.lean` (now also in `evidence/probes/`), `RefChain.lean`, `FastChain.lean` (their logs `refchain.log`, `fastchain.log` are archived; the `.lean` files are local only) |
| `logs/issue-probes/` | submissions | `FintypeDigest.log` |
| `logs/probes/` | submissions | `fieldbench.log`, `flock-2e14.log`, `e2/bfbench.log`, `e2/build.log`, `e2ws/` |
| `logs/V3-S2/` | submissions | S2a: `calibration-r8-n16384.log`, `dos-unfiltered/run.log`, `review/caterpillar.log`, `fix/` (the end-to-end run), `recheck-20261020.log`, `golf-check.log` |
| `logs/blueprint-review/` | submissions | `check.py`, `check.out` (the blueprint's sizes recomputed) |
| `logs/field/` | submissions | `bench-20261019-185727.log`, `nanoda.log` (the field agent's logs, not under `spartan-chain/`) |
| `logs/spartan-chain/` | submissions | per-topic: `rust/` (`leaf-n*.log`, `bench-field.log`, `cargo-test.log`, `build.log`, `kat/`), `leaf-snark/`, `rs-proximity/`, `oracle-merkle-transcript/` (`init-blowup.log`), `soundness-ks/`, `infra/` (`harness-final/` … `harness-final4/`, `harness-final2/nanoda/bisect/`, `gate-fixtures/`), `measure/20261019-204628/`, `measure/20261020-025203/`, `golf/{before,after}/`, `fix-m2/` |
| `logs/s2b-review-probes/`, `logs/s2b-final-review-probes/` | submissions | the midreview's `FactsQueries.lean`, `facts_false`; the final review's `Axioms.lean`, `EpsNegative.lean`, `module-times.log`, `gate.log`, `caterpillar/`, `nanoda-rss.log` (local only) |
| `rf-core-sc/scratch/o25/`, `scratch/o25t/` | the shared clone `/home/devops/Verified-zkEVM/rf-core-sc` | `P1_interface.lean`, `P2_hatches.lean`, `T1_pub_sees.lean` and logs (now also in `evidence/probes/`) |
| `logs/s2r/` | rules worktree | `build-*.log`, `ci*.log`, `loc-contract.log`, `nanoda/`, `gate/`, `probes/Shallow.lean` (now also in `evidence/probes/`), `fix/` (`ci-final.log`, `build-cold.*`, `axiomaudit.log`, `nanoda/`, `loc-contract.log`), `golf/` |
| `logs/review/` | rules worktree | the S2R review's `ci.log`, `probes/Review.lean`, `probes/Review.log` (now also in `evidence/probes/`) |
| `logs/ci/` | rules worktree | the CI steps' logs |

**Archived probes.** The decisive kernel probes and the interim harness that produced both
`HARNESS: ACCEPT` verdicts are now on `v3/contract-archive` (head `f4de3b8`, commits `c198bc3`
and `f4de3b8`) under `evidence/`: `evidence/README.md` (the index, with the contract each probe
was checked against); `evidence/probes/LiteralTrigger.lean`, `CountingForm.lean`, `TaskRfl.lean`,
`Shallow.lean`, `Review.lean`, `P1_interface.lean`, `P2_hatches.lean`, `T1_pub_sees.lean` with
their logs, and `fastchain.log`, `refchain.log`, `build.log`; `evidence/interim-harness/`, the
branches `v3/s2-interim-harness` (`2a4588b`) and `v3/ks-interim-harness` (`2464e97` … `4a1a1ed`)
as `git format-patch` series. None of it is built by `lake build`, and probes written against
`15e4ae5` or `05fde28` do not compile unchanged at `6202402`. Still local only: the KS review
probes, the S2b review probes, `RefChain.lean` and `FastChain.lean` themselves, and every log.

Kernel facts cited by name otherwise live in the committed sources: the core's
`RecursionFast/Controls/` and `RecursionFast/Library/` at `v3/contract-archive` (contract state
`6202402`), the exploration's `RecursionFast/Explore/` at `explore/relativized-nark` `043bcb3`,
and the entries' `submissions/baseline/BaselineV3Controls.lean` and
`submissions/spartan-chain/SpartanChain*.lean` in the submissions repository.
