# V3-S1 RESULT: the v3 contract and its controls (DESIGN-v3 §11 step 1)

One implementing agent, 2026-10-19, on branch `v3/s1-contract`. Nothing is committed (the moves
are staged by `git mv`). Amendments: V3-S1-A1 … A18 in `docs/DESIGN-AMENDMENTS.md`. Logs:
`logs/V3-S1/`.

## Headline

- **The v3 trusted contract builds at 320 code lines** (`scripts/loc.py`, budget ≤ 500, design
  estimate ≈ 400), with no field anywhere in `Contract/` and Mathlib imports limited to
  `Basic.NNReal.Defs`, `SetTheory.Cardinal.Finite` and `Logic.Function.Iterate`.
- **Every clause of `Certificate` is inhabited.** The witness-sending argument
  (`Library/WitnessSending.lean`) has a full, kernel-checked `Certificate`, `computes` included:
  its extractor image is 8 RISC-V instructions that output the proof's words in place, proved
  for every input. Nothing is left out of the certificate. It is a library module and the
  certificate's positive control, not an entry (V3-12, committed during this stage: the baseline
  entry lives in the submissions repository and can import or copy it).
- **Every trusted definition has a positive and a negative control**, kernel-checked in CI
  (`Controls/`, 8 files and the root, 86 theorems).
- **Builds.** `lake build` (default targets): **2 min 03 s cold**, 4.2 GB peak; **3.1 s warm**.
  `lake build gate axiomaudit`: green (13 s). Axiom audit over Contract, Library, Controls: PASS
  (591 declarations; only `propext`, `Classical.choice`, `Quot.sound`). Hygiene and vendor checks
  pass.
- **Three findings need a decision** (details under "Open questions"): the accept-everything
  vacuity control of §4.2 cannot be proved as stated (V3-S1-A13), completeness quantifies over
  every chain length (V3-S1-A14), and chain steps are not domain-separated from oracle queries
  (V3-S1-A6).

## Files

Code lines from `scripts/loc.py` (`logs/V3-S1/loc-*.log`).

### Contract (TRUSTED), 320 code lines

| File | Code | Status | Contents |
|---|---:|---|---|
| `Contract.lean` | 8 | rewritten | reading-order imports (V3-S1-A1) |
| `Contract/Hash/Blake2s.lean` | 68 | unchanged | `blake2s`, `blake2s256` |
| `Contract/Relation.lean` | 22 | **new** | `Digest` (`Vector UInt8 32`), `Proof`, `proofCap = 2^20`, `blake2sDigest`, `tagLeaf/tagNode/tagRO`, `enc64`, `chainEnd`, `leafStmt`, `nodeStmt`, `Wit`, `Rel` (§2.1 exactly, up to the digest representation) |
| `Contract/Oracle.lean` | 19 | **new** | `OProg` (`ret`, `query`), `Log`, `run`, `runLog` (first match, `none` on a miss), `queries` |
| `Contract/Security.lean` | 23 | **rewritten** | `errorCap = 2⁻¹^128`, `KState` (`good`, `bad`, `empty`, `step`, `final`), `KState.Bounded`, `KS`, `Complete` (perfect, every oracle). No `CompleteWithError` (V3-S1-A9) |
| `Contract/Machine.lean` | 110 | semantics unchanged | `clmul` moved in from the deleted `Field.lean`; `Word` is the vendored notation (V3-S1-A2) |
| `Contract/Extractor.lean` | 33 | **rewritten** | `toWord`, `ofLE`, `packBytes`, `bytesWords`, `extractorInput` (input tape), `wordByte`, `digestAt`, `bytesAt`, `decodeWit` (output decoder), `extractorBudget = 2^40 + 2^8(p + l)`, `outCap = 2^24`, `imageCap = 2^20`, `ImageComputes` |
| `Contract/Tree.lean` | 7 | **new** | `treeLevel`, `treeRoot` (V3-S1-A8) |
| `Contract/Certificate.lean` | 30 | **rewritten** | `Submission {V, P, E, img, ε, qV, fuel}`, `blake2sOracle`, `Submission.Vb`, `Certificate {secure, complete, computes, cap}`, `Declared`, `CertificateR` (V3-S1-A10) |
| **deleted** | | `git rm` | `Field.lean`, `Shapes.lean`, `Layout.lean`, `Protocol.lean`, `Compile.lean`, `Recursion.lean` |

The normative byte layouts (statement preimages, tags, extractor tape, extractor output) are in
the headers of `Relation.lean` and `Extractor.lean`.

### Library (untrusted, kernel-checked), 563 code lines, 70 theorems

| File | Code | Thm | Contents |
|---|---:|---:|---|
| `Library/Blake2s.lean` | 13 | 3 | unchanged (v2) |
| `Library/Oracle.lean` | 24 | 3 | **new**: `runLog_eq_run` (a log consistent with `H` containing the run's queries answers the run: the step from `final` to the real run), `runLog_queries` |
| `Library/Security.lean` | 38 | 6 | **new**: `card_digest : Nat.card Digest = 2^256`, `KState.bounded_of_not_bad`, `KState.Bounded.mono`, `KState.one_le_of_bounded`, `errorCap_lt_one`, `no_kstate_of_empty` |
| `Library/Machine.lean` | 79 | 17 | **new**: v2's machine symbolic-execution lemmas, copied verbatim from v2 `Library/Extractor.lean` |
| `Library/Words.lean` | 202 | 20 | **new**: `ofLE` digits, `wordByte_packBytes`, `packBytes_wordsBytes` (unpack then pack is the identity), the output encoder `witWords`, `Wit.Fits`, `decodeWit_witWords` (round trip), `getD` helpers |
| `Library/WitnessSending.lean` | 201 | 21 | **new**: the witness-sending argument `submission` and its `certificate` (V3-S1-A15) |

### Controls (CI), 387 code lines, 86 theorems

`Controls/Blake2s.lean` (v2, unchanged), and new: `Relation`, `Oracle`, `Security`, `Machine`,
`Extractor`, `Tree`, `Certificate` (table below).

### Other files

- `tests/asm/proofwords.S`, `halt.S`, `toolong.S` (+ `.bin`): the three new images, assembled
  with `riscv64-unknown-elf-as -march=rv64im_zbc`; the Lean literals are the assembler's words.
- `legacy/v2/`: the moved v2 modules and `README.md` (below).
- `CLAUDE.md`: a v3 line under "What this is", the Contract row of the trust-layer table, the
  Layout block. Everything else kept, so its build-time line ("5 min cold") and the Library row
  now describe v2.

## Build and checks (`logs/V3-S1/`)

| What | Result | Log |
|---|---|---|
| `lake build` cold (`rm -rf .lake/build` of this package only; packages untouched) | 2:02.5 wall, 4.17 GB peak, 1249 jobs | `build-cold.{log,time}` |
| slowest modules (kernel evaluation) | `Controls.Blake2s` 48 s (v2 KATs), `Controls.Relation` 46 s, `Controls.Tree` 15 s; everything else ≤ 5 s | `build-cold.log` |
| `lake build` warm | 3.1 s | `build-warm.time` |
| `lake build gate axiomaudit` | green, 13.3 s | `build-exes.{log,time}` |
| axiom audit (`AxiomAuditV3.lean`: `scripts/AxiomAudit.lean` with the module list Contract, Library, Controls) | **PASS**, 591 declarations in 22 modules, 67 theorems with no axiom | `axiomaudit.log` |
| `lake exe axiomaudit` (unchanged tool) | fails: it imports `RecursionFast.Bridge`, deferred (V3-S1-A16) | `axiomaudit-exe.log` |
| `#print axioms` on `WitnessSending.certificate`, `ws_certificateR`, `chain16_kat`, `acceptAll_kstate_iff` | `[propext, Classical.choice, Quot.sound]` | `print-axioms.log` |
| `scripts/check-hygiene.sh` | OK | `hygiene.log` |
| `scripts/check-vendor.sh` | byte-identical to `6810fc1` | `vendor.log` |
| deferred targets | each fails on an import of a deleted or moved module (expected) | `deferred-targets.log` |

No `sorry`, `native_decide`, `implemented_by`, `extern` or `csimp` anywhere in Contract, Library
or Controls.

## Controls and what each shows

| File | Positive | Negative |
|---|---|---|
| `Relation` | `chain1_kat`, `chain2_kat`, `chain16_kat`: `chainEnd (00…1f) n` against `hashlib` (the command is in each docstring); `leafStmt_kat`, `nodeStmt_kat`: the 41- and 65-byte preimage layouts; `node_of_two_leaves`: for every two starts and lengths `< 2^64`, the node of two leaf digests is in `Rel` of the witness-sending verifier (which recomputes the chains), with the two leaf proofs as witness | `wrong_end` (a leaf statement of the start, not the end: `¬ Rel Vb`, every `Vb`); `tags_separate` (leaf bytes under `tagNode` ≠ `leafStmt`), `tags_distinct`; `second_child_rejected` (first child correct, second a well-formed leaf proof of the wrong statement); `Vb_over_cap` (every submission's `Vb` rejects `> proofCap`) and `deep_accepted_but_capped` (the witness-sending `V` accepts a 13-level proof of 1,114,024 bytes, `Vb` rejects it: the cap is what rejects) |
| `Oracle` | `prog_queries` (two queries, the second built from the first answer), `prog_run`, `prog_runLog` and `prog_runLog'` (the run's own log answers it), `prog_runLog_first` (first match) | `prog_runLog_miss` (`none` on a miss), `runLog_reads_log` (other answers in the log give another result than the oracle) |
| `Security` | `ws_ks` with `ws_kstate_trivial` (`good := True`, `bad := False`, `ε = 0`, `qV = 0`), `ws_complete` (every oracle); `rejectAll_ks` (reject-all is KS, for every relation and extractor) | `rejectAll_not_complete`; `acceptAll_kstate_iff` (accept-all has a `KState`, for some extractor, iff every statement has a witness), `acceptAll_no_kstate_empty` (empty relation, every extractor), `acceptAll_no_kstate_none` (`Rel Vb`, the non-extracting extractor); `bounded_ge_one`, `badAll_not_capped` (every answer bad: bounded only at `ε ≥ 1 > errorCap`; such a state exists); `oneQuery_not_qV0` (the query bound is not vacuous). What is **not** shown is in V3-S1-A13 and below |
| `Machine` | v2's: `wzbc_run` (W-op, `clmulh`: `clmul` moved unchanged), `tape_below_ok`, `halt_reads` | v2's: `tape_readonly`, `halt_misaligned`, `ecall_trap`, `spin_run_100`, `spin_run` |
| `Extractor` | `ws_computes` (the 8-instruction image computes the witness-sending extractor on every input), `ws_run_8` (8 steps on a concrete tape), `halt_computes` (`HALT` computes the extractor returning nothing) | `halt_not_ws` (wrong output), `ws_fuel_7` (fuel exhaustion, `decide +kernel`), `noCode_computes_nothing` (no code, any fuel), `toolong_not_computes` (an output of `2^24 + 1` words: the output cap) |
| `Tree` | `treeRoot_one/two/four/eight` for all digests (`rfl`, no hash evaluated), `treeRoot_three`, `treeRoot_nil` (the conventions), `treeRoot_kat` (four leaves against `hashlib`: the runner's KAT, S3) | `treeRoot_order` (`[d₀, d₁]` ≠ `[d₁, d₀]`) |
| `Certificate` | `ws_certificate` (every clause), `ws_certificateR` (against a rendered claim: image literal, `ε = 0`, `qV = 0`, fuel 8) | `flipped_image` (one image bit), `fuel_7_claim` (declared fuel below the submission's), `rejectAll_no_certificate`, `acceptAll_no_certificate` (with the non-extracting extractor), `error_one_no_certificate` (the error cap) |
| `Blake2s` | v2's 12 KATs and constants, unchanged | v2's 3 negatives |

Kernel evaluation of BLAKE2s costs about 2.4 s per compression (one 32-byte message: 2.43 s,
`logs/V3-S1/digest-probe/kernel-vector-ofFn.lean`). The Relation KATs evaluate 16 + 2 + 1 chain
steps and two statements (3 compressions), its negatives 5 more compressions; the tree KAT and
negative evaluate 10 compressions. The other kernel evaluations are short machine runs (at most
100 steps) and small lists.

## Deviations from DESIGN-v3 (each an amendment)

1. **`Digest := Vector UInt8 32`**, not `Fin 32 → UInt8` (A4): compiled code re-evaluates a
   function-typed digest per byte read, so chains cost `32^n` (measured, `logs/V3-S1/digest-probe/`).
2. **`blake2sDigest`** wraps the unchanged `blake2s256` (A3).
3. **Reading order** Relation before Oracle (A1).
4. **`Machine.lean`** gains `clmul` from the deleted `Field.lean` (A2).
5. **Extractor output denotes, not equals** (A7): `ImageComputes` asks that the output decode
   (`decodeWit`) to `E`'s result. This is what makes §7.3's "img copies its input" possible.
6. **`ImageComputes` domain**: the tape fits the machine's `2^60` words; output cap as a
   conjunct; image cap in `Certificate.cap` (A11).
7. **`Declared`/`CertificateR`**: `{img, ε, qV, fuel}`, image by equality, numbers as bounds
   (A10).
8. **`CompleteWithError` not in the contract** (A9, O-23).
9. Choices the design left open: tags and `enc64` (A5), tree convention (A8), budget units and
   justification (A12), the library home of the witness-sending argument (A15).

## Legacy moves and deferred targets

- Moved unchanged to `legacy/v2/RecursionFast/Library/`: `Challenges`, `Codec`, `Compile`,
  `Extractor`, `Field`, `Layout`, `R1CS`, `RbrSound`, `Recursion`; to
  `legacy/v2/RecursionFast/Controls/`: `Certificate`, `Chain`, `ChainData`, `Compile`,
  `CompileFS`, `CompileToy`, `Extractor`, `FieldSpec`, `Hit`, `Layout`, `MagicKey`, `Negative`,
  `Recursion`, `RecursionData`, `RecursionNode`, `Toy`; copies of the v2 `Library.lean` and
  `Controls.lean` roots. Not a lake target; `legacy/v2/README.md` says so and that S4 re-targets
  it.
- Kept: `Library/Blake2s.lean`, `Controls/Blake2s.lean`. Re-homed (copied, then the copies
  extended): the machine lemmas (`Library/Machine.lean`) and the machine controls
  (`Controls/Machine.lean`).
- **Left in place, deferred** (sources and lakefile entries untouched): `RecursionFastCandidate`
  (S2: the baseline moves to the submissions repository, DESIGN-v3 §7.7, V3-12),
  `RecursionFastHarness`, `RecursionFastSmoke`, `harness-linkcheck` (S3,
  harness), `RecursionFastBridge`, `RecursionFastClean` (S4, library). `RecursionFast/Bridge/` and
  `RecursionFast/Clean/` stay where they are because the brief says to leave the deferred
  targets' sources in place; they import modules now in `legacy/v2/`. Moving them to legacy is one
  `git mv` if preferred.
- Not touched: `submissions/`, `harness/`, `scripts/`, `RecursionFast/Vendor/`,
  `RecursionFast/Challenge/*.lean.in` (still v2 stubs: S3).

## Open questions for the orchestrator

1. **Accept-everything (V3-S1-A13).** The design's vacuity control "a verifier that accepts
   everything admits no `KState`" is not provable for `Rel`: it needs a digest outside the images
   of `leafStmt`/`nodeStmt`, and if `nodeStmt` is onto there is none, so the accept-all verifier
   has a knowledge state with a choice extractor (`acceptAll_kstate_iff` proves exactly this).
   Security against it rests on `computes` (an image within `B p l` steps would invert BLAKE2s).
   Proposed: reword §4.2's reading and vacuity paragraph; no definition change.
2. **Completeness over every chain length (V3-S1-A14).** `Complete` covers leaves of every
   `n ∈ ℕ`; a SNARK entry needs a fallback for `n` outside its circuit, which spreads to nodes.
   Recommended: bound `n` in `Rel`'s leaf clause (e.g. `n ≤ 2^20`), a one-line change to the
   trusted relation, which also removes the `n mod 2^64` normalisation.
3. **Chain steps vs oracle queries (V3-S1-A6).** A 31-byte query's instantiated input equals the
   chain step of a digest starting with `0x52`. Recommended: tag the chain (`tagChain ‖ d`, still
   one compression), which changes `chainEnd`, its KATs and the runner.
4. **Budget units (V3-S1-A12, O-21).** `l` = log entries, as briefed; an extractor matching query
   contents can exceed `B` on adversarial logs. Keep, or make `l` the log's size in words?
5. **`CompleteWithError` (O-23)**: no form proposed here.
6. **Bridge/Clean placement**: in place or `legacy/v2/` (see above).
7. **Harness notes for S3 (V3-S1-A16)**: the liveness log must include `V`'s queries; the Python
   output decoder is `decodeWit`; `scripts/AxiomAudit.lean`'s module list includes the deferred
   Bridge; the gate allowlist, manifest and challenge stubs are v2's.

## Fix pass (2026-10-19)

Built on the golfed tree (`docs/reviews/V3-S1-golf.md`; the golfed proofs are kept, including
`decodeWit_witWords`, adapted where a statement changed) against `docs/DESIGN-v3.md` at `54140d1`.
Amendments V3-S1-A19 … A26. Nothing is committed. Logs: `logs/V3-S1/fix-*`.

### Numbers

| What | Result |
|---|---|
| Contract (`scripts/loc.py`, budget ≤ 500) | **328** code lines: Contract.lean 8, Blake2s 68, Relation 25, Oracle 19, Security 23, Machine 113, Extractor 34, Tree 8, Certificate 30 (`fix-loc-contract.log`) |
| Library | 511 code lines, 81 theorems (new `Tree.lean`; normalisation deleted) |
| Controls | 544 code lines, 111 theorems (new `Backdoor.lean`) |
| `lake build` cold (`rm -rf .lake/build`, this package only) | **2:09.7**, 4.2 GB peak; slowest `Controls.Relation` 50 s, `Controls.Blake2s` 48 s, `Controls.Tree` 17 s (`fix-build-cold.*`) |
| `lake build` warm | **3.2 s** (`fix-build-warm.time`) |
| every remaining lake target | `RiscvZkvm`, `RecursionFastContract`, `RecursionFastLibrary`, `RecursionFastControls`, `gate`, `axiomaudit`: all built (`fix-targets.log`) |
| `lake exe axiomaudit` (as shipped) | **PASS**: 24 modules, 661 declarations, 74 theorems with no axiom; everything within `propext`, `Classical.choice`, `Quot.sound` (`axiomaudit-exe-fix.log`) |
| hygiene, vendor | OK, byte-identical |
| `step` mutation (`good L` as conclusion) | `Controls.Security` fails to build (`mut-step-fixpass.log`) |

### The four decisions

| Decision | Done |
|---|---|
| (c) chain tag, A19 | `tagChain = 0x43`, `chainStep`, `chainEnd = chainStep^[n]`. Chain, leaf and node KATs recomputed (`python3 -I` commands in each docstring, full hex). `tags_separate` restated structurally (m7). `node_of_two_leaves` and `WitnessSending` follow. |
| (b) `chainCap`, A20 | `chainCap = 2^20`, leaf clause `n ≤ chainCap ∧ …`, bound first. Controls `leaf_at_chainCap` (in) and `leaf_over_chainCap` (out). No lower bound. Dead library lemmas deleted (`norm`, `rel_norm`, `enc64_mod`, `chainEnd_chainEnd`, `fits_norm`), replaced by `fits_of_rel`; `P` sends the witness. |
| (d) tape budget, A21 | `extractorBudget t`, `fuel : ℕ → ℕ` in `Submission`, `Declared`, `cap`, `CertificateR`; the `2^24`-entry bound dropped (M3). `WitnessSending.computes` and every extractor control re-proved. |
| (a) accept-all, A13/A23 | `acceptAll_kstate_iff` moved to `Library/Security.lean`; `acceptAll_no_certificate` kept; `Security.lean` and `Certificate.lean` headers reworded as §4.2 reads. |

### Review majors

- **M1 (fixed as a documented gap).** `Controls/Backdoor.lean`: the review's `Probe.Backdoor2`
  adapted (the leaf check gains `n ≤ chainCap`; completeness without normalisation). `backdoor :
  Certificate S ∧ ∀ c, S.Vb c (magic c) = true ∧ (magic c).size = 32` is kernel-checked. The
  header says it is a known gap, cites O-25, and says the kernel accepting it is the point. The
  `Security.lean` and `Certificate.lean` headers no longer suggest the contract excludes it.
- **M2 (fixed).** `queryThenAccept_ge_one` and `ks1` in `Controls/Security.lean`. Checked: with
  `step` mutated to conclude `good L`, the control fails to build.
- **M3 (fixed by A21).**
- **M4 (fixed).** Bridge and Clean moved to `legacy/v2/`; nine lakefile blocks commented out
  with the stage that restores each; `lake-manifest.json` unchanged; `scripts/AxiomAudit.lean`
  without the Bridge; `CLAUDE.md`'s "DESIGN.md is authoritative" line, Layout, Bridge and Library
  rows and build-time line corrected; `legacy/v2/README.md` updated. Not touched, as instructed:
  `ci.sh`, `org-build.sh`, the manifest, the gate.
  - **CI today (by inspection; step 1 run):** step 1 passes (vendor, hygiene, the source-rule
    fixtures: 95 forms, 4 forgeries). Step 2 fails (`org-build.sh` builds the harness driver and
    `harness-linkcheck`, which import v2). Step 3 fails (the manifest predates the trusted
    change). Step 4's audit and line count would pass if reached (its `loc.py` call still omits
    `Hash/Blake2s.lean`). Step 5's runner self-test reads the moved
    `Controls/RecursionData.lean`. Steps 6–10 exercise the v2 stubs, renderer, toy, gate probes
    and badge path; step 11 the Clean frontend; step 12 the manifest. **S3 owes** the manifest
    regeneration, `org-build.sh`, `ci.sh`, the gate's allowlist, the renderer and the stubs.

### Review minors

| Id | Fixed / argued |
|---|---|
| m1 | Fixed: `first_child_rejected`, `node_statement_mismatch` (two accepted children under a leaf statement, kernel-evaluated) and the general `node_needs_statement`. |
| m2 | Fixed: `oneQuery_not_KS : ¬ KS R queryThenAccept E ε 0` for every `R`, `E`, `ε`. |
| m3 | Fixed: `blake2sOracle_kat` (`Controls/Certificate.lean`); recomputed, equal to the reviewer's `5d32eaa7…cf84`. |
| m4 | Fixed: `extractorInput_kat` (a 3-byte proof, a log of one 9-byte query) and `decodeWit_kat` (a node with 3- and 2-byte proofs), expected words from a Python reference. |
| m5 | Fixed (A22): `decodeWit` returns `none` for a child above `proofCap`; control `decodeWit_long_child`. |
| m6 | Fixed: `fuel_over_budget_no_certificate` (fuel `2^41`), `big_image_no_certificate` (`2^18 + 1` instructions, proved symbolically: a concrete size check made the kernel build the list, 35 s). |
| m7 | Fixed (A19): `tags_separate` is structural; the `Relation.lean` header and §3.4-style wording say the relation hashes oracle inputs only inside `Vb`. |
| m8 | Fixed: `Hash/Blake2s.lean` and `Machine.lean` headers, the KAT commands (full hex), the lakefile header. |
| m9 | Fixed (A21): `CertificateR` bounds `D.fuel` by the budget; name kept ("the certificate against the rendered claim"), its v2 meaning noted for S3. |
| m10 | Skipped: design text (§6.6, §6.7 after O-23). |
| m11 | Argued, not done: restricting `final` to `π.size ≤ proofCap` weakens the law, so it is a statement change, not a term-identical restatement; the instruction was to skip in that case. |
| m12 | Fixed: no line over 100 characters in Contract, Library or Controls. |

Optional review suggestion not taken: a certificate-level accept-all negative for every
statement-ignoring extractor (the existing one fixes `E := none`).

### The submissions agent's findings

- A leaf proof declaring a huge `n` could run a chain-recomputing verifier past its time cap:
  closed by `chainCap`, checked before any hash (`Relation.lean` header, A20).
- Completeness needs no unbounded encodings once `n ≤ chainCap`: the witness-sending prover sends
  the witness unchanged; `enc64` is kept (A20).
- `decodeWit`'s handling of malformed proofs is what makes the copy image work: now said in the
  `Extractor.lean` header (A22).

### The golfer's notes

- `ws_run_8` "exactly 8": now proved, with `ws_run_7 : run img tape0 7 = none`.
- `wrong_end` and the other instance controls now say "an instance" in their docstrings.
- `treeRoot`'s "`|cs|` levels always suffice": proved in `Library/Tree.lean`
  (`length_iterate_length_le_one`, `iterate_treeLevel_of_length_le_one`), with
  `treeRoot_cons_cons` (the root of two or more digests is the root of the level above), and
  cited in the docstring.
- `OProg.queries`: the oracle is now the first argument, as in `run` and `runLog` (A24).

### Design text not yet aligned (for the orchestrator; `DESIGN-v3.md` not edited)

§3.1's `queries` signature (A24); §3.2's code block (`fuel : ℕ → ℕ → ℕ`, `∀ p l, …`), §8's
table (`B p l`) and O-21 (A21); §2.3's control list (the leaf with the node tag is now the
structural `tags_separate`); §6.7's row "Exploiting Blake2s where the relation hashes" lists
three tags, not four.
