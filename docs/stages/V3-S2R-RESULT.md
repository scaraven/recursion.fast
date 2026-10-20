# V3-S2R RESULT: the rules handoff (extractor program, completeness with error, gate rule 4, library)

Stage V3-S2R ("rules"), 2026-10-20. Worktree `/home/devops/Verified-zkEVM/recursion.fast-rules`,
branch `v3/rules-handoff`, on `05fde28` (the head of PR #11, `v3/ks-potential`). **Uncommitted;
the orchestrator commits.**

Input: the submissions repository's `docs/snark-baseline/CORE-HANDOFF.md` (cited "handoff §n"),
issues #4–#10, PR #11, and the user's decisions of 2026-10-20: (a) the extractor is a computable Lean
function with a proved step bound; (b) completeness with error `δ` over a uniformly random oracle,
cap `2^-128` recommended; (c) O-25 must be closed, on a separate track, **not implemented here**.

Phase 1 was an adversarial review of the handoff before any code was written:
`docs/reviews/V3-S2R-handoff-review.md` has 4 major and 17 minor findings, each with the change
made instead. The ledger entries are `docs/DESIGN-AMENDMENTS.md` V3-KS-A8 and V3-S2R-A1 … A7. Every
measurement below has its log under `logs/s2r/` (gitignored).

## 1. What was built

### 1.1 The contract (trusted): 331 → 288 code lines (`logs/s2r/loc-contract.log`)

| File | Code lines | Change |
|---|---:|---|
| `Contract/Machine.lean` | 59 (was 113) | **Rewritten** (V3-S2R-A1). The RISC-V machine is replaced by a step-counting word language: `Word := BitVec 64`, `clmul` (unchanged), `XOp` (15 operations) with `XOp.eval`, `XStmt` (three-address `op const load store input out` and the control statements `seq ite loop`; no function-typed field), `XStmt.size`, `XProg` (`mem` words, `body`), `XStmt.exec` (a small-step interpreter over a statement stack, structural on fuel, one unit per statement) and `XProg.run` (charges `mem` first). It imports nothing. |
| `Contract/Extractor.lean` | 34 (was 34) | `Computes p E fuel` replaces `ImageComputes`, with the domain `π.size ≤ proofCap` and tapes of at most `2^64` words. `extractorBudget t = 2^48 + 2^16·t`. `progCap = 2^20` statements replaces `imageCap`. The header is rewritten: the budget's derivation, and `packBytes`/`bytesAt` marked as specifications (#10). Tape, output format and `decodeWit` are unchanged. |
| `Contract/Oracle.lean` | 22 (was 19) | `OProg.bind` (V3-S2R-A2). |
| `Contract/Security.lean` | 33 (was 26) | `failProb`, `CompleteWithError`, `completenessCap = 2^-128`; `Complete` removed (moved to the library); the header's completeness paragraph is rewritten. `KState`/`KS` are unchanged. |
| `Contract/Certificate.lean` | 31 (was 30) | `Submission.ext : XProg` (was `img : Image`) and `Submission.δ`. `Certificate.complete` is `CompleteWithError … S.δ`, and `computes` is `Computes S.ext S.E S.fuel`. `cap` adds `δ ≤ completenessCap` and `ext.body.size ≤ progCap` (was image bytes). `Declared` is `ε δ qV fuel`. `CertificateR` drops the image binding and gains `δ`. |
| `Contract.lean` | 8 | The reading-order header. |
| `Relation`, `Tree`, `Hash/Blake2s` | 25, 8, 68 | unchanged |
| vendored Rv64 (`RecursionFast/Vendor/RiscvZkvm`) | — | **removed**, with its lake target and `scripts/check-vendor.sh` (in git at `05fde28`). The contract imports Lean core and Mathlib only. |

### 1.2 The library (untrusted, kernel-checked)

| File | Code lines | What |
|---|---:|---|
| `Library/Machine.lean` | 105 (rewritten) | `XStmt.Runs I s M o n M' o'` (`s` runs in exactly `n` steps, whatever follows), one lemma per statement (`runs_op` … `runs_loop_step`), `exec_mono`, `exec_none_of_le`, one-step equations (`exec_seq`, `exec_out`, `exec_loop_ne`, `exec_loop_eq`), `seqs`, `XProg.run_of_runs`, `XProg.run_lt_mem`. The RISC-V symbolic execution left with the machine. |
| `Library/Completeness.lean` | 63 (new) | `Complete` (moved), `Consistent`, `failProb_eq_zero_of_run`, **`complete_withError_zero`** (`Complete → CompleteWithError 0`), `CompleteWithError.mono`, **`failProb_eq_prob`** (the same as `PaperTheorem.prob`), `failProb_le_one`, `avg_const`, `failProb_bind_false`. |
| `Library/Oracle.lean` | 26 | + `run_bind`. |
| `Library/Words.lean` | 196 | + `toWord_add_one`, `toWord_lt_toWord`, `toWord_eq_zero`, and the linear-time twins `packFast`, `bytesAtF`, `decodeWitF`, `witWordsF` with `_eq` theorems (#10, from S2a). |
| `Library/WitnessSending.lean` | 236 | Strict `check` (leaf canonical too), with `decodeF`/`encodeF` (linear) and `check_eq`, `check_canonical`, `check_leaf`, `Vb_iff`. Completeness at `δ = 0` (`complete_perfect` plus the embedding). The extractor is a 21-statement program `ext` with fuel `8·t`: `pre_exec`, `loop_exec` (8 steps per word), `pre_mem`, `ext_run`, `computes`. `certificate`. |
| `Library.lean` | | + `Completeness`. |

### 1.3 The controls

| File | Code lines | Status |
|---|---:|---|
| `Controls/Machine.lean` | 105 (rewritten) | the language's controls (§3) |
| `Controls/Extractor.lean` | 97 (rewritten) | the program and the budget (§3) |
| `Controls/Completeness.lean` | 120 (new) | `CompleteWithError` (§3) |
| `Controls/WitnessSending.lean` | 49 (new) | the strict verifier's canaries (§3) |
| `Controls/Certificate.lean` | 49 (ported) | `δ`, `ext`, the new caps |
| `Controls/Security.lean` | 99 (ported) | `ws_complete` at `δ = 0`; `rejectAll_not_complete` at every `δ < 1` |
| `Controls/Backdoor.lean` | 116 (ported) | O-25 is unchanged and still certified (`backdoor`) |
| `Controls/Relation.lean` | 105 (ported) | one call site |
| `Controls.lean` | | + `Completeness`, `WitnessSending` |

### 1.4 Harness tools and documents

- `scripts/Gate.lean`: `badgeFields = [(Submission, [V, P, ext])]`, and the rule-4 docstrings
  rewritten (V3-S2R-A3; #9 item 4). `scripts/ci.sh`: the vendor step is removed and the steps are
  renumbered. `scripts/olean-manifest.py`: no `RiscvZkvm` prefix, and Clean is no longer in
  `PINNED_PKGS`. `scripts/tools.env`: restored from `v2-archive` (comparator `d03acab`, lean4export
  `076e8e5`, nanoda `3a24072`), with a provenance line. `lakefile.toml`: the `RiscvZkvm` library is
  removed. `tests/asm/` is removed.
- `docs/DESIGN-AMENDMENTS.md`: V3-KS-A8 (the `05fde28` gap, handoff §2.1 item 2) and V3-S2R-A1 …
  A7. `docs/DESIGN-v3.md` (the core copy; the master is the user's to sync) is patched in §1, §1.1,
  §1.2 V3-4, §2.1, §3.1, §3.2, §4.1–§4.5, §5.3, §5.4, §6.3 steps 8 and 9, §6.5, §6.6, §6.7, §7.3,
  §7.6, §8, §10, §11 and §12 (O-15, O-16, O-21, O-23), each passage naming its ledger id.
  `docs/reviews/V3-S2-KS-review.md` is copied in (handoff §2.1 item 1).
  `docs/stages/V3-S2-KS-RESULT.md` has a note on `05fde28`. `CLAUDE.md` and `README.md` follow the
  change.

## 2. Build and check times (development VM; not the reference machine)

| Run | Time | Peak RSS | Log |
|---|---:|---:|---|
| Cold build of the three targets **before** the stage, `05fde28` | 2:31.85 | 4.16 GB | `logs/s2r/build-baseline.log` |
| Cold build after (contract, library, controls, gate, axiomaudit) | 1:47.86 | 4.16 GB | `logs/s2r/build-cold.log` |
| Warm rebuild | 2.77 s | 0.91 GB | `logs/s2r/build-cold.log` |
| `scripts/ci.sh` (hygiene, source-rule fixtures, build, axiom audit, line budget) | 76.97 s, **CI passed** | 4.18 GB | `logs/s2r/ci3.log`, `logs/ci/` |
| Axiom audit | **PASS**, 969 `RecursionFast.*` declarations, 98 using no axiom | | `logs/ci/axiomaudit.log` |
| Line budget | **288 / 500** | | `logs/s2r/loc-contract.log` |
| **Second kernel (nanoda `3a24072`)** on the export closure of 40 target declarations (the certificates, every `decide +kernel` control of the interpreter, the `Fin 256` decides, the `2^255` count, the canaries; `targets.txt`): 52.5 MB, 7,723 theorems | 5.10 s, exit 0 (accepted) | 223 MB | `logs/s2r/nanoda/` |
| Gate rule 4: the witness-sending submission (computable as a whole) | PASS | | `logs/s2r/gate/gate-ws.log` |
| Gate rule 4: the backdoor submission (noncomputable as a whole, `ε := errorCap`): `V`, `P`, `ext` checked one by one | PASS | | `logs/s2r/gate/gate-backdoor.log` |
| Gate rule 4: a submission with a noncomputable `ext` | **REJECT** `badS.ext` | | `logs/s2r/gate/gate-neg.log` |
| Gate against a manifest generated before the last contract edit | **REJECT** stale `Contract.Machine` (incidental) | | `logs/s2r/gate/gate-ws-stale-manifest.log` |

The manifest used by the gate fixtures is a local one (`logs/s2r/gate/manifest.sha256`, 35,074
entries, generated from this tree). It shows rule 4's behaviour, not S3's reference build.

## 3. Controls and what each shows

**The machine (`Controls/Machine.lean`).** Positive: `eval_kat` gives known answers for all 15
operations, including wrap-around, `x/0 = 0`, `x%0 = x`, shifts by the low 6 bits, `mulhu`, and
`clmulh(-1,-1) = 0x5555…` (v2's Zbc control). `straight_run` and `straight_exact` show a
straight-line program halting at exactly `mem + statements` fuel. `bounds_run` shows that an
out-of-memory read gives 0, an out-of-memory write is lost, and a read past the input gives 0.
`indirect_run` covers `load` and `store`. `count_run` shows that counting down from `k` halts in
exactly `2k + 7` steps, for every `k < 2^64`. Negative: `straight_short` (one step fewer does not
halt). `count_short` shows that **a loop of `k` iterations needs more than `2k + 6` steps, for every
`k < 2^64`**. `mem_charged` shows that `m` memory words do not run in `m` steps. `spin_run` shows that a
never-ending loop halts at no fuel.

**The extractor (`Controls/Extractor.lean`).** Positive: `ws_computes`; `ws_run_exact` (the
witness-sending program halts in exactly 26 steps on the empty proof); `halt_computes`; the two
format known answers, unchanged. Negative: `ws_fuel_short` (25 steps are not enough); `halt_not_ws`
(wrong output); `spin_computes_nothing`; `toolong_not_computes` (`2^24 + 1` output words, the output
cap); **`enum_no_computes`**: a program that enumerates `2^64 − 1` candidates computes no extractor
within the budget, for every specification and every declared fuel `≤ B`. The last is the
handoff's "enumerate `2^64` candidates" control, and it is general over `E` and `fuel`.
`decodeWit_long_child` is unchanged.

**Completeness (`Controls/Completeness.lean`).** `sum_bad` shows that exactly `2^255` answers are bad,
using a bit-flip involution. Positive: **`grind_exact`**: `k ≥ 1` nonces fail with probability
exactly `2^-k` (review H-m1: the fallback is the first, already-tried nonce).
`grind128_complete` shows completeness at the cap for every relation. `fixed_complete_half`.
Negative: `grind127_not_complete` (not at the cap, for any relation with a witness).
**`fixed_not_complete`**: a verifier that tests one fixed answer is not complete at any `δ < 1/2`,
**whatever the prover does**, which is proved over all query programs `P`. The embedding control is
`complete_withError_zero` (library), used by `ws_complete` and `Backdoor.certified`.
`rejectAll_not_complete` (`Controls/Security.lean`) now holds at every `δ < 1`, through
`failProb_bind_false`.

**The certificate (`Controls/Certificate.lean`).** `ws_certificate` and `ws_certificateR` (`δ = 0`,
fuel `8·t`) are positive. Negative: `fuel_low_claim`, `fuel_over_budget_claim` (`2^49`),
`rejectAll_no_certificate` (now through the `δ` cap), `acceptAll_no_certificate`,
`error_one_no_certificate`, **`delta_one_no_certificate`**, `fuel_over_budget_no_certificate`
(`2^49`), and **`big_program_no_certificate`** (`2^20 + 1` statements, symbolic). `flipped_image`
has no counterpart, because the claim renders no image (V3-S2R-A3). The gate fixture covers a
noncomputable program instead.

**The strict verifier (`Controls/WitnessSending.lean`, #10).** The four canaries
(`leaf_appended_rejected`, `leaf_truncated_rejected`, `node_appended_rejected`,
`node_truncated_rejected`), `bad_tag_rejected`, `leaf_over_chainCap`, `stmt_unique`,
`node_children_capped`, `leaf_zero_accepted`, the encoding known answers, and `decodeF_kat` (the
linear decoder, evaluated by the kernel).

**O-25 (`Controls/Backdoor.lean`).** The backdoor is still certified (`backdoor`), with
`δ := 0` and the witness-sending program. The gap is unchanged, as it should be: O-25 is the
separate track.

## 4. The handoff, item by item, and the issues

| Item | Status | What |
|---|---|---|
| §2.1 KS amendment (#5, PR #11) | **built on**; housekeeping done | The ledger has V3-KS-A8 for `05fde28`, the KS RESULT has a note, the review is copied in, and the design text is patched (V3-KS-A1/A2/A6 into §1.1, §4.1, §4.2, §4.5, §8). Not done: the PR #11 body and the #5 comment (GitHub writes), the merge, and the submissions pin move. |
| §2.2 O-25 (#4) | **not in scope** (user decision c) | Compatibility assumptions in §6. |
| §2.3 `T_V` (#6 a) | **text**; rule proposed, value open | §6.5's false numbers are withdrawn, with the measured ones in their place. Proposed rule (V3-S2R-A7): CPU time on one pinned core, calibrated against an organiser checker that interleaves at least 8 chains (H-m10). The value needs the reference machine. |
| §2.4 board T and recursion (#6 b) | **text**; rule open | §5.3 and §6.7 are corrected (A6). The choice between a cap at every level and ranking column R is the user's (A7). |
| §2.5 the extractor (#7; decision a) | **done** | V3-S2R-A1, as amended by H-M1, M2, M3, m2–m5, m11, m13, m15. The design text is §4.4 (with the budget's derivation) and §6.3 step 8. |
| §2.6 completeness with error (O-23; decision b) | **done** | V3-S2R-A2, H-M4, m1, m7–m9. `completenessCap = 2^-128`. |
| §2.7 nanoda budget (D-11) | **partially** | `tools.env` is restored. This stage's own closure was checked by nanoda (5.10 s, 223 MB). The cap (proposed 16 GB / 30 min) and its fixture are S3's (V3-S2R-A4). Filing D-11 on #9 is a GitHub write, not done. |
| §2.8 interim harness (#9 item 4) | **partially** | Gate rule 4 is done, with fixtures. `PINNED_PKGS` no longer lists Clean. There is no stub, renderer, allowlist, CompPoly pinning or reference manifest at this commit, so V3-S2R-A4 lists precisely what S3 must do. |
| §2.9a/b/c (#8 1, 3, 4) | **deferred** (user decisions) | §1's accumulation claim is corrected as A6. The indexer (§2.9b) waits for O-25 to fix `V`'s type. |
| §2.10 library (#10) | **done** | Strict check, linear twins, canaries (V3-S2R-A5). |
| §2.11 minor rules (#9) | items 3, 4, 5, 6, 10 **done**; 1, 2 **text** (S3 implements); 7 done by PR #11; 8, 9 **deferred** | Item 1 (liveness on the native prover's log) and item 2 (a fresh directory per repetition) are in §6.3 and A4. Item 3: §2.1 `Digest`. Item 5: externs in §8 item 6. Item 6: the domain in §4.5. Item 8 (ArkLib policy) is the user's. Item 9 (word-level field) is S4. |
| §2.12 caterpillar | **deferred** (decision) | — |
| §2.13 housekeeping | **done**, except `V31` | `V31` (V3-S2-KS-m1) stays for S4 or the paper argument. |
| §2.14, §2.15 | **deferred** | design direction; S4 |
| §2.16 roadmap #1 | **not done** | GitHub write |

Issues: **#4** untouched (separate track). **#5** fixed by PR #11 (the base). **#6** text and a
proposed rule. **#7** resolved by the contract change. **#8**: (2) resolved; (1), (3), (4) deferred,
with (4)'s claim corrected in §1. **#9**: items 3–6 and 10 done, 1–2 specified for S3, 7 done, 8–9
deferred. **#10** done.

## 5. Deviations from the handoff and the design, with reasons

1. **A deep three-address language, not a "step-counting monad"** (H-M1, H-M2). A monad with Lean
   continuations charges nothing for the continuation's work. This is kernel-checked in
   `logs/s2r/probes/Shallow.lean`: `bruteForce_steps : … = 1 := rfl` for a `2^k` search.
2. **`Word` stays `BitVec 64`**, not `UInt64` (H-m2). The cost model counts statements, so the
   representation only affects compiled liveness speed (open question 7).
3. **The tape domain is `2^64` words** (H-m3). Efficient extraction is therefore claimed for about
   `2^61` log entries, below `logCap`, and §4.5 says so.
4. **Budget `2^48 + 2^16·t`** in statements. The handoff gave `2^48` in RV64 steps; the derivation
   is in §4.4 and H-m4.
5. **Memory is charged** one step per word (H-m5). The handoff did not ask for this.
6. **Gate rule 4 lists `V, P, ext`, not `E`** (H-m6). `E` is a specification and may be
   noncomputable.
7. **`Complete` leaves the contract** for the library (H-m8). The handoff kept it implicitly.
8. **The claim renders no extractor literal** (A3), so `flipped_image` has no counterpart.
9. **The vendored Rv64, `tests/asm` and `check-vendor.sh` are deleted**, not just untrusted
   (H-m15). Git keeps them at `05fde28`, for O-18 if it ever needs them.
10. **The witness-sending extractor's fuel is `8·t`**, not 8 (H-m13). The old image hid
    `outCap`-bounded output work in one `HALT` step.
11. **Liveness is a capped smoke test** (H-M3). A node is run only when its declared fuel at the
    tape length is at most a cap, which is the user's to set.
12. The handoff's §2.6 sketch is implemented as written, with `(2^256)⁻¹ * ∑`, the same form as
    `PaperTheorem.prob`, so that `failProb_eq_prob` is one induction.
13. The ledger entry V3-KS-A8 sits at the end of the V3-KS fix-pass list. Design text patched
    here goes into the core copy only. The workspace master must be synced by the user (the core's
    `CLAUDE.md`).

## 6. What these changes assume about O-25 (for the separate track)

- **Logs stay byte-keyed** (`List (ByteArray × Digest)`), and `failProb` reads the table by the
  query's bytes, like `runLog`. If O-25 makes queries structured (`List (ByteArray ⊕ D)`, #4 §3.1),
  `failProb` must be stated after serialisation at `D := Digest`, exactly as #4 plans for `runLog`.
- **`CompleteWithError` composes `P` and `V` with `OProg.bind` at `Digest`.** With a parametric
  `V : ∀ D [DecidableEq D], …`, the contract's wrapper instantiates `D := Digest` (and parses the
  proof) before the bind, and the statement's shape is unchanged. `OProg.bind` generalises to
  `OProg D`. `P` may stay at `Digest` (#4 §3.2).
- **The extractor sees bytes**: `E : Digest → Proof → Log → Option Wit` and the tape
  `extractorInput c π L` are unchanged, as #4 §4 assumed for `ImageComputes`. `Computes` is
  independent of `V`'s type.
- **No prover query bound** (`qP`) is assumed anywhere (H-m9).
- **Gate rule 4 names fields** (`V`, `P`, `ext`). A type check of `V` would be a separate gate rule
  and does not conflict.
- **A new channel to keep in view (H-M4):** under `CompleteWithError`, a `V` that recognises BLAKE2s
  and *rejects* honest proofs there is certified. This harms only its submitter, and the concrete
  harness checks catch it. It is the liveness analogue of O-25 and does not need O-25's fix.
- `Controls/Backdoor.lean` is ported and still certified. The O-25 stage should turn it into its
  negative control.

## 7. Open questions for the user

1. **`completenessCap`**: implemented at `2^-128` (the recommended value). `2^-96` is the
   alternative. The design's old `2^-64` is superseded.
2. **The extractor budget value**: `B t = 2^48 + 2^16·t` statements, derived in DESIGN §4.4 from
   paper estimates of the node decoder (F1 §3.3). Confirm, or give another.
3. **`logCap`**: `2^96` is unchanged (REPORT §6 Q2). Note that efficient extraction is now claimed
   to about `2^61` log entries (the `2^64`-word tape).
4. **Liveness**: the node liveness cap (proposed `2^36` steps), and whether "node liveness not run"
   is acceptable on a record.
5. **Succinctness and recursion** (#6): adopt CPU time on one core with the interleaved-checker
   calibration? Choose between a cap at every level and ranking column R. Set `T_V` on the reference
   machine.
6. **Kernel budget** (§2.7): the caps (proposed 16 GB / 30 min for the whole comparator run) and
   whether the pre-submission check is organiser-provided.
7. **Interpreter speed**: the compiled interpreter's per-step cost was **not measured**. If liveness
   needs it, `Word := UInt64` is a mechanical port (the tape lemmas move with it).
8. **Primitive set**: `clmul`/`clmulh` and `mulhu` are included. A BLAKE2s compression is not: the
   extractor reads answers from the log and never needs to hash. Confirm.
9. **Decision Q1** in `DISCUSSION.md` ("the extractor as a RISC-V image") is the user's record. Should
   the design say it is superseded by decision (a)?
10. **GitHub writes** this stage did not make: the PR #11 description, the #5 status line, filing D-11
    on #9, and the roadmap #1 update.
11. **Entries must be ported before the pin moves.** S2a and R1 certify against the S1/KS shape
    (`img`, `Complete`, `Declared.img`). After this stage they need `ext` (S2a can use the library's
    program and strict `check` unchanged), `δ := 0` through `complete_withError_zero`, and a
    `Declared` without the image. R1's 8-instruction parsing image must be re-expressed as an
    `XProg`. That is entry work in the submissions repository; nothing here edits it.
12. The removed RISC-V machine: keep it deleted (git has it at `05fde28`), or keep a copy for O-18?
