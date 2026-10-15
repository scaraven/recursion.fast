# S7 review: the baseline `P_triv` and the submitter-facing surface it exercises

Adversarial review of Stage 7, 2026-10-15. The reviewer read `CLAUDE.md`, DESIGN §3.3, §4, §6.2–§6.5,
§7.3, §7.4 and §8, the amendments S4-A1 … S4-A14, S5-A3, S5-A10, S6-A1, S6-A7 and S7-A1 … S7-A4,
`docs/stages/S7-RESULT.md`, `submissions/baseline/README.md` and `prover/README.md` (as the documents a
first submitter will read), then in full: `submissions/baseline/RecursionFastCandidate/{Protocol,
Compiled,Submission}.lean`, `audit/{BaselineChallenge,BaselineSolution}.lean`, `audit/*.json`,
`claim.json`, `extractor/*`, `scripts/*`; the contract surface `Contract/{Protocol,Extractor,
Security,Certificate}.lean` and the parts of `Compile.lean`/`Machine.lean`/`Layout.lean` the baseline
touches; `RecursionFast/Challenge/{L,R}.lean.in`, `scripts/render-challenge.py`, `scripts/Gate.lean`,
`scripts/harness.sh`, `scripts/olean-manifest.py`, `scripts/org-build.sh` (Stage 6b's working tree);
`harness/lean/{Main.lean.in,RecursionFastHarness/*}`, `harness/run-benchmark.py`; the comparator's
`Comparator/Compare.lean`. v0.3's `reviews/A4-contract.md` and `A7-report-fm.md` (m17) for
comparison. Nothing under `RecursionFast/`, `submissions/` or `scripts/` was edited.

Snapshot: the statements reviewed are those of the S7 RESULT. The golf agent shortened
`Protocol.lean` during the review (120 → 111 code lines at 03:28); no statement changed. Probes:
`probes/s7/` (`run.sh ORG MANIFEST` reproduces all of them, 75 s); logs: `logs/S7-review/`.
The gate runs use S7's private organiser build `/tmp/s7-org` and its manifest
`/tmp/s7/manifest.sha256` (re-checked unchanged after the probes: 35,092 files match).

## Verdict

**The baseline is correct; the surface it exercises has two major holes.**

- **The baseline itself passes.** Every statement says what the RESULT claims, about `P_triv`'s
  own shapes, at every class and configuration; the certificate is non-vacuous; all 19 theorems
  use only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`/`native_decide`/
  `implemented_by`/`extern`/`csimp`/`noncomputable`; it imports exactly the contract, the Library
  and (through `Library/Field`) CompPoly. The tape arithmetic and the 78.1 MiB witness are right
  (recomputed from the shapes and from `gen-chain-layout.py report`).
- **The certificate is what the comparator checks**, and the gate sees the comparator's build
  (A7-M3 holds). `Declared` + the stub's image conjunct pin the class, hash, arity and image.
- **S7-M1 (major, owner Stage 6b + DESIGN §8).** The *executed* verifier is not bound to the
  proved one. A submission can overwrite the compiler's code for its own `verify` with no
  attribute; the kernel accepts (the kernel terms are untouched, so the comparator's replay has
  nothing to object to; not run), the v2 gate says PASS, and the compiled `NARG` runs the
  substitute. Demonstrated up to linking the badge executable.
- **S7-M2 (major, owner orchestrator + 6b runner + README).** The README's "certified at `k = 24`,
  the benchmark's `k_min`" is wrong for board L: the runner's default leaf board includes
  `L_chain(2^12)`, which needs class 26, and a secure class-24 protocol must reject it. A class-24
  entry that asks for board L is rejected, and with it its board-R result.
- **13 minor findings**, mostly README sentences that over- or under-claim (list below).
- **S7-A1: accept** (the two lines are below, prototyped and checked not to weaken anything).
  **S7-A3: agree**, with the coupling noted under S7-M2.

## 1. Is the certificate what the comparator checks? (Pass A)

**What the comparator compares** (`Comparator/Compare.lean`, `harness-L.log`):

1. `theorem_names = [certified]`: both are theorems, and name, universe parameters and **type**
   are equal (`Expr` equality).
2. `definition_names = [submission]`: both are definitions with equal name, universe parameters,
   type (`Submission declared.k`) and safety; the value is free.
3. Worklist: every constant used in those two types. For each one that is not a target, the
   challenge's and the solution's `ConstantInfo` must be equal (value included), and its own
   constants (type and value) are added. So `declared`, `image`, `image_code`, `image_code_0`,
   `image_code_chunks`, `image_data*`, `Certificate`, `Submission`, `Protocol`, `Protocol.Secure`
   and the whole security cone down to `run` and the vendored Rv64 must be the organiser's,
   value for value. `NARG`, `index`, `HashId.run`, `blake2s` are *not* reached from the statement;
   they are bound by the gate's manifest instead (the solution's environment imports them from
   the same hashed `Contract/*.olean`).
4. Axioms of the two targets ⊆ permitted; then lean4export of the closure of `certified` and
   `submission` is replayed by nanoda and the Lean kernel.

**Consequences.**

- The rendered statement `Certificate declared submission ∧ submission.P.extractor.img = image`
  pins: the class by type (`Submission declared.k`, `declared.k = 24`), hash and arity by
  `Certificate.cfg` (and `Cfg` has no other data field: `arity_ok` is a proof), the image by the
  second conjunct. That image is the one `Secure` is about, since `Submission.secure : P.Secure`
  and `Secure` runs `P.extractor.toExtractor`. Nothing the scoreboard displays for board L is
  left unpinned; the fuel split, `n`, the shapes and `ε` are not displayed and are fixed by the
  same `submission` value.
- **Same `submission` in the gate (A7-M3).** The gate tree's build must be byte-identical to a
  subset of the comparator's (`harness-L.log`: 12 artifacts recorded, the gate tree's 10 all
  identical; the two extra are `BaselineChallenge.{olean,c}`). The gate and the badge use the constant
  `RecursionFast.Challenge.submission` of `SOL_MOD` (`harness/badge-main.py`,
  `Main.lean.in`). So the *kernel* object is the same everywhere. The *compiled code* is not
  bound to it: S7-M1.
- **Non-vacuity.** `Certificate ⟨24, .blake2s, 4⟩ (submission 24 h24)` is false (`2 ≠ 4`), and a
  changed image fails the conjunct (`S7Probe.cert'_other_image`, and S7's
  `negative-claims.log`). A claim with `k ∉ [20, 28]` renders but cannot be met: `Protocol k`
  is empty (`S7Probe.no_protocol_29`).

## 2. Findings, most severe first

### S7-M1 (major): the executed verifier can differ from the proved one; every v2 check passes

- **Where.** `scripts/Gate.lean` rules 3–4, `harness/lean/RecursionFastHarness/Twin.lean`,
  DESIGN §3.2 ("the thing timed is the thing proved, up to the Lean compiler") and §8.
- **Mechanism.** In Lean v4.34.1 a module's C code is emitted from the compiler's impure-phase
  state, `Lean.Compiler.LCNF.impureExt` (`Shell.lean` → `LCNF/EmitC.lean`, `getLocalImpureDecls`).
  Elaboration-time code in the module can overwrite it:
  ```lean
  run_meta do
    let some d := impureExt.getState (← getEnv) |>.find? ``acceptAll | throwError "…"
    modifyEnv (saveImpureDeclCore · { d with name := ``dec })
  ```
  No attribute is registered, no constant in any closure is `unsafe`/`partial`/`opaque`, and the
  kernel terms are untouched. Any submission can do this: `RecursionFast.Contract` imports
  Mathlib, which imports `Lean`.
- **Evidence.**
  - `probes/s7/irforge` (Lean only): the kernel proves `vk_one : vk 1 = false`; the linked
    executable prints `compiled vk 1 = true`; the v2 gate (`--computable vk`) says PASS
    (`irforge.log`).
  - `probes/s7/ForgeGate.lean` (the v2 setting): `S7Forge.submission : Submission 24` is the
    organiser's secure toy with `verify` deciding through a submission function `dec`
    (`dec = toyDecide 24` in the kernel, so `secure := toy_secure 24 _`; `dec_rejects` is
    kernel-checked). The emitted C of `S7Forge.dec` is `return l_S7Forge_acceptAll___redArg(idx)`,
    and `P.verify`'s compiled lambda calls `l_S7Forge_dec`. The v2 gate with S7's manifest and
    `--computable S7Forge.submission`: **PASS** (`forge-gate.log`).
  - The badge's twin copies the field terms of `submission.P` (`Twin.lean`), so its `verify`
    calls the solution's compiled `dec`. Not run: linking a badge executable needs an organiser
    build with `RecursionFastHarness` and prebuilt Mathlib objects, which S7's private build does
    not have.
- **Second route: `@[cpass]`.** A non-module solution file may register a compiler-pass installer
  (`probes/s7/CpassRegister.lean` compiles; `cpass.log`). Installers are evaluated by every
  importer (`passManagerExt.addImportedFn`), so they run when the badge's main module compiles the
  twin, and can rewrite it. Rule 3 lists `implemented_by`, `extern`, `export`, `init`, `csimp`,
  not `cpass`.
- **Concrete failure.** Take `P_triv` with its message Merkle-committed in leaves of `2^10`
  elements and a kernel verifier that opens every leaf: secure by `triv_secure`'s proof. Forge
  its compiled `verify` to `.done true`. The native prover writes the rounds section only (one
  32-byte root); the executed `NARG` (`runQ (.done true) [] = some true`) accepts. Board L ranks
  it first; on board R every "the output proof must verify" check runs the same forged code. The
  A7-M3 binding does not help: the forgery is deterministic, so both builds emit the same `.c`.
- **Why v2 and not v0.3.** v0.3's A7-m17 was this gap, but there the executed verifier was the
  RISC-V image on the organiser's emulator with a kernel-checked `Agrees`; Lean-compiled code was
  only the prover/indexer. In v2 the compiled `verify` *is* the timed verifier.
- **Fix (for Stage 6b; in this order).**
  1. Rule 3 also rejects `cpass` entries of untrusted modules (`Lean.Compiler.LCNF.passManagerExt`
     module entries), next to `csimp`.
  2. A **binding** source rule, checked by the harness on the sources the comparator's tree built:
     every untrusted module that defines a constant in the closure of the badge-path fields, and
     every untrusted module it imports, contains no submitter-written elaboration-time code: no
     `run_cmd`, `run_meta`, `run_elab`, `#eval`, `elab`, `elab_rules`, `macro`, `macro_rules`,
     `syntax`, `declare_syntax_cat`, `notation`-family commands, `initialize`, `builtin_initialize`,
     no `run_tac`/`by_elab` inside terms, and attributes only from a whitelist (`simp`, `inline`,
     `specialize`, `reducible`, `irreducible`, `instance`, `ext`, …). Because custom syntax is
     banned, the lint parses with trusted syntax only. (Recompiling from the kernel terms instead
     is not straightforward: Lean compiles recursive definitions from their pre-definitions, not
     from `brecOn`/`WellFounded.fix` terms; `probes/s7/WfRec.lean` passes the gate with code that
     elaboration-time `decide` cannot evaluate.)
  3. Regression controls in CI: `ForgeGate.lean` and a `cpass` variant must be REJECTed.
  4. DESIGN §3.2/§8: "up to the Lean compiler" becomes "up to the Lean compiler, run on
     definitions elaborated without submitter metaprograms (gate rule …)". Until the fix lands, the
     README must not say the executed verifier is the proved one.

### S7-M2 (major): the class a board-L entry must declare; the worked example's `k = 24` fails board L

- **Facts.**
  - `L_chain(2^12)` has 38,572,105 cells; its least class is 26 (re-run:
    `gen-chain-layout.py report --n 4096`; S6-A1). `L_chain(2^8)` and `L_chain(2^10)` are 24.
  - The runner's default leaf board is `{"256": 16, "4096": 16}` (`run-benchmark.py:65`); S6-A7
    says "`2^12` optional at class 26".
  - `relK k` excludes every witness of more than `2^k` cells (`Layout.rel`), and `RbrKS` covers
    every statement. So a secure protocol at `k ≤ 25` accepts an `L_chain(2^12)` proof with
    probability at most `Σ ε` (with no challenge rounds, never: the `next` chain reaches
    `toFun 0 = relK`).
  - With `"L"` in `boards` the runner adds the leaf-board chains to the same evaluation and caps
    every leaf proof, the tree's included, at `tape_L` (`run-benchmark.py:245, 297`); any failure
    rejects the whole evaluation.
- **Consequence.** A submitter who follows the worked example (`k = 24`) and asks for board L is
  rejected on every default evaluation, and loses board R with it. The README (lines 5–6, 162)
  and S7-RESULT ("the benchmark's `k_min`") say nothing about per-board classes.
- **Fix.**
  1. Orchestrator: either a leaf board within class 24 (`{2^8, 2^10}`, or `{2^8, 2^10, 2^11}` at
     `k ≥ 25`), or "board L requires `k ≥ 26`" in DESIGN §6.2/§6.5.
  2. Runner or renderer: reject up front a claim whose `k` is below the least class of a layout
     of a requested board (one comparison; avoids a 6 h evaluation that must fail).
  3. Decide whether boards L and R are separate evaluations (so L's extra sizes and its 128 KiB
     cap cannot sink R; DESIGN §6.2 gives the tree leaves the 1 MiB cap).
  4. README: state the class each board needs.

### S7-m1 (minor): "Proved (kernel, both kernels via the comparator)" overclaims for the compilation facts

README §5 (lines 166–172) lists `triv_depth`, `triv_uncapped_length`, `triv_prove_none`,
`triv_narg`, `triv_no_entry` and `trivExtractor_fuel_tight` under "both kernels via the
comparator". The comparator exports only the closure of `certified` and `submission`
(`harness-L.log`: "Exporting #[… certified … submission] from BaselineSolution"). `triv_secure`
is in it (through `submission`'s value); the six others are not. They are checked by Lean's kernel
at build time and by `leanchecker` in `check.sh`, which the organiser's `harness.sh` does not run
(README §4's kernel row says "`leanchecker` replays the whole closure" as if it were part of the
harness). They are documentation, not certified claims.

### S7-m2 (minor): "`sound` and `cap` are vacuous … so `ε = 0` is allowed"

README §3.1 item 5 (lines 85–86), DESIGN §7.3 ("`ε = 0`") and `triv_secure`'s docstring ("at
`ε = 0`"). Only the counting bound `RbrKS` and `cap` are vacuous. The existence of the `KSF`, with
its `next` and `full` laws, is the substance of `sound`: `S7Probe.split0_not_secure` shows that the
same protocol with a starved extractor is not secure. And `ε` is a function on an empty type, so
`ε = 0` and `ε = errorCap` are the same protocol (`S7Probe.eps_irrelevant`; `P_cap_secure`):
"`ε = 0`" states nothing. Replace by "no challenge rounds, so the counting bound and the cap are
vacuous for every `ε`; the knowledge content is in the `KSF` laws (items 3–4)".

### S7-m3 (minor): the fuel split's "checked in the kernel"

README §7 (lines 237–240) and RESULT design choice 3: "the `next` law checks this in the kernel.
With 7 the image runs out of fuel (`trivExtractor_fuel_tight`), and the call returns `[]`".
Kernel-checked are: 8 steps suffice on every tape the protocol produces (`triv_extractMid`), and 7
fail on one 5-section tape (`trivExtractor_fuel_tight`). That `P_triv` is *insecure* with less is
not proved in the baseline. `S7Probe.split0_not_secure` proves it for the split `![0, 8]` (the same
total). Suggested: add that theorem to the baseline as its negative control (the worked example of
a declaration that fails), or a general `run firstMsgImg t 7 = none`. Answer to "what forces
`fuel_le` to be honest": nothing beyond the definition. The split is part of the extractor that
`Secure` is stated about; `fuel_le` bounds the total; the call before round 0 must return a
witness in `relK` (`empty` pins `toFun 0`, `[]` fails it), so starving it breaks `next` whenever
some transcript is accepted; any later call may have 0 exactly when the submitter's own state
function ignores its output there, as `trivKSF` does at the last state.

### S7-m4 (minor): README §3.1 item 1 mis-attributes lemmas

Lines 75–78 say `trivDecide_iff` uses `pWit_eWit` and `eWit_length`; it uses `pLayout_eLayout`,
`eLayout_length`, `relBelow_iff` and `rel_normal_iff`. `pWit_eWit`, `eWit_length` and
`rel_trim_iff` are used in `triv_secure.complete`.

### S7-m5 (minor): the gate row lists the wrong badge-path fields and omits the noncomputable case

README §4 gate row (line 161) says "`Submission.P` (`VK`, `IDX`, `verify`, `extractor`) and
`RecursionEntry.decode`". The gate's table is `Submission: P, cfg`; `Protocol: n, shape, vkLen, VK,
idxShape, IDX, verify, extractor`; `ExtractorImage: img` (the fuel split is data);
`SubmissionR: toSubmission, entry`; `RecursionEntry: C, decode`. A real submission with
`ε := errorCap` has no compiled code as a whole; the gate then checks the fields one by one
(`probes/s7/EpsGate.lean`: PASS, `eps-gate.log`), and the solution must write
`noncomputable def submission` (the comparator ignores `noncomputable`). The README's example
(`ε := 0`, computable) never shows this path.

### S7-m6 (minor): "So `submission = rendered` is a kernel-checked equality"

README §3.4 (lines 150–153). What is kernel-checked is the challenge statement: the submission's
class (by type), hash, arity and extractor image equal the rendered claim's. Say that, and give the
comparator's rule in §1's form (targets compared by type; every other constant reachable from the
statement compared by value). Same for the §3.2 `img` row ("the comparator checks that it equals
…"): the challenge states it, the comparator checks the solution proves exactly that statement.

### S7-m7 (minor): `prover/README.md`'s inputs disagree with the runner

`prover/README.md` "Inputs" says the prover reads `L`, `w`, `x` as `layout/1`, `witness/1`,
`statement/1` JSON. Stage 6b's runner gives a leaf prover `layout.json`, `vkc.bin`, `stmt.bin` (256
bytes), `secret.hex`, and `witness.json` only on request, and expects `proof.bin`; a node prover gets
`vkC.bin`, `vkL.bin`, `child{1,2}.{stmt,proof,tag}` (`run-benchmark.py` docstring). Both cite
`harness/README.md`, which does not document the prover interface yet. Align with 6b's interface.

### S7-m8 (minor): the README does not say how the harness builds a solution

`harness.sh` ignores the submitter's lakefile: every `*.lean` under the solution directory becomes a
root of one generated library (no `leanOptions`/`moreLeanArgs`), module roots must be fresh (not
`RecursionFast`, `Mathlib` or any package root), and the solution module is `solution_module` of
the comparator config. The organiser package also exposes `Controls` and `Bridge`
(`org-build.sh`), so "a submission imports only the contract and the organiser's Library"
(line 18) is a convention, not a check (harmless for soundness: they are untrusted, kernel-checked
and subject to the gate like the Library). Say both.

### S7-m9 (minor): `Submission.lean`'s `declared` docstring cites `audit/claim.json`

The file is `submissions/baseline/claim.json`.

### S7-m10 (minor): the 78.1 MiB witness includes the fixed tables

The contract's witness has one table per chip, fixed chips included: 786,464 of the 10,232,905 cells
(6.0 MiB) are `ADD8`/`NIB`, which the index already determines. The prover-chosen part is 72.1 MiB;
"84.1 MiB in all" counts the `add8` table twice (in the layout and in the witness). The
conclusions (78× / 625× over the caps; no "send the witness" protocol fits) are unchanged.

### S7-m11 (minor): units

README §5 says the layout is "6.3 MB", §6 and the RESULT "6.0 MiB" (both 6,342,808 B). Use MiB.

### S7-m12 (minor): the axiom audit lists 11 of the 19 theorems

`scripts/Axioms.lean` omits `trivExtractor_fuel_tight`, `trivDecide_iff`, `triv_noChal`,
`prove_eq_uncapped`, `triv_tape_gt_cap`, `takeN_short`, `h24`, `submission_img`. All are within the
standard three (`baseline-probes.log`; `takeN_short` and `h24` use none). List them all.

### S7-m13 (minor): the indexer's failure is also quadratic time

README §6 (lines 218–220) estimates the indexer's memory. `toOracle m l = fun p => l.getD p 0`, and
`Oracle.leaf` builds the leaf with `List.ofFn`, so committing the `2^32`-element index leaf at
`k = 24` costs about `2^63` list steps before any hashing. A stronger, non-estimated reason.

## 3. The submitter attack surface, through the baseline's shape (Pass A)

- **(a) `ε := errorCap` vs the proved `ε = 0`.** Equivalent for `P_triv` (S7-m2). For a protocol
  with challenge rounds `ε` is honest by proof (`RbrKS` at the declared `ε`), is never displayed,
  and may be noncomputable: the gate's field-wise path passes it (`EpsGate`, S7-m5).
- **(b) The fuel split.** S7-m3: a split that starves the call before round 0 is not secure
  (`split0_not_secure`, kernel-checked); later calls may have 0 only where the submitter's own
  state function ignores them. The total is what the contract bounds, and it is honest by
  construction.
- **(c) The class.** Pinned by type (`Submission declared.k`) and consistent with `k_range` (no
  `Protocol k` outside `[20, 28]`; the renderer accepts any `k < 2^64`, the type rejects). The
  benchmark needs `k ≥ 24` for the tree and `k ≥ 26` for the default leaf board: S7-M2. A claim with
  `k ≤ 23` certifies but cannot pass any benchmark (S7-M2's argument), and nothing rejects it early.
- **(d) Imports.** The baseline's closure is `RecursionFast.Contract.*`, `RecursionFast.Library.
  {Layout, Codec, Extractor, Field, Challenges, RbrSound, Blake2s, Compile}`, CompPoly (via
  `Library/Field`) and Mathlib (`imports.log`): no `Controls`, no `Bridge`. A submission *can*
  import `Controls`/`Bridge` (S7-m8); harmless.
- **(e) Shadowing and the trust-by-hash.** S7's manifest covers every v2 contract module
  (`Certificate`, `Compile`, `Extractor`, `Recursion`, `Hash/Blake2s`, …) and the 16 `RiscvZkvm`
  modules. v0.3's `SpoofCert` re-run as `probes/s7/SpoofNs.lean` (an `implemented_by` on a constant
  in `RecursionFast.Contract.Spoof`, from a fresh-root module): **REJECT** by rule 3
  (`spoof-gate.log`); a module *named* under `RecursionFast` is refused earlier by `harness.sh`'s
  fresh-root check, and an extra `.olean` in a trusted directory by the manifest's extra-file
  check. Overriding `K`'s instances or naming a constant `blake2s256` changes only the
  submission's own kernel terms (the comparator compares the contract's constants by value; a
  duplicate declaration does not import). The hole that remains is compiled code: S7-M1.
- **Recursion is fine.** Structural and well-founded recursion pass the gate (`WfRec.lean`); Lean
  v4.34.1 registers no `implemented_by` for them.

## 4. "Listed, unranked" as a theorem (Pass A)

- `triv_narg cfg vkc x t : NARG cfg (P_triv k hk) vkc x t = false`: every configuration, key,
  statement and tape, every class in range. `triv_prove_none`: the Library's honest prover writes
  none. `triv_uncapped_length`: its uncapped tape has `5 · 2^(k+11)` bytes on every instance
  (`uncapped` is tied to `prove` by `prove_eq_uncapped`). `triv_no_entry`: no `RecursionEntry` at
  any class and configuration. All are about `P_triv`'s shapes only; an agent with smaller shapes
  is unaffected. The RESULT's claims match the statements.
- **Arithmetic, recomputed.** `8·2^(k+10) + 8·2^(k+8) = 5·2^(k+11)`; at `k = 24`,
  171,798,691,840 B = 160 GiB = 163,840 × 1 MiB = 1,310,720 × 128 KiB; `k = 20`: 10 GiB, 10,240,
  81,920; `k = 28`: 2,560 GiB, 2,621,440, 20,971,520. Rounds alone `8·2^(k+10) ≥ 2^33 > 2^20` at
  `k ≥ 20`. Witness of `L_chain(2^10)`: `gen-chain-layout.py` gives 10,232,905 cells (re-run), so
  `(25 + 10,232,905) · 8 = 81,863,440 B = 78.07 MiB`, 78.1× and 624.6× the caps (S7-m10 for the
  fixed part). Layout 792,851 elements = 6,342,808 B. The "best Merkle variant" (84.5 MiB) is a
  model in `tape-size.py`, labelled as such.

## 5. The README as the submitter's guide (Pass B: fidelity to the code and harness)

Corrections, by line of `submissions/baseline/README.md`:

1. L5–6: "certified at `k = 24`, the benchmark's `k_min`" → the tree's `k_min`; board L needs the
   class of its largest leaf (26 for the default `2^12`), S7-M2.
2. L18: "a submission imports only the contract and the organiser's Library" → a convention; the
   organiser package also exposes `Controls` and `Bridge` (S7-m8).
3. L19: "so the prover writes no tape, the verifier accepts none" → the verifier accepts none
   because the rounds section alone exceeds the cap (`triv_narg`), not because of the honest tape.
4. L60 (`verify` row, "it is executed and timed"): add that the executed code is the Lean
   compiler's output on the submission's module, not checked against the kernel term (S7-M1).
5. L75–78: lemma attribution (S7-m4).
6. L85–86: "`sound` and `cap` are vacuous … so `ε = 0` is allowed" (S7-m2).
7. L92 (`img` row) and L150–153: what the comparator checks (S7-m6).
8. L159 (kernel row): `leanchecker` is `check.sh`'s, not the harness's (S7-m1).
9. L161 (gate row): the badge-path field table and the noncomputable path (S7-m5); the gate does
   not check compiled code against kernel terms (S7-M1).
10. L162 (harness row): add the class requirement and the `tape_L` coupling (S7-M2).
11. L166–172: "both kernels via the comparator" only for `certified` and `triv_secure` (S7-m1).
12. L177–178: "6.3 MB" → "6.0 MiB" (S7-m11).
13. L207–211: the fixed cells (S7-m10).
14. L218–220: add the quadratic `toOracle` (S7-m13).
15. L237–240: what the kernel checks about the split (S7-m3).

Missing, for a first submitter (each one or two sentences):

- How the harness builds the solution: generated lakefile, all `*.lean` as roots, fresh module
  roots, the comparator config's two module names (S7-m8).
- A noncomputable `submission` (`ε := errorCap`) is expected and passes the gate field by field
  (S7-m5).
- The claim schema's rules (`render-challenge.py`): the key set equals the stub's placeholders;
  `image.code` is little-endian 32-bit words, `image.data` little-endian 64-bit words, together
  `≤ 2^20` bytes, plain relative paths inside the claim's directory, no symlinks.
- For a large image, prove `submission.P.extractor.img = image` cheaply: define the candidate's
  image in the same packed `unpack` form, or use the Library's chunk lemmas (v0.3's per-lookup
  cost was 80 s / 9 GB).
- Board R: the R stub also binds `submission.entry.C = C` (the rendered layout), and the digests
  are compared by the runner, not proved (README §3.3 mentions only `DeclaredR`).
- The caps outside Lean (DESIGN §6.5): build ≤ 1 h / 48 GB, harness ≤ 2 h.
- `prover/README.md`: the runner's file interface (S7-m7).

S7-RESULT: the same corrections apply to its headline (S7-M2: "the benchmark's `k_min`"), design
choice 3 (S7-m3) and "Proved (kernel)" list (fine as "kernel", not "both kernels"). DESIGN §7.3 as
amended by S7-A2: drop "`ε = 0`" (S7-m2).

## 6. S7-A1: the two trusted lines

In `Contract/Certificate.lean`:

```lean
structure Declared where
  k : ℕ
  hash : HashId
  arity : ℕ
  /-- The extractor image, rendered from the submitted files (S4-A2). -/
  img : Image

structure Certificate (D : Declared) (S : Submission D.k) : Prop where
  cfg : S.cfg.hash = D.hash ∧ S.cfg.arity = D.arity
  /-- The extractor image is the declared one (S4-A2). -/
  img : S.P.extractor.img = D.img
```

- **Checked** as `S7Probe.Declared'`/`Certificate'` (extensions of the current structures, in
  `probes/s7/Baseline.lean`): the baseline's certificate is `⟨⟨rfl, rfl⟩, rfl⟩`
  (`cert'_baseline`); a changed code word is rejected (`cert'_other_image`); and
  `Certificate' D S → Certificate D.toDeclared S ∧ S.P.extractor.img = D.img`
  (`cert'_weakens_nothing`). Adding a field to a `Prop` structure only adds a conjunct; the
  comparator still compares `declared`'s value, now containing `image`, exactly as it compares
  `image` today. `Image` is already in the contract (`Machine.lean`).
- **Knock-on edits.** `L.lean.in`: `declared : Declared := ⟨{{nat:k}}, {{hash:hash}},
  {{nat:arity}}, image⟩` and `certified : Certificate declared submission`. `R.lean.in`:
  `img := image` in `declared`, and `certified : CertificateR declared submission ∧
  submission.entry.C = C`. `Controls/Certificate.lean` (`toy_certificate`,
  `toy_certificate_arity`, plus a new `¬ Certificate` with another image), the baseline's
  `declared`/`certificate`/`certificate_at`, `make-solution.py`'s regex, `scripts/test-render.sh`.
- **Optional, same pattern.** `DeclaredR.C : Layout K` and `CertificateR.layout : S.entry.C = D.C`
  (two more lines) would move the R stub's last conjunct into the contract too; `chips`/`entries`
  then follow from `C`.

**S7-A3: agree.** `NARG` enforces only `tapeCap`; the 128 KiB board-L cap is the runner's, and 6b's
runner implements it (`tape_L = 2^17`). DESIGN §6.5's row should say "checked by the runner". The
runner applies it to every leaf when board L is requested, the tree's leaves included: S7-M2 item 3.

## 7. Hygiene (Pass C)

- **Axioms.** All 18 candidate theorems are within `[propext, Classical.choice, Quot.sound]`
  (`baseline-probes.log`), and so is the solution's `certified` (S7's `axioms.log`, the gate's
  output); 19 in all.
- **Forbidden constructs.** None of `sorry`, `admit`, `native_decide`, `implemented_by`,
  `extern`, `csimp`, `noncomputable`, `unsafe`, `partial`, `opaque`, `axiom`, `set_option`,
  `macro`, `elab`, `run_cmd`, `#eval`, `initialize` in the candidate or the solution (grep, comments
  included). `decide +kernel` only in `trivExtractor_fuel_tight`.
- **Build.** `lake build --no-build RecursionFastCandidate`: up to date. Independent cold compile
  of the 4 modules into a scratch directory: 6.9 + 6.6 + 6.5 + 6.1 s, 2.7 GB peak, no warnings
  (RESULT: 20.4 s with Lake). `lake env lean probes/s7/Baseline.lean`: 6.3 s.
- **Lakefile.** `roots = ["RecursionFastCandidate"]`, `globs = ["RecursionFastCandidate.*"]`
  (root and submodules), not a default target, dropped by `org-build.sh`. Irrelevant to the
  production harness, which writes its own lakefile (S7-m8).
- **Lines** (`scripts/loc.py`): 216 code lines, 19 theorems, as the RESULT says (Protocol 111
  after the golf in progress).
- **Docstrings.** Every definition and theorem has one; S7-m9 is the only wrong reference.

## 8. Probes

| File | What it shows | Result |
|---|---|---|
| `probes/s7/Baseline.lean` | `eps_irrelevant`, `P_cap_secure` (a); `split0_not_secure` (b); `no_protocol_29` (c); S7-A1 prototype; axioms of all 19 theorems | all proved; standard axioms |
| `probes/s7/irforge/` | kernel `vk 1 = false`, executable prints `true`; v2 gate PASS | S7-M1 |
| `probes/s7/ForgeGate.lean` | a secure `Submission 24` whose emitted C for `dec` calls `acceptAll`; v2 gate PASS | S7-M1 |
| `probes/s7/CpassRegister.lean` | a non-module file registers `@[cpass]` | accepted (S7-M1) |
| `probes/s7/SpoofNs.lean` | v0.3 `SpoofCert` analogue, `implemented_by` in the contract's namespace | gate REJECT |
| `probes/s7/EpsGate.lean` | noncomputable `ε := errorCap`; gate checks fields one by one | gate PASS |
| `probes/s7/WfRec.lean` | structural and well-founded recursion | gate PASS |
| `probes/s7/run.sh ORG MANIFEST` | reproduces all of the above into `logs/S7-review/` | 75 s |
