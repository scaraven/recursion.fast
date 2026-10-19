# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

The **recursion.fast v3 trusted core**: the Lean 4 rules of an autoresearch competition in which
agents submit a non-interactive argument in the random-oracle model (a verifier `V` and an honest
prover `P` as Lean query programs over bytes, an extractor `E` with a RISC-V image that computes
it), prove in Lean that `V` is knowledge-sound (a local counting form, query by query over the
oracle's log) and that `P` is complete, for one relation over 32-byte digests (hash-chain leaves and
two-child nodes, parameterised by the submitted verifier), and are ranked by the measured wall time
of their native prover on a whole recursion tree. Plus the organiser's untrusted library, the
positive and negative controls, and the harness tools.

**The design is `docs/DESIGN-v3.md`. It is authoritative.** Where this repository and the design
disagree, the design wins unless a stage RESULT records an agreed deviation with its reason. The
ledger of agreed changes to patch into the design is `docs/DESIGN-AMENDMENTS.md`.

**Entries live elsewhere.** This repository holds no submission and no baseline. Entries, the
baseline first, go to https://github.com/scaraven/recursion.fast-submissions (design §7.7, decision
V3-12), which pins a commit of this repository as its `.contract` submodule. The roadmap and
tracker is https://github.com/scaraven/recursion.fast/issues/1.

**v2 is not in the tree.** The v2 contract, harness, probes, baseline, design and stage records
were removed after Stage V3-S1 landed; git keeps them at the tag `v2-archive`
(`git show v2-archive:<path>`). Design §10 says what v3 carries over: stage S3 rebuilds the
harness, stage S4 re-targets what is worth keeping from v2's library, controls and bridges. v2
finding and amendment IDs cited in comments (S*-A*, A6-G0, …) resolve at the tag.

Read-only references (never edit, never build inside):

- `/home/devops/CambridgePQ/recursion.fast/`: the design workspace. `design/DESIGN-v3-narg-rom.md`
  is the master of `docs/DESIGN-v3.md` (keep the two in sync); `DISCUSSION.md` holds the user's
  decisions Q1–Q6; `report/sections/*.tex` is the v1.0 report (background, prior competitions,
  threat model).

## Toolchain

Lean **v4.34.1**, Mathlib v4.34.1, ArkLib `7653a90`, CompPoly `572f997`, VCVio `a4232d0`,
PolyFun `41d3b21`. `.lake/packages` is a symlink to the prebuilt shared tree
`/home/devops/CambridgePQ/recursion.fast/contract/.lake/packages` (local-only, gitignored):
`mkdir -p .lake && ln -s /home/devops/CambridgePQ/recursion.fast/contract/.lake/packages .lake/packages`.
Elsewhere, `lake exe cache get` supplies Mathlib; CompPoly, ArkLib, VCVio and PolyFun are then
built, although no v3 module imports them yet.

```sh
lake build                          # default targets: contract, library, controls (about 2 min cold, 3 s warm)
lake build gate axiomaudit          # the harness tools
lake exe axiomaudit                 # PASS: every RecursionFast.* declaration within propext, Classical.choice, Quot.sound
lake env lean RecursionFast/Controls/Backdoor.lean   # one file
scripts/ci.sh [RISCV_ZKVM_CHECKOUT] # vendor, hygiene, the source rule's fixtures, build, axiom audit, line budget
python3 scripts/loc.py RecursionFast/Contract.lean RecursionFast/Contract/*.lean RecursionFast/Contract/Hash/Blake2s.lean   # trusted line budget
scripts/check-vendor.sh /home/devops/Verified-zkEVM/riscv-zkvm   # vendored Rv64 is byte-identical
```

## Trust layers

| Layer | Path | Rule |
|---|---|---|
| Contract | `RecursionFast/Contract/*.lean`: `Hash/Blake2s`, `Relation`, `Oracle`, `Security`, `Machine`, `Extractor`, `Tree`, `Certificate` (DESIGN-v3 §8) | **TRUSTED.** Imports Lean core, Mathlib, vendored Rv64 only; never ArkLib/CompPoly/VCVio/PolyFun. No field (V3-1). Budget ≤ 500 code lines for `Contract.lean`, `Contract/*.lean` and `Hash/Blake2s.lean` together (`scripts/loc.py`; 328 after the V3-S1 fix pass). Every definition has a docstring saying what it means, not how it is written. |
| Vendored Rv64 | `RecursionFast/Vendor/RiscvZkvm/` | **TRUSTED**, byte-identical to riscv-zkvm `6810fc1`. Never edit. |
| Library | `RecursionFast/Library/` | Untrusted, kernel-checked helpers for submitters: oracle and security lemmas, machine symbolic execution, tape and output formats, the tree, the witness-sending argument. |
| Controls | `RecursionFast/Controls/` | Positive **and** negative controls for every trusted definition; run in CI. `Backdoor.lean` is the known gap O-25, kept on purpose. |
| Harness tools | `scripts/`, `tests/source-rule/` | `Gate.lean` (the environment gate, rules 1–9), `source-rule.py` with its fixtures and `TokenSweep.lean`, `AxiomAudit.lean`, `olean-manifest.py`, `bwrap-landrun.sh` (the sandbox shim), `check-vendor.sh`, `check-hygiene.sh`, `loc.py`, `ci.sh`. Carried over from v2 unchanged (design §10). The gate's allowlist, the olean manifest, the organiser build, the challenge stubs, the renderer and the full harness order are stage S3's. |

Hard rules for anything trusted: no `sorry`; axioms only `propext`, `Classical.choice`, `Quot.sound`;
no `native_decide`, `implemented_by`, `extern`, `csimp`; statements are non-vacuous (a negative
control shows the definition can fail); a proof never changes the statement it proves.

## Stage protocol (how this repository is built)

The build order is design §11, one stage at a time, each on a branch merged by pull request. Each
stage runs the same cycle:

1. **Implement** (one agent): builds the stage, keeps `lake build` green, writes
   `docs/stages/V3-S<n>-RESULT.md`: what was built (file by file, with code line counts from
   `scripts/loc.py`), build time, the controls and what each shows, every deviation from
   `docs/DESIGN-v3.md` with its reason, open questions for the orchestrator.
2. **Adversarial review** (one agent, in parallel with 3): spec tightness, vacuity, loopholes,
   trust policy, hygiene; writes `docs/reviews/V3-S<n>-review.md` with numbered findings
   (`M<i>` major: must fix; `m<i>` minor) and a verdict.
3. **Golf** (one agent, in parallel with 2): shortens proofs and definitions without changing any
   statement; edits in place; writes `docs/reviews/V3-S<n>-golf.md` (before/after line counts,
   what changed, anything it declined to touch and why).
4. **Fix** (the implementing agent): applies every major finding, answers each minor one (fixed or
   argued), appends `## Fix pass` to the RESULT, re-runs the build and the controls.
5. The orchestrator reads the RESULT and review, records the agreed changes in
   `docs/DESIGN-AMENDMENTS.md`, commits, and opens the next stage.

Subagents **do not commit**; the orchestrator does. Measurements go in `logs/` (gitignored) and
are quoted in the RESULT. Skills to use: `lean-spec-authoring` when writing trusted definitions or
theorem statements; `adversarial-review` and `lean4:review` when reviewing; `lean4:golf` when
golfing; `lean4:lean4` for any Lean work.

## Layout

```
RecursionFast/Contract/   Hash/Blake2s · Relation · Oracle · Security · Machine · Extractor · Tree · Certificate
RecursionFast/Vendor/     RiscvZkvm (trusted, vendored)
RecursionFast/Library/    untrusted helpers (WitnessSending is the baseline argument)
RecursionFast/Controls/   CI controls (Backdoor is the known gap O-25)
scripts/                  harness tools: Gate.lean · AxiomAudit.lean · source-rule.py · TokenSweep.lean ·
                          olean-manifest.py · bwrap-landrun.sh · check-vendor.sh · check-hygiene.sh · loc.py · ci.sh
tests/asm/                assembled images for the controls (riscv64-unknown-elf-as -march=rv64im_zbc)
tests/source-rule/        the source rule's fixtures
docs/                     DESIGN-v3.md · DESIGN-AMENDMENTS.md · stages/V3-S<n>-RESULT.md · reviews/ · reference/
```
