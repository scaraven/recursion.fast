# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

The **recursion.fast v2 contract**: the trusted Lean 4 rules of an autoresearch competition in which
agents submit a hash-based SNARK over GF(2^64) for a structured constraint relation (chips + CCS +
bus), prove it knowledge-sound and complete, supply their verifier as a circuit, and are ranked by
the measured wall time of one 2→1 recursion step. Plus the organiser's untrusted library, the
positive/negative controls, the harness, and the baseline submission.

**The design is `docs/DESIGN-v3.md`. It is authoritative** (stages V3-S1 onward); `docs/DESIGN.md`
is v2, superseded. Where this repository and the design disagree, the design wins unless a stage
RESULT records an agreed deviation with its reason.

Read-only references (never edit, never build inside):

- `/home/devops/CambridgePQ/recursion.fast/contract-v03/`: the v0.3 contract this one descends from
  (its `RESULT.md` documents the harness, gate and comparator that carry over).
- `/home/devops/CambridgePQ/recursion.fast/report/sections/*.tex`: the v1.0 report (background,
  prior competitions, threat model; Appendix A lists the v0.3 contract).
- `/home/devops/CambridgePQ/recursion.fast/DISCUSSION.md`: the user's decisions Q1–Q5.
- `/home/devops/Verified-zkEVM/leanerVM/.lake/packages/Clean`: Clean at `42fe4b26` (untrusted
  frontend, design §9).

## Toolchain

Lean **v4.34.1**, Mathlib v4.34.1, ArkLib `7653a90`, CompPoly `572f997`, VCVio `a4232d0`,
PolyFun `41d3b21`. `.lake/packages` is a symlink to the prebuilt shared tree
`/home/devops/CambridgePQ/recursion.fast/contract/.lake/packages` (local-only, gitignored).

A fresh clone (S9 fix pass, measured): `scripts/setup-clean.sh [LOCAL_CLEAN_CHECKOUT]` (offline with
a local checkout, e.g. `/home/devops/Verified-zkEVM/recursion.fast/ext/Clean`), then
`mkdir -p .lake && ln -s /home/devops/CambridgePQ/recursion.fast/contract/.lake/packages .lake/packages`.
Elsewhere, `lake exe cache get` supplies Mathlib only; CompPoly's cone and Clean are then built. The
comparator and nanoda are external: set `COMPARATOR_HOME` and `COMPARATOR_NANODA` (defaults, pins and
build commands in `scripts/tools.env`; `scripts/harness.sh` stops with a message naming them when
they are missing).

Clean (`42fe4b26`) is an **untrusted** dependency of the non-default library `RecursionFastClean`
(`RecursionFast/Clean/`, design §9), required by path (`ext/Clean`, gitignored). Submissions may
import Clean's 39 modules and the bridge for their circuit proofs, never on the badge path (gate
rules 8/9). It is never imported by `Contract/`, `Library/`, `Controls/` or the harness tools.

```sh
lake build                         # default targets: 2 min 10 s cold (the kernel-evaluated controls), 3 s warm (V3-S1)
lake build gate axiomaudit         # the rest (V3-S1: Bridge, Clean, Candidate, Harness, Smoke deferred, lakefile.toml)
lake env lean RecursionFast/Controls/Layout.lean   # one file
scripts/org-build.sh .lake/org     # organiser package: ≈ 5 min 30 s cold (Clean's cone included)
scripts/ci.sh /home/devops/Verified-zkEVM/riscv-zkvm   # full CI: 15 min warm; ≈ 22 min from a fresh clone
HARNESS=1 ORG=.lake/org MANIFEST=scripts/olean-manifest.sha256 submissions/baseline/scripts/check.sh   # ≈ 6 min
python3 scripts/loc.py RecursionFast/Contract.lean RecursionFast/Contract/*.lean RecursionFast/Contract/Hash/Blake2s.lean   # trusted line budget
scripts/check-vendor.sh /home/devops/Verified-zkEVM/riscv-zkvm   # vendored Rv64 is byte-identical
```

After any change to a trusted file, regenerate `scripts/olean-manifest.sha256` from a clean
organiser build (command in `harness/README.md`); CI step 3 requires equality.

## Trust layers

| Layer | Path | Rule |
|---|---|---|
| Contract | `RecursionFast/Contract/*.lean`: `Hash/Blake2s`, `Relation`, `Oracle`, `Security`, `Machine`, `Extractor`, `Tree`, `Certificate` (v3, DESIGN-v3 §8) | **TRUSTED.** Imports Lean core, Mathlib, vendored Rv64 only; never ArkLib/CompPoly/VCVio/Clean/PolyFun. No field (V3-1). Budget ≤ 500 code lines for `Contract.lean`, `Contract/*.lean` and `Hash/Blake2s.lean` together (`scripts/loc.py`; 328 after the V3-S1 fix pass). Every definition has a docstring saying what it means, not how it is written. |
| Vendored Rv64 | `RecursionFast/Vendor/RiscvZkvm/` | **TRUSTED**, byte-identical to riscv-zkvm `6810fc1`. Never edit. |
| Library | `RecursionFast/Library/` | Untrusted, kernel-checked helpers for submitters (v3: oracle and security lemmas, machine symbolic execution, tape and output formats, the tree, the witness-sending argument; the v2 field, layout and compile library is in `legacy/v2/`). |
| Bridge | `legacy/v2/RecursionFast/Bridge/` (deferred to S4) | Untrusted bridge to ArkLib. |
| Controls | `RecursionFast/Controls/` | Positive **and** negative controls for every trusted definition; run in CI. |
| Harness | `scripts/` | Gate, axiom audit, manifest, sandbox, renderer, CI (carried over from v0.3, adapted stage by stage). |

Hard rules for anything trusted: no `sorry`; axioms only `propext`, `Classical.choice`, `Quot.sound`;
no `native_decide`, `implemented_by`, `extern`, `csimp`; statements are non-vacuous (a negative
control shows the definition can fail); a proof never changes the statement it proves.

## Stage protocol (how this repository is built)

The build order is design §11, one stage at a time. Each stage runs the same cycle:

1. **Implement** (one agent): builds the stage, keeps `lake build` green, writes
   `docs/stages/S<n>-RESULT.md`: what was built (file by file, with code line counts from
   `scripts/loc.py`), build time, the controls and what each shows, every deviation from
   `docs/DESIGN.md` with its reason, open questions for the orchestrator.
2. **Adversarial review** (one agent, in parallel with 3): spec tightness, vacuity, loopholes,
   trust policy, hygiene; writes `docs/reviews/S<n>-review.md` with numbered findings
   (`S<n>-M<i>` major: must fix; `S<n>-m<i>` minor) and a verdict.
3. **Golf** (one agent, in parallel with 2): shortens proofs and definitions without changing any
   statement; edits in place; writes `docs/reviews/S<n>-golf.md` (before/after line counts, what
   changed, anything it declined to touch and why).
4. **Fix** (the implementing agent): applies every major finding, answers each minor one (fixed or
   argued), appends `## Fix pass` to the RESULT, re-runs the build and the controls.
5. The orchestrator reads the RESULT and review, commits, and opens the next stage.

Subagents **do not commit**; the orchestrator does. Measurements go in `logs/` (gitignored) and
are quoted in the RESULT. Skills to use: `lean-spec-authoring` when writing trusted definitions or
theorem statements; `adversarial-review` and `lean4:review` when reviewing; `lean4:golf` when
golfing; `lean4:lean4` for any Lean work.

## Layout

```
RecursionFast/Contract/   Hash/Blake2s · Relation · Oracle · Security · Machine · Extractor · Tree · Certificate (v3)
legacy/v2/                v2 Library, Controls, Bridge and Clean modules that no longer build (not a lake target; S4)
RecursionFast/Vendor/     RiscvZkvm (trusted, vendored)
RecursionFast/Library/    untrusted helpers
RecursionFast/Controls/   CI controls
RecursionFast/Challenge/  challenge stubs (.lean.in) for the renderer
scripts/                  harness (Gate.lean, AxiomAudit.lean, harness.sh, ci.sh, renderer, manifest)
docs/                     DESIGN-v3.md · DESIGN.md (v2) · stages/{S<n>,V3-S<n>}-RESULT.md · reviews/
submissions/baseline/     the trivial baseline (stage 8, separate agent)
```
