# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

**recursion.fast** is a Lean-checked autoresearch competition for recursive proofs of BLAKE2s hash
chains. Version 3 (a non-interactive argument in the random-oracle model with Lean-certified
knowledge soundness) hit a wall, and the project is in an **ideation phase**.

**The product right now is the design documents in `docs/`.** Start at `docs/README.md`: it indexes
the v3 design, the lessons from building entries against it, and the open problem that stopped it.
`docs/reference/` holds the survey of neighbouring competitions and its notes. The Lean library
`RecursionFast.lean` is an empty skeleton: a module docstring and nothing else.

## Where things are

- **v3 code:** the contract, the organiser library, the controls and the harness tools (gate, source
  rule, axiom audit, olean manifest, sandbox shim, line budget, CI) are on the branch
  `v3/contract-archive`, together with the original v3 design, its amendment ledger and the stage
  records and reviews (`docs/DESIGN-v3.md`, `docs/DESIGN-AMENDMENTS.md`, `docs/stages/`,
  `docs/reviews/`) that the documents in `docs/` were compiled from.
- **v2:** the tag `v2-archive` (`git show v2-archive:<path>`).
- **Entries:** https://github.com/scaraven/recursion.fast-submissions, which pins this repository
  at `15e4ae5` as its `.contract` submodule. Its code still builds against that pin, but its own
  guidance (`CLAUDE.md`, `AGENTS.md`, `docs/`) still calls v3 the design in force; a follow-up
  pull request there must say v3 is frozen.
- **Read-only references** (never edit, never build inside): the design workspace
  `/home/devops/CambridgePQ/recursion.fast/` (`DISCUSSION.md` holds the user's decisions Q1–Q6;
  `report/sections/*.tex` is the v1.0 report). Its `design/DESIGN-v3-narg-rom.md` is the
  unpatched v3 master: it predates the KS amendment (PR #11) and the rules stage V3-S2R. The three
  `docs/v3-*.md` documents here supersede it.

Finding and decision ids (V3-n, O-n, S<n>-A<k>, …) are cross-referenced across the documents and
resolve on the archive branch or tag. Keep them when you quote.

## Toolchain

Lean **v4.34.1**, Mathlib v4.34.1, CompPoly `572f997`, ArkLib `7653a90`, VCVio `a4232d0`, PolyFun
`41d3b21`, pinned in `lakefile.toml` and `lake-manifest.json` for the next design. Nothing imports
them yet.

```sh
mkdir -p .lake && ln -s /home/devops/CambridgePQ/recursion.fast/contract/.lake/packages .lake/packages   # local only
lake build    # the empty skeleton
```

**The shared package tree is read-only.** Never run `lake update` or `lake exe cache get` against
it, and do not change the `[[require]]` blocks or the manifest, since that needs `lake update`.
Elsewhere, `lake exe cache get` supplies Mathlib. Give every build that runs in the background or
under a shared lock a `timeout`.

## Hard rules (when implementation resumes)

- **Axioms:** only `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, no `native_decide`.
- **No code-changing attributes:** `implemented_by`, `extern`, `export`, `init`, `csimp`, `cpass`,
  `computed_field`. **No `unsafe`, `partial` or `opaque`.**
- **Controls:** every trusted definition has a positive **and** a negative control, so a statement
  is shown to be non-vacuous.
- **A proof never changes the statement it proves.**
- **Trusted-line budgets:** the trusted base has a code-line budget, fixed by the design and checked
  in CI (v3: the contract was capped at 500 code lines).
- Every trusted definition has a docstring saying what it means, not how it is written.

## Stage protocol (when implementation resumes)

Work is built one stage at a time, each on a branch merged by pull request:

1. **Implement** (one agent): build the stage, keep `lake build` green, and write a RESULT (what was
   built, line counts, build times, the controls, deviations from the design, open questions).
2. **Adversarial review** and **golf** (two agents, in parallel): the review writes numbered findings
   (major: must fix; minor) and a verdict; the golf shortens proofs without changing any statement.
3. **Fix** (the implementing agent): apply every major finding, answer each minor one, re-run the
   build and the controls.
4. **Commit** (the orchestrator).

Subagents **do not commit**; the orchestrator does. Skills: `lean-spec-authoring` for definitions
and statements; `adversarial-review` and `lean4:review` for review; `lean4:golf` for golfing;
`lean4:lean4` for any Lean work.

## General

- **Never push**, and never create remotes or GitHub repositories, unless the user asks.
- **No time estimates.** Describe work by what it consists of and what it depends on. Durations
  that were measured, such as a build time, are facts: quote them with their log under `logs/`
  (gitignored).
