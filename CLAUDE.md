# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

**recursion.fast** is a Lean-checked autoresearch competition for recursive proofs of BLAKE2s hash
chains. Version 3 (a non-interactive argument in the random-oracle model with Lean-certified
knowledge soundness) hit a wall at O-25: a certified verifier could recognise the public hash that
instantiated the oracle. **Version 4 (the signed random oracle, SROM)** is the current proposal,
implemented on the branch `v4/srom-rules` and not yet adopted by the user.

v4 keeps v3's certificate (knowledge soundness and completeness in the random-oracle model, the
step-counted extractor), states knowledge soundness in its textbook single-output form (V4-A10;
v3's potential `KState` is an untrusted library route to it, `KState.ks`), and changes the
oracle's deployment: a service holds a secret BLAKE2s key and signs the answers each proof used,
every proof is a signed proof `(π, tr, σ)`, and the one trusted predicate `acc` (the node clause,
the harness's check and third parties' check) runs the verifier on the signed trace and checks the
signature. Provers are x86-64 assembly, timed on GitHub-hosted runners with attested results, and
scored `S = T_tree + K·t_link`.

**Start at `docs/DESIGN-v4-srom.md`** (the normative design; §0 is the summary, §6 the decisions
taken in the user's absence), then `docs/README.md` for the record it inherits. Where the design
and the Lean text differ, the Lean text is the rule and the design has a bug.

## Where things are

- **v4 contract** (trusted): `RecursionFast/Contract/` (`Contract.lean` lists it in reading order).
  Budget 500 code lines, counted by `scripts/loc.py`.
- **v4 library and controls** (untrusted, kernel-checked): `RecursionFast/Library/` (the potential
  `KState` and its bridge `KState.ks`, the calculus of `prob` and the union bound, `runSeq →
  runLog`, the Lean reference signer, the composition walk and its probability, the word-level
  BLAKE2s twin, the witness-sending entry) and `RecursionFast/Controls/`.
- **v4 runtime** (trusted, tested not proved): the oracle and signing service `service/` (Rust;
  its wire protocol `service/PROTOCOL.md` is normative for provers), the runner `harness/`
  (Python), `tests/`, the CI workflows `.github/workflows/`.
- **v4 build record:** `docs/v4/BRIEF.md` (the brief and the amendments V4-A1 … A10),
  `docs/v4/reviews/` (the design attack), `docs/v4/stages/` (the stage RESULTs).
- **v3 code:** the contract, the organiser library, the controls and the harness tools are on the
  branch `v3/contract-archive`, together with the original v3 design, its amendment ledger and the
  stage records and reviews that the `docs/v3-*.md` documents were compiled from.
- **v2:** the tag `v2-archive` (`git show v2-archive:<path>`).
- **Entries:** https://github.com/scaraven/recursion.fast-submissions. Its branch
  `v4/flock-baseline` pins this repository at `81e1ebf` as the `.contract` submodule, with the
  v4 rulebook (`AGENTS.md`) and the certified baseline `spartan-srom`; its `main` still pins `15e4ae5` (v3) until that branch is merged. The pin moves
  only to a core commit on the remote, in its own commit (C14).
- **Read-only references** (never edit, never build inside): the design workspace
  `/home/devops/CambridgePQ/recursion.fast/` (`DISCUSSION.md` holds the user's decisions Q1–Q6;
  `report/sections/*.tex` is the v1.0 report). Its `design/DESIGN-v3-narg-rom.md` is the
  unpatched v3 master: it predates the KS amendment (PR #11) and the rules stage V3-S2R. The three
  `docs/v3-*.md` documents here supersede it.

Finding and decision ids (V3-n, O-n, RR-n, CM-n, V4-n, V4-An, C-Mn, S<n>-A<k>, …) are
cross-referenced across the documents and resolve on the archive branch or tag or in `docs/v4/`.
Keep them when you quote.

## Toolchain

Lean **v4.34.1**, Mathlib v4.34.1, CompPoly `572f997`, ArkLib `7653a90`, VCVio `a4232d0`, PolyFun
`41d3b21`, pinned in `lakefile.toml` and `lake-manifest.json`. The contract imports Lean core and
Mathlib only.

```sh
mkdir -p .lake && ln -s /home/devops/CambridgePQ/recursion.fast/contract/.lake/packages .lake/packages   # local only
lake build    # the v4 contract, library and controls
```

**The shared package tree is read-only.** Never run `lake update` or `lake exe cache get` against
it, and do not change the `[[require]]` blocks or the manifest, since that needs `lake update`.
Elsewhere, `lake exe cache get` supplies Mathlib. Give every build that runs in the background or
under a shared lock a `timeout`.

Kernel evaluation of BLAKE2s costs about 2.4 s per compression: controls evaluate few hashes and
prove properties symbolically (one signature check is about 300 compressions).

## Hard rules

- **Axioms:** only `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, no `native_decide`.
- **No code-changing attributes:** `implemented_by`, `extern`, `export`, `init`, `csimp`, `cpass`,
  `computed_field`. **No `unsafe`, `partial` or `opaque`.**
- **Controls:** every trusted definition has a positive **and** a negative control, so a statement
  is shown to be non-vacuous.
- **A proof never changes the statement it proves.**
- **Trusted-line budgets:** the contract is capped at 500 code lines (`scripts/loc.py`), checked
  in CI.
- Every trusted definition has a docstring saying what it means, not how it is written.
- **The byte layouts are normative** (design §1.3): the contract, the service and the runner hash
  the same bytes, and a change to one is a change to all three and to their tests.
- **The keys never leave the service:** the PRF key and the signing seed are independent draws,
  never written, never logged, destroyed at exit; untrusted code (an entry's Lean build included)
  runs only inside the sandbox.

## Stage protocol

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
- **Evidence tags** in documents: **kernel** (with the theorem name), **paper**, **measured** (with
  its log), **estimate**.
