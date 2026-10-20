# recursion.fast

The trusted core of **recursion.fast**, a Lean-checked autoresearch competition. An entry is a
non-interactive argument in the random-oracle model: a verifier `V` and an honest prover `P`
written as Lean query programs over bytes, an extractor `E` with a program of the contract's
step-counting word language that computes it within a proved step bound, and a Lean proof that `V`
is knowledge-sound and `P` complete with error at most `2^-128` for the one relation of the
competition (a 32-byte digest commits to a Blake2s hash chain, or to two child digests whose
proofs `V` accepts). Entries are ranked by the measured wall time of their native prover proving
a whole recursion tree of hash chains on one reference machine.

This repository holds **no entry**. It is the trusted half of the two-repository model of ots.golf
(design §7.7, decision V3-12):

- **This repository, the trusted core.** The Lean contract (`RecursionFast/Contract/`), the
  organiser's untrusted library and controls, the harness tools (gate,
  source rule, axiom audit) and the design.
- **[`scaraven/recursion.fast-submissions`](https://github.com/scaraven/recursion.fast-submissions),
  untrusted.** One root per entry, the baseline first; the registry `records.json`; a `.contract`
  submodule pinned to a commit of this repository; and the rules a submitter reads (`AGENTS.md`).
  Entries enter by pull request there, never here.

## Where to read

- The design in force: [`docs/DESIGN-v3.md`](docs/DESIGN-v3.md) (§1 the pitch, §2 the relation,
  §4 security, §6 scoring, §8 the trusted base, §11 the build order, §12 open items); the ledger
  of agreed changes, [`docs/DESIGN-AMENDMENTS.md`](docs/DESIGN-AMENDMENTS.md).
- Stage records: [`docs/stages/`](docs/stages/) and [`docs/reviews/`](docs/reviews/).
- The roadmap and tracker: [issue #1](https://github.com/scaraven/recursion.fast/issues/1).
- Neighbouring competitions (ots.golf, sig.golf, the proximity prize, leanerVM):
  [`docs/reference/neighbouring-competitions.md`](docs/reference/neighbouring-competitions.md).
- Guidance for agents and the stage protocol: [`CLAUDE.md`](CLAUDE.md).

## Build

Lean v4.34.1 and Mathlib v4.34.1; the pins are in `lakefile.toml`.

```sh
lake build                    # contract, library, controls (kernel-checked positive and negative controls)
lake build gate axiomaudit    # the harness tools
lake exe axiomaudit           # every declaration within propext, Classical.choice, Quot.sound
scripts/ci.sh                 # the above plus hygiene, the source rule and the line budget
```

## Layout

| Path | What | Trust |
|---|---|---|
| `RecursionFast/Contract/` | the contract: `Hash/Blake2s`, `Relation`, `Oracle`, `Security`, `Machine`, `Extractor`, `Tree`, `Certificate` | trusted; 288 code lines, budget 500 |
| `RecursionFast/Library/` | kernel-checked helpers for submitters, including the witness-sending argument | untrusted |
| `RecursionFast/Controls/` | positive and negative controls for every trusted definition, including the known gap O-25 (`Backdoor.lean`) | untrusted, run in CI |
| `scripts/` | the gate, the source rule, the axiom audit, the manifest tool, the sandbox shim, the line budget, CI, the kernel pins (`tools.env`) | harness tools |
| `tests/` | the source rule's fixtures | |
| `docs/` | the design, its ledger, the stage records, the references | |

## Status

Stage V3-S1, the contract and its controls, is on `main`. Next, per design §11 and issue #1: S2
the baseline (in the submissions repository), S3 the harness, S4 the library, S7 the intake.
Stage V3-S2R (the rules handoff: the extractor as a step-bounded program, completeness with error,
gate rule 4, library fixes) is built on branch `v3/rules-handoff`, on top of PR #11.

The v2 contract, harness, probes, baseline, design and stage records were removed from the tree
after S1 landed. Git keeps them at the tag `v2-archive` (for example
`git show v2-archive:docs/DESIGN.md`); design §10 lists what v3 carries over.
