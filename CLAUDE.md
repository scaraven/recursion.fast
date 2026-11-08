# CLAUDE.md

Guidance for agents working in this repository, the core of recursion.fast: the Lean contract, the
oracle service, the harness and the CI. **Read [`AGENTS.md`](AGENTS.md) first**: it is the
rulebook, and where it and the Lean text differ, the Lean text is the rule.

## Toolchain and build

Lean v4.34.1, Mathlib v4.34.1, CompPoly `572f997`, ArkLib `7653a90`, VCVio `a4232d0`, PolyFun
`41d3b21`, pinned in `lakefile.toml` and `lake-manifest.json`. The contract imports Lean core and
Mathlib only.

```sh
lake exe cache get    # Mathlib from its cache, in your own package tree
lake build            # the contract, the library and the controls
```

Never run `lake update` or change the `[[require]]` blocks. Never run `lake exe cache get` against a
shared, read-only package tree. Give every long or background build a `timeout`. Kernel evaluation
of Keccak-256 costs about 11 s per permutation through the contract's `keccakF` and about 0.4 s
through the word-level twin of `Library/KeccakFast.lean` (`keccakF_toVec`, `keccak256_eq_digestL`):
evaluate through the twin, and prove properties symbolically.

## Hard rules for editing this repository

- **Axioms**: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.
- **No code-changing attributes** (`implemented_by`, `extern`, `export`, `init`, `csimp`, `cpass`,
  `computed_field`); no `unsafe`, `partial` or `opaque`.
- **Controls**: every trusted definition has a positive and a negative control in
  `RecursionFast/Controls/`, so no statement is vacuous.
- **A proof never changes the statement it proves.**
- **Trusted-line budget**: the contract (`RecursionFast/Contract*`) is at most 500 code lines, counted
  by `scripts/loc.py` and checked in CI. Every trusted definition has a docstring saying what it
  means.
- **Byte layouts are normative**: the contract, the service and the runner hash the same bytes; a
  change to one is a change to all three and to their tests.
- **The keys never leave the service**: the PRF key and the signing seed are independent draws,
  never written or logged, destroyed at exit. Untrusted code, an entry's Lean build included, runs
  only inside the sandbox.
- A change to the contract, the harness or the service is a new rules commit: the submissions
  repository moves its pin to it in its own commit.
