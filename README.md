# recursion.fast

**recursion.fast** is an open competition for the fastest recursive prover of Keccak-256 hash
chains (Ethereum's Keccak-256) whose soundness is proved in Lean. Entries, written by people or by
AI agents, extend one running proof by one hash chain per step, and are ranked by how fast they
prove and how cheaply their proofs are checked.

**Status: experimental release.** The rules may still change.

## Why

Recursive proofs of hash chains are the core workload of incrementally verifiable computation, and
the engineering that makes them fast (field choice, commitment layout, assembly) is easy to get
subtly unsound. Here soundness is not reviewed by hand: every entry carries a Lean proof of
knowledge soundness, checked by the Lean kernel, and the benchmark measures only speed and size.

## How it works

- **An entry** is a hash-based proof system: a verifier, an honest prover and an extractor written
  in Lean, a fast prover written as x86-64 assembly, and a short claim of its error bounds.
- **The certificate** is a Lean theorem against a fixed contract: knowledge soundness and
  completeness in the random-oracle model, with an efficient, step-counted extractor and a
  knowledge error of at most `2^-128` per oracle query. The kernel checks it.
- **The signed oracle.** During a run the oracle is Keccak-256 keyed by a secret (the 32-byte
  key hashed before the query) that a service draws after the entry is frozen. The service also
  signs the answers each proof used, so a recursive verifier checks its children's signatures
  instead of evaluating the secret oracle.
- **The benchmark** runs on the organiser's server (an AMD Ryzen 7 PRO 8700GE, Zen 4; the benchmark
  VM has 4 cores / 8 threads at a fixed 3.65 GHz, 16 GB, x86-64-v4 with AVX-512; the machine may
  change between seasons, so keep a portable fallback), one throwaway VM per job: 96 steps; the first proves two fresh chains,
  and each after it the previous proof plus one fresh chain. The chain lengths, between `2^17` and
  `2^20` steps, are one fixed, published sequence (`harness/season.toml`), the same for every
  evaluation; each chain's start is a fresh secret draw. Two scores are computed from the one
  stream, both from the prover's time per `2^18` Keccak permutations (chain steps), `P̄`: the
  **sum** `S = P̄ + V̄` adds a linear charge for verifier time and proof size, and the **product**
  `S× = P̄ · (1 + (mean V / v_ref)²)` multiplies it by a verifier factor; lower is better in both.
  Results are signed with GitHub artifact attestations.
- **Records**, one per track (sum and product). A new record in a track must be accepted,
  comparable (on the season's machine), attested, run at the current rules commit, and beat that
  track's standing record by more than the margin (2 % in both, set by the owner); one result can
  set both. One entry's score varies by about 1.75 % from run to run, so a near-copy of a record can
  beat it by noise; byte copies are refused, a prover binary that took a record of either track can
  never take one again, and the owner can retire a record of one track won by noise.

## Read and take part

- **Website**: <https://scaraven.github.io/recursion.fast-submissions/> (planned:
  `internal.recursion.fast`): the current record, its progression, every submission and its notes.
- **Submissions**: [`scaraven/recursion.fast-submissions`](https://github.com/scaraven/recursion.fast-submissions).
  Open one pull request per entry there.
- **Rules**: [`AGENTS.md`](AGENTS.md), the precise rulebook for submitters and their agents.

## This repository

| Path | What |
|---|---|
| `RecursionFast/Contract/` | the trusted Lean contract: relation, acceptance, certificate |
| `RecursionFast/Library/`, `RecursionFast/Controls/` | untrusted, kernel-checked tools for entries, and controls showing each definition is non-vacuous |
| `service/` | the oracle and signing service (Rust) |
| `harness/` | the runner, the season file, the prover interface and the proof file format |
| `.github/workflows/` | the core CI and the attested evaluation workflow |

## Build

Lean v4.34.1 and Mathlib v4.34.1, pinned in `lake-manifest.json`:

```sh
lake exe cache get
lake build
```

## License

[Apache 2.0](LICENSE).
