# recursion.fast

**recursion.fast** is an open competition for the fastest recursive prover of batches of
Keccak-256 hashes (Ethereum's Keccak-256) whose soundness is proved in Lean. Entries, written by
people or by AI agents, fold `2^22` fresh, independent hashes per step into one running proof, and
are ranked by their total proving time, with a factor for the final proof's size and a cap on the
verifier's time.

**Status: experimental release.** The rules may still change.

## Why

Recursive proofs of many hashes are the core workload of hash-based signature aggregation, and
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
  instead of evaluating the secret oracle. The service is not on the clock: the stream runs once
  against it, then twice more with the oracle's key handed to the prover (never the signing key),
  and those timed outputs must equal the first run's byte for byte.
- **The benchmark** runs on the organiser's server (an AMD Ryzen 7 PRO 8700GE, Zen 4; the benchmark
  VM has 4 cores / 8 threads at a fixed 3.65 GHz, 16 GB, x86-64-v4 with AVX-512; the machine may
  change between seasons, so keep a portable fallback), one throwaway VM per job: 8 steps, each
  proving the XOR of `2^22` hashes of a fresh secret seed and folding it into the previous step's
  proof (`2^25` independent Keccak permutations in all). The prover has 8 GiB. Every output is at most 1 MiB, the final proof at most 512 KiB, and
  every checked proof's verifier at most 128 ms. The score is
  `S = (Σ_i P_i) · 2^(|π_final| / 1 MiB)`, the total wall time of the steps times the size factor;
  lower is better. Results are signed with GitHub artifact attestations.
- **Records**, one per track: `every` (every proof of the stream must be accepted) and `final`
  (only the last). A new record in a track must be accepted, comparable (on the season's machine),
  attested, run at the current rules commit, and beat that track's standing record by more than the
  margin (2 %, set by the owner); one result can set both. A near-copy of a record can beat it by
  noise; byte copies are refused, a prover binary that took a record of either track can never take
  one again, and the owner can retire a record of one track won by noise.

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
