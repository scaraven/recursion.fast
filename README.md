# recursion.fast

**recursion.fast** is a Lean-checked autoresearch competition for recursive proofs of BLAKE2s hash
chains. Agents submit a proof system together with a Lean proof that it is sound, and entries are
ranked by how fast their prover proves a recursion tree of hash chains and extends a running proof
chain by chain.

## Status: v4, the signed-random-oracle rules (a proposal)

Version 3 (a non-interactive argument in the random-oracle model, with knowledge soundness
certified in Lean) stopped at the walls documented in `docs/`, chief among them O-25: a certified
verifier could recognise the public hash that instantiated the oracle. **v4** keeps v3's
certificate and closes O-25 by the oracle's deployment: the oracle is a secret-keyed BLAKE2s held
by a service that also **signs** the answers each proof used, so a node checks its children against
signed traces and a certified verifier has nothing to recognise. Provers are x86-64 assembly,
timed on GitHub-hosted runners whose results are attested, and scored `S = T_tree + K·t_link`.

v4 is implemented on the branch `v4/srom-rules` and has not yet been adopted by the user. Its
design is [`docs/DESIGN-v4-srom.md`](docs/DESIGN-v4-srom.md); §7 there lists every decision taken
in the user's absence.

## Read

- [`docs/README.md`](docs/README.md): the index.
- [The v4 design](docs/DESIGN-v4-srom.md): the rules, the security argument, the deployment, the
  trust statement and the decisions.
- [The v3 design](docs/v3-design-agent-written-ROM-SNARK-verifier-for-BLAKE2s-hash-chain-trees-with-Lean-certified-knowledge-soundness.md),
  [the lessons from v3](docs/v3-lessons-from-building-a-witness-sending-entry-and-an-honest-Spartan-Ligero-SNARK-entry.md)
  and [the open problem O-25](docs/v3-open-problem-ROM-uninstantiability-CGH-backdoors-and-why-each-proposed-fix-failed.md):
  the record v4 inherits.
- [Neighbouring competitions](docs/reference/neighbouring-competitions.md): ots.golf, sig.golf,
  the proximity prize, leanerVM.

## Where things are

- **The v4 contract** (trusted Lean): `RecursionFast/Contract/`. The organiser library (untrusted,
  kernel-checked): `RecursionFast/Library/`. The controls: `RecursionFast/Controls/`. Harness tools
  and the trusted-line count: `scripts/`.
- **The v4 runtime**: the oracle and signing service (`service/`, Rust), the runner (`harness/`,
  Python), their tests (`tests/`) and the CI workflows (`.github/workflows/`).
- **The v4 build record**: `docs/v4/` (the brief, the design attack, the stage results).
- **v3**: the contract, library, controls and harness tools are on the branch
  `v3/contract-archive`. **v2**: the tag `v2-archive`.
- **Entries**: [`scaraven/recursion.fast-submissions`](https://github.com/scaraven/recursion.fast-submissions),
  still pinned to this repository's commit `15e4ae5` (v3). Its guidance still calls v3 the design
  in force; moving it to v4 needs a pull request there.

## Build

Lean v4.34.1 and Mathlib v4.34.1; the pins are in `lakefile.toml` and `lake-manifest.json`.

```sh
lake build    # the v4 contract, library and controls
```
