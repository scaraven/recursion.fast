# recursion.fast v2

Trusted Lean 4 contract, organiser library, controls, harness and baseline for the recursion.fast
autoresearch competition: hash-based SNARKs over GF(2^64) for a chips + CCS + bus relation, with
verifier-as-circuit recursion and wall-time scoring.

- Design: [`docs/DESIGN.md`](docs/DESIGN.md) (authoritative).
- Agent guidance and stage protocol: [`CLAUDE.md`](CLAUDE.md).
- Toolchain: Lean v4.34.1, Mathlib v4.34.1 (see `lakefile.toml` for the pins). `lake build`.

Status: under construction, stage by stage (`docs/stages/`). Descends from the v0.3 contract in
`CambridgePQ/recursion.fast/contract-v03` (`Field`, `Shapes`, `Security` and the vendored Rv64 are
carried over verbatim).
