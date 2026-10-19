# legacy/v2: v2 modules parked by Stage V3-S1

Stage V3-S1 (`docs/stages/V3-S1-RESULT.md`) replaced the v2 contract by the v3 contract of
`docs/DESIGN-v3.md` and deleted six v2 contract files (`Field`, `Shapes`, `Layout`, `Protocol`,
`Compile`, `Recursion`; git keeps them). The organiser library and controls modules that imported
them no longer build, so they were moved here **unchanged** (`git mv`), under their old relative
paths:

- `RecursionFast/Library/`: `Challenges`, `Codec`, `Compile`, `Extractor`, `Field`, `Layout`,
  `R1CS`, `RbrSound`, `Recursion`;
- `RecursionFast/Controls/`: `Certificate`, `Chain`, `ChainData`, `Compile`, `CompileFS`,
  `CompileToy`, `Extractor`, `FieldSpec`, `Hit`, `Layout`, `MagicKey`, `Negative`, `Recursion`,
  `RecursionData`, `RecursionNode`, `Toy`;
- `RecursionFast/Library.lean`, `RecursionFast/Controls.lean`: copies of the v2 roots (the live
  roots were rewritten for v3);
- `RecursionFast/Bridge/`, `RecursionFast/Bridge.lean` (the ArkLib bridge) and
  `RecursionFast/Clean/`, `RecursionFast/Clean.lean` (the Clean frontend bridge), moved in the
  V3-S1 fix pass (review M4); their lake targets `RecursionFastBridge`, `RecursionFastClean` and
  the `Clean` path requirement are commented out in `lakefile.toml`, deferred to S4.

This directory is **not a lake target** and nothing imports it. It is kept as source for
**Stage S4** (DESIGN-v3 §11), which re-targets what is worth keeping: v2's `Compile` shape and
`Layout` as worked examples in the library, the field facts on top of CompPoly's `BF64`/`Ext3`
(S2/S4, DESIGN-v3 §7.4), and the controls that go with them. What already moved to v3:

- the machine's symbolic-execution lemmas (v2 `Library/Extractor.lean`, section "Machine") are
  `RecursionFast/Library/Machine.lean`;
- the machine controls (v2 `Controls/Extractor.lean`: `wzbc_run`, `tape_readonly`,
  `tape_below_ok`, `halt_misaligned`, `ecall_trap`, `halt_reads`, `spin_run`) are
  `RecursionFast/Controls/Machine.lean`.

The other targets that imported v2 modules are commented out in `lakefile.toml` with the stage
that restores each: `RecursionFastCandidate` (S2; the baseline moves to the submissions
repository), `RecursionFastHarness`, `harness-linkcheck`, `RecursionFastSmoke`, `smoke-verify`,
`smoke-index` (S3).
