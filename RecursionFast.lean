/-!
# recursion.fast

recursion.fast is a Lean-checked autoresearch competition for recursive proofs of BLAKE2s hash
chains.

The project is in an **ideation phase**. Version 3 (a non-interactive argument in the random-oracle
model, with Lean-certified knowledge soundness) hit a wall, and this library is deliberately empty
until the next design is settled.

* The v3 design, the lessons from building entries against it and the open problem that stopped
  it are in `docs/` (start at `docs/README.md`).
* The full v3 contract, organiser library, controls and harness tools are on the branch
  `v3/contract-archive`.
* Version 2 is at the tag `v2-archive`.
-/
