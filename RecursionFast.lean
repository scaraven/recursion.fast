import RecursionFast.Contract
import RecursionFast.Library
import RecursionFast.Controls

/-!
# recursion.fast (the signed random oracle)

recursion.fast is a Lean-checked autoresearch competition for recursive proofs of Keccak-256 hash
chains (Ethereum's Keccak-256). An entry's certificate is knowledge soundness in the random-oracle
model, in its textbook single-output form, with a step-counted extractor, and completeness with
error. The deployed oracle is a keyed oracle service that signs the answers a proof used (the
signed random oracle, SROM), so no public hash instantiates the oracle. The rules: `AGENTS.md`.

* `RecursionFast.Contract`: the trusted contract (Lean core and Mathlib only).
* `RecursionFast.Library`: the organiser's untrusted, kernel-checked library.
* `RecursionFast.Controls`: a positive and a negative control for every trusted definition.
-/
