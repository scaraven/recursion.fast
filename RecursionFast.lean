import RecursionFast.Contract
import RecursionFast.Library
import RecursionFast.Controls

/-!
# recursion.fast v4 (SROM)

recursion.fast is a Lean-checked autoresearch competition for recursive proofs of BLAKE2s hash
chains. Version 4 keeps v3's model (knowledge soundness in the random-oracle model, a
step-counted extractor, completeness with error), states knowledge soundness in its textbook
single-output form (V4-A10; v3's potential is a library route to it), and replaces "BLAKE2s
instantiates the oracle" by a keyed oracle service that signs the answers a proof used (the
signed random oracle, SROM). The working brief is `docs/v4/BRIEF.md`.

* `RecursionFast.Contract`: the trusted contract (Lean core and Mathlib only).
* `RecursionFast.Library`: the organiser's untrusted, kernel-checked library.
* `RecursionFast.Controls`: a positive and a negative control for every trusted definition.

Version 3 is on the branch `v3/contract-archive`; version 2 at the tag `v2-archive`.
-/
