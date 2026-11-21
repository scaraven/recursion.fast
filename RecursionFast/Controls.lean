/-
# recursion.fast: positive and negative controls for every trusted definition (CI)

Keccak (known answers and FIPS 202's constants) · Relation (signed children, the reference
signer) · Oracle (with `runSeq`) · Security · Completeness · Potential · Machine · Extractor (the
output format) · LogScan · MaskedLeaf (a certified verifier that asks the oracle, extracted from
the log: the satisfiability control for log-based extraction) · WitnessSending · Tree · Certificate (the key quantifier) · Backdoor
(certified in the model, harmless under the keyed deployment) · Unforgeability (the forgery
events and the service's signed traces) · Compose (the composition walks over trees and the
stream, their reduction to EUF-CMA and collisions, and their probability) · Signature (trace
digest, WOTS digits, chain, leaf, node, root, `SigOk`) · WotsReduce (EUF-CMA reduced to a
collision or a chain inversion: reached by a forger that knows the key, unsatisfiable by revealed
values or with two messages at one index; reached through the composition walks).
Security holds the direct controls of the textbook `KS`; Security and Potential hold the
potential controls as facts about the library's `KState`.
-/
import RecursionFast.Controls.Keccak
import RecursionFast.Controls.Signature
import RecursionFast.Controls.Relation
import RecursionFast.Controls.Oracle
import RecursionFast.Controls.Security
import RecursionFast.Controls.Completeness
import RecursionFast.Controls.Potential
import RecursionFast.Controls.Machine
import RecursionFast.Controls.Extractor
import RecursionFast.Controls.LogScan
import RecursionFast.Controls.MaskedLeaf
import RecursionFast.Controls.WitnessSending
import RecursionFast.Controls.Tree
import RecursionFast.Controls.Certificate
import RecursionFast.Controls.Backdoor
import RecursionFast.Controls.Unforgeability
import RecursionFast.Controls.Compose
import RecursionFast.Controls.WotsReduce
