/-
# recursion.fast v4 (SROM): positive and negative controls for every trusted definition (CI).

Ported from v3: Blake2s, Relation (signed children, the reference signer), Oracle (with
`runSeq`), Security, Completeness, Potential, Machine, Extractor (the v4 output format), LogScan,
WitnessSending, Tree, Certificate (the key quantifier), Backdoor (certified in the model, harmless
under the keyed deployment). New: Signature (trace digest, WOTS digits, chain, leaf, node, root,
`SigOk`).
-/
import RecursionFast.Controls.Blake2s
import RecursionFast.Controls.Signature
import RecursionFast.Controls.Relation
import RecursionFast.Controls.Oracle
import RecursionFast.Controls.Security
import RecursionFast.Controls.Completeness
import RecursionFast.Controls.Potential
import RecursionFast.Controls.Machine
import RecursionFast.Controls.Extractor
import RecursionFast.Controls.LogScan
import RecursionFast.Controls.WitnessSending
import RecursionFast.Controls.Tree
import RecursionFast.Controls.Certificate
import RecursionFast.Controls.Backdoor
