/-
# Contract: what a submission is and what its record certifies                     (TRUSTED)

DESIGN-v3 §3.2, V3-2, V3-6, amended by V3-S2R-A1 … A3. A submission is a non-interactive argument
in the random-oracle model: the verifier `V` and the honest prover `P` as query programs over
bytes, the extractor's specification `E` and its program `ext` on the contract's step-counting
machine, and four declared numbers. Its **certificate** is knowledge soundness for the relation of
its own instantiated verifier `Vb`, completeness with error `δ` over a random oracle, the program
computing `E` within its fuel, and the caps. The self-application `Rel S.Vb` happens here, in a
statement about a given submission, so no definition is circular. The knowledge content is the
named extractor `E` with its program and budget; `KState` alone excludes little
(`Security.lean`).

**Instantiation (V3-6).** The harness runs `Vb`: `V` with the oracle `q ↦ BLAKE2s-256(tagRO ‖ q)`
(`blake2sOracle`, tag in `Relation.lean`), rejecting proofs above `proofCap`. The theorems are for
a random oracle; that BLAKE2s instantiates it is the heuristic of DESIGN-v3 §5.4. Completeness
over a random oracle does not imply that honest proofs verify under BLAKE2s: the harness checks
that concretely (V3-S2R-H-M4). **Known gap (O-25, V3-S1-A23):** the certificate does not exclude a
`V` that computes `blake2sOracle` itself and accepts a magic proof when the oracle agrees; such a
submission is certified (`Controls/Backdoor.lean`). Until O-25 is resolved, a rule and review of
`V` at intake exclude it.

**Rendering (v2's pattern, S5-A13, S9-A41).** A challenge renders the claim as organiser data
(`Declared`): the declared knowledge error, completeness error, query bound and fuel.
`CertificateR` ("the certificate against the rendered claim") binds them: the submission's numbers
are within the declared ones, and the declared fuel is within the budget, so the harness may run
the program with it (V3-S1-A10, A21). The program is not rendered: it is a term of the submission,
executed by the compiled contract interpreter (gate rule 4 lists `ext`, V3-S2R-A3). Everything
else a record states is measured by the benchmark run, not proved.
-/
import RecursionFast.Contract.Security
import RecursionFast.Contract.Extractor

open scoped NNReal

namespace RecursionFast

/-- **A submission**: verifier, honest prover, extractor specification and program, and the
declared knowledge error, completeness error, verifier query bound and extractor fuel. -/
structure Submission where
  /-- The verifier: a query program deciding a proof for a statement. -/
  V : Digest → Proof → OProg Bool
  /-- The honest prover: a query program computing a proof from a statement and a witness. -/
  P : Digest → Wit → OProg Proof
  /-- The extractor's specification: a witness from a statement, a proof and a query log. -/
  E : Digest → Proof → Log → Option Wit
  /-- The extractor as a program of the contract's machine. -/
  ext : XProg
  /-- The knowledge error per fresh oracle query. -/
  ε : ℝ≥0
  /-- The completeness error. -/
  δ : ℝ≥0
  /-- The bound on the verifier's oracle queries. -/
  qV : ℕ
  /-- The program's step budget, as a function of the input tape's length in words. -/
  fuel : ℕ → ℕ

/-- The oracle as the harness instantiates it: BLAKE2s-256 of `tagRO ‖ q`. -/
def blake2sOracle (q : ByteArray) : Digest := blake2sDigest (tagRO :: q.data.toList)

/-- **The instantiated verifier**: `V` with the BLAKE2s oracle, rejecting every proof longer than
`proofCap`. The relation and the harness use this function. -/
def Submission.Vb (S : Submission) (c : Digest) (π : Proof) : Bool :=
  if π.size ≤ proofCap then (S.V c π).run blake2sOracle else false

/-- **The certificate** of a submission (DESIGN-v3 §3.2). -/
structure Certificate (S : Submission) : Prop where
  /-- Knowledge soundness for the relation of the submission's own instantiated verifier. -/
  secure : KS (Rel S.Vb) S.V S.E S.ε S.qV
  /-- Completeness of the honest prover with error `δ` over a random oracle. -/
  complete : CompleteWithError (Rel S.Vb) S.P S.V S.δ
  /-- The program computes the extractor within the fuel. -/
  computes : Computes S.ext S.E S.fuel
  /-- The caps: both errors at most `2^-128`, at most `2^16` verifier queries, fuel within the
  budget `B`, the program within `progCap` statements. -/
  cap : S.ε ≤ errorCap ∧ S.δ ≤ completenessCap ∧ S.qV ≤ 2 ^ 16 ∧
    (∀ t, S.fuel t ≤ extractorBudget t) ∧ S.ext.body.size ≤ progCap

/-- **The declared claim**, rendered from the claim file. -/
structure Declared where
  /-- The declared knowledge error per fresh query. -/
  ε : ℝ≥0
  /-- The declared completeness error. -/
  δ : ℝ≥0
  /-- The declared verifier query bound. -/
  qV : ℕ
  /-- The declared extractor fuel, as a function of the input tape's length in words. -/
  fuel : ℕ → ℕ

/-- **The certificate against the rendered claim**: the certificate, the submission's errors,
query bound and fuel are within the declared ones, and the declared fuel is within the budget. -/
structure CertificateR (D : Declared) (S : Submission) : Prop extends Certificate S where
  /-- The submission's numbers are within the declared ones; the declared fuel within the budget. -/
  bounds : S.ε ≤ D.ε ∧ S.δ ≤ D.δ ∧ S.qV ≤ D.qV ∧
    ∀ t, S.fuel t ≤ D.fuel t ∧ D.fuel t ≤ extractorBudget t

end RecursionFast
