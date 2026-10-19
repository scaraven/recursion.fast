/-
# Contract: what a submission is and what its record certifies                     (TRUSTED)

DESIGN-v3 §3.2, V3-2, V3-6. A submission is a non-interactive argument in the random-oracle
model: the verifier `V` and the honest prover `P` as query programs over bytes, the extractor's
specification `E` and its RISC-V image, and three declared numbers. Its **certificate** is
knowledge soundness for the relation of its own instantiated verifier `Vb`, perfect completeness,
the image computing `E`, and the caps. The self-application `Rel S.Vb` happens here, in a
statement about a given submission, so no definition is circular. The knowledge content is the
named extractor `E` with its image and budget; `KState` alone excludes little (`Security.lean`).

**Instantiation (V3-6).** The harness runs `Vb`: `V` with the oracle `q ↦ BLAKE2s-256(tagRO ‖ q)`
(`blake2sOracle`, tag in `Relation.lean`), rejecting proofs above `proofCap`. The theorem is for
every oracle function; that BLAKE2s instantiates it is the heuristic of DESIGN-v3 §5.4. **Known
gap (O-25, V3-S1-A23):** the certificate does not exclude a `V` that computes `blake2sOracle`
itself and accepts a magic proof when the oracle agrees; such a submission is certified
(`Controls/Backdoor.lean`). Until O-25 is resolved, a rule and review of `V` at intake exclude it.

**Rendering (v2's pattern, S5-A13, S9-A41).** A challenge renders the claim as organiser data
(`Declared`): the extractor image as a literal from the submitted files, and the declared error,
query bound and fuel. `CertificateR` ("the certificate against the rendered claim") binds them:
the image is the rendered one, the submission's numbers are within the declared ones, and the
declared fuel is within the budget, so the harness may run the image with it (V3-S1-A10, A21).
Everything else a record states is measured by the benchmark run, not proved.
-/
import RecursionFast.Contract.Security
import RecursionFast.Contract.Extractor

open scoped NNReal

namespace RecursionFast

/-- **A submission**: verifier, honest prover, extractor specification and image, and the declared
error, verifier query bound and extractor fuel. -/
structure Submission where
  /-- The verifier: a query program deciding a proof for a statement. -/
  V : Digest → Proof → OProg Bool
  /-- The honest prover: a query program computing a proof from a statement and a witness. -/
  P : Digest → Wit → OProg Proof
  /-- The extractor's specification: a witness from a statement, a proof and a query log. -/
  E : Digest → Proof → Log → Option Wit
  /-- The extractor as a RISC-V image (decision Q1). -/
  img : Image
  /-- The knowledge error per fresh oracle query. -/
  ε : ℝ≥0
  /-- The bound on the verifier's oracle queries. -/
  qV : ℕ
  /-- The image's step budget, as a function of the input tape's length in words. -/
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
  /-- Perfect completeness of the honest prover, for every oracle function. -/
  complete : Complete (Rel S.Vb) S.P S.V
  /-- The image computes the extractor within the fuel. -/
  computes : ImageComputes S.img S.E S.fuel
  /-- The caps: error at most `2^-128`, at most `2^16` verifier queries, fuel within the budget
  `B`, image within `imageCap` bytes. -/
  cap : S.ε ≤ errorCap ∧ S.qV ≤ 2 ^ 16 ∧ (∀ t, S.fuel t ≤ extractorBudget t) ∧
    S.img.byteSize ≤ imageCap

/-- **The declared claim**, rendered from the claim file. -/
structure Declared where
  /-- The extractor image, a literal rendered from the submitted files. -/
  img : Image
  /-- The declared knowledge error per fresh query. -/
  ε : ℝ≥0
  /-- The declared verifier query bound. -/
  qV : ℕ
  /-- The declared extractor fuel, as a function of the input tape's length in words. -/
  fuel : ℕ → ℕ

/-- **The certificate against the rendered claim**: the certificate, the submission's image is the
rendered one, its error, query bound and fuel are within the declared ones, and the declared fuel
is within the budget. -/
structure CertificateR (D : Declared) (S : Submission) : Prop extends Certificate S where
  /-- The extractor image is the rendered literal. -/
  img : S.img = D.img
  /-- The submission's numbers are within the declared ones; the declared fuel within the budget. -/
  bounds : S.ε ≤ D.ε ∧ S.qV ≤ D.qV ∧ ∀ t, S.fuel t ≤ D.fuel t ∧ D.fuel t ≤ extractorBudget t

end RecursionFast
