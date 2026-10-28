/-
# Contract: what a submission is and what its record certifies                     (TRUSTED)

DESIGN-v3 §3.2 (V3-2, V3-6, V3-S2R-A1 … A3), changed for the signed random oracle (docs/v4/
BRIEF.md §2, §4.1; V4-1, V4-6, V4-7). A submission is a non-interactive argument in the
random-oracle model: the verifier `V` and the honest prover `P` as query programs that also take
the **public key** `vk` of the deployment's signer, the extractor's specification `E` and its
program `ext` (neither takes `vk`, V4-6), and four declared numbers.

**Acceptance (`acc`, V4-7, V4-A3, RA-M2, V4-A11).** A signed proof `(π, tr, σ)` is accepted for
the statement `c` under `vk` when the length of `π` fits a 64-bit word, `tr` has at most `qV`
entries (the submission's declared query bound), every query of `tr` at most `queryCap` bytes,
`σ` signs the trace's digest under `vk` (`SigOk`, `traceDigest`), and `V vk c π` returns `true`
with its queries answered in order by `tr`, used up exactly (`OProg.runSeq`). The conjuncts are in
order of cheapest rejection (C-m5); compiled `&&` stops at the first `false`.
This one predicate is the node clause of the relation, the harness's check of every proof it is
given (the root, the samples, the canaries, the stream), and the check any third party runs later
with the published `vk`. It never evaluates the oracle and needs no service.

**The certificate (V4-1).** Knowledge soundness for the relation of the submission's own `acc`,
completeness with error `δ` over a random oracle, the program computing `E` within its fuel, and
v3's caps, the first two **for every public key**. The self-application `Rel (S.acc vk)` happens
here, in a statement about a given submission, so no definition is circular. The knowledge
content is the named extractor `E` with its program and budget (`Security.lean`).
* *Why every key.* The signer is not in the model. The quantifier lets the theorem's adversary
  hold the secret key, so a verifier that accepts what carries a valid signature is not
  certifiable (`Controls/Certificate.lean`, `sigTrust_no_certificate`), and a certificate never
  rests on unforgeability. Unforgeability is used once, outside the certificate: the composition
  argument across the tree (`Library/Compose.lean`, V4-8) returns a forgery when a signed trace in
  the extraction tree is not in the run's one oracle log.
* *Why the trace is used up exactly and its queries capped (V4-A3, C-M3).* Completeness is
  required for every witness of the relation, and a node witness carries its children's traces.
  If a trace could carry entries after the verifier's last query, or queries of any length, the
  relation would have witnesses of every size, which no prover sized for its verifier's queries
  can prove (a node circuit hashes the whole trace to check its signature), and no recursive
  entry, the witness-sending one included, would be complete. Used up exactly, the trace of an
  accepted child is the verifier's query sequence on that trace's answers; `acc` itself bounds it
  by `qV` entries of at most `queryCap` bytes, so the witness space is bounded by a fact of the
  relation, and `traceDigest` is injective on it (`enc64 |q|` is exact). `KS`'s query bound does
  not give this: it ranges over oracle functions, and a non-functional trace follows no
  function's path (RA-M2; a functional trace, such as every trace the service signs, meets it by
  `Library/Trace.lean`'s `runSeq_length_le`).
* *Why no proof cap, and why the word (V4-A11).* v4 capped `π` at `2^20` bytes; V4-A11 removed
  the cap: a proof's size is priced by the benchmark's score, a recursive entry's own `V` bounds
  the children it accepts, and the deployment reads no signed file above 64 MiB. What stays is
  that `|π|` fits a word, as every length the extractor's output and the node encodings carry
  does. Completeness is required for every witness, so an entry's accepted proofs are closed
  under forming a node of two of them; without the word bound, the relation would hold children
  of `2^64` bytes or more, whose length no 64-bit length field writes, and no entry whose node
  proofs grow (the witness-sending one) could be complete.

**Deployment (V4-2, V4-3).** The harness's service answers queries with BLAKE2s-256 keyed by a
secret drawn after `V` is frozen, and signs the trace of each `sign` request; `vk` is published
per run. The theorems are for a random oracle. Completeness over a random oracle does not imply
that honest proofs pass `acc` under the deployment: the harness checks that concretely
(V3-S2R-H-M4). v3's known gap O-25 (a certified `V` that computes the deployed oracle) is closed
by the deployment, not by this file: such a `V` is still certified (`Controls/Backdoor.lean`), but
no public function it can compute is the keyed oracle.

**Rendering (v2's pattern, S5-A13, S9-A41; unchanged).** A challenge renders the claim as
organiser data (`Declared`): the declared knowledge error, completeness error, query bound and
fuel. `CertificateR` binds them: the submission's numbers are within the declared ones, and the
declared fuel is within the budget, so the harness may run the program with it (V3-S1-A10, A21).
The program is not rendered: it is a term of the submission, executed by the compiled contract
interpreter (V3-S2R-A3). Everything else a record states is measured by the benchmark run.
-/
import RecursionFast.Contract.Security
import RecursionFast.Contract.Extractor

open scoped NNReal

namespace RecursionFast

/-- **A submission**: verifier and honest prover (each given the signer's public key), extractor
specification and program, and the declared knowledge error, completeness error, verifier query
bound and extractor fuel. -/
structure Submission where
  /-- The verifier: a query program deciding a proof for a statement, given the public key. -/
  V : Digest → Digest → Proof → OProg Bool
  /-- The honest prover: a query program computing a proof from the public key, a statement and
  a witness. -/
  P : Digest → Digest → Wit → OProg Proof
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

/-- **Acceptance of a signed proof** for the statement `c` under the public key `vk`: the proof's
length fits a 64-bit word, the trace has at most `qV` entries and its queries are within
`queryCap`, the signature on the trace's digest verifies, and the verifier accepts the proof on
the trace's answers in order, using them all. The relation, the harness and third parties use
this predicate. -/
def Submission.acc (S : Submission) (vk c : Digest) (p : Signed) : Bool :=
  decide (p.π.size < 2 ^ 64) && decide (p.tr.length ≤ S.qV) &&
    decide (∀ e ∈ p.tr, e.1.size ≤ queryCap) && SigOk vk (traceDigest p.tr) p.σ &&
    decide ((S.V vk c p.π).runSeq p.tr = some true)

/-- **The certificate** of a submission. -/
structure Certificate (S : Submission) : Prop where
  /-- Knowledge soundness for the relation of the submission's own `acc`, under every key. -/
  secure : ∀ vk, KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV
  /-- Completeness of the honest prover with error `δ` over a random oracle, under every key. -/
  complete : ∀ vk, CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) S.δ
  /-- The program computes the extractor within the fuel. -/
  computes : Computes S.ext S.E S.fuel
  /-- The caps: the knowledge error at most `2^-120` per fresh query, the completeness error at
  most `2^-40`, at most `2^16` verifier queries, fuel within the budget `B`, the program within
  `progCap` statements. -/
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
