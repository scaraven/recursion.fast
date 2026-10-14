/-
# Contract: holographic proof systems for the layout relation                    (TRUSTED)

DESIGN §3.1, S1-A8. A submission provides a `Protocol k`: contract round shapes within the shape
caps, a holographic indexer (`VK`, `IDX`), an honest prover, a verifier, an extractor image and
declared per-round errors. The verifier is a **query program** (`QProg`, as v0.3's T0 programs):
from `VK L`, the statement and the challenges it reads the oracles (oracle 0 is the index oracle
`IDX L`, then the prover's oracles in round order) only leaf by leaf, through `query`, which is
exactly what the compiled argument opens (a leaf plus an authentication path, §3.2). It never
sees the layout `L` itself. Security is `Security.lean`'s, unchanged, over the class-`k` relation
`relK k`, with the extractor image's round-by-round extractor (`Contract/Extractor.lean`, Q1).
"Computable" (no `noncomputable`, `implemented_by`, `extern`, `csimp` in the closure of `VK`,
`IDX`, `verify` and the image) is checked by the harness gate, not by Lean; the image must also be
the literal rendered from the claim.
-/
import RecursionFast.Contract.Extractor

open scoped NNReal

namespace RecursionFast

/-- Contract cap on the verification key: at most `2^10` K-elements. -/
def vkCap : ℕ := 2 ^ 10

/-- **The relation of class `k`**: an admissible layout and a statement (the index and the
public input) with a witness satisfying the layout. -/
def relK (k : ℕ) : Set ((Layout K × Stmt) × List (Table K)) :=
  {p | p.1.1.Admissible k ∧ p.1.1.rel k p.1.2 p.2}

/-- A query program with result type `α`: stop with a result, or read one leaf of one oracle and
continue with any function of its contents (queries may be adaptive). -/
inductive QProg (α : Type) where
  /-- Stop with result `a`. -/
  | done (a : α)
  /-- Read leaf `l` of oracle `j` (its `2^logLeaf` elements) and continue on it. -/
  | query (j l : ℕ) (cont : List K → QProg α)

/-- Run a query program on the oracles `os`; an out-of-range oracle or leaf is `none` (reject). -/
def QProg.eval {α : Type} : QProg α → List Oracle → Option α
  | .done a, _ => some a
  | .query j l cont, os =>
    match os[j]? with
    | some o => if l < o.shape.leaves then (cont (o.leaf l)).eval os else none
    | none => none

/-- The challenges of a full transcript. -/
def chalOf {n : ℕ} {sh : Fin n → Round} (tr : FullTranscript sh) : Challenges sh :=
  fun c => tr c.1

/-- Shape cap of a round at class `k` (v0.3 admission): a message oracle has leaves no longer
than itself and at most `2^(k+10)` elements; an index challenge has at most 64 bits. -/
def Round.Admissible (k : ℕ) : Round → Prop
  | .msg o => o.logLeaf ≤ o.logLen ∧ o.logLen ≤ k + 10
  | .chal _ idx => ∀ b ∈ idx, b ≤ 64

/-- A holographic public-coin IOP for `relK k`. -/
structure Protocol (k : ℕ) where
  /-- The class is in the contract's range (DESIGN §3.1, S1-A2). -/
  k_range : 20 ≤ k ∧ k ≤ 28
  /-- Number of rounds, at most `roundCap = 2^14`. -/
  n : ℕ
  n_le : n ≤ roundCap
  /-- The round shapes (contract menu). -/
  shape : Fin n → Round
  /-- Verification key length and the (honest, computable) key. -/
  vkLen : ℕ
  vkLen_le : vkLen ≤ vkCap
  VK : Layout K → (Fin vkLen → K)
  /-- The index oracle: its shape and the (honest, computable) indexer. -/
  idxShape : OShape
  IDX : Layout K → OVal idxShape
  /-- Shape caps (S1-A9): every round is admissible; the index oracle has leaves no longer than
  itself and at most `2^(k+8)` elements. -/
  shape_ok : (∀ j, (shape j).Admissible k) ∧ idxShape.logLeaf ≤ idxShape.logLen ∧
    idxShape.logLen ≤ k + 8
  /-- The honest prover (a Lean specification; it may be noncomputable). -/
  prover : Strategy shape (Layout K × Stmt) (List (Table K)) Unit Unit
  /-- The verifier: from `VK L`, the statement and the challenges, a query program over the
  oracles (computable: its compiled form is executed and timed). -/
  verify : (Fin vkLen → K) → Stmt → Challenges shape → QProg Bool
  /-- The extractor image (DESIGN §4 item 3, Q1): the named round-by-round extractor is this
  image run on the contract machine, with the submitter's split of `B(k)` over its `n + 1` calls
  (`ExtractorImage.toExtractor`). -/
  extractor : ExtractorImage k n
  /-- Declared per-round errors. -/
  ε : ChallengeIdx shape → ℝ≥0

namespace Protocol
variable {k : ℕ} (P : Protocol k)

/-- The verifier as a pure verifier on the statement `(L, x)`: run the query program on the index
oracle `IDX L` and the transcript's oracles; accept iff it returns `true`. -/
def specVerifier : PureVerifier P.shape (Layout K × Stmt) Unit := fun s tr =>
  if (P.verify (P.VK s.1) s.2 (chalOf tr)).eval (⟨P.idxShape, P.IDX s.1⟩ :: tr.oracles) = some true
  then some () else none

/-- **Security of a protocol**: perfect completeness for `relK k`, worst-case RBR knowledge
soundness with the extractor of the image (`B(k)` steps in all over its `n + 1` calls) at the
declared errors, and `ε ≤ 2^-128` in every round (the round cap `n ≤ 2^14`, the key cap and
the shape caps are fields of `Protocol`). -/
def Secure : Prop :=
  SecureWith (relK k) Set.univ P.prover P.specVerifier (P.extractor.toExtractor P.shape) P.ε

end Protocol

end RecursionFast
