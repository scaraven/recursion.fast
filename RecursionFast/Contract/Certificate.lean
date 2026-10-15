/-
# Contract: what a submission is and what its record certifies                   (TRUSTED)

DESIGN §3.3, §6.2. A challenge (`Challenge/*.lean.in`, Stage 6b) asks for a submission with the
claim rendered in as organiser data (`Declared`, `DeclaredR`, the v0.3 pattern), and for a
certificate tying the two by equalities the solver proves by evaluation. A **leaf-board**
submission (board L) is a protocol, its configuration and the proof that it is secure; a
**recursion-board** submission (board R) adds its recursion entry (`RecursionEntry`: the verifier
as a circuit at the protocol's own class). Everything else a record states is measured by the
benchmark run, not proved: wall times, proof sizes, and that every proof of the run verifies.

What is declared is static. The cells of `C_V` depend on the witness, so they are bounded through
`complete` (S1-A6), not declared; the declared size of `C_V` is its chip count and its number of
matrix entries (the index size). The key digests `D (index cfg P C_V)` and
`D (index cfg P L_chain(2^10))` are declared for the record but **not certified** (S5-A3):
committing an index oracle of up to `2^(k+8)` elements is beyond the kernel, so the harness
computes them with the compiled indexer (untimed indexing, §6.3 step 2) from the submitted `C_V`
and from `L_chain(2^10)`, rejects a claim that differs, and uses its own values in `rootOK` and
as the keys of every `NARG` run (S5-A13).
-/
import RecursionFast.Contract.Recursion

namespace RecursionFast

/-- A **leaf-board submission** at class `k`: a protocol, its compilation configuration, and the
proof that the protocol is secure. -/
structure Submission (k : ℕ) where
  /-- The protocol. -/
  P : Protocol k
  /-- The compilation configuration (hash, Merkle arity). -/
  cfg : Cfg
  /-- The protocol is secure (DESIGN §4). -/
  secure : P.Secure

/-- A **recursion-board submission**: a leaf-board submission and its recursion entry. -/
structure SubmissionR (k : ℕ) extends Submission k where
  /-- The recursion entry: the verifier as a circuit, at the protocol's own class (§5.3). -/
  entry : RecursionEntry P cfg

/-- The **declared claim** of a leaf-board submission (rendered from the claim JSON): the class,
the hash and the Merkle arity. -/
structure Declared where
  /-- The class. -/
  k : ℕ
  /-- The hash of the configuration. -/
  hash : HashId
  /-- The Merkle arity of the configuration. -/
  arity : ℕ

/-- The declared claim of a recursion-board submission: also the chip count and the number of
matrix entries of `C_V` (certified), and the two key digests (harness-checked, S5-A3). -/
structure DeclaredR extends Declared where
  /-- The number of chips of `C_V`. -/
  chips : ℕ
  /-- The number of matrix entries of `C_V`, over all chips. -/
  entries : ℕ
  /-- `D (index cfg P C_V)` for the submitted `C_V`: compared by the harness with the compiled
  indexer's, not certified. -/
  digestC : Digest
  /-- `D (index cfg P L_chain(2^10))`: compared by the harness with the compiled indexer's, not
  certified. -/
  digestL : Digest

/-- **A leaf-board certificate**: the submission (at the declared class, by its type) has the
declared configuration. -/
structure Certificate (D : Declared) (S : Submission D.k) : Prop where
  /-- The configuration is the declared one. -/
  cfg : S.cfg.hash = D.hash ∧ S.cfg.arity = D.arity

/-- **A recursion-board certificate**: the leaf-board certificate, and `C_V` has the declared chip
and entry counts. -/
structure CertificateR (D : DeclaredR) (S : SubmissionR D.k) : Prop
    extends Certificate D.toDeclared S.toSubmission where
  /-- The static size of `C_V` is the declared one. -/
  size : S.entry.C.chips.length = D.chips ∧ (S.entry.C.chips.map Chip.entries).sum = D.entries

end RecursionFast
