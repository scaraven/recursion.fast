/-
# Contract: knowledge soundness and completeness in the random-oracle model        (TRUSTED)

DESIGN-v3 §4, V3-3, V3-4, amended by V3-KS-A1 … A5 (`docs/DESIGN-AMENDMENTS.md`). Mathlib only;
no probability monad and no adversary type: the uniform average over the `2^256` digests (a sum
over `Digest`) is the only measure.

**Knowledge soundness (`KS`)** is stated query by query over the oracle's query log. A submitter
exhibits a **knowledge state** (`KState`) with error `ε`: a potential `μ` on logs, a non-negative
real measuring how close the log is to letting an accepted proof escape the extractor, with three
laws:
* `empty`: the empty log has potential `0`;
* `step`: on a log of fewer than `logCap` entries with potential below `1`, a fresh query raises
  the potential by at most `ε` **on average over its `2^256` answers**;
* `final`: on a log of at most `logCap` entries with potential below `1`, every proof the
  verifier accepts reading its answers from the log is extractable: the extractor `E`, given the
  statement, the proof and the log, returns a witness.
The statement is quantified only in `final`, so an adversary choosing it after seeing answers is
covered.

**The paper theorem (§4.5).** An adversary with `Q` oracle queries, `Q + qV ≤ logCap`, makes the
verifier accept a proof the extractor cannot open with probability at most `(Q + qV) · ε` over a
**random** oracle. Along the log of fresh queries (the verifier's own `qV` included), the potential
capped at `1` and stopped when it first reaches `1` rises by at most `ε` in expectation per query
(`step`): a supermartingale from `0`. By Markov's inequality it reaches `1` with probability at
most `(Q + qV) · ε`; otherwise `final` extracts.

**Why a potential.** A challenge that spans several answers (the query phase of a hash-based IOP:
positions drawn from `H(T ‖ 1), …, H(T ‖ k)`) has error the product of its answers' conditionals;
a potential carries the partial product from answer to answer, where a set of bad answers per
query would charge the largest conditional (`Controls/Potential.lean`, `twoLucky`). A boolean
state (`good`, `bad`) is the special case `μ ∈ {0, 1}` (`Library/Security.lean`,
`KState.ofBool`).

**Why the length guard.** A Merkle commitment is binding only up to collisions: a fresh answer
that equals one of the earlier digests of the log is charged, and there are as many of those as
entries. Over logs of unbounded length that charge exceeds every useful `ε` (V3-KS-A2;
`Controls/Potential.lean`, `collision_no_bool_kstate`), while the theorem says nothing once
`Q + qV ≥ 1 / ε` anyway. With `logCap = 2^64` the collision charge is about `2^-192` per query.

**What this file does not exclude (V3-S1-A13, A23).** `KState` alone excludes little: a verifier
that accepts everything has one exactly when every statement has some witness, which no digest
can be shown to lack (`Library/Security.lean`, `acceptAll_kstate_iff`). The knowledge content of a
certificate is `KS` **with the named extractor**, which `Extractor.lean` requires an image to
compute within a budget (decision Q1). Nor does anything here constrain how `V` behaves on one
particular oracle function: a `V` that recognises the deployment oracle (BLAKE2s,
`Certificate.lean`) and accepts a magic proof there is certified (O-25, `Controls/Backdoor.lean`).

**Completeness (`Complete`)** is perfect, over every oracle function. The counted-error form of
§4.3 (`CompleteWithError`) is not in the contract yet (O-23, V3-S1-A9).
-/
import RecursionFast.Contract.Oracle
import Mathlib.Basic.NNReal.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

open scoped NNReal

namespace RecursionFast

/-- The `2^256` digests are finite, as the images of the functions `Fin 32 → Fin 256`. (Every
`Fintype` instance lists each digest exactly once.) -/
instance : Fintype Digest :=
  Fintype.ofSurjective (fun f : Fin 32 → Fin 256 => Vector.ofFn fun i => UInt8.ofFin (f i))
    fun d => ⟨fun i => d[i].toFin, by ext i hi; simp⟩

/-- The contract's cap on the per-query knowledge error: `2^-128`. -/
noncomputable def errorCap : ℝ≥0 := (2 : ℝ≥0)⁻¹ ^ 128

/-- The longest log the knowledge laws cover: `2^64` entries, an adversary's query budget. -/
def logCap : ℕ := 2 ^ 64

/-- **A knowledge state** with per-query error `ε` for the relation `R`, the verifier `V` and the
extractor `E`: a potential `μ` on query logs with the laws `empty`, `step` and `final`. -/
structure KState (R : Digest → Wit → Prop) (V : Digest → Proof → OProg Bool)
    (E : Digest → Proof → Log → Option Wit) (ε : ℝ≥0) where
  /-- The potential of a log; below `1`, no accepted proof escapes the extractor. -/
  μ : Log → ℝ≥0
  /-- The empty log has potential `0`. -/
  empty : μ [] = 0
  /-- Within `logCap` and below `1`, a fresh query raises the potential by at most `ε` on average
  over its answers. -/
  step : ∀ L q, L.length < logCap → μ L < 1 → q ∉ L.map Prod.fst →
    ∑ a : Digest, μ (L ++ [(q, a)]) ≤ (μ L + ε) * Fintype.card Digest
  /-- Within `logCap` and below `1`, every proof the verifier accepts on the log's answers is
  extracted to a witness. -/
  final : ∀ L c π, L.length ≤ logCap → μ L < 1 → (V c π).runLog L = some true →
    ∃ w, E c π L = some w ∧ R c w

/-- **Knowledge soundness** in the random-oracle model with per-query error `ε` and at most `qV`
verifier queries: a knowledge state with error `ε` exists, and `V` asks at most `qV` queries on
every input and oracle. -/
def KS (R : Digest → Wit → Prop) (V : Digest → Proof → OProg Bool)
    (E : Digest → Proof → Log → Option Wit) (ε : ℝ≥0) (qV : ℕ) : Prop :=
  Nonempty (KState R V E ε) ∧ ∀ H c π, ((V c π).queries H).length ≤ qV

/-- **Perfect completeness** over every oracle function: on every statement and witness in `R`,
the verifier accepts the honest prover's proof. -/
def Complete (R : Digest → Wit → Prop) (P : Digest → Wit → OProg Proof)
    (V : Digest → Proof → OProg Bool) : Prop :=
  ∀ (H : ByteArray → Digest) c w, R c w → (V c ((P c w).run H)).run H = true

end RecursionFast
