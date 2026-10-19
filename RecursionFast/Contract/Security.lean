/-
# Contract: knowledge soundness and completeness in the random-oracle model        (TRUSTED)

DESIGN-v3 §4, V3-3, V3-4. Mathlib only; no probability monad and no adversary type: the counting
measure on `Digest` (`Nat.card`) is the only measure.

**Knowledge soundness (`KS`)** is stated query by query over the oracle's query log. A submitter
exhibits a **knowledge state** (`KState`): a predicate `good` on logs and a predicate `bad` on a
log, a fresh query and its answer, with three laws:
* `empty`: the empty log is good;
* `step`: a good log stays good after a fresh query, unless the answer is bad;
* `final`: in a good log, every proof the verifier accepts reading its answers from the log is
  extractable: the extractor `E`, given the statement, the proof and the log, returns a witness.
`Bounded ε`: for every log and query, at most an `ε` fraction of the `2^256` answers is bad.
The statement is quantified only in `final`, so an adversary choosing it after seeing answers is
covered. The paper theorem (§4.5): an adversary with `Q` oracle queries makes the verifier accept
a proof the extractor cannot open with probability at most `(Q + qV) · ε` over a **random**
oracle, by the union bound over the fresh queries of the log (the verifier's own `qV` queries
included).

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
import Mathlib.SetTheory.Cardinal.Finite

open scoped NNReal

namespace RecursionFast

/-- The contract's cap on the per-query knowledge error: `2^-128`. -/
noncomputable def errorCap : ℝ≥0 := (2 : ℝ≥0)⁻¹ ^ 128

/-- **A knowledge state** for the relation `R`, the verifier `V` and the extractor `E`: a
predicate `good` on query logs and a predicate `bad` on (log, fresh query, answer), with the laws
`empty`, `step` and `final`. -/
structure KState (R : Digest → Wit → Prop) (V : Digest → Proof → OProg Bool)
    (E : Digest → Proof → Log → Option Wit) where
  /-- The logs from which no accepted proof escapes the extractor. -/
  good : Log → Prop
  /-- The answers to a fresh query that may break `good`. -/
  bad : Log → ByteArray → Digest → Prop
  /-- The empty log is good. -/
  empty : good []
  /-- A good log stays good after a fresh query whose answer is not bad. -/
  step : ∀ L q a, good L → q ∉ L.map Prod.fst → ¬ bad L q a → good (L ++ [(q, a)])
  /-- In a good log, every proof the verifier accepts on the log's answers is extracted to a
  witness. -/
  final : ∀ L c π, good L → (V c π).runLog L = some true → ∃ w, E c π L = some w ∧ R c w

/-- For every log and query, at most an `ε` fraction of the possible answers is bad. -/
def KState.Bounded {R : Digest → Wit → Prop} {V : Digest → Proof → OProg Bool}
    {E : Digest → Proof → Log → Option Wit} (k : KState R V E) (ε : ℝ≥0) : Prop :=
  ∀ L q, (Nat.card {a // k.bad L q a} : ℝ≥0) ≤ ε * Nat.card Digest

/-- **Knowledge soundness** in the random-oracle model with per-query error `ε` and at most `qV`
verifier queries: a bounded knowledge state exists, and `V` asks at most `qV` queries on every
input and oracle. -/
def KS (R : Digest → Wit → Prop) (V : Digest → Proof → OProg Bool)
    (E : Digest → Proof → Log → Option Wit) (ε : ℝ≥0) (qV : ℕ) : Prop :=
  (∃ k : KState R V E, k.Bounded ε) ∧ ∀ H c π, ((V c π).queries H).length ≤ qV

/-- **Perfect completeness** over every oracle function: on every statement and witness in `R`,
the verifier accepts the honest prover's proof. -/
def Complete (R : Digest → Wit → Prop) (P : Digest → Wit → OProg Proof)
    (V : Digest → Proof → OProg Bool) : Prop :=
  ∀ (H : ByteArray → Digest) c w, R c w → (V c ((P c w).run H)).run H = true

end RecursionFast
