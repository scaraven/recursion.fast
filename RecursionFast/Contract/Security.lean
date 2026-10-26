/-
# Contract: knowledge soundness and completeness in the random-oracle model        (TRUSTED)

DESIGN-v3 §4, V3-3, V3-4, amended by V3-KS-A1 … A7 (`docs/DESIGN-AMENDMENTS.md`). **Unchanged
in v4** (V4-1): the definitions below are v3's, word for word, except the values of `errorCap`
and `completenessCap` (V4-A9); `Certificate.lean` now requires them for the verifier and prover
under **every** public key. Mathlib only; no probability monad and no adversary type: the uniform
average over the `2^256` digests (a sum over `Digest`) is the only measure.

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
covered. Two of the guards, `final`'s length bound and `step`'s `μ L < 1`, only spare the
submitter a stopping argument and do not weaken the paper theorem (`Library/Security.lean`,
`KState.final_unguarded`, `KState.step_unstopped`). The load-bearing restriction is `step`'s
`L.length < logCap`.

**The paper theorem (§4.5).** An adversary with `Q` oracle queries, `Q + qV ≤ logCap`, makes the
verifier accept a proof the extractor cannot open with probability at most `(Q + qV) · ε` over a
**random** oracle. Along the log of fresh queries (the verifier's own `qV` included), the potential
capped at `1` and stopped when it first reaches `1` rises by at most `ε` in expectation per query
(`step`): a supermartingale from `0`. By Markov's inequality it reaches `1` with probability at
most `(Q + qV) · ε`; otherwise `final` extracts. Kernel-checked for a lazily sampled oracle and a
deterministic game of at most `Q + qV` queries in `Library/PaperTheorem.lean` (`paper`); the
passage to a random function and to randomised adversaries is standard and on paper. Nothing is
claimed for `Q + qV > logCap`. **The extractor is efficient (`Computes`, `Extractor.lean`) only
for tapes of at most `2^64` words, about `2^61` log entries** (V3-S2R-m2): on longer logs `E` is
unconstrained and may be a non-constructive choice (`Controls/Certificate.lean`,
`choice_certificate`), so between about `2^61` and `logCap` entries the bound is a soundness-type
statement, not knowledge.

**Why a potential.** A challenge that spans several answers (the query phase of a hash-based IOP:
positions drawn from `H(T ‖ 1), …, H(T ‖ k)`) has error the product of its answers' conditionals;
a potential carries the partial product from answer to answer, where a set of bad answers per
query would charge the largest conditional (`Controls/Potential.lean`, `twoLucky`). A boolean
state (`good`, `bad`) is the special case `μ ∈ {0, 1}` (`Library/Security.lean`,
`KState.ofBool`).

**Why the length guard.** A Merkle commitment is binding only up to collisions: a fresh answer
that equals one of the earlier digests of the log is charged, and there are as many of those as
entries. Over logs of unbounded length that charge exceeds every useful `ε` (V3-KS-A2;
`Controls/Potential.lean`, `collision_no_bool_kstate`). The guard gives this up: the claim stops
at `Q + qV = logCap`, where S1's form claimed `(Q + qV) · ε` for every `Q`. Its value fixes which
collision-type events are chargeable at `errorCap`: a comparison of `t` bits costs about
`logCap · 2^-t` per query, so at `logCap = 2^96` events of at least `216` bits are (birthday cost
`2^108`), a full digest costs `2^-160`, and an honest Merkle verifier comparing at most `2^15`
digests per query about `2^-145`, both below the cap. At the caps the bound is
`2^96 · 2^-120 = 2^-24` at `2^96` queries and `2^-56` at `2^64` (V3-KS-A6, with v4's cap;
`Controls/Potential.lean`, `v24_no_bool_kstate`).

**What this file does not exclude (V3-S1-A13, A23).** `KState` alone excludes little: a verifier
that accepts everything has one exactly when every statement has some witness, which no digest
can be shown to lack (`Library/Security.lean`, `acceptAll_kstate_iff`). The knowledge content of a
certificate is `KS` **with the named extractor**, which `Extractor.lean` requires a program of the
contract's machine to compute within a step budget (decision Q1, V3-S2R-A1). Nor does anything
here constrain how `V` behaves on one particular oracle function: a `V` that recognises a public
function it can compute and accepts a magic proof when the oracle agrees with it is certified
(`Controls/Backdoor.lean`, v3's O-25). In v4 the deployment, not this file, excludes it: the
deployed oracle is keyed by a secret drawn after `V` is frozen (V4-2), so no such function is the
deployed one except with negligible probability.

**Completeness (`CompleteWithError`, V3-S2R-A2, O-23; the user's decision of 2026-10-20).** On
every statement and witness of the relation, the honest prover's proof, produced and then verified
against one **uniformly random** oracle, is rejected with probability at most `δ`, a declared
number at most `completenessCap = 2^-40` (`Certificate.lean`). The oracle is sampled lazily
(`failProb`): a fresh query, the prover's or the verifier's, is answered uniformly over the `2^256`
digests and recorded, and a repeated one is answered from the record, so the verifier sees the
answers the prover saw. This admits grinding and challenge-dependent exceptional cases, which
perfect completeness over every oracle function (S1's `Complete`, now `Library/Completeness.lean`)
forbids; `Complete` implies `CompleteWithError` at `δ = 0`. Nothing here says that an honest proof
verifies under the one deployed oracle (keyed BLAKE2s, V4-2); the harness's concrete checks of
`acc` do (DESIGN-v3 §5.4, V3-S2R-H-M4).

**Why `2^-40` (V4-A9, the user's decision of 2026-10-26; v3 had `2^-128`).** A completeness
failure is no security event: it costs only its entrant, as one rejected proof and a failed run.
An evaluation's prover makes about 640 proofs (the tree's 127, the stream's 513), so at `2^-40`
each a run fails this way with probability about `2^-30.7`. Grinding to difficulty `2^g` meets
the cap with about `40 · ln 2 · 2^g ≈ 28 · 2^g` attempts (`89 · 2^g` at `2^-128`).

**Why `errorCap = 2^-120` (V4-A9, the user's decision of 2026-10-26; v3 had `2^-128`).** It
admits designs over GF(2^128): a degree-2 sumcheck round costs `2^-127` and a univariate-skip
round about `126 / 2^128 ≈ 2^-121` per fresh query (FB-9). The deployed tree's first error term
stays negligible: `(Q + qV) · ε ≈ 2^30 · 2^-120 = 2^-90` (design §2.4).
-/
import RecursionFast.Contract.Oracle
import Mathlib.Basic.NNReal.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

open scoped NNReal

namespace RecursionFast

/-- The digests are finite, as the images of the functions `Fin 32 → Fin 256`, so `step` can sum
over them. (Every `Fintype` instance lists each digest exactly once.) -/
noncomputable instance : Fintype Digest :=
  Fintype.ofSurjective (fun f : Fin 32 → Fin 256 => Vector.ofFn fun i => UInt8.ofFin (f i))
    fun d => ⟨fun i => d[i].toFin, by ext i hi; simp⟩

/-- The contract's cap on the per-query knowledge error: `2^-120`. -/
noncomputable def errorCap : ℝ≥0 := (2 : ℝ≥0)⁻¹ ^ 120

/-- The longest log the knowledge laws cover: `2^96` entries, an adversary's query budget. -/
def logCap : ℕ := 2 ^ 96

/-- **A knowledge state** with per-query error `ε` for the relation `R`, the verifier `V` and the
extractor `E`: a potential `μ` on query logs with the laws `empty`, `step` and `final`. -/
structure KState (R : Digest → Wit → Prop) (V : Digest → Proof → OProg Bool)
    (E : Digest → Proof → Log → Option Wit) (ε : ℝ≥0) where
  /-- The potential of a log; below `1`, no accepted proof escapes the extractor. -/
  μ : Log → ℝ≥0
  /-- The empty log has potential `0`. -/
  empty : μ [] = 0
  /-- Within `logCap` and below `1`, a fresh query raises the potential by at most `ε` on average
  over its `2^256` answers. (`μ L < 1` is redundant: `KState.step_unstopped`.) -/
  step : ∀ L q, L.length < logCap → μ L < 1 → q ∉ L.map Prod.fst →
    ∑ a : Digest, μ (L ++ [(q, a)]) ≤ (μ L + ε) * 2 ^ 256
  /-- Within `logCap` and below `1`, every proof the verifier accepts on the log's answers is
  extracted to a witness. (The length bound is redundant: `KState.final_unguarded`.) -/
  final : ∀ L c π, L.length ≤ logCap → μ L < 1 → (V c π).runLog L = some true →
    ∃ w, E c π L = some w ∧ R c w

/-- **Knowledge soundness** in the random-oracle model with per-query error `ε` and at most `qV`
verifier queries: a knowledge state with error `ε` exists, and `V` asks at most `qV` queries on
every input and oracle. -/
def KS (R : Digest → Wit → Prop) (V : Digest → Proof → OProg Bool)
    (E : Digest → Proof → Log → Option Wit) (ε : ℝ≥0) (qV : ℕ) : Prop :=
  Nonempty (KState R V E ε) ∧ ∀ H c π, ((V c π).queries H).length ≤ qV

/-- The probability that `p` returns `false` when each query not in the table `L` is answered
uniformly at random and recorded, and a repeated query is answered from the table (first match):
a lazily sampled random oracle. -/
noncomputable def failProb : OProg Bool → Log → ℝ≥0
  | .ret b, _ => if b then 0 else 1
  | .query q k, L =>
    match L.find? fun e => e.1 = q with
    | some e => failProb (k e.2) L
    | none => (2 ^ 256)⁻¹ * ∑ a : Digest, failProb (k a) (L ++ [(q, a)])

/-- **Completeness with error `δ`**: on every statement and witness of `R`, the honest prover's
proof, produced and verified against one random oracle, is rejected with probability at most `δ`. -/
def CompleteWithError (R : Digest → Wit → Prop) (P : Digest → Wit → OProg Proof)
    (V : Digest → Proof → OProg Bool) (δ : ℝ≥0) : Prop :=
  ∀ c w, R c w → failProb ((P c w).bind (V c)) [] ≤ δ

/-- The contract's cap on the completeness error: `2^-40`. -/
noncomputable def completenessCap : ℝ≥0 := (2 : ℝ≥0)⁻¹ ^ 40

end RecursionFast
