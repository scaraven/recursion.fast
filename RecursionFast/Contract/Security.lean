/-
# Contract: knowledge soundness and completeness in the random-oracle model        (TRUSTED)

DESIGN-v3 §4, V3-3, V3-4, as amended by V3-KS-A1 … A7, V4-A9 (the caps' values) and **V4-A10**
(the user's decision of 2026-10-27): knowledge soundness is the textbook single-output notion, and
v3's potential (`KState`) is an untrusted library route to it (`Library/Security.lean`).
`Certificate.lean` requires both definitions for the verifier and prover under **every** public
key. Mathlib only; no probability monad and no adversary type: an adversary is a query program,
and the uniform average over the `2^256` digests (a sum over `Digest`) is the only measure.

**The random oracle (`prob`).** A program runs against a lazily sampled random oracle: a query
not yet in the table is answered uniformly over the `2^256` digests and recorded, a repeated
query is answered from the table (first match, as `runLog` reads it), so a run sees one function
throughout. `prob B p L` is the probability that `p`, started with the table `L`, ends with an
output `x` and a final table `L'` such that `B x L'`. Both definitions below are stated with it.

**Knowledge soundness (`KS`)**, single-output and straight-line. An adversary is a query program
`A` that asks at most `Q` queries under every oracle function and outputs a statement `c` and a
proof `π`. The game runs `A`, then the verifier on its output, against one random oracle; the
adversary wins when `V` accepts `(c, π)` with its answers read from the final query log
(`runLog`) and the extractor `E`, given `c`, `π` and that log, returns no witness of `R`. `KS`
says: `V` asks at most `qV` queries on every input and oracle function, and every adversary with
`Q + qV ≤ logCap` wins with probability at most `(Q + qV) · ε`.
* *The adversary* is computationally unbounded, bounded only in queries, and deterministic. A
  randomised adversary is an average of deterministic ones, and the bound carries over because
  `E` does not depend on the adversary (paper). It chooses the statement after its queries. Its
  budget is stated over every oracle function, like `qV`: a lazily sampled run agrees with some
  function, so the game asks at most `Q + qV` queries on every path.
* *Why `qV` is charged.* An adversary may leave its luck to the verifier: with `Q = 0`, a guessed
  proof still wins when `V`'s own fresh answers favour it. The game counts `V`'s queries as the
  adversary's, so the error is per query of either (`Controls/Security.lean`,
  `queryThenAccept_ks_ge_one`: a verifier that asks one query and accepts needs `ε ≥ 1`).
* *Why `logCap`.* The bound is linear in the queries, while a collision-type event grows with
  their square: among `Q` answers two agree on `t` given bits with probability about
  `Q² · 2^-t`, above `Q · ε` once `Q > ε · 2^t`. So no verifier that relies on a commitment's
  binding could meet the bound for every `Q`; under `logCap` such an event costs at most about
  `logCap · 2^-t` per query, so at `logCap = 2^96` events of at least `216` bits are chargeable
  at `errorCap` (birthday cost `2^108`), a full digest costs `2^-160`, and an honest Merkle
  verifier comparing at most `2^15` digests per query about `2^-145`. At the caps the bound is
  `2^96 · 2^-120 = 2^-24` at `2^96` queries and `2^-56` at `2^64` (V3-KS-A6). Nothing is claimed
  for `Q + qV > logCap`, and a `qV` above `logCap` makes `KS` vacuous, which `Certificate`'s
  `qV ≤ 2^16` excludes (`Controls/Security.lean`, `acceptAll_ks_above_logCap`).
* **The extractor is efficient (`Computes`, `Extractor.lean`) only for tapes of at most `2^64`
  words, about `2^61` log entries** (V3-S2R-m2): on longer logs `E` is unconstrained and may be a
  non-constructive choice (`Controls/Certificate.lean`, `choice_certificate`), so between about
  `2^61` entries and `logCap` the bound is a soundness-type statement, not knowledge.

**The potential is a library route, not a rule (V4-A10).** A submitter proves `KS` by any
correct argument. One route, v3's contract form, is a knowledge state (`Library/Security.lean`,
`KState`): a potential on logs that starts at `0`, rises by at most `ε` on average per fresh
answer, and below `1` makes every accepted proof extractable. `KState.ks`
(`Library/PaperTheorem.lean`) turns it into `KS` by Markov's inequality on the stopped potential;
it prices a challenge spread over several answers (the query phase of a hash-based IOP) at the
product of their conditionals (`Controls/Potential.lean`, `twoLucky`). The certificate does not
name it.

**What this file does not exclude (V3-S1-A13, A23).** `KS` alone excludes little: a verifier
that accepts everything is knowledge-sound, for some extractor, exactly when every statement has
a witness, which no digest can be shown to lack (`Library/KS.lean`, `acceptAll_ks_iff`). The
knowledge content of a certificate is `KS` **with the named extractor**, which `Extractor.lean`
requires a program of the contract's machine to compute within a step budget (decision Q1,
V3-S2R-A1). Nor does anything here constrain how `V` behaves on one particular oracle function:
a `V` that recognises a public function it can compute and accepts a magic proof when the oracle
agrees with it is certified (`Controls/Backdoor.lean`, v3's O-25). In v4 the deployment, not this
file, excludes it: the deployed oracle is keyed by a secret drawn after `V` is frozen (V4-2), so
no such function is the deployed one except with negligible probability.

**Completeness (`CompleteWithError`, V3-S2R-A2, O-23; the user's decision of 2026-10-20).** On
every statement and witness of the relation, the honest prover's proof, produced and then verified
against one **uniformly random** oracle (`prob`), is rejected with probability at most `δ`, a
declared number at most `completenessCap = 2^-40` (`Certificate.lean`). The verifier sees the
answers the prover saw. This admits grinding and challenge-dependent exceptional cases, which
perfect completeness over every oracle function (S1's `Complete`, now `Library/Completeness.lean`)
forbids; `Complete` implies `CompleteWithError` at `δ = 0`. v3's `failProb` is `prob` of a
`false` result (`Library/Completeness.lean`, `failProb_eq_prob`, `completeWithError_iff`). Nothing
here says that an honest proof verifies under the one deployed oracle (keyed BLAKE2s, V4-2); the
harness's concrete checks of `acc` do (DESIGN-v3 §5.4, V3-S2R-H-M4).

**Why `2^-40` (V4-A9, the user's decision of 2026-10-26; v3 had `2^-128`).** A completeness
failure is no security event: it costs only its entrant, as one rejected proof and a failed run.
An evaluation's prover makes about 640 proofs (the tree's 127, the stream's 513), so at `2^-40`
each a run fails this way with probability about `2^-30.7`. Grinding to difficulty `2^g` meets
the cap with about `40 · ln 2 · 2^g ≈ 28 · 2^g` attempts (`89 · 2^g` at `2^-128`).

**Why `errorCap = 2^-120` (V4-A9, the user's decision of 2026-10-26; v3 had `2^-128`).** It
admits designs over GF(2^128): a degree-2 sumcheck round costs `2^-127` and a univariate-skip
round about `126 / 2^128 ≈ 2^-121` per fresh query (FB-9). The deployed run stays negligible:
composing the tree from single-output knowledge soundness takes a union bound over the extracted
proofs, about `513 · 2^30 · 2^-120 ≈ 2^-81` at `2^30` queries (design §2.4).
-/
import RecursionFast.Contract.Oracle
import Mathlib.Basic.NNReal.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

open scoped NNReal

namespace RecursionFast

/-- The digests are finite, as the images of the functions `Fin 32 → Fin 256`, so `prob` can sum
over them. (Every `Fintype` instance lists each digest exactly once.) -/
noncomputable instance : Fintype Digest :=
  Fintype.ofSurjective (fun f : Fin 32 → Fin 256 => Vector.ofFn fun i => UInt8.ofFin (f i))
    fun d => ⟨fun i => d[i].toFin, by ext i hi; simp⟩

/-- The contract's cap on the per-query knowledge error: `2^-120`. -/
noncomputable def errorCap : ℝ≥0 := (2 : ℝ≥0)⁻¹ ^ 120

/-- The most oracle queries, the adversary's and the verifier's together, for which knowledge
soundness is claimed: `2^96`. -/
def logCap : ℕ := 2 ^ 96

/-- **The probability that the program `p`, started with the table `L`, ends with an output `x`
and a final table `L'` such that `B x L'`**, when each query not in the table is answered
uniformly at random and recorded, and a repeated query is answered from the table (first match):
a lazily sampled random oracle. -/
noncomputable def prob {α : Type} (B : α → Log → Prop) : OProg α → Log → ℝ≥0
  | .ret x, L => by classical exact if B x L then 1 else 0
  | .query q k, L =>
    match L.find? fun e => e.1 = q with
    | some e => prob B (k e.2) L
    | none => (2 ^ 256)⁻¹ * ∑ a : Digest, prob B (k a) (L ++ [(q, a)])

/-- **Knowledge soundness** with per-query error `ε` and at most `qV` verifier queries: `V` asks
at most `qV` queries on every input and oracle; and for every adversary asking at most `Q` queries
and outputting a statement and a proof, `Q + qV ≤ logCap`, the probability over one random oracle
that `V` accepts the output on the final query log while `E`, given the statement, the proof and
that log, returns no witness of `R`, is at most `(Q + qV) · ε`. -/
def KS (R : Digest → Wit → Prop) (V : Digest → Proof → OProg Bool)
    (E : Digest → Proof → Log → Option Wit) (ε : ℝ≥0) (qV : ℕ) : Prop :=
  (∀ H c π, ((V c π).queries H).length ≤ qV) ∧
  ∀ (A : OProg (Digest × Proof)) (Q : ℕ), (∀ H, (A.queries H).length ≤ Q) → Q + qV ≤ logCap →
    prob (fun x L => (V x.1 x.2).runLog L = some true ∧ ¬ ∃ w, E x.1 x.2 L = some w ∧ R x.1 w)
      (A.bind fun x => (V x.1 x.2).bind fun _ => .ret x) [] ≤ (Q + qV) * ε

/-- **Completeness with error `δ`**: on every statement and witness of `R`, the honest prover's
proof, produced and verified against one random oracle, is rejected with probability at most `δ`. -/
def CompleteWithError (R : Digest → Wit → Prop) (P : Digest → Wit → OProg Proof)
    (V : Digest → Proof → OProg Bool) (δ : ℝ≥0) : Prop :=
  ∀ c w, R c w → prob (fun b _ => b = false) ((P c w).bind (V c)) [] ≤ δ

/-- The contract's cap on the completeness error: `2^-40`. -/
noncomputable def completenessCap : ℝ≥0 := (2 : ℝ≥0)⁻¹ ^ 40

end RecursionFast
