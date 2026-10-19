/-
  RecursionFast.Library.Security  (UNTRUSTED, kernel-checked)

  Facts about the security definitions (`Contract/Security.lean`).

  * `card_digest`, `fintype_card_digest`: there are `2^256` digests, so the `step` law reads
    "the sum of the potential over the `2^256` answers is at most `(μ L + ε) · 2^256`".
  * **Boolean knowledge states** (the Stage S1 form, V3-KS-A3): `BoolKState` (a predicate `good`
    on logs, a predicate `bad` on answers, the laws `empty`, `step`, `final`), `Bounded ε` (at most
    an `ε` fraction of bad answers for every log and query) and `BoundedBelow ε` (the same for
    logs of fewer than `logCap` entries). `KState.ofBool` embeds a `BoundedBelow ε` boolean state
    as the potential `0` on good logs, `1` elsewhere; `Bounded.below` makes every S1 state one.
  * **Building potentials**: `KState.zero` (potential `0` when every accepted proof is extracted
    on every log), `KState.mono` (a larger error), `step_of_hits` (a potential that rises by at
    most `1`, and only on a set `T` of at most `ε · 2^256` answers, satisfies `step`).
  * **Bounding the error from below**: `KState.one_le_of_jump` (if the potential is below `1` on a
    short log and reaches `1` on every answer to a fresh query, then `1 ≤ μ L + ε`);
    `errorCap_lt_one`.
  * `no_kstate_of_empty`: if the verifier accepts some proof without any oracle answer (on the
    empty log) and the extractor returns no witness of the relation for it on the empty log,
    there is no knowledge state at any error (the laws `empty` and `final`).
  * `acceptAll_kstate_iff`: the verifier that accepts everything has a knowledge state, for some
    extractor, exactly when every statement has a witness (DESIGN-v3 §4.2, V3-S1-A13).
-/
import RecursionFast.Contract.Security
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.NNReal.Basic

open scoped NNReal

namespace RecursionFast

/-- Digests as functions from the 32 positions to bytes as numbers below 256. -/
def digestEquiv : Digest ≃ (Fin 32 → Fin 256) where
  toFun d i := d[i].toFin
  invFun f := Vector.ofFn fun i => UInt8.ofFin (f i)
  left_inv d := by ext i hi; simp
  right_inv f := by funext i; simp

/-- There are `2^256` digests. -/
theorem fintype_card_digest : Fintype.card Digest = 2 ^ 256 := by
  simp [Fintype.card_congr digestEquiv]

/-- There are `2^256` digests (`Nat.card`). -/
theorem card_digest : Nat.card Digest = 2 ^ 256 := by
  rw [Nat.card_eq_fintype_card, fintype_card_digest]

/-- The contract's error cap is below `1`. -/
theorem errorCap_lt_one : errorCap < 1 := pow_lt_one₀ (by positivity) (by norm_num) (by norm_num)

variable {R : Digest → Wit → Prop} {V : Digest → Proof → OProg Bool}
  {E : Digest → Proof → Log → Option Wit}

/-! ## Boolean knowledge states -/

/-- **A boolean knowledge state** (the Stage S1 contract's form): a predicate `good` on query logs
and a predicate `bad` on (log, fresh query, answer), with the laws `empty`, `step` and `final`. -/
structure BoolKState (R : Digest → Wit → Prop) (V : Digest → Proof → OProg Bool)
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

/-- For every log and query, at most an `ε` fraction of the possible answers is bad (the Stage S1
contract's bound). -/
def BoolKState.Bounded (k : BoolKState R V E) (ε : ℝ≥0) : Prop :=
  ∀ L q, (Nat.card {a // k.bad L q a} : ℝ≥0) ≤ ε * Nat.card Digest

/-- For every log of fewer than `logCap` entries and every query, at most an `ε` fraction of the
possible answers is bad. -/
def BoolKState.BoundedBelow (k : BoolKState R V E) (ε : ℝ≥0) : Prop :=
  ∀ L q, L.length < logCap → (Nat.card {a // k.bad L q a} : ℝ≥0) ≤ ε * Nat.card Digest

/-- A bound over every log holds over the short ones. -/
theorem BoolKState.Bounded.below {k : BoolKState R V E} {ε : ℝ≥0} (h : k.Bounded ε) :
    k.BoundedBelow ε := fun L q _ => h L q

/-- A boolean knowledge state with no bad answer is bounded at every error. -/
theorem BoolKState.bounded_of_not_bad (k : BoolKState R V E) (h : ∀ L q a, ¬ k.bad L q a)
    (ε : ℝ≥0) : k.Bounded ε := fun L q => by simp [h]

/-- A larger error bound holds. -/
theorem BoolKState.Bounded.mono {k : BoolKState R V E} {ε ε' : ℝ≥0} (h : k.Bounded ε)
    (hε : ε ≤ ε') : k.Bounded ε' :=
  fun L q => (h L q).trans (mul_le_mul_of_nonneg_right hε (by positivity))

/-- If every answer to the query `q` after the log `L` is bad, the error is at least `1`. -/
theorem BoolKState.one_le_of_bounded {k : BoolKState R V E} {ε : ℝ≥0} (h : k.Bounded ε)
    (L : Log) (q : ByteArray) (hall : ∀ a, k.bad L q a) : 1 ≤ ε := by
  have hb := h L q
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), card_digest] at hb
  exact (le_mul_iff_one_le_left (by positivity)).mp hb

/-! ## Building potentials -/

/-- **`step` from a hit set**: if a fresh answer raises the potential by at most `1`, and only
when it lies in a set `T` of at most `ε · 2^256` answers, the average rise is at most `ε`. -/
theorem step_of_hits {μ : Log → ℝ≥0} {L : Log} {q : ByteArray} {ε : ℝ≥0} (T : Finset Digest)
    (hμ : ∀ a, μ (L ++ [(q, a)]) ≤ μ L + if a ∈ T then 1 else 0)
    (hT : (T.card : ℝ≥0) ≤ ε * Fintype.card Digest) :
    ∑ a : Digest, μ (L ++ [(q, a)]) ≤ (μ L + ε) * Fintype.card Digest := by
  calc ∑ a : Digest, μ (L ++ [(q, a)])
      ≤ ∑ a : Digest, (μ L + if a ∈ T then 1 else 0) := Finset.sum_le_sum fun a _ => hμ a
    _ = μ L * Fintype.card Digest + T.card := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_comm]
    _ ≤ (μ L + ε) * Fintype.card Digest := by rw [add_mul]; gcongr

open Classical in
/-- **The boolean form embeds**: a boolean knowledge state bounded at `ε` on logs shorter than
`logCap` is the potential `0` on good logs and `1` on the others. -/
noncomputable def KState.ofBool (k : BoolKState R V E) {ε : ℝ≥0} (h : k.BoundedBelow ε) :
    KState R V E ε where
  μ L := if k.good L then 0 else 1
  empty := by simp [k.empty]
  step L q hlen hμ hq := by
    have hg : k.good L := by_contra fun hg => by simp [hg] at hμ
    refine step_of_hits (μ := fun L => if k.good L then 0 else 1)
      (Finset.univ.filter (k.bad L q)) (fun a => ?_) ?_
    · by_cases hb : k.bad L q a
      · split_ifs <;> simp_all
      · simp [hg, k.step L q a hg hq hb]
    · have hc : (Finset.univ.filter (k.bad L q)).card = Nat.card {a // k.bad L q a} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rw [hc, ← Nat.card_eq_fintype_card]
      exact h L q hlen
  final L c π _ hμ hacc := k.final L c π (by_contra fun hg => by simp [hg] at hμ) hacc

/-- The potential of `KState.ofBool` is `0` exactly on the good logs. -/
theorem KState.ofBool_μ_eq_zero (k : BoolKState R V E) {ε : ℝ≥0} (h : k.BoundedBelow ε)
    (L : Log) : (KState.ofBool k h).μ L = 0 ↔ k.good L := by
  classical
  simp only [KState.ofBool]
  split_ifs with hg <;> simp [hg]

/-- **The zero potential**: when every proof the verifier accepts on every log is extracted, the
potential `0` is a knowledge state at every error. -/
def KState.zero (ε : ℝ≥0)
    (h : ∀ L c π, (V c π).runLog L = some true → ∃ w, E c π L = some w ∧ R c w) :
    KState R V E ε where
  μ _ := 0
  empty := rfl
  step _ _ _ _ _ := by simp
  final L c π _ _ := h L c π

/-- **A larger error**: a knowledge state with error `ε` is one with every error `ε' ≥ ε`. -/
def KState.mono {ε ε' : ℝ≥0} (k : KState R V E ε) (hε : ε ≤ ε') : KState R V E ε' where
  μ := k.μ
  empty := k.empty
  step L q hlen hμ hq := (k.step L q hlen hμ hq).trans (by gcongr)
  final := k.final

/-! ## Bounding the error from below -/

/-- **A forced jump costs `1`**: if the potential is below `1` on a log shorter than `logCap` and
reaches `1` on every answer to a fresh query, then `1 ≤ μ L + ε`. -/
theorem KState.one_le_of_jump {ε : ℝ≥0} (k : KState R V E ε) {L : Log} {q : ByteArray}
    (hlen : L.length < logCap) (hμ : k.μ L < 1) (hq : q ∉ L.map Prod.fst)
    (hall : ∀ a, 1 ≤ k.μ (L ++ [(q, a)])) : 1 ≤ k.μ L + ε := by
  have hs := (Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hall a).trans
    (k.step L q hlen hμ hq)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, fintype_card_digest] at hs
  exact (le_mul_iff_one_le_left (by positivity : (0 : ℝ≥0) < ((2 ^ 256 : ℕ) : ℝ≥0))).mp hs

/-- **No knowledge state** when the verifier accepts a proof on the empty log and the extractor
does not open it to a witness on the empty log. -/
theorem no_kstate_of_empty {ε : ℝ≥0} {c : Digest} {π : Proof}
    (hV : (V c π).runLog [] = some true) (hE : ¬ ∃ w, E c π [] = some w ∧ R c w) :
    IsEmpty (KState R V E ε) :=
  ⟨fun k => hE (k.final [] c π (Nat.zero_le _) (by rw [k.empty]; exact one_pos) hV)⟩

/-- The verifier that accepts every proof, with no query. -/
def acceptAll (_ : Digest) (_ : Proof) : OProg Bool := .ret true

/-- **The accept-all verifier has a knowledge state, for some extractor, exactly when every
statement has a witness**, at every error. So `KState` alone excludes it only through a
witnessless statement, which no digest can be shown to be under `Rel` (V3-S1-A13). -/
theorem acceptAll_kstate_iff (R : Digest → Wit → Prop) (ε : ℝ≥0) :
    (∃ E, Nonempty (KState R acceptAll E ε)) ↔ ∀ c, ∃ w, R c w :=
  ⟨fun ⟨_, ⟨k⟩⟩ c => (k.final [] c .empty (Nat.zero_le _) (by rw [k.empty]; exact one_pos)
      rfl).imp fun _ h => h.2,
    fun h => ⟨fun c _ _ => some (h c).choose,
      ⟨KState.zero ε fun _ c _ _ => ⟨_, rfl, (h c).choose_spec⟩⟩⟩⟩

end RecursionFast
