/-
  RecursionFast.Library.Security  (UNTRUSTED, kernel-checked)

  Facts about the security definitions (`Contract/Security.lean`).

  * `card_digest`: `Nat.card Digest = 2^256`, so `Bounded ε` reads "at most `ε · 2^256` bad
    answers".
  * `KState.bounded_of_not_bad`: a knowledge state with no bad answer is bounded at every error,
    `0` included.
  * `KState.one_le_of_bounded`: a knowledge state for which every answer to some query is bad is
    bounded only at `ε ≥ 1`; `errorCap_lt_one`: such an error is above the contract's cap.
  * `KState.Bounded.mono`: a larger error bound holds.
  * `no_kstate_of_empty`: if the verifier accepts some proof without any oracle answer (on the
    empty log) and the extractor returns no witness of the relation for it on the empty log,
    there is no knowledge state at all (the laws `empty` and `final`).
  * `acceptAll_kstate_iff`: the verifier that accepts everything has a knowledge state, for some
    extractor, exactly when every statement has a witness (DESIGN-v3 §4.2, V3-S1-A13).
-/
import RecursionFast.Contract.Security
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
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
theorem card_digest : Nat.card Digest = 2 ^ 256 := by simp [Nat.card_congr digestEquiv]

variable {R : Digest → Wit → Prop} {V : Digest → Proof → OProg Bool}
  {E : Digest → Proof → Log → Option Wit}

/-- A knowledge state with no bad answer is bounded at every error. -/
theorem KState.bounded_of_not_bad (k : KState R V E) (h : ∀ L q a, ¬ k.bad L q a) (ε : ℝ≥0) :
    k.Bounded ε := fun L q => by simp [h]

/-- A larger error bound holds. -/
theorem KState.Bounded.mono {k : KState R V E} {ε ε' : ℝ≥0} (h : k.Bounded ε) (hε : ε ≤ ε') :
    k.Bounded ε' := fun L q => (h L q).trans (mul_le_mul_of_nonneg_right hε (by positivity))

/-- If every answer to the query `q` after the log `L` is bad, the error is at least `1`. -/
theorem KState.one_le_of_bounded {k : KState R V E} {ε : ℝ≥0} (h : k.Bounded ε) (L : Log)
    (q : ByteArray) (hall : ∀ a, k.bad L q a) : 1 ≤ ε := by
  have hb := h L q
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), card_digest] at hb
  exact (le_mul_iff_one_le_left (by positivity)).mp hb

/-- The contract's error cap is below `1`. -/
theorem errorCap_lt_one : errorCap < 1 := pow_lt_one₀ (by positivity) (by norm_num) (by norm_num)

/-- **No knowledge state** when the verifier accepts a proof on the empty log and the extractor
does not open it to a witness on the empty log. -/
theorem no_kstate_of_empty {c : Digest} {π : Proof} (hV : (V c π).runLog [] = some true)
    (hE : ¬ ∃ w, E c π [] = some w ∧ R c w) : IsEmpty (KState R V E) :=
  ⟨fun k => hE (k.final [] c π k.empty hV)⟩

/-- The verifier that accepts every proof, with no query. -/
def acceptAll (_ : Digest) (_ : Proof) : OProg Bool := .ret true

/-- **The accept-all verifier has a knowledge state, for some extractor, exactly when every
statement has a witness.** So `KState` alone excludes it only through a witnessless statement,
which no digest can be shown to be under `Rel` (V3-S1-A13). -/
theorem acceptAll_kstate_iff (R : Digest → Wit → Prop) :
    (∃ E, Nonempty (KState R acceptAll E)) ↔ ∀ c, ∃ w, R c w :=
  ⟨fun ⟨_, ⟨k⟩⟩ c => (k.final [] c .empty k.empty rfl).imp fun _ h => h.2,
    fun h => ⟨fun c _ _ => some (h c).choose, ⟨⟨fun _ => True, fun _ _ _ => False, trivial,
      fun _ _ _ _ _ _ => trivial, fun _ c _ _ _ => ⟨_, rfl, (h c).choose_spec⟩⟩⟩⟩⟩

end RecursionFast
