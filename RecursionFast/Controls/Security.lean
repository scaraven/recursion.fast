/-
# Controls: knowledge soundness and completeness (`Contract/Security.lean`)    (DESIGN-v3 §4.2)

The potential form of `KState` (V3-KS-A1). The controls that separate it from the Stage S1
boolean form, and that show the length guard is load-bearing, are in `Controls/Potential.lean`.

Positive:
* `ws_ks`, `ws_complete`: the witness-sending argument (`Library/WitnessSending.lean`) is
  knowledge-sound at error `0` with no verifier query, through the knowledge state with potential
  `0` (`ws_kstate_trivial`), and complete at error `0` (V3-S2R-A2), through perfect completeness
  for every oracle (`ws_complete_perfect`, `Library/Completeness.lean`).
* `rejectAll_ks`: the verifier that rejects everything is knowledge-sound (for every relation and
  extractor, at error `0`). That is correct, and is why completeness is required:
  `rejectAll_not_complete` (negative: at no error below `1`, whatever the prover asks).
* `ks1`: the verifier that asks one query and accepts has a knowledge state at error `1` for the
  empty relation (the potential is `1` on every non-empty log), so in `queryThenAccept_ge_one` it
  is the error that fails.
* `mono_control`: a knowledge state at error `0` is one at `errorCap` (`KState.mono`).

Negative:
* `queryThenAccept_ge_one` (the `step` law, V3-S1 review M2): for a verifier that asks one query
  and accepts, every knowledge state for the empty relation needs `ε ≥ 1`: `final` forces the
  potential to `1` on every one-entry log, and `step` charges that jump to the verifier's own
  fresh query. A contract whose `step` did not average over the answers, or whose `final` did not
  bind on non-empty logs, would not build this control.
* Accept-everything (V3-S1-A13): `acceptAll_kstate_iff` (Library) says it has a knowledge state,
  for some extractor, exactly when every statement has a witness. So it has none for a relation
  with a witnessless statement (`acceptAll_no_kstate_empty`: the empty relation, every
  extractor and error), and none with an extractor that returns no witness
  (`acceptAll_no_kstate_none`: the contract's relation, every verifier instance and error).
  **Not shown**: a digest without a witness in `Rel Vb`; none can be exhibited for BLAKE2s, and if
  `nodeStmt` is onto, the accept-all verifier has a knowledge state with a non-constructive
  extractor. What excludes it is the named extractor with its program and budget
  (`Controls/Certificate.lean`, `acceptAll_no_certificate`).
* `jumpAll_ge_one`, `badAll_not_capped`: a knowledge state whose potential is `1` on every
  non-empty log has `ε ≥ 1`, above `errorCap`; one exists (`badAll`), so this is not vacuous.
* `oneQuery_not_KS`: a verifier that asks one query is not knowledge-sound with the query bound
  `qV = 0`, for every relation, extractor and error (the query conjunct of `KS`).

The boolean form (library `BoolKState`, S1's statements kept): `bool_bounded_ge_one`,
`badAllBool_not_capped` (negative: every answer bad is bounded only at `ε ≥ 1`);
`rejectAllBool_bounded`, `rejectAllBool_μ` (positive: no bad answer is bounded at the cap, and
embeds as the potential `0`).
-/
import RecursionFast.Library.WitnessSending

open scoped NNReal

namespace RecursionFast.Controls.Security
open RecursionFast

/-! ## The witness-sending argument -/

theorem ws_ks : KS (Rel WitnessSending.submission.Vb) WitnessSending.V WitnessSending.E 0 0 :=
  WitnessSending.ks

theorem ws_kstate_trivial : WitnessSending.kstate.μ = fun _ => 0 := rfl

theorem ws_complete_perfect :
    Complete (Rel WitnessSending.submission.Vb) WitnessSending.P WitnessSending.V :=
  WitnessSending.complete_perfect

theorem ws_complete :
    CompleteWithError (Rel WitnessSending.submission.Vb) WitnessSending.P WitnessSending.V 0 :=
  WitnessSending.complete

/-- A knowledge state at error `0` is one at the cap. -/
theorem mono_control :
    Nonempty (KState (Rel WitnessSending.submission.Vb) WitnessSending.V WitnessSending.E
      errorCap) :=
  ⟨WitnessSending.kstate.mono (by positivity)⟩

/-! ## Reject everything -/

/-- The verifier that rejects every proof. -/
def rejectAll (_ : Digest) (_ : Proof) : OProg Bool := .ret false

/-- **Rejecting everything is knowledge-sound**, for every relation and extractor. -/
theorem rejectAll_ks (R : Digest → Wit → Prop) (E : Digest → Proof → Log → Option Wit) :
    KS R rejectAll E 0 0 :=
  ⟨⟨KState.zero 0 fun _ _ _ h => nomatch h⟩, fun _ _ _ => le_rfl⟩

/-- **Rejecting everything is not complete** at any error below `1`: a leaf statement has a
witness, for every verifier instance and prover, and the rejection has probability `1`. -/
theorem rejectAll_not_complete (Vb : Digest → Proof → Bool) (P : Digest → Wit → OProg Proof)
    {δ : ℝ≥0} (hδ : δ < 1) : ¬ CompleteWithError (Rel Vb) P rejectAll δ := fun h =>
  absurd ((failProb_bind_false _ []).symm.trans_le
    (h _ (.leaf (Vector.replicate 32 0) 0) ⟨Nat.zero_le _, rfl⟩)) (not_le.mpr hδ)

/-! ## Accept everything (`acceptAll`, `acceptAll_kstate_iff`: `Library/Security.lean`) -/

example (R : Digest → Wit → Prop) (ε : ℝ≥0) :
    (∃ E, Nonempty (KState R acceptAll E ε)) ↔ ∀ c, ∃ w, R c w := acceptAll_kstate_iff R ε

/-- No knowledge state for the accept-all verifier and the empty relation, whatever the
extractor and the error. -/
theorem acceptAll_no_kstate_empty (E : Digest → Proof → Log → Option Wit) (ε : ℝ≥0) :
    IsEmpty (KState (fun _ _ => False) acceptAll E ε) :=
  no_kstate_of_empty (c := Vector.replicate 32 0) (π := ByteArray.empty) rfl (by simp)

/-- No knowledge state for the accept-all verifier and the extractor that returns nothing, for
the relation of every verifier instance, at every error. -/
theorem acceptAll_no_kstate_none (Vb : Digest → Proof → Bool) (ε : ℝ≥0) :
    IsEmpty (KState (Rel Vb) acceptAll (fun _ _ _ => none) ε) :=
  no_kstate_of_empty (c := Vector.replicate 32 0) (π := ByteArray.empty) rfl (by simp)

/-! ## A jump at every answer -/

/-- The potential `0` on the empty log and `1` on every other. -/
noncomputable def jump (L : Log) : ℝ≥0 := if L = [] then 0 else 1

/-- `jump` satisfies `step` at error `1`: below `1` the log is empty, and no answer raises the
potential by more than `1`. -/
theorem jump_step (L : Log) (q : ByteArray) :
    ∑ a : Digest, jump (L ++ [(q, a)]) ≤ (jump L + 1) * 2 ^ 256 :=
  (Finset.sum_le_sum fun a _ => show jump _ ≤ 1 by unfold jump; split_ifs <;> simp).trans <| by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, fintype_card_digest,
      Nat.cast_pow, Nat.cast_ofNat]
    exact le_mul_of_one_le_left (by positivity) le_add_self

/-- A knowledge state (for the reject-all verifier, at error `1`) whose potential is `1` on every
non-empty log. -/
noncomputable def badAll (R : Digest → Wit → Prop) (E : Digest → Proof → Log → Option Wit) :
    KState R rejectAll E 1 where
  μ := jump
  empty := by simp [jump]
  step L q _ _ _ := jump_step L q
  final _ _ _ _ _ h := nomatch h

/-- **A potential that is `1` off the empty log** needs `ε ≥ 1`. -/
theorem jumpAll_ge_one {R : Digest → Wit → Prop} {V : Digest → Proof → OProg Bool}
    {E : Digest → Proof → Log → Option Wit} {ε : ℝ≥0} (k : KState R V E ε)
    (hall : ∀ L, L ≠ [] → k.μ L = 1) : 1 ≤ ε := by
  simpa [k.empty] using k.one_le_of_jump (L := []) (q := ByteArray.empty) (by simp [logCap])
    (by simp [k.empty]) (by simp) fun a => (hall _ (by simp)).ge

/-- `badAll`'s potential admits no error within the cap. -/
theorem badAll_not_capped {R : Digest → Wit → Prop} {E : Digest → Proof → Log → Option Wit}
    {ε : ℝ≥0} (k : KState R rejectAll E ε) (hk : k.μ = (badAll R E).μ) : ¬ ε ≤ errorCap :=
  fun hc => ((jumpAll_ge_one k fun L hL => by simp [hk, badAll, jump, hL]).trans hc).not_gt
    errorCap_lt_one

/-! ## The boolean form (`BoolKState`, library) -/

/-- S1's every-answer-bad state, as a boolean state of the reject-all verifier. -/
def badAllBool (R : Digest → Wit → Prop) (E : Digest → Proof → Log → Option Wit) :
    BoolKState R rejectAll E :=
  ⟨fun _ => True, fun _ _ _ => True, trivial, fun _ _ _ _ _ _ => trivial,
    fun _ _ _ _ h => nomatch h⟩

/-- S1's `bounded_ge_one`, on `BoolKState`: every answer bad is bounded only at `ε ≥ 1`. -/
theorem bool_bounded_ge_one {R : Digest → Wit → Prop} {V : Digest → Proof → OProg Bool}
    {E : Digest → Proof → Log → Option Wit} (k : BoolKState R V E) (hall : ∀ L q a, k.bad L q a)
    {ε : ℝ≥0} (h : k.Bounded ε) : 1 ≤ ε :=
  k.one_le_of_bounded h [] ByteArray.empty (hall [] _)

/-- `badAllBool` is bounded at no error within the cap. -/
theorem badAllBool_not_capped (R : Digest → Wit → Prop) (E : Digest → Proof → Log → Option Wit)
    {ε : ℝ≥0} (h : (badAllBool R E).Bounded ε) : ¬ ε ≤ errorCap := fun hc =>
  ((bool_bounded_ge_one _ (fun _ _ _ => trivial) h).trans hc).not_gt errorCap_lt_one

/-- The boolean reject-all state with no bad answer. -/
def rejectAllBool (R : Digest → Wit → Prop) (E : Digest → Proof → Log → Option Wit) :
    BoolKState R rejectAll E :=
  ⟨fun _ => True, fun _ _ _ => False, trivial, fun _ _ _ _ _ _ => trivial,
    fun _ _ _ _ h => nomatch h⟩

/-- No bad answer: bounded at `0`, hence at the cap (`bounded_of_not_bad`, `Bounded.mono`). -/
theorem rejectAllBool_bounded (R : Digest → Wit → Prop) (E : Digest → Proof → Log → Option Wit) :
    (rejectAllBool R E).Bounded errorCap :=
  ((rejectAllBool R E).bounded_of_not_bad (fun _ _ _ h => h) 0).mono (by positivity)

/-- Its embedding has potential `0` on every log (`KState.ofBool_μ_eq_zero`). -/
theorem rejectAllBool_μ (R : Digest → Wit → Prop) (E : Digest → Proof → Log → Option Wit)
    (L : Log) : (KState.ofBool (rejectAllBool R E) (rejectAllBool_bounded R E).below).μ L = 0 :=
  (KState.ofBool_μ_eq_zero _ _ L).mpr trivial

/-! ## The `step` law -/

/-- Ask one query (the empty string), then accept. -/
def queryThenAccept (_ : Digest) (_ : Proof) : OProg Bool :=
  .query ByteArray.empty fun _ => .ret true

/-- **The `step` law charges the verifier's query**: for the empty relation, `final` forces the
potential to `1` on every answer to the verifier's fresh query, so every knowledge state has
`ε ≥ 1`. -/
theorem queryThenAccept_ge_one (E : Digest → Proof → Log → Option Wit) {ε : ℝ≥0}
    (k : KState (fun _ _ => False) queryThenAccept E ε) : 1 ≤ ε := by
  have hj : ∀ a, 1 ≤ k.μ ([] ++ [(ByteArray.empty, a)]) := fun a => by
    by_contra hb
    obtain ⟨w, -, hw⟩ := k.final _ (Vector.replicate 32 0) ByteArray.empty
      (by simp [logCap]) (not_le.mp hb)
      (by simp [queryThenAccept, OProg.runLog])
    exact hw
  simpa [k.empty] using k.one_le_of_jump (by simp [logCap]) (by simp [k.empty]) (by simp) hj

/-- Such a knowledge state exists at error `1` (the potential is `1` on every non-empty log), so
the error is what fails, not the laws. -/
noncomputable def ks1 (E : Digest → Proof → Log → Option Wit) :
    KState (fun _ _ => False) queryThenAccept E 1 where
  μ := jump
  empty := by simp [jump]
  step L q _ _ _ := jump_step L q
  final L c π _ hL h := by
    have : L = [] := by by_contra hne; simp [jump, hne] at hL
    subst this; simp [queryThenAccept, OProg.runLog] at h

/-! ## The query bound -/

/-- **One query is not `qV = 0`**: the verifier asking one query is not knowledge-sound with the
query bound `0`, for every relation, extractor and error. -/
theorem oneQuery_not_KS (R : Digest → Wit → Prop) (E : Digest → Proof → Log → Option Wit)
    (ε : ℝ≥0) : ¬ KS R queryThenAccept E ε 0 := fun h =>
  Nat.not_succ_le_zero 0 (h.2 (fun _ => Vector.replicate 32 0) (Vector.replicate 32 0) .empty)

end RecursionFast.Controls.Security
