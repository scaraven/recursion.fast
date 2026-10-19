/-
# Controls: knowledge soundness and completeness (`Contract/Security.lean`)    (DESIGN-v3 §4.2)

Positive:
* `ws_ks`, `ws_complete`: the witness-sending argument (`Library/WitnessSending.lean`) is
  knowledge-sound at error `0` with no verifier query, through the knowledge state with
  `good := True`, `bad := False` (`ws_kstate_trivial`), and perfectly complete for every oracle.
* `rejectAll_ks`: the verifier that rejects everything is knowledge-sound (for every relation and
  extractor, at error `0`). That is correct, and is why completeness is required:
  `rejectAll_not_complete` (negative).
* `ks1`: the verifier that asks one query and accepts has a knowledge state for the empty
  relation (every answer bad), so in `queryThenAccept_ge_one` it is the bound that fails.

Negative:
* `queryThenAccept_ge_one` (the `step` law, V3-S1 review M2): for a verifier that asks one query
  and accepts, every knowledge state for the empty relation needs `ε ≥ 1`: the verifier's own
  fresh query is charged, and `final` binds on the non-empty log `step` produces. A contract whose
  `step` concluded `good L` would not build this control.
* Accept-everything (V3-S1-A13): `acceptAll_kstate_iff` (Library) says it has a knowledge state,
  for some extractor, exactly when every statement has a witness. So it has none for a relation
  with a witnessless statement (`acceptAll_no_kstate_empty`: the empty relation, every
  extractor), and none with an extractor that returns no witness (`acceptAll_no_kstate_none`: the
  contract's relation, every verifier instance). **Not shown**: a digest without a witness in
  `Rel Vb`; none can be exhibited for BLAKE2s, and if `nodeStmt` is onto, the accept-all verifier
  has a knowledge state with a non-constructive extractor. What excludes it is the named
  extractor with its image and budget (`Controls/Certificate.lean`, `acceptAll_no_certificate`).
* `bounded_ge_one`, `badAll_not_capped`: a knowledge state for which every answer is bad is
  bounded only at `ε ≥ 1`, above `errorCap`; one exists (`badAll`), so this is not vacuous.
* `oneQuery_not_KS`: a verifier that asks one query is not knowledge-sound with the query bound
  `qV = 0`, for every relation, extractor and error (the query conjunct of `KS`).
-/
import RecursionFast.Library.WitnessSending

open scoped NNReal

namespace RecursionFast.Controls.Security
open RecursionFast

/-! ## The witness-sending argument -/

theorem ws_ks : KS (Rel WitnessSending.submission.Vb) WitnessSending.V WitnessSending.E 0 0 :=
  WitnessSending.ks

theorem ws_kstate_trivial : WitnessSending.kstate.good = (fun _ => True) ∧
    WitnessSending.kstate.bad = (fun _ _ _ => False) := ⟨rfl, rfl⟩

theorem ws_complete :
    Complete (Rel WitnessSending.submission.Vb) WitnessSending.P WitnessSending.V :=
  WitnessSending.complete

/-! ## Reject everything -/

/-- The verifier that rejects every proof. -/
def rejectAll (_ : Digest) (_ : Proof) : OProg Bool := .ret false

/-- **Rejecting everything is knowledge-sound**, for every relation and extractor. -/
theorem rejectAll_ks (R : Digest → Wit → Prop) (E : Digest → Proof → Log → Option Wit) :
    KS R rejectAll E 0 0 :=
  ⟨⟨⟨fun _ => True, fun _ _ _ => False, trivial, fun _ _ _ _ _ _ => trivial,
    fun _ _ _ _ h => nomatch h⟩, KState.bounded_of_not_bad _ (fun _ _ _ h => h) 0⟩,
    fun _ _ _ => le_rfl⟩

/-- **Rejecting everything is not complete**: a leaf statement has a witness, for every
verifier instance and prover. -/
theorem rejectAll_not_complete (Vb : Digest → Proof → Bool) (P : Digest → Wit → OProg Proof) :
    ¬ Complete (Rel Vb) P rejectAll := fun h =>
  Bool.false_ne_true
    (h (fun _ => Vector.replicate 32 0) _ (.leaf (Vector.replicate 32 0) 0) ⟨Nat.zero_le _, rfl⟩)

/-! ## Accept everything (`acceptAll`, `acceptAll_kstate_iff`: `Library/Security.lean`) -/

example (R : Digest → Wit → Prop) :
    (∃ E, Nonempty (KState R acceptAll E)) ↔ ∀ c, ∃ w, R c w := acceptAll_kstate_iff R

/-- No knowledge state for the accept-all verifier and the empty relation, whatever the
extractor. -/
theorem acceptAll_no_kstate_empty (E : Digest → Proof → Log → Option Wit) :
    IsEmpty (KState (fun _ _ => False) acceptAll E) :=
  no_kstate_of_empty (c := Vector.replicate 32 0) (π := ByteArray.empty) rfl (by simp)

/-- No knowledge state for the accept-all verifier and the extractor that returns nothing, for
the relation of every verifier instance. -/
theorem acceptAll_no_kstate_none (Vb : Digest → Proof → Bool) :
    IsEmpty (KState (Rel Vb) acceptAll (fun _ _ _ => none)) :=
  no_kstate_of_empty (c := Vector.replicate 32 0) (π := ByteArray.empty) rfl (by simp)

/-! ## Every answer bad -/

/-- A knowledge state (for the reject-all verifier) in which every answer is bad. -/
def badAll (R : Digest → Wit → Prop) (E : Digest → Proof → Log → Option Wit) :
    KState R rejectAll E where
  good _ := True
  bad _ _ _ := True
  empty := trivial
  step _ _ _ _ _ _ := trivial
  final _ _ _ _ h := nomatch h

/-- **Every answer bad**: bounded only at `ε ≥ 1`. -/
theorem bounded_ge_one {R : Digest → Wit → Prop} {V : Digest → Proof → OProg Bool}
    {E : Digest → Proof → Log → Option Wit} (k : KState R V E) (hall : ∀ L q a, k.bad L q a)
    {ε : ℝ≥0} (h : k.Bounded ε) : 1 ≤ ε :=
  k.one_le_of_bounded h [] ByteArray.empty (hall [] _)

/-- `badAll` is bounded at no error within the cap. -/
theorem badAll_not_capped (R : Digest → Wit → Prop) (E : Digest → Proof → Log → Option Wit)
    {ε : ℝ≥0} (h : (badAll R E).Bounded ε) : ¬ ε ≤ errorCap := fun hc =>
  ((bounded_ge_one _ (fun _ _ _ => trivial) h).trans hc).not_gt errorCap_lt_one

/-! ## The `step` law -/

/-- Ask one query (the empty string), then accept. -/
def queryThenAccept (_ : Digest) (_ : Proof) : OProg Bool :=
  .query ByteArray.empty fun _ => .ret true

/-- **The `step` law charges the verifier's query**: for the empty relation, every answer to the
verifier's fresh query is bad, so every bounded knowledge state has `ε ≥ 1`. -/
theorem queryThenAccept_ge_one (E : Digest → Proof → Log → Option Wit)
    (k : KState (fun _ _ => False) queryThenAccept E) {ε : ℝ≥0} (h : k.Bounded ε) : 1 ≤ ε := by
  refine k.one_le_of_bounded h [] ByteArray.empty fun a => ?_
  by_contra hb
  obtain ⟨w, -, hw⟩ := k.final _ (Vector.replicate 32 0) ByteArray.empty
    (k.step [] ByteArray.empty a k.empty (by simp) hb) (by simp [queryThenAccept, OProg.runLog])
  exact hw

/-- Such a knowledge state exists (every answer bad), so the bound is what fails, not the laws. -/
def ks1 (E : Digest → Proof → Log → Option Wit) :
    KState (fun _ _ => False) queryThenAccept E where
  good L := L = []
  bad _ _ _ := True
  empty := rfl
  step _ _ _ _ _ h := absurd trivial h
  final L c π hL h := by subst hL; simp [queryThenAccept, OProg.runLog] at h

/-! ## The query bound -/

/-- **One query is not `qV = 0`**: the verifier asking one query is not knowledge-sound with the
query bound `0`, for every relation, extractor and error. -/
theorem oneQuery_not_KS (R : Digest → Wit → Prop) (E : Digest → Proof → Log → Option Wit)
    (ε : ℝ≥0) : ¬ KS R queryThenAccept E ε 0 := fun h =>
  Nat.not_succ_le_zero 0 (h.2 (fun _ => Vector.replicate 32 0) (Vector.replicate 32 0) .empty)

end RecursionFast.Controls.Security
