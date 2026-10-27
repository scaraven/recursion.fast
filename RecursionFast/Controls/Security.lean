/-
# Controls: knowledge soundness and completeness (`Contract/Security.lean`) (DESIGN-v3 §4.2; V4-A10)

`KS` is the textbook single-output statement (V4-A10). The negatives below are proved against it
directly, each by exhibiting the adversary and its success probability; the positives either
directly or through the library's potential and the bridge `KState.ks`. The potential's own
controls (it against the Stage S1 boolean form, its length guard) are in
`Controls/Potential.lean`; those of this file are kept at the end as library facts.

**`KS`, positive:**
* `ws_ks`, `ws_complete`: the witness-sending argument (`Library/WitnessSending.lean`) is
  knowledge-sound at error `0` with no verifier query **under every public key** (v4: `Rel` of
  its own `acc vk`), through the potential `0` (`ws_kstate_trivial`), and complete at error `0`
  (V3-S2R-A2), through perfect completeness for every oracle and key (`ws_complete_perfect`,
  `Library/Completeness.lean`).
* `rejectAll_ks`: the verifier that rejects everything is knowledge-sound (for every relation and
  extractor, at error `0`). That is correct, and is why completeness is required:
  `rejectAll_not_complete` (negative: at no error below `1`, whatever the prover asks).
* `queryThenAccept_ks_one` (direct): the verifier that asks one query and accepts is
  knowledge-sound for the empty relation at error `1` (no probability exceeds `1`), so in
  `queryThenAccept_ks_ge_one` it is the error that fails.

**`KS`, negative:**
* Accept-everything (V3-S1-A13): for the empty relation the adversary that asks nothing and
  outputs `(0, ∅)` wins with probability exactly `1` (`acceptAll_wins`), so the accept-all
  verifier is knowledge-sound at no error with no query, whatever the extractor
  (`acceptAll_not_ks`); for the relation of every `acc` with the extractor that returns nothing,
  at no `qV ≤ logCap` with `qV · ε < 1` (`acceptAll_not_ks_none`). `acceptAll_ks_iff`
  (`Library/KS.lean`): it is knowledge-sound for some extractor exactly when every statement has a
  witness. **Not shown**: a digest without a witness in `Rel acc`; none can be exhibited for
  BLAKE2s, and if `nodeStmt` is onto, the accept-all verifier is knowledge-sound with a
  non-constructive extractor. What excludes it is the named extractor with its program and budget
  (`Controls/Certificate.lean`, `acceptAll_no_certificate`). The v4 analogue for a verifier that
  trusts signatures is `Library/SigTrust.lean` (C-m1).
* **The verifier's queries are charged** (`queryThenAccept_wins`, `queryThenAccept_ks_ge_one`):
  for the verifier that asks one query and accepts, and the empty relation, the adversary that
  asks nothing wins on every answer to the verifier's own query, with probability `1`; so `KS`
  with `qV = 1` needs `ε ≥ 1`. A bound charging only the adversary's `Q` would be `0` there, and
  the definition would be false of every verifier that draws a challenge itself.
* `oneQuery_not_KS`: a verifier that asks one query is not knowledge-sound with the query bound
  `qV = 0`, for every relation, extractor and error (the query conjunct of `KS`).

**What `KS` does not say** (`acceptAll_ks_above_logCap`): with `qV > logCap` no adversary is in
range, so the accept-all verifier is knowledge-sound for the empty relation at every error. The
certificate's cap `qV ≤ 2^16` excludes it (`Contract/Certificate.lean`).

**The library's potential (`KState`)**, v3's controls kept as facts about the library tool:
`queryThenAccept_ge_one` and `ks1` (the `step` law charges the verifier's query; the error is
what fails), `mono_control`, `acceptAll_no_kstate_empty`, `acceptAll_no_kstate_none`,
`jumpAll_ge_one`, `badAll_not_capped`; the boolean form (`BoolKState`): `bool_bounded_ge_one`,
`badAllBool_not_capped`, `rejectAllBool_bounded`, `rejectAllBool_μ`.
-/
import RecursionFast.Library.WitnessSending
import RecursionFast.Library.KS

open scoped NNReal

namespace RecursionFast.Controls.Security
open RecursionFast

/-! ## The witness-sending argument -/

theorem ws_ks (vk : Digest) :
    KS (Rel (WitnessSending.submission.acc vk)) (WitnessSending.V vk) WitnessSending.E 0 0 :=
  WitnessSending.ks vk

theorem ws_kstate_trivial (vk : Digest) : (WitnessSending.kstate vk).μ = fun _ => 0 := rfl

theorem ws_complete_perfect (vk : Digest) :
    Complete (Rel (WitnessSending.submission.acc vk)) (WitnessSending.P vk)
      (WitnessSending.V vk) :=
  WitnessSending.complete_perfect vk

theorem ws_complete (vk : Digest) :
    CompleteWithError (Rel (WitnessSending.submission.acc vk)) (WitnessSending.P vk)
      (WitnessSending.V vk) 0 :=
  WitnessSending.complete vk

/-! ## Reject everything -/

/-- The verifier that rejects every proof. -/
def rejectAll (_ : Digest) (_ : Proof) : OProg Bool := .ret false

/-- **Rejecting everything is knowledge-sound**, for every relation and extractor. -/
theorem rejectAll_ks (R : Digest → Wit → Prop) (E : Digest → Proof → Log → Option Wit) :
    KS R rejectAll E 0 0 :=
  KState.ks (KState.zero 0 fun _ _ _ h => nomatch h) fun _ _ _ => le_rfl

/-- **Rejecting everything is not complete** at any error below `1`: a leaf statement has a
witness, for every acceptance predicate and prover, and the rejection has probability `1`. -/
theorem rejectAll_not_complete (acc : Digest → Signed → Bool) (P : Digest → Wit → OProg Proof)
    {δ : ℝ≥0} (hδ : δ < 1) : ¬ CompleteWithError (Rel acc) P rejectAll δ := fun h =>
  absurd ((failProb_bind_false _ []).symm.trans_le (completeWithError_iff.mp h _
    (.leaf (Vector.replicate 32 0) 0) ⟨Nat.zero_le _, rfl⟩)) (not_le.mpr hδ)

/-! ## Accept everything (`acceptAll`, `Library/Security.lean`; `acceptAll_ks_iff`, `Library/KS`) -/

example (R : Digest → Wit → Prop) (ε : ℝ≥0) :
    (∃ E, KS R acceptAll E ε 0) ↔ ∀ c, ∃ w, R c w := acceptAll_ks_iff R ε

/-- **The adversary that asks nothing and outputs `(0, ∅)` wins with probability `1`** against
the accept-all verifier for the empty relation, whatever the extractor. -/
theorem acceptAll_wins (E : Digest → Proof → Log → Option Wit) :
    prob (Wins (fun _ _ => False) acceptAll E)
      ((OProg.ret (Vector.replicate 32 0, ByteArray.empty)).bind fun x =>
        (acceptAll x.1 x.2).bind fun _ => .ret x) [] = 1 :=
  accept_wins rfl (by simp)

/-- **Accepting everything is not knowledge-sound** for the empty relation, at any error, with
no query, whatever the extractor. -/
theorem acceptAll_not_ks (E : Digest → Proof → Log → Option Wit) (ε : ℝ≥0) :
    ¬ KS (fun _ _ => False) acceptAll E ε 0 :=
  not_ks_of_accept (c := Vector.replicate 32 0) (π := .empty) rfl (by simp) (Nat.zero_le _)
    (by simp)

/-- Nor for the relation of every acceptance predicate with the extractor that returns nothing, at
every `qV ≤ logCap` with `qV · ε < 1`. -/
theorem acceptAll_not_ks_none (acc : Digest → Signed → Bool) {ε : ℝ≥0} {qV : ℕ}
    (hq : qV ≤ logCap) (hε : (qV : ℝ≥0) * ε < 1) :
    ¬ KS (Rel acc) acceptAll (fun _ _ _ => none) ε qV :=
  not_ks_of_accept (c := Vector.replicate 32 0) (π := .empty) rfl (by simp) hq hε

/-- **What `KS` does not say**: above `logCap` no adversary is in range, so the accept-all
verifier is knowledge-sound for the empty relation at every error. -/
theorem acceptAll_ks_above_logCap (E : Digest → Proof → Log → Option Wit) (ε : ℝ≥0) :
    KS (fun _ _ => False) acceptAll E ε (logCap + 1) :=
  ⟨fun _ _ _ => Nat.zero_le _, fun _ _ _ hQ => absurd hQ (by omega)⟩

/-! ## The verifier's queries are charged -/

/-- Ask one query (the empty string), then accept. -/
def queryThenAccept (_ : Digest) (_ : Proof) : OProg Bool :=
  .query ByteArray.empty fun _ => .ret true

/-- **The adversary that asks nothing wins with probability `1`**: every answer to the verifier's
own query makes it accept, and the empty relation has no witness. -/
theorem queryThenAccept_wins (E : Digest → Proof → Log → Option Wit) :
    prob (Wins (fun _ _ => False) queryThenAccept E)
      ((OProg.ret (Vector.replicate 32 0, ByteArray.empty)).bind fun x =>
        (queryThenAccept x.1 x.2).bind fun _ => .ret x) [] = 1 := by
  have h : ∀ a : Digest, prob (Wins (fun _ _ => False) queryThenAccept E)
      (.ret (Vector.replicate 32 0, ByteArray.empty)) ([] ++ [(ByteArray.empty, a)]) = 1 :=
    fun a => (prob_ret _ _ _).trans
      (ind_of ⟨by simp [queryThenAccept, OProg.runLog], by simp⟩)
  show prob _ (.query ByteArray.empty fun _ => .ret _) [] = 1
  simp only [prob.eq_2, List.find?_nil, h, avg_const]

/-- **`KS` charges the verifier's query**: for the empty relation, a verifier that asks one query
and accepts is knowledge-sound with `qV = 1` only at `ε ≥ 1`. -/
theorem queryThenAccept_ks_ge_one (E : Digest → Proof → Log → Option Wit) {ε : ℝ≥0}
    (h : KS (fun _ _ => False) queryThenAccept E ε 1) : 1 ≤ ε := by
  simpa using (queryThenAccept_wins E).symm.trans_le
    (h.bound _ (Q := 0) (fun _ => le_rfl) (by decide))

/-- It is knowledge-sound at error `1`, so the error is what fails, not the definition. -/
theorem queryThenAccept_ks_one (E : Digest → Proof → Log → Option Wit) :
    KS (fun _ _ => False) queryThenAccept E 1 1 :=
  ⟨fun _ _ _ => le_rfl, fun _ _ _ _ => (prob_le_one _ _ _).trans (by simp)⟩

/-! ## The query bound -/

/-- **One query is not `qV = 0`**: the verifier asking one query is not knowledge-sound with the
query bound `0`, for every relation, extractor and error. -/
theorem oneQuery_not_KS (R : Digest → Wit → Prop) (E : Digest → Proof → Log → Option Wit)
    (ε : ℝ≥0) : ¬ KS R queryThenAccept E ε 0 := fun h =>
  Nat.not_succ_le_zero 0 (h.1 (fun _ => Vector.replicate 32 0) (Vector.replicate 32 0) .empty)

/-! ## The library's potential (`KState`): v3's controls, kept as library facts -/

/-- A knowledge state at error `0` is one at the cap. -/
theorem mono_control (vk : Digest) :
    Nonempty (KState (Rel (WitnessSending.submission.acc vk)) (WitnessSending.V vk)
      WitnessSending.E errorCap) :=
  ⟨(WitnessSending.kstate vk).mono (by positivity)⟩

example (R : Digest → Wit → Prop) (ε : ℝ≥0) :
    (∃ E, Nonempty (KState R acceptAll E ε)) ↔ ∀ c, ∃ w, R c w := acceptAll_kstate_iff R ε

/-- No knowledge state for the accept-all verifier and the empty relation, whatever the
extractor and the error. -/
theorem acceptAll_no_kstate_empty (E : Digest → Proof → Log → Option Wit) (ε : ℝ≥0) :
    IsEmpty (KState (fun _ _ => False) acceptAll E ε) :=
  no_kstate_of_empty (c := Vector.replicate 32 0) (π := ByteArray.empty) rfl (by simp)

/-- No knowledge state for the accept-all verifier and the extractor that returns nothing, for
the relation of every acceptance predicate, at every error. -/
theorem acceptAll_no_kstate_none (acc : Digest → Signed → Bool) (ε : ℝ≥0) :
    IsEmpty (KState (Rel acc) acceptAll (fun _ _ _ => none) ε) :=
  no_kstate_of_empty (c := Vector.replicate 32 0) (π := ByteArray.empty) rfl (by simp)

/-- The potential `0` on the empty log and `1` on every other. -/
noncomputable def jump (L : Log) : ℝ≥0 := if L = [] then 0 else 1

/-- `jump` satisfies `step` at error `1`: below `1` the log is empty, and no answer raises the
potential by more than `1`. -/
theorem jump_step (L : Log) (q : ByteArray) :
    ∑ a : Digest, jump (L ++ [(q, a)]) ≤ (jump L + 1) * 2 ^ 256 :=
  (Finset.sum_le_sum fun a _ => (ite_eq_right (by simp) : jump _ = 1).le).trans <| by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, fintype_card_digest,
      Nat.cast_pow, Nat.cast_ofNat]
    exact le_mul_of_one_le_left (by positivity) le_add_self

/-- A knowledge state (for the reject-all verifier, at error `1`) whose potential is `1` on every
non-empty log. -/
noncomputable def badAll (R : Digest → Wit → Prop) (E : Digest → Proof → Log → Option Wit) :
    KState R rejectAll E 1 where
  μ := jump
  empty := ite_eq_left rfl
  step L q _ _ _ := jump_step L q
  final _ _ _ _ _ h := nomatch h

/-- **A potential that is `1` off the empty log** needs `ε ≥ 1`. -/
theorem jumpAll_ge_one {R : Digest → Wit → Prop} {V : Digest → Proof → OProg Bool}
    {E : Digest → Proof → Log → Option Wit} {ε : ℝ≥0} (k : KState R V E ε)
    (hall : ∀ L, L ≠ [] → k.μ L = 1) : 1 ≤ ε := by
  simpa [k.empty] using k.one_le_of_jump (L := []) (q := ByteArray.empty) (by decide)
    (k.empty ▸ one_pos) nofun fun a => (hall _ (List.cons_ne_nil _ _)).ge

/-- `badAll`'s potential admits no error within the cap. -/
theorem badAll_not_capped {R : Digest → Wit → Prop} {E : Digest → Proof → Log → Option Wit}
    {ε : ℝ≥0} (k : KState R rejectAll E ε) (hk : k.μ = (badAll R E).μ) : ¬ ε ≤ errorCap :=
  fun hc => ((jumpAll_ge_one k fun L hL => (congrFun hk L).trans (ite_eq_right hL)).trans hc).not_gt
    errorCap_lt_one

/-- **The `step` law charges the verifier's query**: for the empty relation, `final` forces the
potential to `1` on every answer to the verifier's fresh query, so every knowledge state has
`ε ≥ 1`. -/
theorem queryThenAccept_ge_one (E : Digest → Proof → Log → Option Wit) {ε : ℝ≥0}
    (k : KState (fun _ _ => False) queryThenAccept E ε) : 1 ≤ ε := by
  have hj : ∀ a, 1 ≤ k.μ ([] ++ [(ByteArray.empty, a)]) := fun a => not_lt.mp fun hb =>
    (k.final _ (Vector.replicate 32 0) .empty (by simp [logCap]) hb
      (by simp [queryThenAccept, OProg.runLog])).elim fun _ h => h.2
  simpa [k.empty] using k.one_le_of_jump (by simp [logCap]) (k.empty ▸ one_pos) (by simp) hj

/-- Such a knowledge state exists at error `1` (the potential is `1` on every non-empty log), so
the error is what fails, not the laws. -/
noncomputable def ks1 (E : Digest → Proof → Log → Option Wit) :
    KState (fun _ _ => False) queryThenAccept E 1 where
  μ := jump
  empty := ite_eq_left rfl
  step L q _ _ _ := jump_step L q
  final L c π _ hL h := by
    obtain rfl : L = [] := by_contra fun hne => by simp [jump, hne] at hL
    simp [queryThenAccept, OProg.runLog] at h

/-! ### The boolean form (`BoolKState`, library) -/

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

end RecursionFast.Controls.Security
