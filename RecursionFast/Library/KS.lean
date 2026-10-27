/-
  RecursionFast.Library.KS  (UNTRUSTED, kernel-checked)

  Facts about the contract's knowledge soundness (`Contract/Security.lean`, `KS`, V4-A10).

  * `Wins R V E x L`: the event `KS` bounds, on the output `x` and the final log `L` (`V` accepts
    `x` on `L`, `E` returns no witness of `R` for it on `L`); `KS.bound` restates `KS` with it.
  * **An adversary that reads its own log** (`KS.select`): for every query program `A` asking at
    most `Q` queries, of any output type, and every function `sel` of its output and its final
    log to a statement and a proof, the probability that `sel`'s pair wins on `A`'s final log is
    at most `(Q + qV) · ε`. The `KS` adversary is `withLog A` followed by `sel`
    (`Library/Prob.lean`): `E` and `sel` are Lean functions and the adversary is unbounded, so it
    computes them; and `V` run after it on a pair it accepts on the log asks nothing fresh.
  * **The union bound** (`KS.union`): over a finite family of such selections, at most
    `|I| · (Q + qV) · ε`. The tree's composition (`Library/Compose.lean`) rests on it.
  * `KS.of_extracts` (positive, the twin of `KState.zero`): when every proof the verifier accepts
    on every log is extracted, `KS` holds at every error. `KS.mono`: a larger error and bound.
  * `not_ks_of_accept` (negative): a verifier that accepts some proof with no oracle answer, which
    the extractor does not open on the empty log, is not knowledge-sound at any `ε` and
    `qV ≤ logCap` with `qV · ε < 1`: the adversary that outputs that pair and asks nothing wins
    with probability `1` (`accept_wins`). `small_of_caps`: the certificate's caps give both
    conditions.
  * `acceptAll_ks_iff`: the verifier that accepts everything is knowledge-sound with no query, for
    some extractor, exactly when every statement has a witness (V3-S1-A13), at every error: `KS`
    alone does not exclude it, the named extractor's program and budget do.
-/
import RecursionFast.Library.Prob

open scoped NNReal

namespace RecursionFast
variable {α : Type} {R : Digest → Wit → Prop} {V : Digest → Proof → OProg Bool}
  {E : Digest → Proof → Log → Option Wit} {ε : ℝ≥0} {qV : ℕ}

/-- **The adversary wins** on the output `x` and the final log `L`: `V` accepts `x` reading its
answers from `L`, and `E`, given `x` and `L`, returns no witness of `R`. -/
def Wins (R : Digest → Wit → Prop) (V : Digest → Proof → OProg Bool)
    (E : Digest → Proof → Log → Option Wit) (x : Digest × Proof) (L : Log) : Prop :=
  (V x.1 x.2).runLog L = some true ∧ ¬ ∃ w, E x.1 x.2 L = some w ∧ R x.1 w

/-- `KS`'s bound, with the event named. -/
theorem KS.bound (h : KS R V E ε qV) (A : OProg (Digest × Proof)) {Q : ℕ}
    (hA : ∀ H, (A.queries H).length ≤ Q) (hQ : Q + qV ≤ logCap) :
    prob (Wins R V E) (A.bind fun x => (V x.1 x.2).bind fun _ => .ret x) [] ≤ (Q + qV) * ε :=
  h.2 A Q hA hQ

/-- **Knowledge soundness against an adversary that outputs a function of its own log**: the
probability that the pair `sel x L` wins on the final log `L` of a run of `A`, `A` asking at most
`Q` queries, is at most `(Q + qV) · ε`. -/
theorem KS.select (h : KS R V E ε qV) (A : OProg α) {Q : ℕ} (hA : ∀ H, (A.queries H).length ≤ Q)
    (hQ : Q + qV ≤ logCap) (sel : α → Log → Digest × Proof) :
    prob (fun x L => Wins R V E (sel x L) L) A [] ≤ (Q + qV) * ε := by
  let A' : OProg (Digest × Proof) := (withLog A []).bind fun y => .ret (sel y.1 y.2)
  have hA' : ∀ H, (A'.queries H).length ≤ Q := fun H => by
    simp only [A', OProg.queries_bind, List.length_append, OProg.queries, List.length_nil,
      Nat.add_zero]
    exact (queries_withLog_le H A [] fun _ _ h => nomatch h).trans (hA H)
  refine le_trans ?_ (h.bound A' hA' hQ)
  rw [OProg.bind_assoc, prob_bind, expect_withLog, prob_eq_expect]
  refine expect_mono (fun x L => ?_) A []
  by_cases hw : Wins R V E (sel x L) L
  · rw [ind_of (B := fun x L => Wins R V E (sel x L) L) hw]
    show 1 ≤ prob _ ((V (sel x L).1 (sel x L).2).bind fun _ => .ret (sel x L)) L
    rw [prob_bind_of_runLog _ _ hw.1, prob_ret, ind_of hw]
  · rw [ind_of_not (B := fun x L => Wins R V E (sel x L) L) hw]; exact bot_le

/-- **The union bound over selections**: the probability that one of the pairs `sel i x L`,
`i ∈ I`, wins on the final log of a run of `A` is at most `|I| · (Q + qV) · ε`. -/
theorem KS.union (h : KS R V E ε qV) (A : OProg α) {Q : ℕ} (hA : ∀ H, (A.queries H).length ≤ Q)
    (hQ : Q + qV ≤ logCap) {ι : Type} (I : Finset ι) (sel : ι → α → Log → Digest × Proof) :
    prob (fun x L => ∃ i ∈ I, Wins R V E (sel i x L) L) A [] ≤ I.card * ((Q + qV) * ε) := by
  refine (prob_exists_le I _ A []).trans ?_
  rw [← nsmul_eq_mul]
  exact Finset.sum_le_card_nsmul _ _ _ fun i _ => h.select A hA hQ (sel i)

/-- **No escape, no error**: when every proof the verifier accepts on every log is extracted to a
witness, `KS` holds at every error. -/
theorem KS.of_extracts (hq : ∀ H c π, ((V c π).queries H).length ≤ qV)
    (h : ∀ L c π, (V c π).runLog L = some true → ∃ w, E c π L = some w ∧ R c w) (ε : ℝ≥0) :
    KS R V E ε qV :=
  ⟨hq, fun _ _ _ _ => (prob_eq_zero (fun x L hx => hx.2 (h L x.1 x.2 hx.1)) _ _).trans_le
    bot_le⟩

/-- A larger error and a larger query bound. -/
theorem KS.mono (h : KS R V E ε qV) {ε' : ℝ≥0} {qV' : ℕ} (hε : ε ≤ ε') (hq : qV ≤ qV') :
    KS R V E ε' qV' :=
  ⟨fun H c π => (h.1 H c π).trans hq, fun A Q hA hQ =>
    (h.2 A Q hA (by omega)).trans (by gcongr)⟩

/-- **The adversary that outputs `(c, π)` and asks nothing wins with probability `1`** when the
verifier accepts it with no answer and the extractor does not open it on the empty log. -/
theorem accept_wins {c : Digest} {π : Proof} (hV : (V c π).runLog [] = some true)
    (hE : ¬ ∃ w, E c π [] = some w ∧ R c w) :
    prob (Wins R V E) ((OProg.ret (c, π)).bind fun x => (V x.1 x.2).bind fun _ => .ret x) [] =
      1 :=
  (prob_bind_of_runLog (Wins R V E) (fun _ => .ret (c, π)) hV).trans (ind_of ⟨hV, hE⟩)

/-- **Not knowledge-sound**: a verifier that accepts a proof with no oracle answer which the
extractor does not open on the empty log, at every `ε` and `qV ≤ logCap` with `qV · ε < 1`. -/
theorem not_ks_of_accept {c : Digest} {π : Proof} (hV : (V c π).runLog [] = some true)
    (hE : ¬ ∃ w, E c π [] = some w ∧ R c w) (hq : qV ≤ logCap) (hε : (qV : ℝ≥0) * ε < 1) :
    ¬ KS R V E ε qV := fun h => by
  have hb := h.bound (.ret (c, π)) (Q := 0) (fun _ => le_rfl) (by simpa using hq)
  rw [accept_wins hV hE] at hb
  exact absurd hb (not_le.mpr (by simpa using hε))

/-- The certificate's caps (`qV ≤ 2^16`, `ε ≤ errorCap`) give `qV ≤ logCap` and `qV · ε < 1`. -/
theorem small_of_caps (hq : qV ≤ 2 ^ 16) (hε : ε ≤ errorCap) :
    qV ≤ logCap ∧ (qV : ℝ≥0) * ε < 1 := by
  refine ⟨hq.trans (by simp [logCap]), ?_⟩
  calc (qV : ℝ≥0) * ε ≤ 2 ^ 16 * errorCap := mul_le_mul' (by exact_mod_cast hq) hε
    _ < 1 := by
      rw [errorCap, ← NNReal.coe_lt_coe]
      push_cast
      norm_num

/-- **The accept-all verifier is knowledge-sound with no query, for some extractor, exactly when
every statement has a witness**, at every error (V3-S1-A13). -/
theorem acceptAll_ks_iff (R : Digest → Wit → Prop) (ε : ℝ≥0) :
    (∃ E, KS R acceptAll E ε 0) ↔ ∀ c, ∃ w, R c w :=
  ⟨fun ⟨_, h⟩ c => by_contra fun hno =>
      not_ks_of_accept (c := c) (π := .empty) rfl (fun ⟨w, _, hw⟩ => hno ⟨w, hw⟩)
        (Nat.zero_le _) (by simp) h,
    fun h => ⟨fun c _ _ => some (h c).choose,
      KS.of_extracts (fun _ _ _ => le_rfl) (fun _ c _ _ => ⟨_, rfl, (h c).choose_spec⟩) ε⟩⟩

end RecursionFast
