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
    on every log is extracted, `KS` holds at every error.
  * `prob_accept_eq_verdict` (review E-ks m-3): the event's acceptance, read from the final log by
    `runLog`, is the verifier's verdict in the game's run (`expect_congr_runLog`).
  * **The textbook notion, and how `KS` relates to it** (review E-ks M-1; the user's choice of
    2026-10-27, V4-A10). `KSTextbook`: the extractor reads only the **adversary's** log
    (`withLog`), the verifier runs afterwards on the same oracle (Chiesa–Yogev; CGSY24). `KS`'s
    extractor reads the final log, which also holds the verifier's own answers: `KS` is the
    textbook notion for adversaries that ask the verifier's queries themselves (normalised).
    **`KSTextbook.ks`**: textbook ⇒ `KS`, same extractor, error doubled (`KS`'s game is a textbook
    adversary of `Q + qV` queries whose log is `KS`'s final log), for queries up to
    `logCap + qV`. The converse fails: `Controls/Security.lean`, `lucky_ks`, `lucky_not_textbook`.
    `KSTextbook.of_extracts`: an extractor that opens every accepted proof from any log is
    textbook-sound at error `0`.
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
    rw [OProg.queries_bind, List.length_append]
    exact (queries_withLog_le H A [] fun _ _ h => nomatch h).trans (hA H)
  refine le_trans ?_ (h.bound A' hA' hQ)
  rw [OProg.bind_assoc, prob_bind, expect_withLog, prob_eq_expect]
  refine expect_mono (fun x L => ind_le fun hw => ?_) A []
  dsimp only [OProg.bind]
  rw [prob_bind_of_runLog _ _ hw.1, prob_ret, ind_of hw]

/-- **The union bound over selections**: the probability that one of the pairs `sel i x L`,
`i ∈ I`, wins on the final log of a run of `A` is at most `|I| · (Q + qV) · ε`. -/
theorem KS.union (h : KS R V E ε qV) (A : OProg α) {Q : ℕ} (hA : ∀ H, (A.queries H).length ≤ Q)
    (hQ : Q + qV ≤ logCap) {ι : Type} (I : Finset ι) (sel : ι → α → Log → Digest × Proof) :
    prob (fun x L => ∃ i ∈ I, Wins R V E (sel i x L) L) A [] ≤ I.card * ((Q + qV) * ε) :=
  (prob_exists_le I _ A []).trans ((Finset.sum_le_card_nsmul _ _ _ fun i _ =>
    h.select A hA hQ (sel i)).trans_eq (nsmul_eq_mul _ _))

/-- **No escape, no error**: when every proof the verifier accepts on every log is extracted to a
witness, `KS` holds at every error. -/
theorem KS.of_extracts (hq : ∀ H c π, ((V c π).queries H).length ≤ qV)
    (h : ∀ L c π, (V c π).runLog L = some true → ∃ w, E c π L = some w ∧ R c w) (ε : ℝ≥0) :
    KS R V E ε qV :=
  ⟨hq, fun _ _ _ _ => (prob_eq_zero (fun x L hx => hx.2 (h L x.1 x.2 hx.1)) _ _).trans_le
    bot_le⟩

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
    ¬ KS R V E ε qV := fun h =>
  ((accept_wins hV hE).symm.trans_le (h.bound _ (Q := 0) (fun _ => le_rfl)
    ((Nat.zero_add qV).trans_le hq))).not_gt (by simpa using hε)

/-- The certificate's caps (`qV ≤ 2^16`, `ε ≤ errorCap`) give `qV ≤ logCap` and `qV · ε < 1`. -/
theorem small_of_caps (hq : qV ≤ 2 ^ 16) (hε : ε ≤ errorCap) :
    qV ≤ logCap ∧ (qV : ℝ≥0) * ε < 1 :=
  ⟨hq.trans (by decide),
    (mul_le_mul' (by exact_mod_cast hq : (qV : ℝ≥0) ≤ 2 ^ 16) hε).trans_lt (by norm_num [errorCap])⟩

/-- **The accept-all verifier is knowledge-sound with no query, for some extractor, exactly when
every statement has a witness**, at every error (V3-S1-A13). -/
theorem acceptAll_ks_iff (R : Digest → Wit → Prop) (ε : ℝ≥0) :
    (∃ E, KS R acceptAll E ε 0) ↔ ∀ c, ∃ w, R c w :=
  ⟨fun ⟨_, h⟩ c => by_contra fun hno =>
      not_ks_of_accept (c := c) (π := .empty) rfl (fun ⟨w, _, hw⟩ => hno ⟨w, hw⟩)
        (Nat.zero_le _) (by simp) h,
    fun h => ⟨fun c _ _ => some (h c).choose,
      KS.of_extracts (fun _ _ _ => le_rfl) (fun _ c _ _ => ⟨_, rfl, (h c).choose_spec⟩) ε⟩⟩

/-! ## The verdict, and the textbook notion -/

/-- **The event reads the verifier's verdict**: in `KS`'s game, accepting on the final log is the
verifier's result in the run. -/
theorem prob_accept_eq_verdict (A : OProg (Digest × Proof)) (P : Digest × Proof → Log → Prop) :
    prob (fun x L => (V x.1 x.2).runLog L = some true ∧ P x L)
        (A.bind fun x => (V x.1 x.2).bind fun _ => .ret x) [] =
      prob (fun y L => y.2 = true ∧ P y.1 L)
        (A.bind fun x => (V x.1 x.2).bind fun b => .ret (x, b)) [] := by
  rw [prob_bind, prob_bind]
  refine congrArg (expect · A []) (funext fun x => funext fun L => ?_)
  rw [prob_bind, prob_bind]
  refine expect_congr_runLog _ L fun b L' _ hb => ?_
  rw [prob_ret, prob_ret]
  refine ind_congr ?_
  show _ ∧ _ ↔ _ ∧ _
  rw [hb, Option.some.injEq]

/-- **Textbook single-output knowledge soundness** (Chiesa–Yogev; CGSY24), for at most `N`
queries in all: as `KS`, but the extractor reads only the adversary's log; the verifier then runs
on the same oracle. -/
def KSTextbook (R : Digest → Wit → Prop) (V : Digest → Proof → OProg Bool)
    (E : Digest → Proof → Log → Option Wit) (ε : ℝ≥0) (qV N : ℕ) : Prop :=
  (∀ H c π, ((V c π).queries H).length ≤ qV) ∧
  ∀ (A : OProg (Digest × Proof)) (Q : ℕ), (∀ H, (A.queries H).length ≤ Q) → Q + qV ≤ N →
    prob (fun y L => (V y.1.1 y.1.2).runLog L = some true ∧
        ¬ ∃ w, E y.1.1 y.1.2 y.2 = some w ∧ R y.1.1 w)
      ((withLog A []).bind fun y => (V y.1.1 y.1.2).bind fun _ => .ret y) [] ≤ (Q + qV) * ε

/-- **Textbook ⇒ `KS`**, with the same extractor and the error doubled: `KS`'s game, the adversary
followed by the verifier, is a textbook adversary of `Q + qV` queries whose own log is `KS`'s
final log. -/
theorem KSTextbook.ks (h : KSTextbook R V E ε qV (logCap + qV)) : KS R V E (2 * ε) qV := by
  refine ⟨h.1, fun A Q hA hQ => ?_⟩
  have hG : ∀ H, ((A.bind fun x => (V x.1 x.2).bind fun _ => .ret x).queries H).length ≤
      Q + qV := fun H => by
    rw [OProg.queries_bind, OProg.queries_bind, List.length_append, List.length_append]
    exact Nat.add_le_add (hA H) (h.1 H _ _)
  refine le_trans ?_ ((h.2 _ (Q + qV) hG (by omega)).trans ?_)
  · rw [prob_bind _ (withLog _ []), expect_withLog, prob_eq_expect]
    refine expect_mono (fun x L => ind_le fun hw => ?_) _ []
    dsimp only [OProg.bind]
    rw [prob_bind_of_runLog _ _ hw.1, prob_ret, ind_of ⟨hw.1, hw.2⟩]
  · push_cast
    calc ((Q : ℝ≥0) + qV + qV) * ε ≤ (Q + qV + (Q + qV)) * ε := by gcongr; exact le_add_self
      _ = (Q + qV) * (2 * ε) := by ring

/-- **No escape from any log, no textbook error**: an extractor that opens every proof the
verifier accepts on some log, whatever log it reads, is textbook-sound at every error. -/
theorem KSTextbook.of_extracts (hq : ∀ H c π, ((V c π).queries H).length ≤ qV)
    (h : ∀ L L' c π, (V c π).runLog L = some true → ∃ w, E c π L' = some w ∧ R c w)
    (ε : ℝ≥0) (N : ℕ) : KSTextbook R V E ε qV N :=
  ⟨hq, fun _ _ _ _ => (prob_eq_zero (fun y L hy => hy.2 (h L y.2 y.1.1 y.1.2 hy.1)) _ _).trans_le
    bot_le⟩

end RecursionFast
