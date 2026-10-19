/-
# Control (negative, A2-C3): the "hit" protocol is no longer a counterexample

A2's §B: `k` challenge rounds, empty relation, accept iff *some* challenge is `0`. Each round
has exactly one bad challenge, so the per-round error sits at the cap, yet with `k = N` rounds
a false statement is accepted with probability `≥ 1/2`; nothing bounded `k`.

Under the contract: challenges are E elements (`N = 2^192`) and `n ≤ roundCap = 2^14`.
* `hit_secure`: the hit protocol *does* satisfy the security clause, at `ε = 2^-192 ≤ 2^-128`
  (the definitions are not over-strict: it is a legitimately sound, if silly, verifier);
* `hit_reject_card`: exactly `(N − 1)^n` of the `N^n` transcripts reject;
* `hit_accepts_lt_half`: for every admissible `n ≤ 2^14`, fewer than half of all transcripts
  accept, refuting A2's conclusion (`hit_reject_le_half`) at every admissible round count (the
  true bound is `≤ n/N ≤ 2^-178`, `hit_accept_frac`).
-/
import RecursionFast.Contract.Security
import RecursionFast.Library.RbrSound
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped NNReal

namespace RecursionFast.Controls
open RecursionFast

variable (n : ℕ)

/-- `n` rounds, each one uniform element of E. -/
def hitShape : Fin n → Round := fun _ => .chal 1 []

/-- The E element of a hit round. -/
def hitVal (v : Round.Ty (.chal 1 [])) : E := v.1 0

/-- Accept iff some challenge is `0`. -/
def hitV : PureVerifier (hitShape n) Unit Unit :=
  fun _ tr => if ∃ l : Fin n, hitVal (tr l) = 0 then some () else none

def hitE : Extractor (hitShape n) Unit Unit Unit (fun _ => Unit) :=
  { eqIn := rfl, extractMid := fun _ _ _ _ => (), extractOut := fun _ _ _ => () }

/-- State: "a zero challenge has already appeared". -/
def hitKSF : KSF (∅ : Set (Unit × Unit)) Set.univ (hitV n) (hitE n) where
  toFun := fun m _ tr _ => ∃ l : Fin m, hitVal (tr l) = 0
  empty := fun _ _ => ⟨fun h => h.elim, fun ⟨l, _⟩ => l.elim0⟩
  next := fun m => absurd m.2 (by simp [hitShape, Round.isMsg])
  full := fun s tr sOut wOut hV _ => by
    simp only [hitV] at hV
    split_ifs at hV with h
    exact h

theorem hit_bad_imp (c : ChallengeIdx (hitShape n)) (tr : Transcript (hitShape n) c.1.castSucc)
    (ch : (hitShape n c.1).Ty) (h : (hitKSF n).Bad c () tr ch) : hitVal ch = 0 := by
  obtain ⟨_, hnot, l, hl⟩ := h
  revert hl
  refine Fin.lastCases ?_ (fun j => ?_) l
  · intro hl; rwa [Transcript.concat_last] at hl
  · intro hl; rw [Transcript.concat_castSucc] at hl; exact absurd ⟨j, hl⟩ hnot

theorem hitVal_inj (u v : Round.Ty (.chal 1 [])) (h : hitVal u = hitVal v) : u = v := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  refine Prod.ext (funext fun j => ?_) (funext fun j => j.elim0)
  rw [Subsingleton.elim j 0]; exact h

theorem hit_card_bad (c : ChallengeIdx (hitShape n)) (tr : Transcript (hitShape n) c.1.castSucc) :
    Nat.card {ch // (hitKSF n).Bad c () tr ch} ≤ 1 := by
  rw [Finite.card_le_one_iff_subsingleton]
  refine ⟨fun a b => Subtype.ext ?_⟩
  have ha := hit_bad_imp n c tr a.1 a.2
  have hb := hit_bad_imp n c tr b.1 b.2
  exact hitVal_inj _ _ (ha.trans hb.symm)

/-- **The definitions accept it, at error `2^-192`.** -/
theorem hit_secure :
    SecureWith (∅ : Set (Unit × Unit)) Set.univ
      ({ next := fun _ _ m _ => absurd m.2 (by simp [hitShape, Round.isMsg]),
         output := fun _ _ _ => ((), ()) } : Strategy (hitShape n) Unit Unit Unit Unit)
      (hitV n) (hitE n) (fun _ => (2 : ℝ≥0)⁻¹ ^ 192) where
  complete := fun _ _ h => h.elim
  sound := ⟨hitKSF n, fun s c tr => by
    have h1 := hit_card_bad n c tr
    have hC : Nat.card (hitShape n c.1).Ty = 2 ^ 192 := by
      show Nat.card (Round.chal 1 []).Ty = _
      rw [natCard_chal]; simp
    rw [hC]
    have hone : (1 : ℝ≥0) ≤ (2 : ℝ≥0)⁻¹ ^ 192 * ((2 ^ 192 : ℕ) : ℝ≥0) := by
      rw [inv_pow, Nat.cast_pow, Nat.cast_ofNat, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)]
    exact le_trans (by exact_mod_cast h1) hone⟩
  cap := fun _ => pow_le_pow_of_le_one (by positivity) (by norm_num) (by norm_num)

/-! ### Counting rejecting transcripts -/

theorem natCard_nonzero : Nat.card {v : Round.Ty (.chal 1 []) // hitVal v ≠ 0} = 2 ^ 192 - 1 := by
  have e : {v : Round.Ty (.chal 1 []) // hitVal v ≠ 0} ≃ {x : E // x ≠ 0} :=
    { toFun := fun v => ⟨hitVal v.1, v.2⟩
      invFun := fun x => ⟨(fun _ => x.1, fun j => j.elim0), x.2⟩
      left_inv := fun ⟨⟨a, b⟩, h⟩ => by
        apply Subtype.ext
        refine Prod.ext (funext fun j => ?_) (funext fun j => j.elim0)
        rw [Subsingleton.elim j 0]; rfl
      right_inv := fun _ => rfl }
  have h := Nat.card_congr (Equiv.optionSubtypeNe (0 : E))
  rw [Finite.card_option, natCard_E] at h
  rw [Nat.card_congr e]; omega

theorem hit_reject_card :
    Nat.card {tr : FullTranscript (hitShape n) // hitV n () tr = none} = (2 ^ 192 - 1) ^ n := by
  have e1 : {tr : FullTranscript (hitShape n) // hitV n () tr = none} ≃
      {tr : FullTranscript (hitShape n) // ∀ l, hitVal (tr l) ≠ 0} :=
    Equiv.subtypeEquivRight fun tr => by simp [hitV]
  rw [Nat.card_congr (e1.trans (Equiv.subtypePiEquivPi (p := fun _ v => hitVal v ≠ 0))), Nat.card_pi]
  simp only [natCard_nonzero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem hit_total_card : Nat.card (FullTranscript (hitShape n)) = (2 ^ 192) ^ n := by
  rw [Nat.card_pi]
  simp only [hitShape, natCard_chal]; simp

/-- Arithmetic core: `2·(N−1)^n > N^n` for `N = 2^192` and `n ≤ 2^14` (Bernoulli). -/
theorem two_mul_pow_gt (hn : n ≤ roundCap) : (2 ^ 192 : ℕ) ^ n < 2 * (2 ^ 192 - 1) ^ n := by
  have hN : (0 : ℝ) < 2 ^ 192 := by positivity
  have hb : (1 : ℝ) + n * (-(1 / 2 ^ 192)) ≤ (1 + -(1 / 2 ^ 192)) ^ n :=
    one_add_mul_le_pow (by norm_num) n
  have hn' : (n : ℝ) ≤ 2 ^ 14 := by exact_mod_cast hn
  have hlow : (1 : ℝ) / 2 < (1 + -(1 / 2 ^ 192)) ^ n := by
    refine lt_of_lt_of_le ?_ hb
    have : (n : ℝ) * (1 / 2 ^ 192) ≤ 2 ^ 14 * (1 / 2 ^ 192) := by gcongr
    norm_num at this ⊢; linarith
  have hsub : ((2 ^ 192 - 1 : ℕ) : ℝ) = 2 ^ 192 * (1 + -(1 / 2 ^ 192)) := by
    rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow]; field_simp; ring
  have key : ((2 ^ 192 : ℕ) : ℝ) ^ n < 2 * ((2 ^ 192 - 1 : ℕ) : ℝ) ^ n := by
    rw [hsub, mul_pow, Nat.cast_pow, Nat.cast_ofNat]
    have hp : (0 : ℝ) < (2 ^ 192) ^ n := by positivity
    generalize ((2 : ℝ) ^ 192) ^ n = b at hp ⊢
    generalize (1 + -(1 / (2 : ℝ) ^ 192)) ^ n = a at hlow ⊢
    nlinarith
  exact_mod_cast key

/-- **A2-C3 refuted at every admissible round count**: fewer than half of all transcripts accept
the false statement. -/
theorem hit_accepts_lt_half (hn : n ≤ roundCap) :
    Nat.card (FullTranscript (hitShape n)) < 2 * Nat.card {tr : FullTranscript (hitShape n) // hitV n () tr = none} := by
  rw [hit_total_card, hit_reject_card]; exact two_mul_pow_gt n hn

end RecursionFast.Controls
