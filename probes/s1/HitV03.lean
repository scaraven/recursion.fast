/- S1 review probe: v0.3 `Library/RbrSound.lean` and `Controls/Hit.lean`, concatenated with their
imports merged and otherwise unchanged. Checks that v0.3's positive control with challenge rounds
(`hit_secure`: the cap is met at ε = 2^-192) still holds against this repository's contract. -/
import RecursionFast.Contract.Security
import RecursionFast.Library.Challenges
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real


open scoped NNReal

namespace RecursionFast

variable {n : ℕ} {sh : Fin n → Round}

@[simp] theorem Transcript.concat_last {m : Fin n} (tr : Transcript sh m.castSucc) (a : (sh m).Ty) :
    tr.concat a (Fin.last m) = a :=
  Fin.snoc_last (α := fun i : Fin (m.val + 1) => (sh (Fin.castLE m.isLt i)).Ty) _ _

@[simp] theorem Transcript.concat_castSucc {m : Fin n} (tr : Transcript sh m.castSucc) (a : (sh m).Ty)
    (j : Fin m) : tr.concat a j.castSucc = tr j :=
  Fin.snoc_castSucc (α := fun i : Fin (m.val + 1) => (sh (Fin.castLE m.isLt i)).Ty) _ _ _

/-! ## RBR soundness ⇒ contract RBR-KS (A2 §D) -/

section Collapse
variable {Stmt Wit : Type} {relIn : Set (Stmt × Wit)} {V : PureVerifier sh Stmt Unit}

/-- A witness-free state function (CY Def. 31.1.1 shape). -/
structure SF (relIn : Set (Stmt × Wit)) (V : PureVerifier sh Stmt Unit) where
  toFun : (m : Fin (n + 1)) → Stmt → Transcript sh m → Prop
  empty : ∀ s, (∃ w, (s, w) ∈ relIn) ↔ toFun 0 s (Transcript.empty sh)
  next : ∀ (m : MessageIdx sh) s (tr : Transcript sh m.1.castSucc) msg,
    toFun m.1.succ s (tr.concat msg) → toFun m.1.castSucc s tr
  full : ∀ s tr, V s tr = some () → toFun (Fin.last n) s tr

/-- RBR soundness at errors `ε`, counting form. -/
def SF.Rbr (S : SF relIn V) (ε : ChallengeIdx sh → ℝ≥0) : Prop :=
  ∀ s (c : ChallengeIdx sh) (tr : Transcript sh c.1.castSucc),
    (Nat.card {ch // ¬ S.toFun c.1.castSucc s tr ∧ S.toFun c.1.succ s (tr.concat ch)} : ℝ≥0) ≤
      ε c * Nat.card (sh c.1).Ty

variable (bf : Stmt → Wit) (hbf : ∀ s, (∃ w, (s, w) ∈ relIn) → (s, bf s) ∈ relIn)

/-- The brute-force extractor: always answer `bf s`. -/
def bfE : Extractor sh Stmt Wit Unit (fun _ => Wit) :=
  { eqIn := rfl, extractMid := fun _ s _ _ => bf s, extractOut := fun s _ _ => bf s }

theorem SF.at_zero (S : SF relIn V) (k : Fin (n + 1)) (hk : k = 0) (s : Stmt) (tr : Transcript sh k) :
    S.toFun k s tr ↔ ∃ w, (s, w) ∈ relIn := by
  subst hk
  rw [show tr = Transcript.empty sh from funext fun i => Fin.elim0 i]
  exact (S.empty s).symm

open Classical in
/-- The KSF built from a state function and a witness finder. -/
def SF.toKSF (S : SF relIn V) : KSF relIn Set.univ V (bfE (sh := sh) bf) where
  toFun := fun m s tr w => if m = 0 then (s, w) ∈ relIn else S.toFun m s tr
  empty := fun s w => by simp
  next := fun m s tr msg w h => by
    have hs : m.1.succ ≠ 0 := Fin.succ_ne_zero _
    simp only [hs, ite_false] at h
    have h' := S.next m s tr msg h
    by_cases h0 : m.1.castSucc = 0
    · simp only [h0, ite_true]; exact hbf s ((S.at_zero _ h0 s tr).mp h')
    · simp only [h0, ite_false]; exact h'
  full := fun s tr sOut _ hV _ => by
    have h' := S.full s tr (by cases sOut; exact hV)
    by_cases h0 : (Fin.last n) = 0
    · simp only [h0, ite_true]; exact hbf s ((S.at_zero _ h0 s tr).mp h')
    · simp only [h0, ite_false]; exact h'

/-- **RBR soundness (+ brute force) ⇒ the contract's RBR-KS, same `ε`** (A2-M2). -/
theorem SF.rbrKS_of_rbr (S : SF relIn V) (ε : ChallengeIdx sh → ℝ≥0) (h : S.Rbr ε) :
    RbrKS (S.toKSF bf hbf) ε := by
  intro s c tr
  refine le_trans ?_ (h s c tr)
  have hmono : Nat.card {ch // (S.toKSF bf hbf).Bad c s tr ch} ≤
      Nat.card {ch // ¬ S.toFun c.1.castSucc s tr ∧ S.toFun c.1.succ s (tr.concat ch)} := by
    refine Nat.card_mono (Set.toFinite _) ?_
    intro ch ⟨w, hnot, hyes⟩
    have hs : c.1.succ ≠ 0 := Fin.succ_ne_zero _
    simp only [SF.toKSF, hs, ite_false] at hyes
    refine ⟨?_, hyes⟩
    intro hS
    by_cases h0 : c.1.castSucc = 0
    · simp only [SF.toKSF, h0, ite_true] at hnot
      exact hnot (hbf s ((S.at_zero _ h0 s tr).mp hS))
    · simp only [SF.toKSF, h0, ite_false] at hnot
      exact hnot hS
  exact_mod_cast hmono

end Collapse

/-! ## Straight-line extraction along an accepting transcript (A2 §E) -/

section Chain
variable {Stmt Wit StmtOut WitOut : Type} {relIn : Set (Stmt × Wit)} {relOut : Set (StmtOut × WitOut)}
  {V : PureVerifier sh Stmt StmtOut} {WitMid : Fin (n + 1) → Type} {E : Extractor sh Stmt Wit WitOut WitMid}

/-- The length-`k` prefix of a full transcript. -/
def pre (tr : FullTranscript sh) (k : Fin (n + 1)) : Transcript sh k :=
  fun i => tr (Fin.castLE (Nat.le_of_lt_succ k.isLt) i)

theorem pre_succ (tr : FullTranscript sh) (m : Fin n) :
    pre tr m.succ = (pre tr m.castSucc).concat (tr m) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Transcript.concat_last]; rfl
  · rw [Transcript.concat_castSucc]; rfl

/-- The backward chain of extracted witnesses. -/
def chain (E : Extractor sh Stmt Wit WitOut WitMid) (s : Stmt) (tr : FullTranscript sh)
    (wOut : WitOut) : (k : Fin (n + 1)) → WitMid k :=
  Fin.reverseInduction (E.extractOut s tr wOut) (fun m w => E.extractMid m s (pre tr m.succ) w)

theorem chain_state (kSF : KSF relIn relOut V E) (s : Stmt) (tr : FullTranscript sh)
    (sOut : StmtOut) (wOut : WitOut) (hV : V s tr = some sOut) (hrel : (sOut, wOut) ∈ relOut)
    (hgood : ∀ c : ChallengeIdx sh, ¬ kSF.Bad c s (pre tr c.1.castSucc) (tr c.1)) :
    ∀ k, kSF.toFun k s (pre tr k) (chain E s tr wOut k) := by
  intro k
  induction k using Fin.reverseInduction with
  | last =>
    rw [chain, Fin.reverseInduction_last]
    exact kSF.full s tr sOut wOut hV hrel
  | cast m ih =>
    rw [chain, Fin.reverseInduction_castSucc, ← chain]
    rw [pre_succ] at ih ⊢
    cases hd : (sh m).isMsg with
    | true => exact kSF.next ⟨m, hd⟩ s _ _ _ ih
    | false =>
      have hg := hgood ⟨m, hd⟩
      by_contra hc
      exact hg ⟨_, hc, ih⟩

/-- **Straight-line extraction** from an accepting transcript with no bad challenge. -/
theorem chain_extracts (kSF : KSF relIn relOut V E) (s : Stmt) (tr : FullTranscript sh)
    (sOut : StmtOut) (wOut : WitOut) (hV : V s tr = some sOut) (hrel : (sOut, wOut) ∈ relOut)
    (hgood : ∀ c : ChallengeIdx sh, ¬ kSF.Bad c s (pre tr c.1.castSucc) (tr c.1)) :
    (s, cast E.eqIn (chain E s tr wOut 0)) ∈ relIn := by
  have h0 := chain_state kSF s tr sOut wOut hV hrel hgood 0
  rw [show pre tr 0 = Transcript.empty sh from funext fun i => Fin.elim0 i] at h0
  exact (kSF.empty s _).mpr h0

/-- On a false statement, every accepting transcript contains a challenge that is bad for its
own prefix (for a proof system: `relOut = univ`). -/
theorem no_bad_imp_false (kSF : KSF relIn Set.univ V E) (s : Stmt) (hs : ∀ w, (s, w) ∉ relIn)
    (tr : FullTranscript sh) (sOut : StmtOut) (wOut : WitOut) (hV : V s tr = some sOut) :
    ∃ c : ChallengeIdx sh, kSF.Bad c s (pre tr c.1.castSucc) (tr c.1) := by
  by_contra h
  push Not at h
  exact hs _ (chain_extracts kSF s tr sOut wOut hV (Set.mem_univ _) h)

end Chain

end RecursionFast



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
#print axioms RecursionFast.Controls.hit_secure
