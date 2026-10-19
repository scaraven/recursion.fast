/-
  RecursionFast.Library.RbrSound  (UNTRUSTED, kernel-checked)

  Two facts about the contract's RBR knowledge soundness, ported from A2's probes
  (`probes/a2-probes/A2Probes.lean` §D, §E) to the contract's local definitions:

  * `SF.rbrKS_of_rbr` (A2-M2, honest labelling): witness-free RBR *soundness* at errors `ε`,
    plus any witness finder that succeeds on the language, already gives a contract `KSF` with
    `RbrKS` at the same `ε`. So at L1 (unbounded extraction) the certificate is RBR soundness.
  * `chain_extracts` (A2-M1, WARP Claim B.6): an accepting full transcript none of whose
    challenges is bad for its own prefix yields a valid input witness by backward extraction.
    Hence `no_bad_imp_false`: on a false statement every accepting transcript contains a bad
    challenge, the event the per-round bound `ε` controls.
-/
import RecursionFast.Contract.Security
import RecursionFast.Library.Challenges

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
