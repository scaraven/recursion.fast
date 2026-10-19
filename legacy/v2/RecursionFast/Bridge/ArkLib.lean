/-
  RecursionFast.Bridge.ArkLib  (UNTRUSTED, kernel-checked; ArkLib 7653a90)

  Carried over from v0.3 (`contract-v03/RecursionFast/Bridge/ArkLib.lean`) unchanged, plus the v2
  corollary `Protocol.secure_toArk` (S9-A4). The contract's local security definitions imply
  ArkLib's (the organisers' sanity check, A2-m2, D1 §2.6, ported from
  `probes/d1-probes/LocalDefs.lean` §3):
  * a round shape is an ArkLib `ProtocolSpec` (`toPSpec`), with *definitionally the same*
    transcripts, `concat` and empty transcript;
  * a contract extractor is an ArkLib `Extractor.RoundByRound` (field by field);
  * a contract `KSF` is an ArkLib `KnowledgeStateFunction` for the pure verifier as an ArkLib
    verifier with no shared oracle (`KSF.toArk`);
  * contract `RbrKS` (counting form) ⇒ ArkLib `rbrKnowledgeSoundnessWorstCaseWith` for any
    uniform sampler on the challenge types (`RbrKS.toArk`);
  * contract `PerfectComplete` ⇒ the pure verifier accepts every honest transcript (used with
    ArkLib's perfect completeness, not restated here);
  * v2: `Protocol.Secure` ⇒ ArkLib worst-case RBR knowledge soundness of the protocol's verifier
    (its query program run on `IDX L` and the transcript's oracles, as a pure verifier) for
    `relK k`, with the image's extractor, at the declared errors (`Protocol.secure_toArk`).

  What the bridge does not carry (S9-A4): (1) the direction is contract → ArkLib only, so a
  submitter cannot obtain `Secure` from ArkLib's proofs through it; (2) ArkLib's extractor is
  unbounded, so the image's step bound `B(k)` (the "knowledge" content of Q1) is forgotten: the
  ArkLib statement is about the same extractor function, not about its cost; (3) perfect
  completeness is not restated in ArkLib's probabilistic form (the contract's, for every challenge
  vector, is the stronger one).
-/
import ArkLib.OracleReduction.Security.RoundByRound
import RecursionFast.Contract.Protocol
import RecursionFast.Library.Challenges

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

namespace RecursionFast

/-- No shared oracle: the information-theoretic model. -/
abbrev NoOracle : OracleSpec PEmpty := emptySpec.{0, 0}

/-- Direction of a contract round. -/
def Round.dir (r : Round) : Direction := if r.isMsg then .P_to_V else .V_to_P

theorem Round.dir_eq_P_to_V (r : Round) : r.dir = .P_to_V ↔ r.isMsg = true := by
  unfold Round.dir; cases r.isMsg <;> simp

theorem Round.dir_eq_V_to_P (r : Round) : r.dir = .V_to_P ↔ r.isMsg = false := by
  unfold Round.dir; cases r.isMsg <;> simp

variable {n : ℕ} (sh : Fin n → Round)

/-- A contract round shape as an ArkLib protocol specification. -/
abbrev toPSpec : ProtocolSpec n := ⟨fun i => (sh i).dir, fun i => (sh i).Ty⟩

/-- Transcripts coincide definitionally. -/
example (m : Fin (n + 1)) : (toPSpec sh).Transcript m = Transcript sh m := rfl
example (m : Fin n) (tr : Transcript sh m.castSucc) (a : (sh m).Ty) :
    ProtocolSpec.Transcript.concat (pSpec := toPSpec sh) a tr = tr.concat a := rfl

abbrev chalIdx {sh : Fin n → Round} (c : (toPSpec sh).ChallengeIdx) : ChallengeIdx sh :=
  ⟨c.1, (Round.dir_eq_V_to_P _).mp c.2⟩

variable {sh} {Stmt Wit StmtOut WitOut : Type}

/-- A contract extractor as an ArkLib round-by-round extractor. -/
def Extractor.toArk {WitMid : Fin (n + 1) → Type} (E : Extractor sh Stmt Wit WitOut WitMid) :
    _root_.Extractor.RoundByRound NoOracle Stmt Wit WitOut (toPSpec sh) WitMid :=
  ⟨E.eqIn, E.extractMid, E.extractOut⟩

/-- A pure verifier as an ArkLib verifier with no shared oracle. -/
def PureVerifier.toArk (V : PureVerifier sh Stmt StmtOut) : Verifier NoOracle Stmt StmtOut (toPSpec sh) where
  verify := fun s tr => match V s tr with
    | some o => pure o
    | none => failure

section Bridge
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl NoOracle (StateT σ ProbComp))

/-- Positive acceptance probability of the ArkLib verifier is acceptance of the pure verifier. -/
theorem toArk_prEvent_pos_iff (V : PureVerifier sh Stmt StmtOut) (s : Stmt) (tr : FullTranscript sh)
    (P : StmtOut → Prop) :
    (Pr{let sOut ← OptionT.mk do
      (simulateQ impl ((PureVerifier.toArk V).run s tr)).run' (← init)}[P sOut] > 0) ↔
      ∃ sOut, V s tr = some sOut ∧ P sOut := by
  rw [gt_iff_lt, OptionT.prEvent_mk_pos_iff]
  simp only [PureVerifier.toArk, Verifier.run]
  constructor
  · rintro ⟨o, ho, hP⟩
    refine ⟨o, ?_, hP⟩
    cases h : V s tr with
    | none =>
      rw [h] at ho
      change some o ∈ support (do
        let a ← init
        (simulateQ impl (pure none : OracleComp NoOracle (Option StmtOut))).run' a) at ho
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure, bind_pure_comp,
        support_map, Set.mem_image] at ho
      obtain ⟨_, _, h'⟩ := ho
      cases h'
    | some o' =>
      rw [h] at ho
      change some o ∈ support (do
        let a ← init
        (simulateQ impl (pure (some o') : OracleComp NoOracle (Option StmtOut))).run' a) at ho
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure, bind_pure_comp,
        support_map, Set.mem_image] at ho
      obtain ⟨_, _, h'⟩ := ho
      cases h'
      rfl
  · rintro ⟨o, ho, hP⟩
    refine ⟨o, ?_, hP⟩
    rw [ho]
    change some o ∈ support (do
      let a ← init
      (simulateQ impl (pure (some o) : OracleComp NoOracle (Option StmtOut))).run' a)
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure, bind_pure_comp,
      support_map, Set.mem_image]
    obtain ⟨a, ha⟩ := support_nonempty init
    exact ⟨a, ha, trivial⟩

variable {relIn : Set (Stmt × Wit)} {relOut : Set (StmtOut × WitOut)}
  {V : PureVerifier sh Stmt StmtOut} {WitMid : Fin (n + 1) → Type} {E : Extractor sh Stmt Wit WitOut WitMid}

/-- A contract KSF is an ArkLib knowledge state function. -/
def KSF.toArk (kSF : KSF relIn relOut V E) :
    (PureVerifier.toArk V).KnowledgeStateFunction init impl relIn relOut E.toArk where
  toFun := kSF.toFun
  toFun_empty := kSF.empty
  toFun_next := fun m hm => kSF.next ⟨m, (Round.dir_eq_P_to_V _).mp hm⟩
  toFun_full := fun s tr wOut hpos => by
    obtain ⟨sOut, hV, hrel⟩ := (toArk_prEvent_pos_iff init impl V s tr _).mp hpos
    exact kSF.full s tr sOut wOut hV hrel

/-- **Contract RBR-KS ⇒ ArkLib worst-case RBR-KS** (same errors), for any uniform sampler. -/
theorem RbrKS.toArk [∀ i, Fintype ((toPSpec sh).Challenge i)] [∀ i, SampleableType ((toPSpec sh).Challenge i)]
    (kSF : KSF relIn relOut V E) (ε : ChallengeIdx sh → ℝ≥0) (h : RbrKS kSF ε) :
    (PureVerifier.toArk V).rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut WitMid E.toArk
      (kSF.toArk init impl) (fun c => ε (chalIdx c)) := by
  intro s i tr
  classical
  let _ : Fintype (sh i.1).Ty := (inferInstance : Fintype ((toPSpec sh).Challenge i))
  have hcard := h s (chalIdx i) tr
  rw [probOutput_true_eq_probEvent, probEvent_uniformSample]
  have hne : (Fintype.card ((toPSpec sh).Challenge i) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [ENNReal.div_le_iff hne (ENNReal.natCast_ne_top _)]
  have hc : Nat.card {c // kSF.Bad (chalIdx i) s tr c} =
      (Finset.univ.filter (fun c => kSF.Bad (chalIdx i) s tr c)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hC : Nat.card (sh i.1).Ty = Fintype.card ((toPSpec sh).Challenge i) := Nat.card_eq_fintype_card
  change ((Finset.univ.filter (fun c => kSF.Bad (chalIdx i) s tr c)).card : ℝ≥0∞) ≤
    (ε (chalIdx i) : ℝ≥0∞) * (Fintype.card ((toPSpec sh).Challenge i) : ℝ≥0∞)
  have hcard' : ((Finset.univ.filter (fun c => kSF.Bad (chalIdx i) s tr c)).card : ℝ≥0) ≤
      ε (chalIdx i) * Fintype.card ((toPSpec sh).Challenge i) := by
    rw [← hc, ← hC]; exact hcard
  exact_mod_cast hcard'

/-- **v2: a secure protocol is ArkLib round-by-round knowledge sound** (worst case, same errors,
any uniform sampler on its challenge types), for `relK k`, with the image's extractor. -/
theorem Protocol.secure_toArk {k : ℕ} (P : Protocol k) (hP : P.Secure)
    [∀ i, Fintype ((toPSpec P.shape).Challenge i)]
    [∀ i, SampleableType ((toPSpec P.shape).Challenge i)] :
    ∃ kSF : KSF (relK k) Set.univ P.specVerifier (P.extractor.toExtractor P.shape),
      (PureVerifier.toArk P.specVerifier).rbrKnowledgeSoundnessWorstCaseWith init impl (relK k)
        Set.univ _ (P.extractor.toExtractor P.shape).toArk (kSF.toArk init impl)
        (fun c => P.ε (chalIdx c)) :=
  let ⟨kSF, h⟩ := hP.sound
  ⟨kSF, RbrKS.toArk init impl kSF P.ε h⟩

end Bridge

end RecursionFast
