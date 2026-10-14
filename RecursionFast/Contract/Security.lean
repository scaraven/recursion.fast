/-
# Contract: security definitions over round shapes                              (TRUSTED)

D1 §2 restated over the contract's round shapes, Mathlib only (no ArkLib in the trusted cone;
`Bridge/ArkLib.lean` proves the translation). Public-coin, information-theoretic, pure
(deterministic) verifier, deterministic prover (w.l.o.g. for unbounded provers).

* `PerfectComplete`: for every pair in the input relation and **every** challenge vector the
  honest transcript is accepted with the prover's output (= probability 1).
* `KSF`, `KSF.Bad`, `RbrKS`: worst-case-per-prefix round-by-round knowledge soundness with a
  named backward extractor, in counting form `#bad ≤ ε · #challenges` (D1 §2.3, A2-M1).

Reading guide (A2-m2): `Transcript sh m` is the prefix of *length* `m`; `m.castSucc` / `m.succ`
are "before / after round `m`"; `cast E.eqIn` is an identity coercion between equal types;
`Bad`'s `∃ w` ranges over the *next-stage* witness, which the extractor maps backwards.
For an unconstrained extractor `RbrKS` is equivalent to RBR *soundness* (`Library/RbrSound.lean`,
A2-M2); `Protocol.Secure` names the submitted image (`Contract/Extractor.lean`, Q1), to which the
collapse does not apply.
-/
import RecursionFast.Contract.Shapes
import Mathlib.Basic.NNReal.Defs
import Mathlib.SetTheory.Cardinal.Finite

open scoped NNReal

namespace RecursionFast

/-- Contract error cap (DESIGN §5): every round's error is at most `2^-128`. -/
noncomputable def errorCap : ℝ≥0 := (2 : ℝ≥0)⁻¹ ^ 128

variable {n : ℕ} (sh : Fin n → Round) (Stmt Wit StmtOut WitOut : Type)

/-- A deterministic prover: each message is a function of the input and the transcript so far;
the output (statement, witness) is a function of the full transcript. -/
structure Strategy where
  next : Stmt → Wit → (m : MessageIdx sh) → Transcript sh m.1.castSucc → (sh m.1).Ty
  output : Stmt → Wit → FullTranscript sh → StmtOut × WitOut

/-- A pure verifier: a total function of the statement and the full transcript; `none` = reject. -/
abbrev PureVerifier := Stmt → FullTranscript sh → Option StmtOut

variable {sh Stmt Wit StmtOut WitOut}

/-- The honest transcript prefixes on challenge vector `ρ`: round `j` is the prover's message if
`j` is a prover round, and `ρ`'s entry otherwise. -/
def Strategy.prefixes (P : Strategy sh Stmt Wit StmtOut WitOut) (s : Stmt) (w : Wit)
    (ρ : Challenges sh) : (m : Fin (n + 1)) → Transcript sh m :=
  Fin.induction (Transcript.empty sh) fun j tr =>
    tr.concat (if h : (sh j).isMsg then P.next s w ⟨j, h⟩ tr else ρ ⟨j, by simpa using h⟩)

/-- The full honest transcript on challenge vector `ρ`. -/
def Strategy.transcript (P : Strategy sh Stmt Wit StmtOut WitOut) (s : Stmt) (w : Wit)
    (ρ : Challenges sh) : FullTranscript sh :=
  P.prefixes s w ρ (Fin.last n)

/-- **Perfect completeness**: for every `(s, w) ∈ relIn` and every challenge vector, the verifier
accepts the honest transcript with the prover's output statement, and the output pair is in
`relOut`. -/
def PerfectComplete (relIn : Set (Stmt × Wit)) (relOut : Set (StmtOut × WitOut))
    (P : Strategy sh Stmt Wit StmtOut WitOut) (V : PureVerifier sh Stmt StmtOut) : Prop :=
  ∀ s w, (s, w) ∈ relIn → ∀ ρ : Challenges sh,
    V s (P.transcript s w ρ) = some (P.output s w (P.transcript s w ρ)).1 ∧
      P.output s w (P.transcript s w ρ) ∈ relOut

variable (sh Stmt Wit WitOut) in
/-- A round-by-round extractor with intermediate witness types `WitMid` (ArkLib's
`Extractor.RoundByRound`): `extractMid m` maps a witness after round `m` to one before it. -/
structure Extractor (WitMid : Fin (n + 1) → Type) where
  eqIn : WitMid 0 = Wit
  extractMid : (m : Fin n) → Stmt → Transcript sh m.succ → WitMid m.succ → WitMid m.castSucc
  extractOut : Stmt → FullTranscript sh → WitOut → WitMid (Fin.last n)

/-- A **knowledge state function** for `V` and the named extractor `E`. Laws: `empty` (before
round 0 the state is the input relation), `next` (a prover message cannot make the state true
unless it was true before, with the extracted witness), `full` (an accepted full transcript with
an output pair in `relOut` makes the state true with the extracted final witness). -/
structure KSF (relIn : Set (Stmt × Wit)) (relOut : Set (StmtOut × WitOut))
    (V : PureVerifier sh Stmt StmtOut) {WitMid : Fin (n + 1) → Type}
    (E : Extractor sh Stmt Wit WitOut WitMid) where
  toFun : (m : Fin (n + 1)) → Stmt → Transcript sh m → WitMid m → Prop
  empty : ∀ s w, (s, cast E.eqIn w) ∈ relIn ↔ toFun 0 s (Transcript.empty sh) w
  next : ∀ (m : MessageIdx sh) s (tr : Transcript sh m.1.castSucc) (msg : (sh m.1).Ty) w,
    toFun m.1.succ s (tr.concat msg) w → toFun m.1.castSucc s tr (E.extractMid m.1 s (tr.concat msg) w)
  full : ∀ s tr sOut wOut, V s tr = some sOut → (sOut, wOut) ∈ relOut →
    toFun (Fin.last n) s tr (E.extractOut s tr wOut)

variable {relIn : Set (Stmt × Wit)} {relOut : Set (StmtOut × WitOut)}
  {V : PureVerifier sh Stmt StmtOut} {WitMid : Fin (n + 1) → Type}
  {E : Extractor sh Stmt Wit WitOut WitMid}

/-- A fresh challenge `ch` in round `c` is **bad** for prefix `tr` if some witness makes the state
true after `ch` while the extracted witness does not make it true before `ch`. -/
def KSF.Bad (kSF : KSF relIn relOut V E) (c : ChallengeIdx sh) (s : Stmt)
    (tr : Transcript sh c.1.castSucc) (ch : (sh c.1).Ty) : Prop :=
  ∃ w, ¬ kSF.toFun c.1.castSucc s tr (E.extractMid c.1 s (tr.concat ch) w) ∧
    kSF.toFun c.1.succ s (tr.concat ch) w

/-- **Worst-case RBR knowledge soundness with errors `ε`**, counting form: for every statement,
challenge round and prefix, at most an `ε c`-fraction of the round's challenges is bad. (All
challenge types are finite and nonempty, `Library/Field.lean`, so `Nat.card` is the size.) -/
def RbrKS (kSF : KSF relIn relOut V E) (ε : ChallengeIdx sh → ℝ≥0) : Prop :=
  ∀ s (c : ChallengeIdx sh) (tr : Transcript sh c.1.castSucc),
    (Nat.card {ch // kSF.Bad c s tr ch} : ℝ≥0) ≤ ε c * Nat.card (sh c.1).Ty

/-- The security clause shared by protocols and reductions: perfect completeness, an RBR-KS
state function for the named extractor at errors `ε`, and the error cap `ε c ≤ 2^-128`. -/
structure SecureWith (relIn : Set (Stmt × Wit)) (relOut : Set (StmtOut × WitOut))
    (P : Strategy sh Stmt Wit StmtOut WitOut) (V : PureVerifier sh Stmt StmtOut)
    (E : Extractor sh Stmt Wit WitOut WitMid) (ε : ChallengeIdx sh → ℝ≥0) : Prop where
  complete : PerfectComplete relIn relOut P V
  sound : ∃ kSF : KSF relIn relOut V E, RbrKS kSF ε
  cap : ∀ c, ε c ≤ errorCap

end RecursionFast
