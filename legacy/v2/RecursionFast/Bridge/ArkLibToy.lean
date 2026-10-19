/-
  RecursionFast.Bridge.ArkLibToy  (UNTRUSTED, kernel-checked; a control of the ArkLib bridge)

  `Protocol.secure_toArk` instantiated on the toy protocol at class 20 (`Controls/Toy.lean`): the
  ArkLib statement is inhabited (non-vacuity of the bridge's hypotheses). The toy has no challenge
  rounds, so the sampler instances on its challenge types are vacuous, and the empty oracle has one
  implementation. Kept in `Bridge/` so that `Controls/` never imports ArkLib.
-/
import RecursionFast.Bridge.ArkLib
import RecursionFast.Controls.Toy

open OracleComp OracleSpec ProtocolSpec

namespace RecursionFast.Controls
open RecursionFast

/-- The empty oracle's implementation (it has no queries). -/
def noImpl : QueryImpl NoOracle (StateT Unit ProbComp) := fun q => PEmpty.elim q

/-- The toy has no challenge rounds, in ArkLib's indexing either. -/
theorem toy20_noChalArk (i : (toPSpec toy20.shape).ChallengeIdx) : False :=
  toy_noChal 20 (chalIdx i)

instance : ∀ i, Fintype ((toPSpec toy20.shape).Challenge i) := fun i => (toy20_noChalArk i).elim
instance : ∀ i, SampleableType ((toPSpec toy20.shape).Challenge i) :=
  fun i => (toy20_noChalArk i).elim

/-- **The bridge applies**: the toy is ArkLib worst-case RBR knowledge sound for `relK 20`. -/
theorem toy20_arkRbrKS :
    ∃ kSF : KSF (relK 20) Set.univ toy20.specVerifier (toy20.extractor.toExtractor toy20.shape),
      (PureVerifier.toArk toy20.specVerifier).rbrKnowledgeSoundnessWorstCaseWith (pure ()) noImpl
        (relK 20) Set.univ _ (toy20.extractor.toExtractor toy20.shape).toArk
        (kSF.toArk (pure ()) noImpl) (fun c => toy20.ε (chalIdx c)) :=
  Protocol.secure_toArk (pure ()) noImpl toy20 toy20_secure

end RecursionFast.Controls
