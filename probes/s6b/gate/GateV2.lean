import RecursionFast.Contract
import RecursionFast.Controls.Toy
import RecursionFast.Controls.CompileToy
/-! # Stage 6b gate probes: rule 4 (`--computable`) on the v2 badge-path fields (S5-A9)

The gate's rule 4 requires compiled code exactly for the fields the v2 badge path executes:
`Submission`: `P`, `cfg`; `SubmissionR`: also `entry`; `Protocol`: `n`, `shape`, `vkLen`, `VK`,
`idxShape`, `IDX`, `verify`, `extractor`; `ExtractorImage`: `img`; `RecursionEntry`: `C`, `decode`
(`scripts/Gate.lean`, `badgeFields`). Every other field may be `noncomputable`.

* **Positive** `submission`: the secure toy at class 20 with the declared error `errorCap`
  (`ε := fun _ => errorCap`, a noncomputable real), so `submission` as a whole has no code; every
  badge-path field has. `submissionNcProver`: also a noncomputable `prover` (v2 never executes the
  Lean prover). `submissionNcFuel`: a noncomputable fuel split of the image (data, not executed).
* **Negative**, each rejected at exactly one path: `submissionBadIdx` (`P.IDX`),
  `submissionBadVK` (`P.VK`), `submissionBadVerify` (`P.verify`), `submissionBadImg`
  (`P.extractor.img`). The noncomputable fields are the toy's own terms behind `noncomputable def`
  (no code is generated for them), so the toy's security proof still applies by unfolding.
* **Board R** (`SubmissionR`). No secure protocol has a recursion entry (DESIGN §7.3; the toy has
  none, `toy_no_entry`), so `entryProbe`'s proof fields are `sorry`: these constants exist only
  for rule 4, which never compiles proofs; rules 1–3 run on `cert`, which does not mention them.
  `submissionR` (positive: `C` and `decode` computable, `ε` and the proofs not) and
  `submissionRBadDecode` (negative: rejected at `entry.decode` only); `submissionRBadC`
  (negative: `entry.C`).
-/
namespace GateV2
open RecursionFast RecursionFast.Controls
open scoped NNReal

/-- The toy at class 20 with the declared error `errorCap` (no challenge rounds: any error). -/
noncomputable abbrev toyErr : Protocol 20 := { toy20 with ε := fun _ => errorCap }

/-- Security at the declared error (no challenge rounds, so soundness is vacuous). -/
theorem toyErr_secure : toyErr.Secure where
  complete := toy20_secure.complete
  sound := ⟨toyKSF 20 (by norm_num), fun _ c _ => (toy_noChal 20 c).elim⟩
  cap := fun c => (toy_noChal 20 c).elim

/-- **Positive**: every badge-path field compiles; `ε` does not. -/
noncomputable def submission : Submission 20 := ⟨toyErr, Compile.cfg2, toyErr_secure⟩

/-- The certificate whose closure the gate's rules 1–3 walk. -/
theorem cert : submission.P.Secure := submission.secure

/-- The toy's prover, without compiled code. -/
noncomputable def ncProver : Strategy toyErr.shape (Layout K × Stmt) (List (Table K)) Unit Unit :=
  toy20.prover

/-- **Positive**: a noncomputable Lean prover (not executed in v2). -/
noncomputable def submissionNcProver : Submission 20 :=
  ⟨{ toyErr with prover := ncProver }, Compile.cfg2, toyErr_secure⟩

/-- The toy image's fuel split, without compiled code. -/
noncomputable def ncFuel : Fin (1 + 1) → ℕ := toy20.extractor.fuel

/-- **Positive**: a noncomputable fuel split (data). -/
noncomputable def submissionNcFuel : Submission 20 :=
  ⟨{ toyErr with extractor := { toy20.extractor with fuel := ncFuel, fuel_le := toy20.extractor.fuel_le } },
    Compile.cfg2, toyErr_secure⟩

/-- The toy's indexer, without compiled code. -/
noncomputable def badIDX (L : Layout K) : OVal ⟨20 + 8, 20 + 8⟩ := toy20.IDX L

/-- **Negative**: a noncomputable `IDX`. -/
noncomputable def submissionBadIdx : Submission 20 :=
  ⟨{ toyErr with IDX := badIDX }, Compile.cfg2, toyErr_secure⟩

/-- The toy's key, without compiled code. -/
noncomputable def badVK (L : Layout K) : Fin 1 → K := toy20.VK L

/-- **Negative**: a noncomputable `VK`. -/
noncomputable def submissionBadVK : Submission 20 :=
  ⟨{ toyErr with VK := badVK }, Compile.cfg2, toyErr_secure⟩

/-- The toy's verifier, without compiled code. -/
noncomputable def badVerify (vk : Fin 1 → K) (x : Stmt) (ρ : Challenges toy20.shape) : QProg Bool :=
  toy20.verify vk x ρ

/-- **Negative**: a noncomputable `verify` (the executed verifier). -/
noncomputable def submissionBadVerify : Submission 20 :=
  ⟨{ toyErr with verify := badVerify }, Compile.cfg2, toyErr_secure⟩

/-- The toy's extractor image, without compiled code. -/
noncomputable def badImg : Image := toy20.extractor.img

/-- **Negative**: a noncomputable extractor image. -/
noncomputable def submissionBadImg : Submission 20 :=
  ⟨{ toyErr with extractor := { toy20.extractor with img := badImg, img_le := toy20.extractor.img_le } },
    Compile.cfg2, toyErr_secure⟩

/-- A node witness of zeros (what the probe's decoder returns). -/
def zeroNode : NodeWitness 1 :=
  ⟨(fun _ => 0, []), (fun _ => 0, []), .leaf, .leaf, fun _ => 0, fun _ => 0, [], []⟩

/-- NOT AN ENTRY: a rule-4 probe only (proof fields `sorry`, see the header). -/
noncomputable def entryProbe : RecursionEntry toyErr Compile.cfg2 where
  C := Compile.L0
  fits := sorry
  decode := fun _ => zeroNode
  sound := sorry
  complete := sorry
  live := sorry

/-- **Positive (board R)**: `C` and `decode` compile; `ε` and the proofs do not. -/
noncomputable def submissionR : SubmissionR 20 := { submission with entry := entryProbe }

/-- The probe's decoder, without compiled code. -/
noncomputable def badDecode (_ : List (Table K)) : NodeWitness 1 := zeroNode

/-- **Negative (board R)**: a noncomputable `decode`. -/
noncomputable def submissionRBadDecode : SubmissionR 20 :=
  { submission with entry := { entryProbe with decode := badDecode } }

/-- The probe's layout, without compiled code. -/
noncomputable def badC : Layout K := Compile.L0

/-- NOT AN ENTRY: `entryProbe` with a noncomputable layout (rule-4 probe only). -/
noncomputable def entryBadC : RecursionEntry toyErr Compile.cfg2 where
  C := badC
  fits := sorry
  decode := fun _ => zeroNode
  sound := sorry
  complete := sorry
  live := sorry

/-- **Negative (board R)**: a noncomputable `C`. -/
noncomputable def submissionRBadC : SubmissionR 20 := { submission with entry := entryBadC }

end GateV2
