/-
  RecursionFast.Library.SigTrust  (UNTRUSTED, kernel-checked)

  **No certified verifier trusts a signature** (C-m1, V4-A7 (a); the reason for V4-1's `∀ vk`).

  `Vsig vk c π` accepts, with no oracle query, a proof that carries a signature of the statement
  `c` valid under `vk`: the "trust the signer" verifier. For a key whose signer is known (every
  `Signer.pk sk`, so every key the certificate quantifies over includes them), anyone can sign
  every statement, so:
  * `sigTrust_kstate_iff`: for every relation `R` and error `ε`, `Vsig (pk sk)` has a knowledge
    state for some extractor **exactly when every statement has a witness** (the shape of
    `acceptAll_kstate_iff`, `Library/Security.lean`): a signature is no knowledge.
  * `sigTrust_extracts`: a knowledge state for it with a named extractor `E` opens the signature
    of every statement to a witness on the empty log, so `E` must find witnesses from signatures
    alone; with an extractor that returns nothing there is no knowledge state at all
    (`sigTrust_no_kstate_none`).
  * `sigTrust_ks_of_unsignable` (the twin): under a key for which no signature verifies, the same
    verifier is knowledge-sound at error `0` for every relation and extractor. So it is exactly the
    quantification over keys whose secret the adversary may hold that excludes it; a certificate
    for one fixed key would not.
  `Controls/Certificate.lean` turns these into statements about `Certificate`.
-/
import RecursionFast.Library.Signer
import RecursionFast.Library.Security

open scoped NNReal

namespace RecursionFast.SigTrust
open RecursionFast

/-- The signature a proof carries: its words read as a signature (`readSig`). -/
def sigOf (π : Proof) : Option Sig := readSig.run' (packBytes π.data.toList)

/-- The proof that carries the signature `σ`: the bytes of its output words. -/
def sigProof (σ : Sig) : Proof := ⟨(wordsBytes (sigWords σ)).toArray⟩

theorem sigOf_sigProof (σ : Sig) (hi : σ.idx < 2 ^ 64) (ho : σ.ots.length = wotsLen)
    (hp : σ.path.length = sigHeight) : sigOf (sigProof σ) = some σ := by
  have h := readSig_sigWords σ hi ho hp []
  rw [List.append_nil] at h
  simp only [sigOf, sigProof, packBytes_wordsBytes, StateT.run', StateT.run] at h ⊢
  show (fun p => p.1) <$> readSig (sigWords σ) = some σ
  rw [show readSig (sigWords σ) = some (σ, []) from h]; rfl

/-- **The signature-trusting verifier**: accept, with no query, a proof carrying a signature of
the statement under `vk`. -/
def Vsig (vk c : Digest) (π : Proof) : OProg Bool :=
  .ret (match sigOf π with
    | some σ => SigOk vk c σ
    | none => false)

/-- Under the key of a known signer, the signature of every statement is accepted on the empty
log. -/
theorem Vsig_accepts (sk : ℕ → ℕ → Digest) (c : Digest) :
    (Vsig (Signer.pk sk) c (sigProof (Signer.sign sk 0 c))).runLog [] = some true := by
  have hs : sigOf (sigProof (Signer.sign sk 0 c)) = some (Signer.sign sk 0 c) :=
    sigOf_sigProof _ (by simp [Signer.sign]) (by simp [Signer.sign, Signer.wotsDigits_length])
      (Signer.sibs_length _ _ _ _)
  simp only [Vsig, hs, OProg.runLog, Signer.sigOk_sign sk 0 (by decide) c]

/-- **A knowledge state opens every statement's signature to a witness.** -/
theorem sigTrust_extracts {R : Digest → Wit → Prop} {E : Digest → Proof → Log → Option Wit}
    {ε : ℝ≥0} (sk : ℕ → ℕ → Digest) (k : KState R (Vsig (Signer.pk sk)) E ε) (c : Digest) :
    ∃ w, E c (sigProof (Signer.sign sk 0 c)) [] = some w ∧ R c w :=
  k.final [] c _ (Nat.zero_le _) (by rw [k.empty]; exact one_pos) (Vsig_accepts sk c)

/-- **A signature is no knowledge**: the signature-trusting verifier under a known signer's key
has a knowledge state, for some extractor, exactly when every statement has a witness. -/
theorem sigTrust_kstate_iff (sk : ℕ → ℕ → Digest) (R : Digest → Wit → Prop) (ε : ℝ≥0) :
    (∃ E, Nonempty (KState R (Vsig (Signer.pk sk)) E ε)) ↔ ∀ c, ∃ w, R c w :=
  ⟨fun ⟨_, ⟨k⟩⟩ c => (sigTrust_extracts sk k c).imp fun _ h => h.2,
    fun h => ⟨fun c _ _ => some (h c).choose,
      ⟨KState.zero ε fun _ c _ _ => ⟨_, rfl, (h c).choose_spec⟩⟩⟩⟩

/-- With an extractor that returns nothing, there is no knowledge state at any error. -/
theorem sigTrust_no_kstate_none (sk : ℕ → ℕ → Digest) (R : Digest → Wit → Prop) (ε : ℝ≥0) :
    IsEmpty (KState R (Vsig (Signer.pk sk)) (fun _ _ _ => none) ε) :=
  ⟨fun k => by obtain ⟨_, h, _⟩ := sigTrust_extracts sk k 0; cases h⟩

/-- **The twin**: under a key for which no signature verifies, the signature-trusting verifier is
knowledge-sound at error `0` with no query, for every relation and extractor. -/
theorem sigTrust_ks_of_unsignable {vk : Digest} (hvk : ∀ m σ, SigOk vk m σ = false)
    (R : Digest → Wit → Prop) (E : Digest → Proof → Log → Option Wit) :
    KS R (Vsig vk) E 0 0 := by
  refine ⟨⟨KState.zero 0 fun L c π h => ?_⟩, fun _ _ _ => le_rfl⟩
  simp only [Vsig, OProg.runLog, Option.some.injEq] at h
  split at h
  · rw [hvk] at h; cases h
  · cases h

end RecursionFast.SigTrust
