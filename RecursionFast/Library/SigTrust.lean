/-
  RecursionFast.Library.SigTrust  (UNTRUSTED, kernel-checked)

  **No certified verifier trusts a signature** (C-m1, V4-A7 (a); the reason for V4-1's `∀ vk`).

  `Vsig vk c π` accepts, with no oracle query, a proof that carries a signature of the statement
  `c` valid under `vk`: the "trust the signer" verifier. For a key whose signer is known (every
  `Signer.pk sk`, so every key the certificate quantifies over includes them), anyone can sign
  every statement, so:
  * **The adversary holds the key** (`adversary sk c`): it asks nothing and outputs `c` with the
    proof carrying `sk`'s signature of `c`; it wins with probability `1` unless the extractor
    opens that signature to a witness on the empty log (`adversary_wins`).
  * `sigTrust_ks_extracts`: so knowledge soundness at any `qV ≤ logCap` with `qV · ε < 1` (the
    certificate's caps give both) makes the named extractor open the signature of every
    statement to a witness on the empty log: `E` must find witnesses from signatures alone. With
    an extractor that returns nothing it fails (`sigTrust_not_ks_none`).
  * `sigTrust_ks_iff`: for every relation `R` and error `ε`, `Vsig (pk sk)` is knowledge-sound
    with no query, for some extractor, **exactly when every statement has a witness** (the shape
    of `acceptAll_ks_iff`, `Library/KS.lean`): a signature is no knowledge.
  * `sigTrust_ks_of_unsignable` (the twin): under a key for which no signature verifies, the same
    verifier is knowledge-sound at error `0` for every relation and extractor. So it is exactly the
    quantification over keys whose secret the adversary may hold that excludes it; a certificate
    for one fixed key would not.
  * The same facts about the library's potential (`KState`): `sigTrust_extracts`,
    `sigTrust_kstate_iff`, `sigTrust_no_kstate_none`.
  `Controls/Certificate.lean` turns these into statements about `Certificate`.
-/
import RecursionFast.Library.Signer
import RecursionFast.Library.KS
import RecursionFast.Library.PaperTheorem

open scoped NNReal

namespace RecursionFast.SigTrust
open RecursionFast

/-- The signature a proof carries: its words read as a signature (`readSig`). -/
def sigOf (π : Proof) : Option Sig := readSig.run' (packBytes π.data.toList)

/-- The proof that carries the signature `σ`: the bytes of its output words. -/
def sigProof (σ : Sig) : Proof := ⟨(wordsBytes (sigWords σ)).toArray⟩

theorem sigOf_sigProof (σ : Sig) (hi : σ.idx < 2 ^ 64) (ho : σ.ots.length = wotsLen)
    (hp : σ.path.length = sigHeight) : sigOf (sigProof σ) = some σ := by
  rw [sigOf, sigProof, packBytes_wordsBytes]
  exact congrArg (Prod.fst <$> ·) (List.append_nil (sigWords σ) ▸ readSig_sigWords σ hi ho hp [])

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
    sigOf_sigProof _ (Nat.two_pow_pos 64) (by simp [Signer.sign, Signer.wotsDigits_length])
      (Signer.sibs_length _ _ _ _)
  simp only [Vsig, hs, OProg.runLog, Signer.sigOk_sign sk 0 (by decide) c]

/-- **The adversary that holds the signing key `sk`**: it asks nothing and outputs the statement
`c` with the proof carrying `sk`'s signature of `c`. -/
def adversary (sk : ℕ → ℕ → Digest) (c : Digest) : OProg (Digest × Proof) :=
  .ret (c, sigProof (Signer.sign sk 0 c))

/-- **It wins with probability `1`** unless the extractor opens the signature of `c` to a witness
on the empty log. -/
theorem adversary_wins {R : Digest → Wit → Prop} {E : Digest → Proof → Log → Option Wit}
    (sk : ℕ → ℕ → Digest) (c : Digest)
    (hE : ¬ ∃ w, E c (sigProof (Signer.sign sk 0 c)) [] = some w ∧ R c w) :
    prob (Wins R (Vsig (Signer.pk sk)) E) ((adversary sk c).bind fun x =>
      (Vsig (Signer.pk sk) x.1 x.2).bind fun _ => .ret x) [] = 1 :=
  accept_wins (Vsig_accepts sk c) hE

/-- **Knowledge soundness opens every statement's signature to a witness**, on the empty log. -/
theorem sigTrust_ks_extracts {R : Digest → Wit → Prop} {E : Digest → Proof → Log → Option Wit}
    {ε : ℝ≥0} {qV : ℕ} (sk : ℕ → ℕ → Digest) (h : KS R (Vsig (Signer.pk sk)) E ε qV)
    (hq : qV ≤ logCap) (hε : (qV : ℝ≥0) * ε < 1) (c : Digest) :
    ∃ w, E c (sigProof (Signer.sign sk 0 c)) [] = some w ∧ R c w :=
  by_contra fun hE => not_ks_of_accept (Vsig_accepts sk c) hE hq hε h

/-- With an extractor that returns nothing, it is not knowledge-sound at `qV · ε < 1`. -/
theorem sigTrust_not_ks_none {ε : ℝ≥0} {qV : ℕ} (sk : ℕ → ℕ → Digest) (R : Digest → Wit → Prop)
    (hq : qV ≤ logCap) (hε : (qV : ℝ≥0) * ε < 1) :
    ¬ KS R (Vsig (Signer.pk sk)) (fun _ _ _ => none) ε qV :=
  fun h => by obtain ⟨_, h, _⟩ := sigTrust_ks_extracts sk h hq hε 0; cases h

/-- **A signature is no knowledge**: the signature-trusting verifier under a known signer's key
is knowledge-sound with no query, for some extractor, exactly when every statement has a
witness. -/
theorem sigTrust_ks_iff (sk : ℕ → ℕ → Digest) (R : Digest → Wit → Prop) (ε : ℝ≥0) :
    (∃ E, KS R (Vsig (Signer.pk sk)) E ε 0) ↔ ∀ c, ∃ w, R c w :=
  ⟨fun ⟨_, h⟩ c => (sigTrust_ks_extracts sk h (Nat.zero_le _) (by simp) c).imp fun _ h => h.2,
    fun h => ⟨fun c _ _ => some (h c).choose,
      KS.of_extracts (fun _ _ _ => le_rfl) (fun _ c _ _ => ⟨_, rfl, (h c).choose_spec⟩) ε⟩⟩

/-- **A knowledge state opens every statement's signature to a witness.** -/
theorem sigTrust_extracts {R : Digest → Wit → Prop} {E : Digest → Proof → Log → Option Wit}
    {ε : ℝ≥0} (sk : ℕ → ℕ → Digest) (k : KState R (Vsig (Signer.pk sk)) E ε) (c : Digest) :
    ∃ w, E c (sigProof (Signer.sign sk 0 c)) [] = some w ∧ R c w :=
  k.final [] c _ (Nat.zero_le _) (k.empty ▸ one_pos) (Vsig_accepts sk c)

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
  refine (KState.zero 0 fun L c π h => ?_).ks fun _ _ _ => le_rfl
  simp only [Vsig, OProg.runLog, Option.some.injEq, hvk] at h
  split at h <;> cases h

end RecursionFast.SigTrust
