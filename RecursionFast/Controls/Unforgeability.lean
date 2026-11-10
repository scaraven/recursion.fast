/-
# Controls: the forgery events and the service's signed traces (`Library/Unforgeability.lean`)

On the contract's scheme under the reference signer's key (`Signer.pk sk`, every `sk`), with
`sign sk 0 m` and `sign sk 1 m` two signatures of one message under two one-time keys:
* `EufForgery`. Positive: a signature on a message other than the one signed (`euf_pos`).
  Negative: nothing on a signed message (`euf_signed`), and no invalid signature (`euf_invalid`).
* `SufForgery`. Positive: a second valid signature of a signed message, not issued
  (`suf_pos`). Negative: an issued pair (`suf_issued`).
* `SigOnlyForgery`. Positive: the same second signature (`sigOnly_pos`). Negative: an issued
  signature (`sigOnly_issued`).
* A second valid signature of a signed message, not issued by the signer, is a SUF-CMA and a
  signature-only forgery but **not an EUF-CMA forgery** (`resign_not_euf`): EUF-CMA does not
  forbid it, and the walk does not need it to. (A second signature the signer itself issues is in
  the record and no forgery of any kind.)
* The other non-implications, on a toy scheme where every signature verifies on every message:
  an EUF-CMA forgery that is no signature-only forgery (`euf_not_sigOnly`) and a SUF-CMA forgery
  that is neither (`suf_not_euf_sigOnly`).
* `Honest`. Positive: a one-entry trace signed by the reference signer, accounted for by a log
  holding its entry (`honest_one`), whose signing record holds its digest (`issued_one`).
  Negative: the same trace against the empty log (`not_honest_empty`), and a trace with a query
  over `queryCap` (`not_honest_cap`). `accounted` keeps that trace with that log
  (`accounted_one`) and drops it against the empty log (`accounted_empty`).
Symbolic (`sigOk_sign`); no hash is evaluated.
-/
import RecursionFast.Library.Unforgeability
import RecursionFast.Library.Signer

namespace RecursionFast.Controls.Unforgeability
open RecursionFast

variable (sk : ℕ → ℕ → Digest)

/-- Two signatures of one message under two one-time keys differ. -/
theorem sign_ne (m : Digest) : Signer.sign sk 0 m ≠ Signer.sign sk 1 m :=
  fun h => absurd (congrArg Sig.idx h) (by simp [Signer.sign])

/-- A signature with index `2^16` verifies on no message. -/
theorem sigOk_bad (vk m : Digest) : SigOk vk m ⟨2 ^ sigHeight, [], []⟩ = false := by
  simp [SigOk]

/-! ## `EufForgery` -/

/-- **Positive**: a signature on a message other than the one signed is an EUF-CMA forgery. -/
theorem euf_pos {m m' : Digest} (h : m ≠ m') :
    EufForgery (SigOk (Signer.pk sk)) {(m', Signer.sign sk 0 m')} m (Signer.sign sk 1 m) :=
  ⟨Signer.sigOk_sign sk 1 (by decide) m, by simpa using h⟩

/-- **Negative**: no signature on a signed message is an EUF-CMA forgery. -/
theorem euf_signed (vk m : Digest) (σ₀ σ : Sig) : ¬ EufForgery (SigOk vk) {(m, σ₀)} m σ :=
  fun h => h.2 ⟨_, rfl, rfl⟩

/-- **Negative**: an invalid signature is no EUF-CMA forgery, against every signing record. -/
theorem euf_invalid (vk m : Digest) (Iss : Set (Digest × Sig)) :
    ¬ EufForgery (SigOk vk) Iss m ⟨2 ^ sigHeight, [], []⟩ :=
  fun h => absurd h.1 (by simp [sigOk_bad])

/-! ## `SufForgery` and `SigOnlyForgery` -/

/-- **Positive**: the second signature of a signed message is a SUF-CMA forgery. -/
theorem suf_pos (m : Digest) :
    SufForgery (SigOk (Signer.pk sk)) {(m, Signer.sign sk 0 m)} m (Signer.sign sk 1 m) :=
  ⟨Signer.sigOk_sign sk 1 (by decide) m, fun h => sign_ne sk m (Prod.ext_iff.mp h).2.symm⟩

/-- **Negative**: an issued pair is no SUF-CMA forgery. -/
theorem suf_issued (vk m : Digest) (σ : Sig) : ¬ SufForgery (SigOk vk) {(m, σ)} m σ :=
  fun h => h.2 rfl

/-- **Positive**: the second signature of a signed message is a signature-only forgery. -/
theorem sigOnly_pos (m : Digest) :
    SigOnlyForgery (SigOk (Signer.pk sk)) {(m, Signer.sign sk 0 m)} (Signer.sign sk 1 m) :=
  ⟨⟨m, Signer.sigOk_sign sk 1 (by decide) m⟩, fun ⟨x, hx, he⟩ =>
    sign_ne sk m (by rw [← he, Set.mem_singleton_iff.mp hx])⟩

/-- **Negative**: an issued signature is no signature-only forgery. -/
theorem sigOnly_issued (vk m : Digest) (σ : Sig) : ¬ SigOnlyForgery (SigOk vk) {(m, σ)} σ :=
  fun h => h.2 ⟨_, rfl, rfl⟩

/-- **A second, unissued signature of a signed message is not an EUF-CMA forgery**: with only
`sign sk 0 m` issued, the valid `sign sk 1 m` is a SUF-CMA and a signature-only forgery, and not
an EUF-CMA forgery. -/
theorem resign_not_euf (m : Digest) :
    SufForgery (SigOk (Signer.pk sk)) {(m, Signer.sign sk 0 m)} m (Signer.sign sk 1 m) ∧
      SigOnlyForgery (SigOk (Signer.pk sk)) {(m, Signer.sign sk 0 m)} (Signer.sign sk 1 m) ∧
      ¬ EufForgery (SigOk (Signer.pk sk)) {(m, Signer.sign sk 0 m)} m (Signer.sign sk 1 m) :=
  ⟨suf_pos sk m, sigOnly_pos sk m, euf_signed _ m _ _⟩

/-! ## The other non-implications, on a toy scheme -/

/-- A toy scheme on one-bit messages and signatures: every signature verifies. -/
def anyOk : Bool → Bool → Bool := fun _ _ => true

/-- **An EUF-CMA forgery that is no signature-only forgery**: the issued signature, on another
message. -/
theorem euf_not_sigOnly :
    EufForgery anyOk {(false, false)} true false ∧ ¬ SigOnlyForgery anyOk {(false, false)} false :=
  ⟨⟨rfl, by simp⟩, fun h => h.2 ⟨_, rfl, rfl⟩⟩

/-- **A SUF-CMA forgery that is neither**: two issued pairs, crossed. -/
theorem suf_not_euf_sigOnly :
    SufForgery anyOk {(false, false), (true, true)} false true ∧
      ¬ EufForgery anyOk {(false, false), (true, true)} false true ∧
      ¬ SigOnlyForgery anyOk {(false, false), (true, true)} true :=
  ⟨⟨rfl, by simp⟩, fun h => h.2 ⟨(false, false), by simp, rfl⟩,
    fun h => h.2 ⟨(true, true), by simp, rfl⟩⟩

/-! ## `Honest` and `issued` -/

/-- A one-entry trace: the empty query and the answer `a`. -/
abbrev tr₁ (a : Digest) : Trace := [(ByteArray.empty, a)]

/-- The reference signer's signed set of that trace, with key `0`. -/
abbrev T₁ (a : Digest) : List (Trace × Sig) := [(tr₁ a, Signer.sign sk 0 (traceDigest (tr₁ a)))]

/-- **Positive**: a log holding the trace's entry accounts for it. -/
theorem honest_one (a : Digest) : Honest (T₁ sk a) (tr₁ a) :=
  ⟨by simp, by simp [queryCap]⟩

/-- **Positive**: the signing record holds the signed trace's digest and signature. -/
theorem issued_one (a : Digest) :
    (traceDigest (tr₁ a), Signer.sign sk 0 (traceDigest (tr₁ a))) ∈ issued (T₁ sk a) :=
  ⟨_, List.mem_singleton_self _, rfl⟩

/-- **Negative**: the empty log does not account for it. -/
theorem not_honest_empty (a : Digest) : ¬ Honest (T₁ sk a) [] :=
  fun h => absurd (h.inLog _ (List.mem_singleton_self _) _ (List.mem_singleton_self _))
    List.not_mem_nil

/-- A query one byte over `queryCap`. -/
def bigQuery : ByteArray := ⟨Array.replicate (queryCap + 1) 0⟩

/-- **Negative**: a signed trace with a query over `queryCap` is not accounted for, even by a log
that holds it. -/
theorem not_honest_cap (a : Digest) (σ : Sig) :
    ¬ Honest [([(bigQuery, a)], σ)] [(bigQuery, a)] :=
  fun h => absurd (h.cap _ (List.mem_singleton_self _) _ (List.mem_singleton_self _))
    (by simp [bigQuery, ByteArray.size])

/-- **Positive**: `accounted` keeps a signed trace the log accounts for. -/
theorem accounted_one (a : Digest) : accounted (T₁ sk a) (tr₁ a) = T₁ sk a :=
  accounted_of_honest (honest_one sk a)

/-- **Negative**: `accounted` drops a signed trace the log does not account for. -/
theorem accounted_empty (a : Digest) : accounted (T₁ sk a) [] = [] := by
  simp [accounted]

end RecursionFast.Controls.Unforgeability
