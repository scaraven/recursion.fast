/-
  RecursionFast.Library.Unforgeability  (UNTRUSTED, kernel-checked)

  **The forgery events of the signature games**, and the record of what the service signed.

  A game is fixed by a verification function `ver : M → Sg → Bool` (for the contract's scheme,
  `SigOk vk` on 32-byte messages) and the **signing record** `Iss : Set (M × Sg)`, the
  message–signature pairs the signer issued during the attack (the signing oracle's answers).
  The adversary wins with:
  * `EufForgery ver Iss m σ` (**existential unforgeability under chosen-message attack**,
    EUF-CMA; Chiesa–Guan–Yildiz 2026, Definition 3.22): a valid signature `σ` on a message `m` the
    signer was never asked to sign;
  * `SufForgery ver Iss m σ` (**strong unforgeability**, SUF-CMA; the "super-secure" schemes of
    Chiesa–Tromer, ICS 2010, footnote 5): a valid pair the signer did not issue, possibly on a
    message it did sign;
  * `SigOnlyForgery ver Iss σ` (**security against signature-only forgery**, Chiesa–Tromer
    §2: "it is infeasible for a chosen-message attack to forge a hitherto-unseen signature that is
    valid for any message (the forger is not required to say which one)"): a signature valid for
    some message, which the signer never issued with any message.
  The original signed-oracle construction (Chiesa–Tromer) assumes both EUF-CMA and
  signature-only security, which it calls independent properties.

  **The implications** (`EufForgery.suf`, `SigOnlyForgery.suf`): an EUF-CMA forgery and a
  signature-only forgery are each a SUF-CMA forgery, so a strongly unforgeable scheme is secure in
  both senses. **Conversely** (`SufForgery.cases`), a SUF-CMA forgery is an EUF-CMA forgery, a
  signature-only forgery, or a signature the signer issued for one message, re-used valid on
  another message it also signed. The three games are pairwise different
  (`Controls/Unforgeability.lean`).

  **The service's signed traces.** The service signs, per request, the digest of the trace it
  answered (hash-then-sign). `issued T` is the signing record of a list `T` of signed traces, each
  trace replaced by its digest. `Honest T L` says what the composition argument needs of the
  service in a run whose oracle log is `L`: every trace it signed has its entries in `L` (each
  answer it signs is an oracle evaluation it made), and its queries within `queryCap` (the wire
  cap). `accounted T L` keeps the traces of `T` that `L` accounts for (`honest_accounted`), and
  is `T` when `L` accounts for all of them (`accounted_of_honest`). `eufForgery_issued_iff`: the
  EUF-CMA event against `issued T` depends on the digests of the signed traces only, never on the
  signatures the service issued. The reduction that uses them:
  `Library/Compose.lean`, `Forgery.reduce` and `walkSigned`.
-/
import RecursionFast.Library.Trace

namespace RecursionFast

/-! ## The games -/

section Games
variable {M Sg : Type} (ver : M → Sg → Bool) (Iss : Set (M × Sg))

/-- **An EUF-CMA forgery** against the verification `ver` and the signing record `Iss`: a valid
signature `σ` on a message `m` that the signer was never asked to sign. -/
def EufForgery (m : M) (σ : Sg) : Prop := ver m σ = true ∧ m ∉ Prod.fst '' Iss

/-- **A SUF-CMA forgery** against `ver` and `Iss`: a valid message–signature pair that the signer
did not issue. -/
def SufForgery (m : M) (σ : Sg) : Prop := ver m σ = true ∧ (m, σ) ∉ Iss

/-- **A signature-only forgery** against `ver` and `Iss` (Chiesa–Tromer): a signature valid for
some message, which the signer never issued with any message. -/
def SigOnlyForgery (σ : Sg) : Prop := (∃ m, ver m σ = true) ∧ σ ∉ Prod.snd '' Iss

variable {ver Iss}

/-- **An EUF-CMA forgery is a SUF-CMA forgery.** -/
theorem EufForgery.suf {m : M} {σ : Sg} (h : EufForgery ver Iss m σ) : SufForgery ver Iss m σ :=
  ⟨h.1, fun hm => h.2 ⟨_, hm, rfl⟩⟩

/-- **A signature-only forgery is a SUF-CMA forgery**, on a message the signature is valid for. -/
theorem SigOnlyForgery.suf {σ : Sg} (h : SigOnlyForgery ver Iss σ) :
    ∃ m, SufForgery ver Iss m σ :=
  h.1.imp fun _ hm => ⟨hm, fun hi => h.2 ⟨_, hi, rfl⟩⟩

/-- **A SUF-CMA forgery** is an EUF-CMA forgery, a signature-only forgery, or an issued
signature valid on a second signed message. -/
theorem SufForgery.cases {m : M} {σ : Sg} (h : SufForgery ver Iss m σ) :
    EufForgery ver Iss m σ ∨ SigOnlyForgery ver Iss σ ∨
      ((∃ σ', (m, σ') ∈ Iss) ∧ ∃ m', m' ≠ m ∧ (m', σ) ∈ Iss) := by
  by_cases hm : m ∈ Prod.fst '' Iss
  · by_cases hσ : σ ∈ Prod.snd '' Iss
    · obtain ⟨⟨m₁, σ'⟩, h₁, rfl⟩ := hm
      obtain ⟨⟨m', σ₂⟩, h₂, rfl⟩ := hσ
      exact .inr (.inr ⟨⟨σ', h₁⟩, m', fun he => h.2 (he ▸ h₂), h₂⟩)
    · exact .inr (.inl ⟨⟨m, h.1⟩, hσ⟩)
  · exact .inl ⟨h.1, hm⟩

end Games

/-! ## The service's signed set -/

/-- **The signing record of a list of signed traces**: each trace's digest, the message the
service signs, with its signature. -/
def issued (T : List (Trace × Sig)) : Set (Digest × Sig) :=
  (fun x => (traceDigest x.1, x.2)) '' {x | x ∈ T}

/-- **Signed traces the log accounts for**: every trace in `T` has its entries in the log `L` and
its queries within `queryCap`. -/
structure Honest (T : List (Trace × Sig)) (L : Log) : Prop where
  /-- Every entry of a signed trace is in the log. -/
  inLog : ∀ x ∈ T, ∀ e ∈ x.1, e ∈ L
  /-- Every query of a signed trace is within `queryCap`. -/
  cap : ∀ x ∈ T, ∀ e ∈ x.1, e.1.size ≤ queryCap

/-- A message the service signed is the digest of a signed trace. -/
theorem mem_fst_issued {T : List (Trace × Sig)} {m : Digest} :
    m ∈ Prod.fst '' issued T ↔ ∃ x ∈ T, traceDigest x.1 = m :=
  ⟨fun ⟨_, ⟨x, hx, hy⟩, hm⟩ => ⟨x, hx, by rw [← hm, ← hy]⟩,
    fun ⟨x, hx, hm⟩ => ⟨_, ⟨x, hx, rfl⟩, hm⟩⟩

/-- **The EUF-CMA event against the service reads no signature of its record**: a valid signature
on a message that is the digest of no signed trace. -/
theorem eufForgery_issued_iff {ver : Digest → Sig → Bool} {T : List (Trace × Sig)} {m : Digest}
    {σ : Sig} : EufForgery ver (issued T) m σ ↔ ver m σ = true ∧ ∀ x ∈ T, traceDigest x.1 ≠ m := by
  rw [EufForgery, mem_fst_issued]
  simp only [not_exists, not_and]

/-- Membership of an entry in a log is decidable, by the entries' decidable equality
(`ByteArray`'s own `BEq` is not known lawful, so the instance is given explicitly). -/
instance decMemLog (e : ByteArray × Digest) (L : Log) : Decidable (e ∈ L) :=
  @List.instDecidableMemOfLawfulBEq _ instBEqOfDecidableEq _ e L

/-- **The signed traces of `T` that the log `L` accounts for**: those whose entries are in `L`
and whose queries are within `queryCap`. -/
def accounted (T : List (Trace × Sig)) (L : Log) : List (Trace × Sig) :=
  T.filter fun x => decide (∀ e ∈ x.1, e ∈ L ∧ e.1.size ≤ queryCap)

/-- The log accounts for `accounted T L`. -/
theorem honest_accounted (T : List (Trace × Sig)) (L : Log) : Honest (accounted T L) L := by
  have h {x} (hx : x ∈ accounted T L) := of_decide_eq_true (List.mem_filter.mp hx).2
  exact ⟨fun x hx e he => (h hx e he).1, fun x hx e he => (h hx e he).2⟩

/-- On signed traces the log accounts for, `accounted` changes nothing. -/
theorem accounted_of_honest {T : List (Trace × Sig)} {L : Log} (h : Honest T L) :
    accounted T L = T :=
  List.filter_eq_self.mpr fun x hx =>
    decide_eq_true fun e he => ⟨h.inLog x hx e he, h.cap x hx e he⟩

end RecursionFast
