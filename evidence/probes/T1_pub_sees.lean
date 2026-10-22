/-
O25T probe T1. A literal sketch of Candidate T's `TSubmission` (memo R2.2, T-1..T-4) over the
contract at 05fde28, with a toy template (seed query, root absorb, one squeeze, fixed checks).
Question: can a submission-authored component receive / compute a challenge-dependent value?
-/
import RecursionFast.Contract.Certificate

namespace O25T
open RecursionFast

abbrev F := UInt64   -- stand-in for EF; the attack does not use field structure

/-- T-1, verbatim shape: first-order data, with the memo's `wf : Bool` as a FIELD. -/
structure UniformR1CS where
  s : ℕ
  m : ℕ
  k : ℕ
  A : List (ℕ × ℕ × F)
  B : List (ℕ × ℕ × F)
  C : List (ℕ × ℕ × F)
  chain : List (ℕ × ℕ)
  pubSlots : List ℕ
  wf : Bool

/-- T-2 (toy). -/
structure Params where
  rate : ℕ
  queries : ℕ
  grind : ℕ

def enc8 (a : F) : List UInt8 := (List.range 8).map fun i => (a >>> (8 * i).toUInt64).toUInt8

/-- Contract-side digests of the data (toy serialisations; any public function will do). -/
def csDigest (cs : UniformR1CS) : Digest :=
  blake2sDigest (0x63 :: enc8 cs.s.toUInt64 ++ enc8 cs.m.toUInt64 ++ enc8 cs.k.toUInt64)
def paramsDigest (p : Params) : Digest :=
  blake2sDigest (0x70 :: enc8 p.rate.toUInt64 ++ enc8 p.queries.toUInt64)

/-- The template's FIXED layout: the pre-challenge segment is bytes 0..40 (header + root). -/
def preSeg (π : Proof) : ByteArray := π.extract 0 40
def rootOfSeg (seg : ByteArray) : Digest := Vector.ofFn fun i : Fin 32 => seg.data.getD (8 + i.val) 0

/-- The seed query `0x10 ‖ c ‖ csDigest ‖ paramsDigest ‖ x` (R2.2 T-4). -/
def seedQ (c csd pd : Digest) (x : List F) : ByteArray :=
  ⟨(0x10 :: c.toList ++ csd.toList ++ pd.toList ++ x.flatMap enc8).toArray⟩
def absorbQ (st r : Digest) : ByteArray := ⟨(0x11 :: st.toList ++ r.toList).toArray⟩

/-- The rest of the fixed protocol (sumchecks, PCS): opaque organiser code. -/
def rest (_p : Params) (_cs : UniformR1CS) (_x : List F) (τ : Digest) (π : Proof) : Bool :=
  decide (π.size > 40) && decide (τ.get 0 ≠ 0xFF)  -- any fixed function

/-- The organiser's template (toy): seed, absorb root, squeeze `τ`, fixed checks. -/
def Template.verify (p : Params) (cs : UniformR1CS) (x? : Option (List F)) (c : Digest)
    (π : Proof) : OProg Bool :=
  match x? with
  | none => .ret false
  | some x =>
    .query (seedQ c (csDigest cs) (paramsDigest p) x) fun seed =>
    .query (absorbQ seed (rootOfSeg (preSeg π))) fun τ =>
    .ret (rest p cs x τ π)

/-- T-3 (the fields that matter here). -/
structure TSubmission where
  cs : UniformR1CS
  params : Params
  pub : Digest → ByteArray → Option (List F)

/-- T-4, verbatim. -/
def TSubmission.V (S : TSubmission) (c : Digest) (π : Proof) : OProg Bool :=
  Template.verify S.params S.cs (S.pub c (preSeg π)) c π

def TSubmission.Vb (S : TSubmission) (c : Digest) (π : Proof) : Bool :=
  S.cs.wf && decide (π.size ≤ proofCap) && (S.V c π).run blake2sOracle

/-- The challenge the template consumes, as a function of the oracle `H`. -/
def tmplTau (H : ByteArray → Digest) (cs : UniformR1CS) (p : Params) (c : Digest) (x : List F)
    (π : Proof) : Digest :=
  H (absorbQ (H (seedQ c (csDigest cs) (paramsDigest p) x)) (rootOfSeg (preSeg π)))

theorem verify_run (H : ByteArray → Digest) (p cs x c π) :
    (Template.verify p cs (some x) c π).run H = rest p cs x (tmplTau H cs p c x π) π := rfl

/-! ## Attack A: `pub` computes the outer proof's challenge (INV's "pub cannot see challenges")

`pub` is authored after `cs` and `params` are fixed, so it may hard-code their digests: no fixed
point. It decides its own output `x` first, then computes the deployment challenge for that `x`. -/

def honestX : List F := [7]

/-- What an adversarial `pub` computes from `(c, preSeg)` alone, with local BLAKE2s. -/
def pubTau (cs : UniformR1CS) (p : Params) (c : Digest) (seg : ByteArray) : Digest :=
  blake2sOracle (absorbQ (blake2sOracle (seedQ c (csDigest cs) (paramsDigest p) honestX))
    (rootOfSeg seg))

/-- **Kernel fact.** In deployment, `pub`'s local value IS the challenge the template consumes. -/
theorem pubTau_eq_challenge (cs p c π) :
    pubTau cs p c (preSeg π) = tmplTau blake2sOracle cs p c honestX π := rfl

/-- An adversarial `pub` that branches on the deployment challenge (here: rejects when byte 0 of
`τ` is zero; any predicate of `τ` and of locally computed BLAKE2s values may be used). -/
def evilPub (cs : UniformR1CS) (p : Params) (c : Digest) (seg : ByteArray) : Option (List F) :=
  if (pubTau cs p c seg).get 0 = 0 then none else some honestX

def cs0 : UniformR1CS := ⟨1, 1, 0, [], [], [], [], [], true⟩
def p0 : Params := ⟨2, 64, 0⟩

/-- It is a legal T submission: the field has exactly the type T-3 prescribes. -/
def S_evil : TSubmission := ⟨cs0, p0, evilPub cs0 p0⟩

/-- Deployment behaviour: `Vb` is a function of the outer challenge through `pub`. -/
theorem evil_Vb (c : Digest) (π : Proof) (hπ : π.size ≤ proofCap) :
    S_evil.Vb c π = if (tmplTau blake2sOracle cs0 p0 c honestX π).get 0 = 0 then false
      else rest p0 cs0 honestX (tmplTau blake2sOracle cs0 p0 c honestX π) π := by
  show (cs0.wf && decide (π.size ≤ proofCap) &&
      (Template.verify p0 cs0 (evilPub cs0 p0 c (preSeg π)) c π).run blake2sOracle) = _
  unfold evilPub
  rw [pubTau_eq_challenge]
  by_cases h : (tmplTau blake2sOracle cs0 p0 c honestX π).get 0 = 0
  · rw [if_pos h, if_pos h]; simp [Template.verify, OProg.run]
  · rw [if_neg h, if_neg h, verify_run]; simp [cs0, hπ]

/-! ## Attack B: `wf` is a field, so the submitter decides it -/

def csIllFormed : UniformR1CS := ⟨0, 0, 0, [(99, 99, 1)], [], [], [(5, 7)], [42], true⟩
example : csIllFormed.wf = true := rfl   -- "decided by the contract" is decided by the submitter

/-! ## Attack C (illustration): a multi-phase constraint language with a challenge term

If a menu item lets constraints mention a challenge `α` and columns committed after it
(LogUp/permutation phase-2 columns in a generic AIR/Plonkish format), data alone expresses the
post-hoc identity `α = g(phase-1 data)`, `g` = BLAKE2s wires laid out in phase-2 columns. -/

inductive Term | col (i : ℕ) | chal | const (a : F)
structure Gate where
  l : Term
  r : Term
  o : Term
def evalT (w : ℕ → F) (α : F) : Term → F
  | .col i => w i | .chal => α | .const a => a
def holds (gs : List Gate) (w : ℕ → F) (α : F) : Prop :=
  ∀ g ∈ gs, evalT w α g.l * evalT w α g.r = evalT w α g.o

/-- "the challenge equals phase-2 column 0" — the last line of the post-hoc check, as DATA. -/
def postHoc : List Gate := [⟨.chal, .const 1, .col 0⟩]
theorem postHoc_iff (w : ℕ → F) (α : F) : holds postHoc w α ↔ α = w 0 := by
  simp [holds, postHoc, evalT]

end O25T

#print axioms O25T.pubTau_eq_challenge
#print axioms O25T.evil_Vb
#print axioms O25T.postHoc_iff
