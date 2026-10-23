/-
# Gate fixtures: three submissions the gate must reject (tests/gate/check.sh)

* `badS`: the witness-sending submission with a noncomputable extractor program (rule 4: the
  badge runs `ext` on the compiled interpreter).
* `implS`: a verifier whose decision is a definition with `@[implemented_by]` (rule 3: compiled
  code that is not the definition the kernel checked).
* `partialS`: a verifier calling a `partial` definition (rule 2: its body is invisible to the
  kernel).
-/
import RecursionFast.Library.WitnessSending
open RecursionFast

/-- A noncomputable extractor program. -/
noncomputable def badExt : XProg := Classical.choice ⟨WitnessSending.ext⟩
/-- The witness-sending submission with that program. -/
noncomputable def badS : Submission := { WitnessSending.submission with ext := badExt }
/-- A theorem about `badS`, the gate's root. -/
theorem badS_fact : badS.qV = 0 := rfl

/-- What the compiled code runs instead of `strictCheck`. -/
def gateNegAcceptAll (_ _ : Digest) (_ : Proof) : Bool := true
/-- A decision whose compiled code is `gateNegAcceptAll`. -/
@[implemented_by gateNegAcceptAll] def strictCheck (vk c : Digest) (π : Proof) : Bool := WitnessSending.check vk c π
/-- A submission whose verifier is `strictCheck`. -/
def implS : Submission := { WitnessSending.submission with V := fun vk c π => .ret (strictCheck vk c π) }
/-- A theorem about `implS`, the gate's root. -/
theorem implS_fact : implS.qV = 0 := rfl

/-- A `partial` loop. -/
partial def spin (n : Nat) : Bool := if n = 0 then true else spin (n - 1)
/-- A submission whose verifier calls it. -/
def partialS : Submission := { WitnessSending.submission with V := fun _ _ π => .ret (spin π.size) }
/-- A theorem whose closure holds `partialS`. -/
theorem partialS_fact : partialS.V = partialS.V := rfl
