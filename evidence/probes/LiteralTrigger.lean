/-
ADV1 probe: the O-25 backdoor with a hard-coded 32-byte trigger.

`Controls/Backdoor.lean` computes its trigger as `blake2sOracle q0`, so the verifier's code calls
BLAKE2s on the oracle's domain. Here the trigger is a literal, computed offline
(`python3 -c "import hashlib; print(list(hashlib.blake2s(b'R').digest()))"`). The verifier is
*equal* to the control's, so it is certified by the same proof; but its constant closure contains
neither `blake2sOracle`, nor `tagRO`, nor `Submission.Vb`: the S1 review's proposed gate rejection
("reject a `V` whose closure contains `blake2sOracle`, `Submission.Vb` or `tagRO`") does not
fire, and the remaining "flag `compress`" signal fires equally on the honest witness-sending `V`.
The only trace of the backdoor in `V` is "an oracle answer is compared with a 32-byte constant",
which is also what an honest preprocessing verifier does with its verification-key root.
-/
import RecursionFast.Controls.Backdoor
import Lean

open scoped NNReal

namespace AdvProbe.Literal
open RecursionFast RecursionFast.Controls.Backdoor

/-- BLAKE2s-256(`'R'`), computed offline. -/
def lit : Digest := Vector.ofFn fun i => (#[29, 86, 144, 164, 133, 121, 229, 221, 32, 72, 179, 95,
  206, 34, 163, 46, 197, 81, 185, 199, 1, 29, 162, 42, 214, 148, 125, 104, 168, 33, 116, 127] :
  Array UInt8)[i]!

theorem lit_eq : trigger = lit := by decide +kernel

/-- The backdoored verifier, with the literal trigger. -/
def Vlit (c : Digest) (π : Proof) : OProg Bool :=
  .query q0 fun a => .ret ((decide (a = lit) && decide (π = magic c)) || check c π)

theorem Vlit_eq : Vlit = Controls.Backdoor.V := by
  funext c π; simp only [Vlit, Controls.Backdoor.V, lit_eq]

noncomputable def Slit : Submission := { S with V := Vlit }

theorem Slit_eq : Slit = S := by simp only [Slit, Vlit_eq]; rfl

theorem backdoor_lit :
    Certificate Slit ∧ ∀ c, Slit.Vb c (magic c) = true ∧ (magic c).size = 32 :=
  Slit_eq ▸ backdoor

end AdvProbe.Literal

open Lean in
/-- The constants reachable from `n` through definitions' values and types. -/
partial def closureOf (env : Environment) (n : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := [n]
  while !todo.isEmpty do
    match todo with
    | [] => break
    | m :: rest =>
      todo := rest
      if seen.contains m then continue
      seen := seen.insert m
      if let some ci := env.find? m then
        let cs := ci.type.getUsedConstants ++ (ci.value?.map Expr.getUsedConstants).getD #[]
        for c in cs do
          if !seen.contains c then todo := c :: todo
  return seen

open Lean Elab Command in
elab "#probe_closure " id:ident : command => do
  let env ← getEnv
  let n := id.getId
  let cl := closureOf env n
  let watch := [``RecursionFast.blake2sOracle, ``RecursionFast.tagRO,
    ``RecursionFast.Submission.Vb, ``RecursionFast.blake2s256, ``RecursionFast.Blake2s.compress]
  for w in watch do
    logInfo m!"{n}: closure contains {w}: {cl.contains w}"

#probe_closure AdvProbe.Literal.Vlit
#probe_closure RecursionFast.WitnessSending.V
#probe_closure RecursionFast.Controls.Backdoor.V

#print axioms AdvProbe.Literal.backdoor_lit
