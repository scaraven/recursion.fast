import GClean.Core
import RecursionFast.Clean
/-! S6b-A11 probe: the circuit part of a board-R submission imports the Clean frontend. NOT AN
ENTRY: the proof fields are `sorry` (no secure protocol has a recursion entry, DESIGN §7.3), as in
`GateV2.entryProbe`; the gate's rules 4, 8, 9 never look at proofs. `uses_clean` is a theorem
that uses Clean (it goes into the certificate the gate walks). -/
namespace GClean
open RecursionFast RecursionFast.Controls

/-- A Clean fact (`RecursionFast.Clean`'s `FiniteField K`): its size is `2^64`. -/
theorem uses_clean : FiniteField.size K = 2 ^ 64 := K.size_eq

/-- NOT AN ENTRY (proofs `sorry`): `C` and `decode` do not use Clean. -/
noncomputable def entry : RecursionEntry GateV2.toyErr Compile.cfg2 where
  C := Compile.L0
  fits := sorry
  decode := fun _ => GateV2.zeroNode
  sound := sorry
  complete := sorry
  live := sorry

/-- NOT AN ENTRY (proofs `sorry`): `decode` calls Clean code (`FiniteField.val`, rule 9). -/
noncomputable def entryBadDecode : RecursionEntry GateV2.toyErr Compile.cfg2 where
  C := Compile.L0
  fits := sorry
  decode := fun _ => if FiniteField.val (0 : K) = 0 then GateV2.zeroNode else GateV2.zeroNode
  sound := sorry
  complete := sorry
  live := sorry

/-- A protocol part declared in a module that imports Clean (rule 8 rejects it as a badge root). -/
noncomputable def leafBad : Submission 20 := GateV2.submission

end GClean
