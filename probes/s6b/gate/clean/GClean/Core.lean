import GateV2
/-! S6b-A11 probe: the protocol part `leaf` of a board-R submission, in a module that imports
neither Clean nor anything outside the compiler-free closure (gate rule 8 passes). -/
namespace GClean
open RecursionFast

/-- The protocol part: `GateV2.submission` (the toy at class 20, `ε := errorCap`). -/
noncomputable def leaf : Submission 20 := GateV2.submission

end GClean
