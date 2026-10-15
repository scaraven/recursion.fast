import RecursionFast.Contract
/-! P2d probe (A6-G1, `@[export]`): an exported C symbol can interpose on another symbol of the same
name in a linked badge executable; the gate rejects any `@[export]` entry of an untrusted module. -/
namespace ExportSol
@[export lean_recursionfast_evil] def shownVk (_ : Unit) : Nat := 1337
def submission : RecursionFast.Sub := ⟨0⟩
theorem cert : submission.vk = 0 := rfl
end ExportSol
