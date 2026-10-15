import RecursionFast.Contract
/-! A6 probe: compiled-vs-kernel divergence through `@[init]` on an ordinary `def` (no
`implemented_by`, `extern`, `csimp`, `opaque`, `partial` or `unsafe`). -/
namespace InitSol
open RecursionFast

def evilInit : IO Nat := pure 1337

/-- The kernel sees `0`; compiled code (any executable importing this module) sees `1337`. -/
@[init evilInit] def vk : Nat := 0

def submission : Sub := ⟨vk⟩

theorem cert : submission.vk = 0 := rfl
end InitSol
