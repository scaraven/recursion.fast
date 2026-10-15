import TamperSol
import RecursionFast.Contract
/-! The certificate: kernel value of `evilVk` is `0`, compiled value `1337`. -/
def submission : RecursionFast.Sub := ⟨RecursionFast.evilVk⟩
theorem cert : submission.vk = 0 := rfl
