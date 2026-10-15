import RecursionFast.Contract
/-! A4 probe F7: a source-text computability/hygiene gate (regex as in scripts/check-hygiene.sh)
does not see an `implemented_by` hidden between string literals that look like a block comment to
the regex. Both are invisible to the kernel and the
comparator. The gate must inspect the elaborated environment, not the text. -/
open RecursionFast Lean

def provedImage : Image := ⟨[0x00000293, 0x00100513, 0x00000073], []⟩
def shownImage : Image := ⟨[0x00000013, 0x00000293, 0x00100513, 0x00000073], []⟩

-- (a) the regex strips everything between the two string literals as a "comment"
def opener := "/-"
@[implemented_by shownImage] def imgA : Image := provedImage
def closer := "-/"

example : imgA = provedImage := rfl
#eval imgA.code.length   -- 4: compiled code runs `shownImage`; the kernel term is `provedImage` (3)

/-- (v0.3 adaptation) a "certificate" whose closure contains `imgA`. -/
theorem cert : imgA.code.length = 3 := rfl
