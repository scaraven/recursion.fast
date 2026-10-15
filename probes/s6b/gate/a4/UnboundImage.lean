import RecursionFast.Contract
/-! # A4 probe F2 — the image bytes and the score's shape inputs are not bound by the challenge

`Certificate1 S claim` pins `claim` (rendered), but the image the harness runs and the shape
quantities the scorer needs (`n`, `chalWords`, `msgCount`, `Σ 2^logLen`, `vkLen`) live inside
the solution's `submission`. Nothing in the statement fixes them as numbers, and the
computability gate (RESULT §6.10) covers only VK/IDX/prover/extractor. If the harness extracts
them by compiled evaluation (`#eval`, `lake exe`), `@[implemented_by]` makes it read different
values from the ones the kernel-checked certificate is about. Comparator accepts this: no axiom. -/
open RecursionFast

/-- The image the certificate is proved about. -/
def provedImage : Image := ⟨[0x00000293, 0x00100513, 0x00000073], []⟩
/-- What compiled evaluation returns instead (e.g. a different, unproved program). -/
def shownImage : Image := ⟨[0x00000013, 0x00000013, 0x00000293, 0x00100513, 0x00000073], [42]⟩

@[implemented_by shownImage] def submittedImage : Image := provedImage

-- the kernel sees the proved image
example : submittedImage = provedImage := rfl
theorem kernel_len : submittedImage.code.length = 3 := rfl
-- the compiler sees the other one
#eval submittedImage.code.length   -- 5
#eval submittedImage.data          -- [42]
#print axioms kernel_len           -- no axioms

/-- Same trick for a score input: the round count the scorer would print. -/
def roundsShown (_ : Unit) : ℕ := 1
@[implemented_by roundsShown] def roundsOf (_ : Unit) : ℕ := 2 ^ 14
#eval roundsOf ()                  -- 1  (the certificate's protocol has 2^14 rounds)
example : roundsOf () = 2 ^ 14 := rfl

/-- And the shape need not be evaluable at all (no gate on it): -/
noncomputable def oddShape : Fin 1 → Round :=
  fun _ => if Classical.propDecidable (∀ n : ℕ, n = n) |>.decide then .msg ⟨0, 0⟩ else .chal 1 []

/-- (v0.3 adaptation) a "certificate" mentioning the spoofed image and round count. -/
theorem cert : submittedImage.code.length = 3 ∧ roundsOf () = 2 ^ 14 := ⟨rfl, rfl⟩
