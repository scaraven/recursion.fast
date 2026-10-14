import RecursionFast.Controls.Toy
/-! S4 review probe (S4-m3): after the swap the extractor image is load-bearing in `Secure`.

Fix pass: `toy_not_secure_of` and `toy_spin_not_secure` moved to `Controls/Toy.lean`, and
`nil_not_relK` to `Library/Extractor.lean`. This probe keeps the class-20 instance for the
over-long output (`longImage`), which needs the round cap since the fuel is now split. -/

open scoped NNReal
namespace RecursionFast.Probe
open RecursionFast RecursionFast.Controls

/-- **An over-long output makes the toy insecure** (class 20). -/
theorem toy_long_not_secure (ε : ChallengeIdx (toyShape 20) → ℝ≥0) :
    ¬ SecureWith (relK 20) Set.univ (toy 20 (by norm_num)).prover
        (toy 20 (by norm_num)).specVerifier
        ((longImage 1).toExtractor (toyShape 20)) ε :=
  toy_not_secure_of 20 (by norm_num) (longImage 1) (fun w => by
    rw [long_extractMid (by decide)]; exact nil_not_relK 20 _) ε

end RecursionFast.Probe

#print axioms RecursionFast.Controls.toy_spin_not_secure
#print axioms RecursionFast.Probe.toy_long_not_secure
