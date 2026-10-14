import RecursionFast.Controls.Toy
import RecursionFast.Controls.Hit
/-! S4 review probe: axioms of the trusted S4 definitions, the refinement interface and every
control; structural (not well-founded) recursion of `execute`; `@[irreducible]` on
`extractorFuel` is invisible to the kernel. (Fix pass: names updated to the split fuel and the
controls added by the fix pass; the toy's controls are in `Controls/Toy.lean`.) -/
open RecursionFast RecursionFast.Controls

-- Trusted definitions
#print axioms RecursionFast.run
#print axioms RecursionFast.execute
#print axioms RecursionFast.ExtractorImage.toExtractor
#print axioms RecursionFast.ExtractorImage.call
#print axioms RecursionFast.extractorTape
#print axioms RecursionFast.decTables
#print axioms RecursionFast.decMid
-- Refinement interface
#print axioms RecursionFast.ExtractorImage.extractMid_eq_of_run
#print axioms RecursionFast.ExtractorImage.extractMid_eq_nil_of_run
#print axioms RecursionFast.ExtractorImage.extractOut_eq_of_run
#print axioms RecursionFast.ExtractorImage.extractOut_eq_nil_of_run
#print axioms RecursionFast.run_mono
#print axioms RecursionFast.unframe_extractorTape
#print axioms RecursionFast.pLayout_words
#print axioms RecursionFast.decTables_map_bits
#print axioms RecursionFast.firstMsg_extractMid
#print axioms RecursionFast.ExtractorImage.composed_fuel_le
#print axioms RecursionFast.ExtractorImage.even
#print axioms RecursionFast.ExtractorImage.atZero
#print axioms RecursionFast.nil_not_relK
#print axioms RecursionFast.run_none_of_le
#print axioms RecursionFast.Protocol.Secure
-- Controls
#print axioms copy_run
#print axioms copy_steps
#print axioms copy_extractMid
#print axioms copy_run0
#print axioms copy_extract_relK
#print axioms wzbc_run
#print axioms tape_readonly
#print axioms tape_below_ok
#print axioms halt_misaligned
#print axioms ecall_trap
#print axioms halt_reads
#print axioms spin_run_100
#print axioms spin_run
#print axioms spin_extractMid
#print axioms long_extractMid
#print axioms long32_extractMid
#print axioms tape_roundTrip
#print axioms layout_roundTrip
#print axioms brute_cost
#print axioms brute_none
#print axioms bruteTarget_tape
#print axioms brute_extractMid_nil
#print axioms brute_nonvacuous
#print axioms chain_finds
#print axioms chain_round0
#print axioms chain_search_fails
#print axioms composed_lt_word
#print axioms composed_lt_two_words
#print axioms word_le_budget
#print axioms budget_24_25
#print axioms brute_steps_exceed
#print axioms oracle_sq
#print axioms cube_gt
#print axioms quadratic_fits
#print axioms toy_extractMid
#print axioms toy_secure
#print axioms toy20_secure
#print axioms toy_not_secure_of
#print axioms toy_spin_not_secure
#print axioms rejectAll_not_secure
#print axioms hit_secure

/-! `execute` is compiled by structural recursion on the fuel (no `WellFounded.fix`). -/
open Lean Meta in
#eval show MetaM Unit from do
  let env ← getEnv
  for n in [``RecursionFast.execute, ``RecursionFast.decTables, ``RecursionFast.frame,
      ``RecursionFast.run] do
    let some ci := env.find? n | throwError "missing {n}"
    let used := (ci.value?.map (·.getUsedConstants) |>.getD #[])
    let wf := used.any fun c => c == ``WellFounded.fix || c == ``WellFounded.fixF
    IO.println s!"{n}: WellFounded.fix used = {wf}; partial/unsafe = {ci.isUnsafe || ci.isPartial}"

/-! The attribute is elaboration-only: the kernel unfolds the fuel. -/
example : extractorBudget 20 = 2 ^ 56 := by decide +kernel
example : extractorBudget 28 = 2 ^ 72 := by decide +kernel
example : resumeImage.fuel 0 = 2 ^ 54 := by decide +kernel
