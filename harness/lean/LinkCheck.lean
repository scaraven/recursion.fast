/-
# Harness: organiser link and start-up check (Stage 6b)

Imports every organiser library a submission may import (contract, library, controls) and the
harness driver. `scripts/org-build.sh` builds it, so the object files a badge executable links are
prebuilt in the organiser package, which is read-only in the gate tree's sandbox (an import outside
this closure needs `scripts/badge-prereqs.sh`, harness/README.md); and runs it: a compiled
executable evaluates every closed term of every imported module when it starts, so an organiser
definition that is expensive to evaluate (Library/Field.lean's `Fintype K` was one: `2^64`
elements, out of memory) fails here instead of in every badge run.
-/
import RecursionFast.Contract
import RecursionFast.Library
import RecursionFast.Controls
import RecursionFastHarness

/-- Returns at once: reaching `main` means every imported module initialised. -/
def main : IO UInt32 := do
  IO.println "harness-linkcheck: the organiser libraries initialised"
  return 0
