/-
# Gate fixture: an entry that imports CompPoly's binary field (FIXLIST Q2)

CompPoly's `BF64`/`Ext3` closure is organiser-built and pinned in the manifest
(`harness/org-setup.sh`), so the gate reports its `@[csimp]` lemma (`CompPoly.Fields.Extension.
Arithmetic`) as a note on a pinned dependency instead of rejecting it (gate rule 3), and the
import is allowed (rule 6). Run by `tests/gate/check.sh`.
-/
import RecursionFast.Library.WitnessSending
import CompPoly.Fields.Binary.BF64.Ext3
import CompPoly.Fields.Binary.BF64.Bytes
open RecursionFast

/-- The witness-sending submission, in a module that imports the field. -/
def compS : Submission := WitnessSending.submission
/-- A theorem about `compS`, the gate's root. -/
theorem compS_fact : compS.qV = 0 := rfl
