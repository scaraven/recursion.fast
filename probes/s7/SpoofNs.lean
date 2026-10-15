/-
S7 review probe: v0.3's `SpoofCert` in the v2 setting. A solution module (fresh root, as the
harness requires) puts an `@[implemented_by]` on a constant in the contract's namespace. v0.3's
first gate trusted by name prefix; v2's trusts by `.olean` hash, so this module is untrusted and
rule 3 must reject it.
-/
import RecursionFast.Contract
import RecursionFast.Controls.Toy

namespace RecursionFast.Contract.Spoof
open RecursionFast

def fastDecide (_ : List K) : Bool := true
@[implemented_by fastDecide] def decide' (l : List K) : Bool := l.isEmpty

def submission : Submission 24 :=
  ⟨RecursionFast.Controls.toy 24 (by decide), ⟨.blake2s, 2, by decide⟩, RecursionFast.Controls.toy_secure 24 _⟩

end RecursionFast.Contract.Spoof
