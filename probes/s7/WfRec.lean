/-
S7 review probe: does an ordinary recursive verifier helper (structural and well-founded
recursion, `partial` excluded) pass the v2 gate? Real verifiers recurse; the gate's rule 3 rejects
`implemented_by` entries of untrusted modules, which Lean may add for compiled recursion.
-/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

def lg2 (n : Nat) : Nat := if h : n ≤ 1 then 0 else 1 + lg2 (n / 2)
termination_by n
decreasing_by omega

theorem wf_ok : sumTo 3 = 6 := by decide
