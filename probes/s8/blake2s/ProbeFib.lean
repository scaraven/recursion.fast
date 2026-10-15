import Clean.Examples.FibonacciWithChannels
import RecursionFast.Clean.ToLayout
import Mathlib.Tactic.NormNum.Prime

open RecursionFast RecursionFast.Clean Air.Flat

instance : Fact (Nat.Prime 521) := ⟨by norm_num⟩
instance : Fact (521 > 512) := ⟨by norm_num⟩

-- Clean's own FibonacciWithChannels ensemble over F 521, through the generic `toLayout`
-- (no registered tables: its byte "lookups" are channel interactions, not `lookup`s).
abbrev ensP := (fibonacciEnsemble (p := 521)).ensemble

-- (cols, cons, t, q, ports, degree, entries, max message length) per chip
#eval ((toLayout [] ensP).chips.map fun C =>
  (C.cols, C.gadget.cons, C.gadget.t, C.gadget.q, C.ports.length,
    (List.ofFn fun i => (C.gadget.S i).length).foldr max 0, Chip.entries C,
    (C.ports.map fun p => p.msg.length).foldr max 0))
#eval (toLayout [] ensP).chips.map fun C => decide C.Admissible
#eval (chNames ensP)
