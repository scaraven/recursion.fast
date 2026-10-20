/-
# Probe P4: the lift (UNTRUSTED)

`docs/explore/notes/P4-lift-lean.md`.
* `Lift/Basic`: the lift of a flat argument (`lift`, `liftState`), the flat relation, witness-sending
  systems, knowledge states over any statement type.
* `Lift/WS`: the library's witness-sending format (`lift_ws`) and a cap-free one (`lift_free`).
* `Lift/Tree`: the runner's `treeRoot` as a perfect shape, and the lift for the runner's flat
  statement (`lift_runner`, `lift_runner_ws`).
* `Lift/Deferral`: the deterministic core of deferral (`reask`, `flip_reask`).
-/
import RecursionFast.Explore.Lift.Basic
import RecursionFast.Explore.Lift.WS
import RecursionFast.Explore.Lift.Tree
import RecursionFast.Explore.Lift.Deferral
