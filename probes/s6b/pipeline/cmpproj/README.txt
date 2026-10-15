A6 probe G0: comparator's guarantee depends on build ORDER (comparator README assumption 2).
Contract stand-in: `Good s := s.vk = 42 ∧ s.vk = 43` (unsatisfiable). The solution imports a module
`Tamper` whose elaboration rewrites the contract .olean (`Good := True`); lake does not notice.
  C=../../../contract/tools/comparator
  export COMPARATOR_LANDRUN=$C/scripts/fake-landrun.sh COMPARATOR_LEAN4EXPORT=$C/.lake/packages/lean4export/.lake/build/bin/lean4export
  A) rm -rf .lake; lake env $C/.lake/build/bin/comparator config.json
     -> "Const does not match between challenge and target 'RecursionFast.Good'"  (rejected, correct)
  B) rm -rf .lake; lake build Contract Solution; lake env $C/.lake/build/bin/comparator config.json
     -> "Your solution is okay!"  (accepted: the challenge was elaborated against the tampered contract)
B is the order of contract-v03/scripts/ci.sh (line 12 builds RecursionFastAudit = ToyChallenge +
ToySolution, then the gate reads ToySolution, and the comparator runs last).
