A6 gate probes (Lean core only; mini project mirroring the contract's module layout).
  lake build Contract Sol badge
  lake env <contract-v03>/.lake/build/bin/gate InitSol InitSol.cert --computable InitSol.submission,InitSol.vk   # PASS (G1: @[init] on a def)
  .lake/build/bin/badge     # compiled submission.vk = 1337, kernel: cert proves 0 by rfl
  lake env <contract-v03>/.lake/build/bin/gate TamperCert cert --computable submission                   # PASS (G2: olean tamper at build time)
  lake env lean --run Badge2.lean   # compiled submission.vk = 1337, kernel: 0
GateCopy.lean.txt = byte copy of contract-v03/scripts/Gate.lean used for `lake env lean --run`.
