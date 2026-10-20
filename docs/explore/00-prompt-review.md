# Review of the exploration prompt

The prompt asks for an exploration of an alternative design: relativized knowledge soundness for the
recursion relation, a prover benchmark over many hash chains, and an oracle-proving charge. Below are
the points where it is ambiguous or incomplete, and how this exploration resolved each one. The user
was not available, so every resolution is the orchestrator's.

## Ambiguities, and how they were resolved

| # | Point | Why it matters | Resolution |
|---|---|---|---|
| 1 | `H` names two things: the concrete leaf hash ("x = H(w), H concrete") and the oracle of `NP^H`. | If the leaf hash is the oracle (`x = O^n(w)`), the leaf is the impossibility paper's own hard relation family: no argument can verify it with fewer than about `n` oracle queries, so nothing compresses. | The leaf hash stays concrete BLAKE2s, as in v3. Only the node relation queries the oracle. |
| 2 | "Relativized NARK for 2→1 or 1→1 recursion": which relation, which oracle. | v3's node clause runs the child verifier under concrete BLAKE2s. The relativized version runs it under the *same* oracle as the security game. These differ in what they prove and what they allow at deployment. | `RelO`: node clause `V^O c₁ π₁ ∧ V^O c₂ π₂`. In the potential form the child verdicts are read from the log. 1→1 is the one-child case. |
| 3 | "A million hash chains", with geomean/average/median of wall time. | A million leaf proofs at the measured honest speed (7.4–8.0 s per leaf at `n = 2^14` on 32 vCPUs) is about 90 machine-days per evaluation. Per-proof statistics also measure latency, not recursion throughput. | The benchmark shape is treated as a parameter. Per-proof statistics (D1) and whole-tree makespan (D2, v3) are both analysed. |
| 4 | Is recursion executed, or only priced? | If it is only priced, the relativized requirement is never exercised, and the score must estimate the cost of a recursion step from a proxy. | Both are studied: D1 (priced, not run) and D2/D4 (run). |
| 5 | "The cost of proving a random oracle call from the previous wall-time measurement", added or multiplied. | Units, gameability, and what the proxy omits (the verifier's local work) decide whether the charge rewards recursion-friendly verifiers. | Measured from leaf time per hash, as a marginal slope, or as a fixed constant. Each is analysed for gaming. Addition is the dimensionally sound form. |
| 6 | How the oracle is instantiated at deployment. | This decides whether O-25, the uninstantiability backdoor, closes. A public BLAKE2s oracle leaves it open whatever the theorem says. | Public BLAKE2s and a secret harness service are both studied. |
| 7 | "Lean 4 verifier (or RISC-V bytecode)". | A RISC-V verifier puts a machine-code program under the knowledge-soundness proof. Its cycle count could, however, price the verifier's local work. | The verifier stays a Lean query program (`OProg`). RISC-V is discussed only as a pricing tool. |
| 8 | "Compressing (but not necessarily succinct)": smaller proof, or less verifier work? | Witnesses are 48 bytes per leaf, so no proof is shorter than witness-sending's. Only verifier work can compress. | Compression means root-verifier work (oracle calls plus local computation) below witness-sending's. |
| 9 | Which version of the rules to build on. | The user is rewriting v3 in a separate worktree: potential-form `KState`, completeness with error `δ ≤ 2^-128`, extractor as a step-counted program. | The probes build on the committed head of `v3/rules-handoff` (`05fde28`). Designs are written against the rules worktree's text. |

## Scope the prompt leaves out

- **Deployment of the oracle.** As row 6 says, this decides O-25. The prompt does not mention it.
- **Composition across tree levels.** v3 does not claim it (DESIGN-v3 §5.4). The relativized relation
  is the standard route to making it a theorem, so it should be a goal of the exploration, not a
  side effect.
- **The admission rule that excludes non-proofs.** Without a compression or succinctness cap,
  witness-sending wins every wall-time board. Issue #6 shows that v3's `T_V` cap fails. The prompt's
  design needs its own cap.
- **Incentives against non-recursive strategies.** Concatenation, a flat SNARK of a subtree, and
  witness-sending below some level all compete with recursion (issue #6(b)). Which one wins is the
  core question for a recursion competition.
- **Realism.** The competition's purpose is designs that transfer to real recursive systems
  ("Flock 2.0"). A model in which the oracle is never proved in-circuit needs an argument that its
  winners transfer.
- **The extractor.** Node extraction is decoding, not log lookup (issue #7), and the extractor has a
  proved step bound. The design must stay within it.
- **The trusted-base and assumption budget.** V3-5 says ROM only. A harness service, signatures or a
  named collision-resistance assumption leave the pure ROM. Whether that is acceptable is a user
  decision. This exploration states the cost of each and does not assume one.
- **Deliverables and success criteria.** The prompt does not define success. This exploration uses:
  (i) O-25 closed by construction, not by review; (ii) recursion is the winning honest strategy;
  (iii) the security claim covers the whole tree; (iv) the trusted base stays near v3's 500-line
  budget; (v) an honest certified baseline exists or is in reach.

## How the prompt could be improved

1. Say which hash is the oracle and which is concrete (row 1), and how the oracle is deployed (row 6).
2. Fix the benchmark shape: chain length, number of chains, tree or IVC, and per-proof or makespan.
3. State the success criteria above, and say whether leaving the pure ROM for a trusted harness
   capability is acceptable.
4. Ask for the comparison with v3 explicitly, so the result is a decision ("adopt / amend / reject")
   rather than an essay.
5. Name the deliverables (report, Lean probes, design patch) and where they go.
