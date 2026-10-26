# v4 (SROM) against the record: constraints C1–C15, the O-25 criteria, earlier decisions

Companion to [`../DESIGN-v4-srom.md`](../DESIGN-v4-srom.md) ("design §n"), for the user and the
record. It checks the design against the constraints any next design must satisfy (v3 design
§16), against the ten criteria a solution to O-25 must meet (O-25 record §11), and lists the
decisions of the earlier proposals that v4 settles. Ids as in the sources.

## 1. The constraints C1–C15 of v3 §16

| | Constraint | v4 |
|---|---|---|
| C1 | knowledge is a bounded program | kept verbatim (`XProg`, `Computes`, `B t`); the node decoder's fit to the budget remains an estimate (F-D1) |
| C2 | the certificate says what it does not say | the trust statement names the PRF assumption and every paper step (design §2.7); no property rests on review |
| C3 | KS satisfiable by a Merkle/BCS verifier | the potential form is v3's, and so are its controls (`Controls/Potential.lean`: `twoLucky`, `Vcol`, `V24`), re-instanced for `errorCap = 2^-120` (V4-A9, which also admits GF(2^128) rounds, FB-9) |
| C4 | extraction from what the log holds | the clause no longer instantiates the oracle; a bounded node still forces a decoding extractor, paper (#7) |
| C5 | caps admit an honest recursive entry, sized first | **not met**: no sizing redone for v4 (design §4.2); the certified baseline's measured frontier stops far below the season shape (design §3.6) |
| C6 | succinctness is not wall time | partly: the wall time of one `acc` check pinned to one core (an upper bound on its CPU time, not the unpinned wall time v3 found gameable), against the organiser's chain checker timed the same way in the same job (V4-12); the SIMD caveat stays, and binary fields are disadvantaged (Q11) |
| C7 | the score prices recursion | `S = T_tree + K·t_link` |
| C8 | completeness with error; the deployment checked concretely | kept (`δ ≤ 2^-40` since V4-A9); every scored proof, the tree's root and every stream output, checked with `acc`; no per-entry extractor liveness since V4-A9 (`Computes` is kernel; the core CI runs the compiled interpreter on the library's entry) |
| C9 | the badge path linear and strict | `runSeq` linear, strict `decodeWit`, `acc` ordered for rejection, word-level twins (`acc` on a `2^16`-query trace 135–155 ms); crafted-input DoS open (design §4.3) |
| C10 | the toolchain is part of the rules | certificate job separated; Lean kernel only on CI (nanoda above 16 GB); the image's `gcc`/`as` versions are part of the rules; the compile traps listed (design §3.7); the 30-minute caps of V4-A9 (build and kernel 10 min each on a 4-vCPU runner) are a rule, not yet run against a real entry on a runner |
| C11 | the design space stays open | no menu, no review of `V`, no manual step; the assembly rule fixes the prover's delivery format, not its proof system |
| C12 | the trusted base stays readable | 355 of 500 code lines, core and Mathlib only, controls for every definition, three axioms |
| C13 | a reference machine before any cap is valued | the GitHub-hosted runner, measured (`T_triv,best` 1.78 s); `T_V` and the service self-calibrate per job; `K` and `R` provisional |
| C14 | the pin discipline | unchanged: the submissions repository's pin moves to a core commit on the remote, in its own commit, before any entry is certified against it |
| C15 | every transcript seed binds the statement | not a contract rule; a rulebook rule and the statement-flip canary (`stmt-bit`); the secret key removes the premise of Fenzi's attack (paper) |

## 2. The ten criteria of O-25 §11

| # | Criterion | v4 |
|---|---|---|
| 1 | no narrowing of the design space | met in the authors' reading: the rule restricts how the oracle is deployed and what `V` reads (a signed trace), not which proof system; not put to the user |
| 2 | no large human review surface | the recognition rule and the review of `V` are deleted; the contract (355 code lines) and the runtime (3,677 after V4-A9, of which the service 953) are read once |
| 3 | no manual intervention | the harness decides; approving a first-time contributor's workflow is compute admission; unlike D4 there is no key release and no designated-verifier window |
| 4 | survives the kernel attacks and the post-hoc one | the backdoor is ported and certified in the model (kernel, `Controls/Backdoor.lean`, `backdoor`; `magic_needs_trigger`: its magic proof is accepted only on a signed trace answering the empty query with the public hash) and stopped by the PRF hybrid (paper); the post-hoc attack needs `PRF_k` wires nobody outside the service can make; its signed-trace variant is uncertifiable (design §2.2) |
| 5 | a kernel certificate within the trusted budget | yes: 355 of 500 code lines |
| 6 | states its guarantee and adversary | design §2.7: PRF, collision resistance, one-wayness, a correct service, the organiser's key management, an attested machine; "ROM-secure ⇒ BLAKE2s-secure" is not claimed |
| 7 | covers the liveness mirror | closed by the same reduction (paper); every scored proof is checked under the deployment |
| 8 | honest recursion expressible | yes: a node checks children against signed traces; the node-clause positive control uses the Lean signer (kernel, `node_of_two_leaves`); the succinct node's extractor is paper (#7) |
| 9 | statement binding of every seed | not mandated by the contract; see C15 |
| 10 | built against a real entry first | in part: the witness-sending entry and the certified baseline `spartan-srom` are ACCEPTed end to end at the smoke shape on the development VM; the baseline found Q2–Q5, Q7, Q11 and Q15; no entry runs the season-1 shape, and nothing has run end to end on a GitHub runner (design §0) |

## 3. The earlier proposals' decisions v4 settles

| Id | Settled as |
|---|---|
| RU-1 (leave V3-5 for a trusted service and the PRF assumption) | taken: V4-2, V4-3; W5 not adopted (V4-14) |
| RU-2 (designated-verifier window, or D3) | D3 (P1): no window |
| RU-3 ("a witness or a collision" as `final`) | moot: `final` stays v3's; collisions appear only in the composition walk |
| RU-4 (the shape, or a flattening policy) | both: `r = 6`, `n = 2^18` with flattening allowed, recursion priced by the stream |
| RU-5 (records certify the deployment) | yes, relative to the organiser's key management (V4-A8) |
| RU-6 (R3 D4+, R4 W5) | neither (V4-14) |
| RR-2, RR-7, RR-8 | adopted in substance (V4-2; `Vb` and the recognition rule deleted; the service on the prover's CPUs) |
| RR-3, RR-4, RR-9, RR-11, RR-12 | replaced by signatures; `queryCap` only; no key release; no W5; no D4+ |
| CM-1, CM-4, CM-6, CM-7 | adopted |
| CM-2 | `K = 20` for season 1, provisional |
| CM-3 | modified: `r = 6`, `n = 2^18` instead of `r = 4`, `n = 2^20` (16 GB) |
| CM-5 | `M = 512`, `n_f = 2^16`; `M = 256` since V4-A9 |
| CM-8 | `R = 10`, provisional (Q11); R3 not run |
