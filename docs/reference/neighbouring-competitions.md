# Neighbouring competitions: what they do, what recursion.fast took from them, what to re-check

Reference for whoever tweaks the competition rules, the harness or the baseline. It condenses the
four research notes in `docs/reference/notes/` (written 2026-10-10 against the pinned checkouts
below) and the report's prior-competitions section (`CambridgePQ/recursion.fast/report/sections/
04-prior-competitions.tex`). Facts carry the note's label where the note had one: **[V]** read in
the cited file, **[M]** measured on the development machine, **[I]** inference. Line references are
to the pinned revisions and may have moved upstream.

| Neighbour | What is contested | Upstream | Pinned checkout | Note |
|---|---|---|---|---|
| **ots.golf** (leanEthereum) | cheapest verification of a hash-based one-time signature; five tracks, proved bounds | https://ots.golf, https://github.com/leanEthereum/ots.golf-dev | `8b140a9` (2026-09-30), Lean v4.33.1 | [R1](notes/R1-ots-golf.md) |
| **sig.golf** (Yukon / Eigen Labs / EF) | stateless hash-based signature minimising signature bytes × proved honest verify cycles | https://www.yukon.org/sig.golf, https://github.com/Layr-Labs/sig.golf-dev | `eaa0c7f` (2026-09-30), Lean v4.33.1, riscv-zkvm `4634e41`, VCVio `25f26bf` | [R2](notes/R2-sig-golf.md) |
| **Proximity Prize** on better.codes (Yukon / zkSecurity) | a threshold radius of one fixed toy IOP (ABF26 §6) over interleaved RS codes; two-sided bracket | https://better.codes, https://github.com/proximity-prize/proximity-prize | `ed2b68c` (2026-10-01), Lean v4.32.2, ArkLib `e651978` | [R3](notes/R3-proximity-prize.md) |
| **leanerVM** (Verified-zkEVM) | not a competition: the end-to-end Lean formalisation of leanVM's proof system on ArkLib; the model for our trust policy and for the roadmap issue | https://github.com/Verified-zkEVM/leanerVM | `485d046` here (note written at `8aaf8a0`), pins ArkLib `7653a90`, VCVio `a4232d0`, CompPoly `572f997`, Clean `42fe4b26` | [R5](notes/R5-leanervm.md) |
| zk.golf (zkSecurity) | Clean circuits minimising allocations and constraints; soundness **and** completeness required | https://zk.golf, https://blog.zksecurity.xyz/posts/zkgolf/ | not checked out | report §4.4 |
| Yukon challenges (precompile.fast, SNARK.fast, …) | the host's common model: the creator supplies verifier and baseline, a deterministic gate runs before merge | https://www.yukon.org | not checked out | report §4.4 |

All three Lean-scored competitions permit exactly the axioms `propext`, `Quot.sound`,
`Classical.choice`, refuse `native_decide`, and check with leanprover/comparator against a
rendered challenge stub [V]. recursion.fast does the same (harness order A6-G0, design v3 §7.6).

---

## 1. ots.golf

**Object and score** [V]. "How cheaply can a hash-based one-time signature be verified?" Every
score is a proved bound; no emulator is in the scoring path. One random oracle on bit strings,
one compression per started 512-bit block. Tracks: a lower bound for whole-word DAG schemes;
compressions; RISC-V cycles over *every* run; hinted RISC-V cycles over every accepting run under
every prover-chosen view; leanISA cycles. Records at `30cff14`: 90, 86, 341, 310, 1088.

**Trusted contract** [M]. 1,625 lines, 623 code, across `Model`, `OracleAlgorithm`, `Dag`,
`WholeWords`, `RiscvMachine`, `Riscv`, `RiscvHint`, `LeanIsaMachine`, `LeanIsa` and five stubs;
the RISC-V path alone is about 220 code lines plus about 1,500 code lines of riscv-zkvm
semantics plus VCVio's `OracleComp`, `IsQueryBound`, `randomOracle`, `simulateQ`, `Pr[…]`.
Security is concrete: for every adversary and every pathwise query budget `B` of the whole
experiment, honest parties included, forgery probability `< B / 2^127`. The RISC-V certificate
bundles `admissible` (perfect correctness, determinism, size limits, `2^20` budgets for keygen,
sign and verify), `secure`, `implements` (the machine's run equals the Lean verifier as an
equality of oracle-computation trees) and `cycles` (a bound over every execution). A separate
theorem caps the image under 1 MiB.

**Machine** [V]. A 79-code-line wrapper around riscv-zkvm `4634e41`: Harvard image (`List Instr`
plus data bytes), raw-input loader with a length sentinel, `HASH` and `HALT` syscalls selected by
`t0`, fuel-indexed `execute` in `OracleComp`. The admitted subset has only five W-ops, which bites
32-bit field arithmetic. The hinted track's four clauses, `Sound`, `Faithful`, `Expands`,
`CyclesAtMost` over all views and all fuel, are the template for "a verifier reading an untrusted
proof".

**Pipeline** [V]. Trusted dev repository and untrusted submissions repository; PR-only intake of
one flat root, never merged, retention tags, durable verdict comments, bot record snapshots, a
`NOTES.md` journal published as untrusted text; protected-file pin whose SHA-256 is the contract
id; header import policy (exact modules for the contract, prefixes for Mathlib and VCVio); warm
`.lake` clone with stale-olean deletion; claim rendered into the stub; comparator under a
transient systemd unit with Landlock, syscall filter, private namespaces and a cleared
environment. Limits: 1,200 s, 24 GiB, 200 files, 16 MiB. nanoda available but disabled.

**Measured** [M]. The 341-cycle record checked end to end in 1,516 s on a contended 32-core box,
above the 1,200 s production limit; one 176-line module with four `decide +kernel` proofs over
5,328 positions took 472 s. Record roots are 20–100k lines.

**Bugs that shipped** [V]. (1) `Secure` was vacuous until commit `30e33a7` (2026-09-21) capped
verification cost: a verifier hashing one `2^137`-bit input made every budget `B` give
`B/2^127 ≥ 2`. (2) Decision agreement does not transfer compression counts (a cached oracle lets
the spec query twice and the machine once). (3) Free lookup tables until proved size caps
(`b38f3c5`). (4) `probTrue … = 0` soundness is unsatisfiable once a long statement is bound
through a digest, so the leanISA boundary was idealised and priced at 120 cycles. (5) The
protected-file pin changed 46 times in the first ten days.

**What recursion.fast took.** The harness order and pipeline shape (comparator first in a fresh
tree, the gate, then the badge; the rendered challenge stub; the exact-module allowlist; the
sandbox), the definition-hole discipline ("the certificate pins the hole so completely that any
inhabitant is a legitimate win"), kernel-checked vacuity facts beside the contract (our positive
and negative controls), the never-`= 0` rule (our counting form with an error cap), proved size
caps (v2 `Admissible`, v3 `proofCap` and the image cap), and the expectation of contract churn.

## 2. sig.golf

**Object and score** [V]. Minimise `S × C`: signature bytes times the proved maximum honest
verification cycles. A submission is four RV64IM images (keygen, sign, expand, verify), sizes,
buffer offsets and Lean proofs. Budgets `2^20 / 2^17 / 2^20` compressions, `FAILURE = 2^-128`,
`LIFETIME = 2^32`, 127 security bits, `CYCLE_LIMIT = 2^32`, program bytes ≤ `2^20`.

**Trusted contract** [V]. 712 lines, 412 code: `Parameters`, `Oracle`, `Riscv`, `Programs`,
`Security`, `Statements`. One semantic object, `execute : Image → ℕ → MachineState → OracleComp
HashSpec Execution`, read three ways: against a lazy random oracle (completeness), against an
arbitrary fixed hash (worst-case cost and termination), inside a counted oracle (security). The
`Certificate` has six fields: `admission` (decidable), `completeness` (≥ `1 − 2^-128` for every
key and all `2^256` messages simultaneously), `compressionBudgets` (exponential moments
`E[2^(N/B)] ≤ 2`, which permit grinding while bounding tails), `verificationCycles` (every
successful honest run under every fixed oracle), `security` (`Pr[won ∧ calls ≤ Q] ≤ Q/2^127`),
`termination` (fewer than `2^32` cycles on all typed inputs). HASH is an oracle query in the free
monad, 8 cycles per 64-byte block; MUL/DIV/REM cost 4, everything else 1; witness bytes are
charged `⌈W/256⌉`. The contract decodes the W-ops itself because the upstream decoder modelled two
of ten.

**Pipeline and limits** [V]. Source policy (file and byte caps, allowlisted imports, no
`prelude`/`module`), challenge generated from `claim.json`, trusted `.lake` cloned by reflink with
candidate artifacts purged, comparator under systemd + Landlock + seccomp, **two CPUs**, 24 GiB,
4 h. Score computed by Python from the claim, re-checked by the runner.

**Image extraction was removed** [V]. Commit `bb5ae34` (2026-09-29, "Stop extracting and recording
the images"): the verifier had evaluated the four images with `#eval` and published digests, which
"runs the candidate's compiled Lean, which the candidate controls: `implemented_by`, an `#eval`
override, or files written during the build". This is the precedent for our open item O-12 (badge
executables regenerated from kernel terms).

**The accepted submission** [V, M]. SPHINCS+ with PORS+FP, `S = 6061`, `C = 11,712`: 958 files,
154,526 lines, near the caps; 59 % abstract security in VCVio, 22 % RISC-V refinement by a custom
verified symbolic executor certified by `Eq.refl` (never `native_decide`), 10 % generated image
literals, 1 % a 1.8k-line transfer from an older contract. The verify image has 145,952
instructions, half NOP padding: code size is free up to the cap so agents spend it on unrolling.
Build 16 min 07 s on 32 cores (2.83 CPU-hours), comparator replay a further 23 min 25 s; about
1.7–1.9 h of the 4 h budget on two CPUs.

**Documentation worth copying** [V]. `RULES.md` links every Lean statement by line range and lists
known limitations as flat bullets with real-world consequences; `site/llms.txt` has a
"Consequences that bite" section, each item one that cost a real submission. recursion.fast should
ship the equivalent for v3 before launch (every proof byte must be checked; the statement digest
binds the children; termination on adversarial proofs; the root check must fit the succinctness
cap; …).

**What recursion.fast took.** The `Certificate` as one `Prop` structure with one field per
obligation; the RISC-V machine shape with explicit prices (v0.3, now only for the extractor);
proved worst-case cost statements over all fixed oracles (v0.3 cost theorems; v3 replaces them by
measured wall time plus a measured succinctness cap); the "advice, not information" view of
untrusted inputs (our proof bytes); the image-extraction lesson (O-12); the contract-freeze
lesson. Not taken: exponential-moment prover budgets (v3 measures the prover instead).

## 3. The Proximity Prize (better.codes)

**Object and score** [V]. The protocol is fixed; only a number is contested. Lower track: prove the
combination-round error `certifiedGammaError(δ) ≤ 2^-128` at radius `P/Q` and claim `B` with
`(1−δ)^128 ≤ 2^-B/100`. Upper track: prove the winning-set density `> 2^-128` on the whole suffix
`[δ*, δ_C)`, which avoids assuming an unproved monotonicity lemma. The README says the score "is
not a full-protocol security claim". Instance: KoalaBear `Ext6`, `n = 2^18`, message length
`2^20`, interleaving 8, rate 1/2, 128 spot checks. Bracket after six weeks: safe at δ ≈ 0.3086
(68.15 bits), unsafe from δ ≈ 0.4668 (116.13 bits).

**Trusted contract** [V]. Three files, 290 lines, about 30 lines of scored statements; each claim is
a `structure … : Prop` with named fields `admissible`, `reduction`/`unsafeAbove`, `score`; scalars
are rendered from strictly parsed text files into the challenge type. Unchanged for six weeks and
about 125 validated submissions. All game semantics sits in ArkLib behind one bridge theorem
(certified error ⇒ knowledge soundness of a named, executable straight-line extractor) that the
organisers audited once. An executability gate (`assert_toy_ir`) in the trusted import closure
fails the build if the encoder, decoders, extractors, prover or verifier stop being executable.

**Pipeline and limits** [V]. Textual audit after stripping comments and strings: rejects
module-system headers, `run_cmd`, `#eval`, `elab`, `macro`, `addDecl`, `implemented_by`,
`extern`, …; comparator patched to replace its fresh-environment replay by a sandboxed
`leanchecker`, because CompPoly's kernel-checked `Ext6` irreducibility certificate in the trusted
cone could not be replayed; axiom audit of 13 protected declarations and a module-prefix
allowlist; the authoritative verifier is a remote service, the repository holds a local replica.
Limits: 4 h, 24 GiB, 4 vCPU, 1,000 files, 16 MiB. ArkLib at the pin has 263 `sorry` tokens in 82
files, harmless because the candidate's axiom closure is checked.

**Measured** [M]. Trusted import closure 5,398 modules, 495,846 constants, about 4 GB and 9 s to
load per process; setup 615 s on 32 shared cores; baselines check in 15 s and 33 s; the current
lower submission (153 files, 14.7 MB, about 13k `decide` uses) had not finished after 50 min.
Agent-optimised submissions grow to the resource ceilings.

**What recursion.fast took.** Scalars as parameters of the theorem statement, rendered by the
harness, never computed by trusted code (our claim JSON and renderer); naming the executable
object in the theorem type (v3's `KS` names the extractor `E`, and the image must compute it);
"axiom closure, not sorry-freeness of dependencies" (our allowlist plus audit); the heavy-certificate
lesson (v3 keeps `BF64`'s Rabin certificate in the untrusted library and off the trusted cone);
the warning about `ENNReal.toNNReal` and `toNat` sending `∞` to `0` (our counting form uses
`Nat.card` over a finite type and has no such truncation); resource ceilings as first-class rules
with a performance guide for agents.

## 4. leanerVM

Not a competition, but the neighbour whose conventions we follow most. Layers Parameters →
Semantics → Arithmetization → Protocol with "the wall" (the protocol layer imports nothing from the
arithmetisation beyond an allowlist); two master theorems, `piop_perfectCompleteness` and
`piop_rbrKnowledgeSoundness`, in ArkLib's worst-case-per-prefix form with a named computable
extractor; the non-interactive theorem planned as a ROM statement conditional on named *assumed
interface structures* (`RbrToStateRestoration`, `BcsSecurity`, `ChainFiatShamirSecurity`,
`McaJohnson`), never axioms; recursion ("Recursive CTE") declared an open problem because the
relation itself queries the oracle [V]. Its kernel axiom audit rejects `sorryAx` anywhere, so no
admitted ArkLib theorem can be depended on. Its roadmap issue #12 is the template of our issue #1,
and its `protocol-blueprint.md` / `protocol-status.md` split is the template of our design and
RESULT documents.

**What recursion.fast took.** The trust policy (standard three axioms over everything, assumed
interfaces as explicit arguments if ever needed, never a bridging axiom); the hole interfaces and
refutation lemmas as negative controls; the honesty about recursion (v3 §5.4 states the one-level
theorem and the tree heuristic); the field (`BF64` and `Ext3` are leanerVM's pins too); the
tracker style.

---

## 5. The lessons, and where v3 answers them

The report's table of lessons (§4.5), updated for the v3 design **as of `DESIGN-v3.md` of
2026-10-19**. The section numbers in the "v3 answer" column (§2.2, §4.2, §4.5, §6.5, §7.4, …) are
that file's, on branch `v3/contract-archive`, not the compiled design's
([`docs/v3-design-agent-written-ROM-SNARK-verifier-for-BLAKE2s-hash-chain-trees-with-Lean-certified-knowledge-soundness.md`](../v3-design-agent-written-ROM-SNARK-verifier-for-BLAKE2s-hash-chain-trees-with-Lean-certified-knowledge-soundness.md)).
Several rows describe v3 before its amendments and are superseded there: rows (1), (2) and (10)
describe the counting form over `Nat.card`, replaced by the potential form with `logCap`
(V3-KS-A1, A2; compiled design §6.1); row (9)'s "accept-all admits no `KState`" was withdrawn
(V3-S1-A13; §6.2); the completeness row's `Complete` is now `CompleteWithError` with
`δ ≤ 2^-128` (V3-S2R-A2; §6.4); row (4)'s "image cap" became the program cap `progCap`
(V3-S2R-A1; §6.5). The table is kept as the 2026-10-19 record.

| Lesson (source) | v2 answer | v3 answer |
|---|---|---|
| (1) Concrete bounds that count honest work become vacuous without caps (ots.golf `30e33a7`) | information-theoretic RBR definition, no query budget | counting form over logs, no budget; `qV` declared and charged in the paper bound only (§4.5) |
| (2) "`= 0`" soundness with hashing is unsatisfiable (ots.golf leanISA) | RBR-KS with a per-round error cap | per-fresh-query error cap `errorCap`, counting form (§4.2) |
| (3) Decision agreement does not transfer costs (ots.golf) | costs read off the machine; `Agrees` decision-only | verifier cost priced through the node's proving time; succinctness a measured admission cap (§6.5) |
| (4) Free lookup tables (ots.golf `b38f3c5`, sig.golf's 57 % image) | proved caps on image, key, tape, oracle lengths | `proofCap`, image cap, `qV`; no relation caps because there is no relation class (§2.2) |
| (5) Candidate code on the trust path (sig.golf `bb5ae34`) | image literal rendered into the challenge; O-12 open | unchanged; O-12 required before board T opens |
| (6) Heavy certificates break replay (Proximity Prize) | `K` restated in 24 core-only lines; Rabin certificate in the library | no field in the contract; `BF64` with its certificate in the untrusted library (§7.4) |
| (7) Sorried instances in dependencies (ots.golf, Clean's BN254 `Fact`) | exact-module allowlist, axiom audit | unchanged; allowlist gains CompPoly's `BF64` modules |
| (8) Statement rewriting by agents (swarm case study) | comparator against a trusted challenge | unchanged |
| (9) Vacuous theorems (SP1 audit; ArkLib's own extractor-in-`OptionT` bug) | positive and negative controls per trusted definition | unchanged; accept-all admits no `KState`, reject-all fails `Complete` (§4.2) |
| (10) Library-level traps: truncation, declared errors | finite nonempty challenge types, numeral caps, contract-fixed ε | `Nat.card` over `Digest`, no `ENNReal`; `errorCap` contract-fixed |
| Completeness blocks trivial wins (zk.golf) | perfect completeness per certificate | `Complete` required, proved for the Lean prover (V3-4) |
| Definition holes are gameable (comparator's own warning) | the certificate pins the hole | unchanged: `Certificate S` is about the submitted `S` |
| (11) Churn and check time (ots.golf's 46 pin changes; sig.golf's 1.8k-line transfer) | freeze before launch; record porting | unchanged; plus the v2 → v3 move itself is the first "port" |
| Proof-checking time is the binding constraint (all three) | budgets 3 h / 8 CPUs / 48 GiB from measurements | unchanged; the trusted base is smaller, agents' proofs are not |

## 6. What to re-check when tweaking rules or the baseline

Questions to ask of any change, with the neighbour that taught each.

1. **Does a new cap, budget or error term count honest work?** If so, every honest party needs its
   own cap or the statement can be vacuous (ots.golf `30e33a7`).
2. **Can the statement be satisfied by a verifier that accepts nothing, or a prover that never
   finishes?** Keep a positive and a negative control for every trusted definition, and keep
   completeness mandatory (zk.golf, ots.golf's `Admissible.correct`, our `Controls/`).
3. **Is any number computed by trusted code?** It should be a parameter of the theorem rendered
   from a strictly parsed claim (Proximity Prize, sig.golf).
4. **Does anything on the badge path run candidate-controlled code?** sig.golf removed exactly
   that; our O-12 closes it. Never add an `#eval` of a submission object to the harness.
5. **Does a new dependency bring a heavy certificate or a sorried instance into the trusted
   cone?** Replay it under the unpatched comparator in CI, and allowlist by exact module
   (Proximity Prize, ots.golf).
6. **Is a new size free?** Proof bytes, image bytes, query counts, log sizes: cap what the score
   cannot see (ots.golf's lookup tables, sig.golf's NOP padding, leanISA's `seeded_rows`).
7. **Does the change alter what a record means?** Then it is a contract change: re-pin the
   protected files, port or revalidate standing records, and expect churn after launch
   (ots.golf re-pinned 46 times in its first ten days; its `record-revalidations.json`).
8. **Will agents' proofs fit the check-time budget?** Agent-optimised submissions grow to every
   ceiling: files, bytes, `decide` tables, memory per module. Measure the baseline cold and warm
   after every harness change (all three; our CI step timings).
9. **Is the new rule explained where agents read?** sig.golf's "Consequences that bite" and
   ots.golf's `AGENTS.md` are the models; our submitter-facing guide is open item O-8's sibling.
10. **For the baseline specifically:** it must be certified, listed and excluded by a rule the
    design states (v3: the succinctness cap, §7.3), small enough to check in minutes, and it
    should exercise every harness path, including the liveness check of the extractor. Keep it
    trivial; the neighbours' winners are 100k-line proofs and the baseline is not where that
    effort belongs.
