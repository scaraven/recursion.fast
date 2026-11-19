# Assurance review of the trusted contract and its harness (November 2026)

This report collects six independent adversarial reviews of the recursion.fast core's trusted
contract and of the harness code that runs it, a mutation test of the contract, the fixes made in
response, and what is left open. It is written for a reader who knows what a SNARK, a hash function
and a test harness are, but not Lean.

## 1. Scope

**Commit.** The reviews read commit `2287bb1` (rules v6, pull request scaraven/recursion.fast#30).
The fixes are on the branch `v6/contract-assurance`, on top of `ffe5531` (the pushed head of #30):
the mutation testing (`b018ee8`, `8f1c347`), then this pass: `4c72602` (the badge's isolation from the
entry, external timing, regression fixtures), `c00a2ca` (new controls, known answers and tests) and the
commit that adds this report (documentation; every change to a contract file in it is a comment).

**The trusted contract** is the ten Lean files under `RecursionFast/Contract/`, 335 lines of code
(`scripts/loc.py`; CI caps it at 500). Nothing proves that they say what their comments say; every
record of the competition is a kernel-checked theorem about them. In reading order:

| file | what it defines |
|---|---|
| `Contract.lean` | the import list |
| `Hash/Keccak.lean` | Keccak-256 (FIPS 202 permutation, Ethereum's padding) |
| `Relation.lean` | the relation: a leaf statement (the XOR of `n ≤ 2^22` hashes of a seed) and a node statement (two children whose signed proofs `acc` accepts); byte layouts and domain tags |
| `Signature.lean` | the trace digest and the signature check `SigOk` (Winternitz one-time signatures under a height-16 Merkle tree) |
| `Oracle.lean` | query programs (`OProg`): how a verifier asks the oracle; `runSeq` (answers from a trace) and `runLog` (answers from a log) |
| `Security.lean` | the lazily sampled random oracle `prob`, knowledge soundness `KS`, completeness with error, and the caps `2^-128`, `2^-40`, `2^96` |
| `Machine.lean` | the extractor's machine: a step-counting 64-bit word language |
| `Extractor.lean` | the extractor's input tape and output format, its domain, its step budget and size caps (`Computes`) |
| `Tree.lean` | the stream's statement (what the runner computes) and a tree root (used by the library only) |
| `Certificate.lean` | a submission, its acceptance predicate `acc`, and the certificate an entry must prove |

**The harness trust boundary**, as far as it touches the contract: the badge executable `verify`
(the compiled `acc`, the file and hex parsers, the timer), the gate (`harness/lean-tools/Gate.lean`),
the source rule (`scripts/source-rule.py`), the olean manifest, `harness/evaluate.py`'s certificate
job, and the runner's checks (`harness/rfh/checks.py`, `harness/rfh/bench.py`).

## 2. Method

**Six reviewers.** Six agents, each given one slice of the contract and the instruction to break it
(find a definition that does not mean what its comment says, a certifiable entry that should not be,
a check that does not happen), wrote probes in Lean and Python against the real build and reported
findings ranked by severity, with what they checked and found correct. None saw another's report.

| reviewer | scope |
|---|---|
| R1 | `Oracle.lean`, `Security.lean`: the random oracle, `KS`, completeness, the caps |
| R2 | `Certificate.lean` and how the harness consumes it: the comparator binding, the gate, the badge |
| R3 | `Hash/Keccak.lean`, `Relation.lean`, `Tree.lean`: fidelity to FIPS 202 and the runner, encodings |
| R4 | `Signature.lean`: WOTS and Merkle against the service (Rust) and the reference signer |
| R5 | `Machine.lean`, `Extractor.lean`: the step-counted extractor and its encoding |
| R6 | the whole contract and its deployment, as a red team: can a certified, accepted entry cheat? |

**Mutation testing.** 98 mutants (99 after this pass), each one small change of a contract definition (a dropped
conjunct, a swapped argument, a cap off by one power of two, a wrong tag, an equivalent rewrite as a
calibration), applied in scratch copies. A mutant is *killed* when some organiser check fails on it:
the build of the library's proofs and of the controls (kernel-checked theorems that pin each
definition with positive and negative examples and known answers), or, optionally, the core CI's
tests of compiled contract code. Result at `8f1c347`: **95 killed, 2 invalid** (the change does not compile: a
31-byte Keccak output, a loop that consumes no fuel), **1 survivor**, a docstring-only change
(equivalent). The first run left five meaningful mutants alive and three killed only incidentally;
the controls added in `b018ee8` kill each of them on its own (`tests/mutation/targeted.md`). In
this pass one more mutant, `ext-progcap-2^21` (the program-size cap doubled), is killed by the new
lookup-table control on its own (section 4); the full rerun on the final tree, with every comment
change of this pass, gives **96 killed, 2 invalid, 1 accepted survivor** of 99. Details and how to
rerun:
[`tests/mutation/README.md`](../../tests/mutation/README.md) (about 30 minutes with 3 jobs on 16
cores: `python3 -I tests/mutation/run.py`), results in
[`tests/mutation/results.md`](../../tests/mutation/results.md).

## 3. Verdict per file

No reviewer found a wrong contract **definition**. Every contract change in this pass is to a
comment. The one high-severity defect was in the harness around the contract (R2 HIGH-1), and is
fixed.

| file | verdict |
|---|---|
| `Hash/Keccak.lean` | Faithful to FIPS 202 (constants re-derived independently; agrees with OpenSSL on 426 lengths through the Lean interpreter and with the Python and Rust twins). One stale comment (R3 LOW-1). Known answers added at 271, 273 and 408 bytes. |
| `Relation.lean` | Encodings domain-separated (seven distinct tags) and injective on every input hashed; `streamStmt` matches the runner. Comment nits; known answers added for the season's `n = 2^22`. |
| `Signature.lean` | A correct and complete WOTS (`w = 4`, 133 chains) plus height-16 Merkle check, byte-identical to the service and the reference signer. One comment nit; test coverage of high key indices added (R4 L2). |
| `Oracle.lean` | `runSeq` consumes the trace exactly; `prob` is a correct lazily sampled random oracle (normalisation, consistency and independence proved in probes). No finding. |
| `Security.lean` | `KS` is straight-line, adaptive knowledge soundness with the documented deviation (the extractor reads the verifier's answers, as in ArkLib). Comments overstated or omitted three things (R1 L1, N1–N3), corrected. |
| `Machine.lean` | A sound unit-cost word RAM; fuel is a real step bound. One comment nit (`divu` by zero). |
| `Extractor.lean` | `Computes` binds the same extractor `KS` uses, on the same log; the tape is injective on the domain (now a control). The program-size cap is load-bearing and now has its rationale and a control (R5 LOW-1); one false sentence corrected (R5 LOW-2). |
| `Tree.lean` | Correct; the tree root does not commit to the number of leaves, which is harmless where it is used (now said). |
| `Certificate.lean` | All five conjuncts of `acc` present and ordered cheapest first; the caps and the declared numbers bind as intended; degenerate verifiers (accept-all, reject-all, brute-force extractors) are excluded. Comments on the completeness gap and on running the extractor corrected. |
| `Contract.lean` | Import list only. |

## 4. Findings and resolutions

Severity is the reviewer's. "Docs" is the commit that adds this report. A finding marked *by design*
or *recorded* is explained, not changed.

### High

| id | finding | resolution |
|---|---|---|
| R2 HIGH-1 | The badge's glue (file parser, hex parser, timer) was elaborated in a module that imported the entry's solution, so a high-priority `instance` declared by the entry (`HSub Nat Nat Nat`, `HOr UInt64`, `GetElem?` on `Array Char`) silently replaced the arithmetic in it. A 2-second check could report 1 ns, so a verifier the 128 ms cap must reject would pass it; the parser and the statement/key hex could be redirected too. No check saw it (the comparator compares only the certificate's closure; the gate's rules do not cover plain instances). | Fixed in `4c72602`: the glue moved to `RecursionFast/Badge.lean`, compiled with the organiser's package before any entry exists and hashed in the olean manifest; the per-entry module only passes `submission` to it; the runner times each check from outside the process and judges the cap on the larger time; a hostile fixture proves it (section 5). |
| A1 (found while fixing HIGH-1) | The same module was also exposed to the entry's **notation**, which the source rule allows: `notation "RFBadge.main" => fakeMain` turns the text `RFBadge.main` into another function in every module that imports the entry. Against the old badge an entry could have replaced its whole check by an accept-all one. | Fixed in `4c72602`: gate rule 9 (`--wiring`) checks after the badge build that the per-entry module declares `main` alone, whose elaborated value is exactly `RFBadge.main RecursionFast.Challenge.submission`; a gate fixture (`tests/gate/GateWiringHijack.lean`) is rejected for it. |
| R6 HIGH | The badge executes compiled code, not the kernel-checked term. A known route (`tests/source-rule/forge/ForgeRaw.lean`: a metaprogram run at elaboration time rewrites the compiler's data through `persistentEnvExtensionsRef` and `unsafeCast`) passes the gate; only the lexical source rule stops it, and a compiler bug would have the same effect. Impact if exploited: an accept-all badge. | Recorded, not fixed here: the main open item (section 6). |

### Low, nits and observations

| id | sev. | finding | resolution |
|---|---|---|---|
| R1 L1 | low | The completeness game fixes the witness before drawing the oracle, but in the stream a node's witness carries its children's traces from the same oracle; the comments put the whole model-to-deployment gap on the keyed instantiation. | Docs: `Security.lean` and `Certificate.lean` now name this gap. |
| R1 N1 | nit | Completeness is about `V` alone, not `acc` (its size, trace-length and signature conjuncts are not in the game). | Docs: one sentence in `Security.lean`. |
| R1 N2 | nit | The "lucky" verifier is knowledge-sound at error 0, not certified (it has no complete prover). | Docs: `Security.lean`. |
| R1 N3 | nit | "The prover asked the service for every answer": `SIGN` computes the answers itself; what is normalised is the whole run (prover plus the service's evaluations). | Docs: `Security.lean`, AGENTS.md §12. |
| R2 LOW-2 | low | The signature covers the trace digest only, not the statement; statement binding rests on `V` (and `KS`), with the canaries as the runtime check. | By design (AGENTS.md §4); the canaries' hex parsing is now outside the entry's reach (HIGH-1). |
| R2 LOW-3 | low | `acc` may hash a trace of up to `2^36` bytes before running `V`; the guards before it bound that size, in the right order. | By design; documented in AGENTS.md §12 ("`acc` has no time bound"). |
| R3 LOW-1 | low | `Hash/Keccak.lean` still called its use "the chain step" (v5). | Docs. |
| R3 LOW-2 | low | No Lean known answer at 271 bytes (the only case of the padding byte `0x81` in a second block), 273, 408; none of `enc64` beyond its first byte (the season's `n = 2^22`). | `c00a2ca`: `len271_kat`, `len273_kat`, `len408_kat` (Keccak); `itemBig_kat` (`leafItem` at index `0x123456`), `leafStmt_season_kat` (`n = 2^22`), `enc64_season`, `enc64_kat`; each with its `python3 -I` command, values also checked with OpenSSL. The 1000-byte answer is left out (95 s in the kernel). |
| R3 OBS-1 | obs. | At `n = 0` the leaf statement is the same for every seed. | Docs (`Relation.lean`) and the control `leafStmt_zero_seed`; the runner requires `1 ≤ n` (`bench.py`'s shape check). Not a contract change. |
| R3 OBS-2 | obs. | `treeRoot` does not commit to its number of leaves; the title called it a specification of the runner, which computes no tree root. | Docs (`Tree.lean`): retitled, the convention's consequence stated. |
| R3 NIT-1 | nit | `Tree.lean` hard-coded `M = 8`, a season constant. | Docs: points to `harness/season.toml`. |
| R3 NIT-2 | nit | `service/src/keccak.rs` and `service/Cargo.toml` still spoke of the chain step and the chain hasher. | Docs. |
| R3 NIT-3, NIT-4 | nit | "`Rel` decides `n ≤ leafCap` first" (a `Prop` decides nothing); a stray line break and a chain of colons. | Docs. |
| R4 L1 | low | The EUF-CMA reduction's hypothesis asked for pairwise distinct indices, while replay mode re-issues a signature at the same index. | Resolved in `ffe5531` (before this pass): the hypothesis is a functional record, one message per index, replays allowed (`Transcript.oneMsg`). |
| R4 L2 | low | The Lean-signer cross-check covered indices 0 and 1 only; the exhaustion test did not check that the `2^16` indices are distinct. | `c00a2ca`: index `0xFFFF` (every path bit set) cross-checked against the Lean signer; the exhaustion test asserts the indices are exactly `0 … 2^16 − 1`. |
| R4 N1 | nit | "The digest of the whole trace it answered": the service signs one request's trace. | Docs (`Signature.lean`). |
| R4 N2 | nit | The CI step around the Lean-signer test had a thin margin (83 s of 120 s). | `c00a2ca`: 300 s (the test now also signs `2^16` times). |
| R4 N3 | obs. | Tree nodes and messages are not tweaked: the tree's security is collision resistance, which is what the reduction states. | By design; recorded. |
| R5 LOW-1 | low | The program-size cap `progCap` is the only barrier against lookup-table extractors (a short Lean term can denote an exponentially large decision tree), with no rationale and no control. | Docs (`Extractor.lean`) and `c00a2ca`: `table_run` (a `k`-level decision tree computes any function of the low `k` bits of a tape word in `7k + 13` steps), `table_size` (`10 · 2^k − 1` statements), `table_over_progCap` (over the cap from `k = 17`), `table16_fits`; the new mutant `ext-progcap-2^21` shows the controls pin the cap's value. |
| R5 LOW-2 | low | A false sentence: two children near the file cap "do not fit". They may not; with word-aligned fields they fit up to 36 bytes below the cap. | Docs (`Extractor.lean`, AGENTS.md §4). |
| R5 LOW-3 | low | The limitation text omitted two exits from the extractor's domain (a query of `2^64` bytes, a tape over `2^64` words). | Docs (AGENTS.md §12). |
| R5 NIT-1 | nit | "The harness may run the program": no evaluation runs the extractor. | Docs (`Certificate.lean`). |
| R5 NIT-2 | nit | "One instruction" is not exact for `divu` by zero. | Docs (`Machine.lean`). |
| R5 NIT-3 | nit | AGENTS.md line anchors had drifted. | Docs: every anchor re-checked against its declaration. |
| R5 NIT-4 | nit | Stale control comments ("start/length", "21 statements" where the size is 28). | `c00a2ca`, with the control `ws_size` (28 statements). |
| R5 NIT-5 | nit | No control for the tape's injectivity. | `c00a2ca`: `extractorInput_inj` (with `readTape_run`). |
| R5 obs. | obs. | Memory beyond cell `2^64` is unreachable by address, a burden only on honest extractors of absurd tapes. | Recorded. |
| R6 L2 | low | AGENTS.md §6 said nothing key-dependent can run in the untimed start-up; `vk.hex` is in `/work` then. | Docs: the start-up sees `vk` and may do any work that depends on nothing else. |
| R6 L3 | low | The runner's warm read of `/setup` charges those pages to its own memory cgroup, so read-only setup data sits outside the prover's 8 GiB. | Docs (AGENTS.md §9, `warm_caches`): not fixed, since charging the request would mean evicting and re-reading up to 4 GiB from disk before every request. |
| R6 L4 | low | "A trace is within `v_cap`" is false for intermediate outputs of the track `final`, which are not V-capped. | Docs (AGENTS.md §12). |
| R6 nit | nit | A `SIGN` body is capped at 16 MiB, below the `2^36` bytes of trace `acc` admits. | Docs (`Certificate.lean`, AGENTS.md §12). |
| R6 nit | nit | AGENTS.md anchors (as R5 NIT-3). | Docs. |

## 5. The badge fix in detail (R2 HIGH-1, A1)

**Before.** `harness/evaluate.py` rendered two Lean modules into the entry's build tree. The first
imported the entry's `Solution` module and then defined the parser, the hex reader and `check`; the
second defined the timer and `main`. Lean resolves type-class instances (which `+`, `-`, `|||` and
`a[i]!` mean for a given type) and notation where a definition is *elaborated*, and an `import`
brings every instance and notation of the imported module into scope. So the entry's declarations
decided what the badge's own arithmetic meant. Confirmed: with an entry-declared `HSub Nat Nat Nat`,
the old badge reported a 230 ms check as `accept 1` (1 ns); with an `HOr UInt64` and a `GetElem?`
instance as well, it rejected a valid proof (the key read as zeros, the length word 7 as 1000).

**After.**

1. *What moved where.* Everything the badge does around the check (`u64At`, `digestAt`,
   `parseSigned`, `hexVal`, `parseHex32`, `check`, `timedCheck`, `runLine`, the new `serve` loop and
   `main`) is in [`RecursionFast/Badge.lean`](../../RecursionFast/Badge.lean) (moved from
   `harness/badge/Common.lean.in`). It imports only the organiser's `RecursionFast.Library.Fast`,
   is built by `lake build` and `harness/org-setup.sh` before any entry exists, and its `.olean` is
   in the olean manifest, which the certificate job checks before and after the badge build. The
   per-entry module [`harness/badge/Verify.lean.in`](../../harness/badge/Verify.lean.in) is now one
   definition: `def main : List String → IO UInt32 := RFBadge.main
   RecursionFast.Challenge.submission`. `RFBadge.main` takes the submission as an ordinary argument
   and has no instance argument, so nothing is resolved in the per-entry module. Lean's compiler may
   inline or specialise the glue there, but it does so on the compiled code stored with the glue,
   never by elaborating it again.
2. *Notation.* The per-entry module is still elaborated with the entry in scope, so its text could
   be redirected (A1). Gate rule 9 (`gate --wiring`, run by `evaluate.py` after the badge build, in
   the sandbox) reads the built module's environment, not its text, and rejects unless it declares
   `main` alone, `main`'s value is exactly the constant application above, `main` has compiled code,
   no code-substituting attribute is registered, and the glue's module is trusted by its hash.
3. *External timing.* The runner now drives the badge in a request-response mode (`verify
   --serve`): it writes one request line, waits for the answer line, and only then writes the next.
   It times each request on its own clock, outside the badge's process, and judges `v_cap` on the
   larger of that time and the badge's self-reported time. The external time includes the pipe
   round trip, reading the file and parsing the hex: measured 0.3 ms for a 5 KB file and 3.6 to
   5.7 ms for a 9.2 MB one, against a 128 ms cap. An answer that arrives before its request is a
   crash. The verifier is not scored, so this changes no score.
4. *Fixtures.* `tests/harness/accprobe/` builds the real badge around a hostile submission
   (`HostileSub.lean`: a 0.2 s verifier plus the three instances above) and checks through the
   runner's own request loop that the proof is accepted with a self-reported time above 50 ms,
   rejected for a flipped statement and when one byte longer, and that rule 9 passes. Against the
   old templates this fixture fails (the valid proof is rejected; with the `HSub` instance alone the
   time reads 1 ns). `tests/gate/check.sh` renders the template around an honest module (PASS),
   around one whose notation redirects `RFBadge.main` (REJECT), and with one extra declaration
   (REJECT). Both run in the core CI.
5. *Not adopted:* rejecting entry-declared instances of classes the entry does not define (orphan
   instances). After the isolation they can change only the entry's own code, which is the verifier
   the kernel checked; and the rule would reject common, harmless declarations such as
   `instance : Fact (Nat.Prime p)`.

## 6. Open items

1. **The badge runs compiled code, not the kernel's term (R6 HIGH).** The certificate is a theorem
   about Lean terms; the badge runs the machine code Lean's compiler produced from them, linked
   with the entry's compiled modules. Anything that makes the two differ makes `acc` as run differ
   from `acc` as certified: the raw forgery route (`ForgeRaw.lean`, which passes the gate; the
   lexical source rule is the only barrier, and it is a word list, not a proof), a bug in Lean's
   compiler or runtime, or a route not yet known. If exploited, the impact is total: an accept-all
   verifier with a valid certificate. *Recommended follow-up:* build the executed verifier from
   kernel terms, without linking the entry's compiled objects (export the certified `submission`'s
   term, as the comparator already does, and compile or interpret it in a trusted process); or
   check `V` a second way on every judged output and canary, for example by evaluating the kernel
   term of `acc` in a trusted evaluator and requiring both verdicts to agree.
2. **Everything recorded as by design** in section 4 (R2 LOW-2/LOW-3, R3 OBS-1/OBS-2, R4 N3, R5's
   memory observation, R6 L3): each is stated in AGENTS.md or the contract's comments.

## 7. Residual trust surface after this pass

What a record still rests on, beyond the kernel-checked theorem:

- **The contract's meaning**: ten files, 335 lines of code, read by six reviewers and pinned by the
  controls and the mutation test, but not proved to mean what their comments say.
- **One kernel**: Lean v4.34.1's, through the comparator; Lean core, Mathlib and the pinned packages
  as hashed in the olean manifest.
- **The compiler and runtime** for everything the badge runs (open item 1), including the
  organiser's executable code: the glue (`RecursionFast/Badge.lean`) and the word-level `accF`
  (`RecursionFast/Library/Fast.lean`, proved equal to `acc` in the kernel; its compiled code is
  trusted to match).
- **The gate and the source rule**, which keep compiler-changing code out of entries (rules 3, 6,
  7, 8, 9 and the word list); the source rule is lexical.
- **The runner** (sandbox, statements, canaries, the two clocks), **the service** (keys, signatures,
  replay), and **the machine**; all tested, none proved.
- **Cryptographic assumptions**: Keccak-256 collision resistance and PRF security, and the WOTS
  chain's one-wayness; the probability bounds of the stream's composition outcomes are on paper.
