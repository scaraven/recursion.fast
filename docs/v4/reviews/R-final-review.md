# RF: final adversarial review of the v4 pull request (`v4/srom-rules` at `81e1ebf`)

Reviewer: Fable, final pass before the PR against `main`. Read: `docs/DESIGN-v4-srom.md`,
`docs/v4/BRIEF.md`, the stage RESULTs, the reviews C, RA, RB (GA/GB skimmed), `FIXLIST.md`, the
trusted Lean under `RecursionFast/Contract/` in full, the Library and Controls the design cites
(`Compose`, `Trace`, `SigTrust`, `Signer.sigOk_sign`, `PaperTheorem.paper`, `Fast.accF_eq`,
`Controls/{Backdoor,Certificate,Compose,Relation}`), the whole runner (`harness/evaluate.py`,
`run-benchmark.py`, `aggregate.py`, `rfh/*`, the badge templates, `FORMAT.md`, `PROVER.md`,
`season.toml`, `smoke.toml`), the service protocol and (through a delegated read) its Rust
source, `scripts/{source-rule.py,olean-manifest.py,bwrap-landrun.sh,loc.py}`, the gate's rule
list, both workflows and the caller template, `README.md`, `CLAUDE.md`, `docs/README.md`, and the
baseline team's `F3-harness-RESULT.md` §5. Method: `adversarial-review` (specification, fidelity
and hygiene passes run separately) and `lean4:review`. CI run `39952420263` was watched to its end.
Nothing was built; one local assembly of the toy prover (scratchpad) to confirm RF-M2.

## 0. Verdict

**Not yet ready to open as the PR that claims what §2.7 claims. Three majors, all fixable on the
branch without touching a trusted Lean line.** The contract and the Library say what the design
says (RA's verdict stands after the fix pass; I re-read every quoted block and statement and
found no new gap). The two soundness defects are in the *deployment*, not the certificate:
the attested verdict is computed from whichever benchmark jobs happened to finish (RF-M1), and
the trusted machine cannot build the organiser's own honest assembly prover, so no end-to-end
run has ever happened on it and the branch's CI is red (RF-M2). The third major is that the
normative document and the fix queue misstate what is open (RF-M3). The minors are mostly
clarity for the three audiences and small honest-harm biases in the measurement.

## 1. Majors (fix before the PR)

### RF-M1. `aggregate.py` accepts a result assembled from whichever benchmark jobs finished; a job an entry can push past the 6 h limit drops the DoS column and the liveness check from the verdict

**Evidence.** `.github/workflows/evaluate.yml`: the benchmark matrix has `fail-fast: false`
(RB-M1's fix), a part whose `run-benchmark.py` writes no JSON exits 1 **without uploading an
artifact**, and the `attest` job runs on `if: always() && needs.certificate.result == 'success'`,
downloading `result-*` with `merge-multiple: true`. `harness/aggregate.py` builds the verdict from
`parts = [json.load(open(f)) for f in sorted(a.parts)]` with no notion of how many parts were
expected or which (`calibrate,tree,dos,liveness` is job 0 only): `verdict = ACCEPT` when
`cert.status == ok` and every *arriving* part says `pass`. Stage B RESULT §9 records this as the
intent: "RB-m1: `aggregate.py` decides from the parts that arrive."

**The concrete failure.** Job 0 is the only job that runs the DoS column and the extractor
liveness check. In `rfh/bench.py` `dos()` the 1,000 DoS inputs are checked with one
`badge.verify` call whose timeout is `verify_s · n + 60 = 60,060 s`, each item failing only if
it alone exceeds `verify_s = 60 s`; about three quarters of those inputs (kinds 1–3 in
`checks.dos_inputs`) carry the root's genuine trace and signature, so `SigOk` passes and the
entry's own `V` runs on a mutated `π`. A `V` that is fast on well-formed proofs (so the root and
samples pass `T_V`) and spends 30 s on a malformed `π` makes the DoS column take about 6 h,
the job hits GitHub's 360 min limit, job 0 writes no `result-0.json`, and `aggregate.py` returns
**ACCEPT** from jobs 1–5: a ranked record with no DoS column, **no liveness check of the
extractor**, two tree repeats presented as "the median of three", and `comparable = true`. The
same happens without malice when any one job is lost to a runner failure. The design's trust
statement (§2.7) promises "measured `T_tree` and the stream" per the season file and §3.4 lists
liveness and DoS as steps of every evaluation; neither is guaranteed by the code.

**Fix.** (1) Give `aggregate.py` the expected part list (the same JSON the matrix is built from,
passed as an input or derived from `split`), and require for each expected part exactly one JSON
whose `parts` field matches and whose `benchmark` is `pass`; a missing or mismatched part is
`ERROR` (and `comparable = false`), never ACCEPT. (2) Bound the DoS column's total time: a per-item
cap tied to the calibration (for example `10 · T_V`, or `verify_s` at the smoke shape) and a total
budget, with a breach recorded as the entry's `fail` with the slow input kept, which also answers
the baseline's friction F3 §5.13 and the open "crafted-input DoS" item (§4.3) in part. (3) State in
§3.1/§2.7 that a result is a record only when all six parts are present, and add a smoke check
that feeds `aggregate.py` five of six parts and expects `ERROR`.

### RF-M2. The trusted machine cannot assemble the organiser's own honest prover; the branch's CI is red and the end-to-end smoke has never run on a GitHub runner

**Evidence.** Run `39952420263` (the one in progress when this review started) finished
**failure**: `lean` and `service` passed; `harness` failed at "harness smoke with the stand-in
badge" with `FAIL honest toy prover: fail ['prover build: gcc exited with 1']` while the five
broken provers (compiled on the runner from `toy.c`) built and were rejected as expected; the
`smoke` job (the real end-to-end with the compiled `accF` badge) was skipped. The two earlier runs
on the branch (`39940607844`, `39935079265`) are also failures. The cause:
`harness/toy-prover/honest/prover.s` was produced by GCC 15.2 on the development VM
(`.ident "GCC: (Ubuntu 15.2.0-16ubuntu1) 15.2.0"`, line 2147) and contains ten `.base64`
directives (lines 2124–2130), a binutils ≥ 2.43 feature; `ubuntu-24.04` ships binutils 2.42. It
assembles here (binutils 2.46, exit 0) and not there.

**Why it is major.** The rule "the prover is x86-64 assembly built with the runner image's
toolchain" (P4, §3.3, `PROVER.md` §1) is met by nothing on the branch on the machine the rules
name; every end-to-end number in the design (§0 "certified and ACCEPTed end to end at the smoke
shape", §3.6) is from the development VM; the attestation path of §3.1 has never produced an
attestation; and a PR whose CI has never been green claims "CI as the trusted machine". The
baseline team's prover presumably has the same exposure (its `.s` was also produced on the VM).

**Fix.** Regenerate `prover.s` with a toolchain the runner accepts (GCC 13 / binutils 2.42, or
`gcc -S` on the runner in CI and commit the result; `.base64` lines can also be rewritten as
`.byte`), and state in `PROVER.md` §1 and the design §3.3 that the assembly must be accepted by
**the image's `as`**, naming the image's gcc/binutils versions as part of the rules and recording
them (the result already records them). Get `ci.yml` green including the `smoke` job and quote the
run in the design. Say in §0 and §2.8, in one sentence each, that (a) the full evaluation workflow
and its attestation have not run on GitHub and the caller template is not yet installed in the
submissions repository, and (b) until then every end-to-end claim is from the development VM.

### RF-M3. The normative design and the fix queue say work is open that is done, and do not say which commit closed what

**Evidence.** `DESIGN-v4-srom.md` carries seven `TODO(B, fix pass)` markers (lines 636, 652, 785,
845, 1000, 1101, 1108). Of these: §3.5 line 785 "RB-M1 (one timed sample against a best-of-N cap,
with `fail-fast`) is TODO" is **done** (`rfh/bench.py` `check`, `evaluate.yml` `fail-fast:
false`, `tests/harness/test_tv.py`); §3.6 line 845 "Q2 … and Q7 …, both TODO" are **done**
(`harness/org-setup.sh` CompPoly roots; `evaluate.py` step 4 builds `+Challenge +Solution` and
binds the badge's closure); §7.3 line 1101 lists "FIXLIST Q2, Q7–Q10, RB-M1" as the open fix
pass, all closed by `5b2b591`. `docs/v4/FIXLIST.md` says "Each item is closed with the commit that
fixes it" and then leaves Q2, Q7, Q8, Q9, Q10, Q12, Q13, Q14 at "B fix pass" and Q3–Q5, Q15 at
"doc pass" although `88d4566` and `5b2b591` closed them. Stage B RESULT §9 is the only place the
truth is recorded. §3.1's "the second kernel … the result states which kernels ran" is right;
§2.7 item 10 and §3.5 are right. The remaining genuinely open items are: build caps from a runner
measurement (line 636, 1000), the full evaluation on GitHub (line 652, 1108), and Q11.

**Fix.** Delete the stale markers and sentences, keep the three genuinely open ones under one
"not yet done" list in §7.3, and close every FIXLIST row with its commit. The user reads §0 and §7
(the design's own reading path); today §7.3 tells them the harness fix pass is still owed.

## 2. Minors

### Soundness and the trust statement

- **RF-m1. What `gh attestation verify --signer-workflow` binds.** It matches the certificate's
  signer URI by workflow path and `--owner` by source-repository owner; it does **not** check the
  ref the reusable workflow ran at, and the harness commit in the JSON is self-reported from the
  caller's `core_ref` input (`RF_HARNESS_COMMIT`), which the caller passes separately from the
  `uses: …@CORE_COMMIT_SHA` ref. Both are organiser-controlled (any caller must be under
  `scaraven`), so this stays inside trust item 9, but §3.1 should say that a reader checking a
  record also reads the certificate's `job_workflow_ref` and requires it to equal the recorded
  commit; otherwise "the organiser's workflow at the recorded commit" is not what is verified.
- **RF-m2. `T_V` is wall time in a pinned single-threaded process, not CPU time.** `Verify.lean.in`
  `timedCheck` uses `IO.monoNanosNow`; the design says "CPU time" in §3.4 step 4, §3.5 and the C6
  row of §6.1. Wall time of a pinned process bounds CPU time and the cap is measured the same way,
  so this is wording, but the three audiences will read "CPU time" as `clock_gettime(CPUTIME)`.
  Say "wall time of the pinned check (an upper bound on its CPU time), with the cap measured the
  same way".
- **RF-m3. The first item of every `verify --batch` is the coldest, and it is always the root.**
  `Bench.check` puts the root first in a fresh 140 MB process; page-faults and cache misses of the
  first check are charged to the entry's `T_V` sample (RB-M1's re-measure starts another fresh
  process, equally cold). Honest harm only. Warm the process with one untimed check of the same
  file before the timed items, or shuffle the batch.
- **RF-m4. `t_leaf = Σ(M+1 leaves)/M`** (bench.py, stated in §3.5; F3 §5.11): a `1/M` bias in
  the recursion term for no stated reason. Divide by `M + 1`, or say why the extra leaf is charged.
- **RF-m5. Service calibration threads.** `calibrate` uses `os.cpu_count()`; under a CPU affinity
  that is the machine's count, not the job's (F3 §5.11 saw `threads_32` under 16 cores). Use
  `len(os.sched_getaffinity(0))`, as `pinned_core` already does.
- **RF-m6. The DoS column is `T_V`-blind** (F3 §5.13): its worst input is published but not
  bounded below `verify_s`. Folded into RF-M1's fix (2); if not adopted there, at least record
  whether `max_ns` exceeds `T_V`.
- **RF-m7. Failure records lose the measurements** (F3 §5.4, partly fixed by Q13/Q14): when
  `tree_repeat` raises, `rec` (status, seconds, prover log, `T_V` samples) is not attached to the
  result. Attach the partial `rec` to the `Fail` so a rejected run keeps its timings.

### Doc ↔ code (beyond RF-M3)

- **RF-m8. Numbers and sentences in the design that the branch contradicts** (the delegated
  sweep, §4; each with the fix "write what the branch has"):
  - line 330, `acc_changed_answer` "both digests verify only if they collide": the theorem
    (`Controls/Relation.lean:244`) concludes both signatures verify **unconditionally** and the
    digests differ **or** the encodings collide; the sentence inverts it;
  - line 559, trust item 5 "gate rules 3, 6–9": the gate has rules 1–8, rule 9 is gone
    (`Gate.lean:26–28`, "v3's rule 9 … is gone with the frontend");
  - line 753, the canary list omits `trace-query` (RB-m9's fix, `checks.py:124`);
  - lines 955–956: Library "1,780 code lines and 220 theorems", Controls "2,029 lines and 292
    theorems"; `loc.py` gives 1,856 / 233 and 2,089 / 309;
  - lines 971–974 (also 81, 1012): the runtime "about 3,660 code lines … service 1,002 (957 after
    GB), runner 959, sandbox 220, badge mains 133, proof-side order 404 …"; the stage B RESULT §1.1
    it cites says service 963, runner 1,028, sandbox 238, badge mains 135, proof-side 449, **total
    3,559**, and the design's own components sum to 3,580 or 3,625, not 3,660;
  - line 952, "1,264 jobs": the cited log says 1,262;
  - lines 687–688 and the §3.6 memory row: the season files have a third cgroup, `badge = 4G`;
    `check_every`, `checker_runs`, `service_calibration_s`, `setup_s`, `build_s` are in the season
    file and not in the §3.6 table (say the table is a selection, or complete it);
  - lines 1112–1114, and `README.md:45`, `CLAUDE.md:40`, `docs/README.md:75`: the submissions
    branch `v4/flock-baseline` now pins **`81e1ebf`** (its commit d77478d), not `ea2e8ab`; the
    contract is identical between the two, the id is stale;
  - §5's controls table lists `decodeWit_witWords` and `accF_eq` as controls; they are Library
    theorems (`Words.lean:284`, `Fast.lean:200`).
  Everything else the sweep checked matches: the three quoted Lean blocks character for character
  in code, all cited names in the files named, the key statements saying what the sentences say,
  the contract's per-file line table (355, 10 files, no theorem), every constant and byte layout,
  the §3.6 values against both season files, the service caps against `proto.rs`, the six matrix
  parts, the score formulas and the file layout.
- **RF-m9. §3.1 says GitHub's first-time-contributor approval is "compute admission"**: correct,
  but the caller template is a `harness/ci-template/` file with `CORE_COMMIT_SHA` placeholders;
  §3.1's "Evaluation runs only from … the submissions repository's `evaluate-entry.yml`" reads as
  installed. Say it is a template to be installed with the pin (part of RF-M2's status sentence).
- **RF-m10. `README.md` and `CLAUDE.md`** are consistent with the branch (the `15e4ae5` note is
  now about the submissions `main`, correctly). `docs/README.md` still opens with "State of play
  (2026-10-22)"; update the date with the PR.
- The delegated consistency sweep of every quoted Lean block, theorem name, number, path and
  season value is reported in §4 below.

### Minimality

- **RF-m11.** `proofCap` and `queryCap` are two trusted constants with one value (`2^20`); one
  constant with two docstring sentences saves a line and a question. Not a defect.
- **RF-m12.** The `liveness` badge and `rf-bench` are listed as trusted runtime (§5) although the
  design says liveness is "never the security claim" and the calibration column is published, not
  enforced. Either move them out of the trusted set in §5's table (recommended) or say what a
  reader trusts them for.
- **RF-m13.** `Controls/Compose.lean` `walk_two_leaves` closes four impossible branches by
  `absurd` on `walkFrom_leaf`; a `rcases` on the two outcomes would halve it. Golf only.

### For the three audiences (clarity and concision)

- **RF-m14. The document says the baseline's frontier three times** (§0 "Where it stands", §3.6
  table and paragraph, §4.3 fourth bullet) and the signature's in-circuit cost three times (§0
  "What it costs", §1.3 "Cost of one check", §4.2). Keep each once: the frontier in §3.6, the cost
  in §4.2, and one clause in §0 pointing to them.
- **RF-m15. §0 is two pages; make it one.** Cut the v3/v4 table to the rows that changed a
  reader's obligations (oracle, node clause, certificate quantifier, machine, score) and move the
  rest into §1.2. Replace the last two paragraphs of "Where it stands" by a **status box** of
  three lines: what has run on the development VM, what has run on a GitHub runner, what has
  never run (the evaluation workflow, the attestation, a season-shape entry). That box is what the
  user asked for ("no superfluous detail") and what RF-M2 and RF-M3 are about.
- **RF-m16. §6 (C1–C15 and the ten O-25 criteria) and §7.2 are for the user and the record,
  not for cryptographers or zkVM engineers**; move them to `docs/v4/` (or an appendix after §8)
  and keep one sentence in §0 saying where they are. §3.3's two Lean compile traps (computable
  `ε`, `ByteArray.data`) belong in the rulebook `AGENTS.md`, as the paragraph itself says.
- **RF-m17. For cryptographers**, §2.3's hybrid is right but the displayed inequality lacks the
  running time of `D` at that point (it appears only in §2.4 "about `2^58` steps"); put the one
  number beside the inequality. §2.2's "Statement" is the general-`q` claim and the kernel control
  is `q = 0`; the text says so, but say in the same sentence that the general case is paper.
- **RF-m18. For formal-verification readers**, §1.4 quotes `KState` but the reader meets
  `runLog` only in §1.1's `runSeq` block; one line "`runLog` answers a query from the first
  matching log entry; `runSeq` from the next trace entry" before the quote saves a trip to
  `Oracle.lean`. §2.4's table is the best part of the document for them; make `walk`'s type the
  first row's text (it is the statement), not a parenthesis.
- **RF-m19. For zkVM engineers**, §4.2 should state the per-child totals in one line at the end
  ("a 64-query child: about 104 + 300 ≈ 400 compressions; a 4,096-query child: about 6,600 + 300")
  and name the memory of a node circuit's trace walk (`qV · (|q| + 32)` bytes), which is what they
  will size first.

## 3. What was checked and found right

**Pass A, specification.** `Rel`, `runSeq`, `Submission.acc` (five conjuncts in the stated
order, `|tr| ≤ qV` present), `Certificate` (`∀ vk` on both laws), `SigOk`, `traceDigest`,
`decodeWit` (strict), `Computes`, `treeRoot`: as the design quotes them. The certificate cannot be
vacuous for the known reasons: accept-all needs every digest to have a witness and `Computes`
within `B t` excludes the only extractor that could supply one (v3 §6.2, `enum_no_computes`); a
signature-trusting `V` is uncertifiable under a known signer's key (`sigTrust_no_certificate`,
`Controls/Certificate.lean:109`), and the deployed key is always one a signer knows. `walk`'s
type (`Library/Compose.lean:252`) is the composition statement with the hypotheses §2.4 names;
`Forgery` carries `cap`, `sig`, `notIn`; `compose` keeps `InTree`; the negative control
`forgery_trivial` and the positives `walk_one_leaf`, `walk_two_leaves` exist and are symbolic.
`runLog_of_runSeq` needs exactly a functional log and containment. `paper`
(`PaperTheorem.lean:146`) is `n · ε` for `n ≤ logCap`. `backdoor` is `Certificate S` plus the
magic acceptance on the trigger trace; `magic_needs_trigger` is an iff. The paper steps are
tagged where they are made (§2.3, §2.4 table, §2.5, §2.8).

**Pass B, fidelity.** The byte layouts of §1.3 match `Signature.lean` and `Relation.lean`
(43, 4,265, 65, 41, 33 bytes; tags `43 4C 4E 54 57 4B 4D`); `FORMAT.md` and `Common.lean.in`
`parseSigned` read the same fields strictly; `PROTOCOL.md`'s `SIGN` body is
`32·m + 4 + 32·149`; `rfh/digest.py` hashes the contract's bytes; `season.toml` and `smoke.toml`
hold the §3.6 values (checked row by row: `r, n, M, n_f, K, R`, repeats, samples, canaries, DoS
proofs, the four time caps, memory, `file_cap`). The Rust service is reported in §4.

**Pass C, hygiene and the verdict pipeline.** The source rule's banned list covers `macro`,
`macro_rules`, `syntax`, `elab`, `notation`-free, `initialize`, `unsafe`, `partial`, the
code-changing attributes and the compiler's `set_option`s; the gate's rules 1–8 are v3's with
rule 9 gone; `check-hygiene.sh` runs in CI; `loc.py` is the line counter the budget uses.
`evaluate.py`: the certificate verdict is the comparator's exit code in its own memory scope
(RB-m2, Q12 fixed), the gate tree is bound byte for byte to the comparator's build on
`Solution`'s closure (Q7 fixed), the badge build cannot add or change an entry artifact, the
manifest is checked before and after every step that could touch an olean; `claim.json` is
rendered through a strict schema (`render-challenge.py`: integers below `2^64`, rationals
`a/b` as digit strings, key set equality), so no Lean text can be injected into the challenge
stub; `fetch-entry.sh` fetches by SHA, checks `FETCH_HEAD`, refuses non-regular files; the
sandbox (bwrap, seccomp deny-list, `--disable-userns`, memory scopes, `choom`) and `read_output`
(no link, regular file, size cap) are as RB found them; `run-benchmark.py` turns every exception
into a result (`fail` or `error`) and the stream's checks all happen before the service exits;
`check()` implements RB-M1's statistic; RB-m4's guard is present. `ACCEPT` requires
`cert.status == ok` and `benchmark == pass` in every arriving part (hence RF-M1).

**The user's request, item by item.** SROM security definitions: delivered (v3's verbatim,
`∀ vk`, `acc`, the signature, the composition walk). The keyed-BLAKE2s signing service:
delivered and tested against hashlib and the Lean signer. CI as the trusted machine: the
workflows and the anchor are written; **not yet exercised** (RF-M2) and the aggregate is unsound
until RF-M1. The assembly prover: delivered as a rule and a toy; **does not build on the machine
the rule names** (RF-M2). The additive score: delivered (`score`, `season.toml`, `K = 20`
provisional). Minimality: 355 trusted lines, three axioms, every definition with a docstring and
controls; the runtime is about 3,660 lines, which the design states. What is only partly
delivered is said plainly in §2.8 and §4.3 (no season-shape entry, kernel only for witness-sending
composition, EUF-CMA and the PRF hybrid on paper), with the two exceptions RF-M2 names.

### The service (delegated cryptographer's read of `service/src/*.rs`; no accept-all path found)

- **RF-m20 (robustness, honest harm). The service's own caps do not fit its 2 GiB cgroup.**
  `main.rs:148` `body.resize(blen, 0)` allocates up to 16 MiB per connection before a body byte
  is read; with `resp` (8 MiB at `2^18` items), the sort temporaries (about 13 MiB) and, in
  liveness mode, a duplicate log buffer (about 25 MiB), 64 connections at maximal batches reach
  2.3–3.9 GiB against `memory.service = 2G` with `MemorySwapMax=0`. The OOM kill then lands on the
  service and `alive()` aborts the run as the entry's failure; `PROTOCOL.md` §3 says the caps
  "bound the service's memory". An honest 64-thread prover with maximal batches can trip it. Fix:
  a global in-flight budget (a counting semaphore taken before `resize`), and write liveness items
  straight to the `BufWriter` under the lock.
- **RF-m21 (wording).** `PROTOCOL.md` §5 "a prover cannot tell whether the service runs in
  liveness mode": every request in `--log` mode does `write_all` + `flush` under one global mutex
  (`main.rs:194–196`), which serialises connections and changes latency. Drop the sentence (the
  liveness shape is public anyway) or flush only at shutdown. Design §2.5/§3.2 "assigned under one
  lock": it is a lock-free `AtomicU32::try_update` under the keys' shared read lock
  (`wots.rs:223`), stronger than stated; say "one atomic read-modify-write".
- **RF-m22 (hardening).** Zeroisation misses the `random32` buffer, the `Hasher::new_keyed`
  temporary, the chain values in `advance` and the chain starts in `compute_leaves`; no exposure
  path exists (non-dumpable, no swap under systemd; under the `prlimit` fallback swapping is not
  prevented). A panic in `serve` would leak a connection slot (`conns.fetch_sub` runs only on
  return); no panic path was found. Tests do not check the indices of 8 concurrent signers form a
  permutation, that a failed `SIGN` burns its index, or 64 × 16 MiB bodies (RF-m20).
- Verified correct by that read, with file:line evidence: index taken atomically before signing
  and never reused, refusal at `2^16`; `SIGN` hashes only queries and the service's own answers;
  RFC 7693 keyed mode including the empty-message case on both the scalar and AVX2 paths, with
  only key-derived state cached; `k` and the seed two separate `getrandom` draws; the test-key
  feature off by default, `cfg`-gated out of the release binary, refused by the harness; no key
  material on stdout, stderr, the log or the wire; no answer table; every cap enforced before
  allocation as an error plus close; every WOTS, Merkle and trace byte layout equal to
  `Signature.lean`, `Signer.lean` and `Relation.lean`, and byte-identical to the compiled Lean
  signer.

## 4. Delegated sweeps

Two independent reads were delegated and their findings are folded in above: a mechanical
consistency check of every quoted Lean block, cited name, number, path and season value in
`DESIGN-v4-srom.md` and the three guidance files against the branch (its mismatches are RF-m8,
its confirmations of RF-M3 and RF-m2 are cited there), and a cryptographer's read of
`service/src/*.rs` against `Signature.lean`, `Signer.lean`, `PROTOCOL.md` and the tests
(RF-m20 to RF-m22; no accept-all finding).

## 5. CI

Run `39952420263` (push of `81e1ebf`): **failure**. `lean` passed in 7 min 21 s, `service` in
1 min 32 s; `harness` failed in 1 min 8 s at the stand-in smoke (RF-M2: the honest prover's
`.base64` directives); `smoke` was skipped. The earlier runs on the branch, `39940607844` and
`39935079265`, also failed. No CI run of this branch has been green.
