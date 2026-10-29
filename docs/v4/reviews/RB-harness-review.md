# RB — adversarial review of stage B (v4 SROM): the trusted runtime

Reviewer: Fable adversarial agent. Target: worktree `recursion.fast-v4h`, branch `v4/harness`,
commit `e572344`; `service/`, `harness/`, `scripts/`, `tests/`, `.github/workflows/`. Report:
`docs/v4/stages/B-harness-RESULT.md`. Measured against `docs/v4/BRIEF.md` (V4-1…16, §4,
amendments V4-A1…A8), `docs/v4/reviews/C-design-attack.md` (C-M1…M4, C-m1…m13),
`docs/DESIGN-cost-incentive-model.md` §3.

Method: `adversarial-review` skill, Pass B (fidelity of the service/badge/FORMAT bytes against the
stage-A contract) run before Pass A (what the harness accepts/rejects, and what it leaks or lets an
untrusted prover do), plus a CI/isolation pass. Code read in full; a few targeted reads of the
stage-A contract (`Contract/{Certificate,Oracle,Signature}.lean`, `Library/Fast.lean`) to check
byte-for-byte agreement. I did **not** rebuild the service or run the smoke here (the RESULT and CI
document green runs; the development VM is loaded and I was asked not to change its settings); every
claim below rests on the source, cross-checked against the contract and the protocol docs, and I say
so where I could not reproduce.

Overall: a careful, defense-in-depth implementation. The service crypto is byte-faithful to the
contract and independently tested; the sandbox, the fetch-by-SHA/attestation trust anchor (V4-A1),
the "entry code only in the sandbox" rule, the no-memoisation service (V4-A5) and the authentic-log
liveness check all hold up to inspection. The findings are one measurement-robustness defect that
rejects correct entries, and a set of minors/hardening. No path to a false ACCEPT, a key leak, a
sandbox escape, or cross-request state was found.

---

## Pass B — fidelity (service / badge / FORMAT vs the stage-A contract)

Checked and **correct**, byte for byte:

- `traceDigest` — contract `tagTrace(0x54) :: (enc64 |q| ‖ q ‖ a)*` (`Contract/Signature.lean`)
  = service `trace_digest` / `TAG_T=0x54` (`service/src/lib.rs`) = badge `traceBytesB`
  (`Library/Fast.lean`, `traceDigestF_eq`) = FORMAT.md.
- WOTS: `wotsStep F(j,i,s,x)=tagWots(0x57)‖enc64 j‖i‖s‖x` (43 B), digits `(m[i]>>2t)&3` ×128 +
  checksum `Σ(3−d)` ×5, leaf `tagWotsLeaf(0x4B)‖enc64 j‖ends`, node `tagSigNode(0x4D)‖l‖r`, root by
  bit `t` of `j` — contract `Signature.lean` = service `wots.rs` (`f_msg`/`digits`/`leaf_msg`/
  `node_msg`/`verify`) = `Library/Fast.lean` (`SigOkF_eq`). The reference `sk` derivation
  `tagS(0x53)‖enc64 j‖i` keyed under the independent seed matches V4-A4. `tests/service/
  test_lean_signer.py` is reported byte-identical against the compiled Lean signer; `SigOk` /
  `SigOkF` / Rust `verify` agree.
- `acc` conjunct order (V4-A3, cheapest-rejection-first): `proofCap` size, per-query `queryCap`,
  `SigOk`, then `runSeq` — contract `Submission.acc` = badge `Submission.accF` (`accF_eq`) = the
  service wire caps (`queryCap=2^20`) = FORMAT.md. `runSeq` exact consumption
  (`[] (.ret)=some`, `(_::_) (.ret)=none`, trailing entry ⇒ `none`) matches V4-A3
  (`Contract/Oracle.lean`).
- Keyed BLAKE2s: RFC-7693 keyed mode, empty message = single final key block; scalar and AVX2
  paths; tested against `hashlib` and each other. Correct.

No fidelity defect found. One caveat carried as RB-m7 (the contract's `acc` still lacks the
`tr.length ≤ qV` conjunct; the badge mirrors `acc` through `accF` and will inherit the fix with no
badge change — I confirmed `accF`/`accF_eq` reference the same conjuncts).

## Pass A — what the harness accepts, rejects, leaks, or permits

The verdict pipeline is sound: ACCEPT ⟺ (comparator-certified **and** every benchmark part passed);
PROVISIONAL never becomes ACCEPT or `comparable` (`evaluate.py bench_job`, `aggregate.py`); a record
counts only through `gh attestation verify --signer-workflow scaraven/recursion.fast/.github/
workflows/evaluate.yml`. The one check the harness trusts is the compiled `accF` (= `acc`), run
sandboxed and pinned, on the runner's own statement for the root, samples, canaries, every stream
output and the DoS column. The service is unreachable except by socket; keys are `getrandom`,
never written, wiped at exit, `PR_SET_DUMPABLE=0`; no answer memoisation (V4-A5); index reserved by
one atomic `try_update` before signing and never reused (V4-A4); refusals carry no usable answer.
Liveness runs the entry's `ext` on the contract interpreter over the **service's own** log (prover
never touches it), fuel/mem-capped. All as designed.

---

## Findings

### RB-M1 (major, honest harm). `T_V` is enforced on a single wall-clock sample per output while the cap is the *best* of N calibration runs, and `fail-fast: true` cancels the whole evaluation on the first breach — a transient scheduling spike on the shared runner rejects a correct entry.

**Claim.** `calibrate()` sets `T_V = min(runs)/R` over `checker_runs` chain-checker runs
(`harness/rfh/bench.py:172-174`: `best = min(runs)`), i.e. the *fastest* calibration — the
*strictest* cap. Each enforced check is then a **single** measurement: `check()` runs the badge
`verify` once per item and does `if ns > self.tv_cap_ns: raise Fail` (`bench.py:148-149`). The badge
times `parse + accF` with `IO.monoNanosNow` (wall clock; `badge/Verify.lean.in`, `timedCheck`),
pinned to one core. In `evaluate.yml` the benchmark is six jobs with `strategy.fail-fast: true`
(`.github/workflows/evaluate.yml:95`), so one `Fail` cancels the rest and the run has no usable
result.

**Why it harms an honest entry.** A season entry is enforced on ~1 root + 16 samples per tree repeat
and every `ℓ_i`/`π_i` of the stream (≈ 2·(M+1) ≈ 1025 per stream repeat), so ~3000 single-shot
wall-clock measurements per entry. The pinned core is quiet but not silent (kernel work, page
faults, the live service, GC). The margin is ~2× (a real root check is 135–155 ms against
`T_V = 310 ms`, RESULT §3), so one ≥2× spike on any one of ~3000 samples over a multi-hour run
breaches the cap. Because the cap is the *minimum* of the calibration runs but the check is a *single
draw*, the comparison is biased toward rejection: calibration is given its best case, the entry is
not. With `fail-fast` the single breach discards the other jobs' work.

**Fix.** (a) Measure the enforced check the same way the cap is measured — take the best of a few
badge `verify` runs per output (or re-measure once on a borderline result before failing), so cap
and check use the same statistic. (b) Set `fail-fast: false` so a transient breach or infra hiccup
in one job does not cancel the others; `aggregate.py` already tolerates missing/partial parts and
computes the verdict from what arrives. (c) Consider comparing each output against a freshly
re-measured `T_triv` on the same core rather than a once-per-job cap, to track drift within the job.

---

### RB-m1 (minor). `fail-fast: true` also loses all partial benchmark results on any single job failure.
Beyond RB-M1, a genuine failure in one of the six jobs (e.g. a timeout on one stream repeat) cancels
the five others, so the attested result has no data for the parts that did pass and the entry must be
re-run from scratch. `aggregate.py` already handles a subset of parts and marks `mixed_cpu`; set
`fail-fast: false` and let the verdict reflect the real per-part outcomes.

### RB-m2 (minor). The "certified" decision matches a substring in a log that also carries entry-controlled build output.
`evaluate.py:231`: `certified = rc == 0 and "Your solution is okay" in out`, where `out` is the
combined stdout+stderr of `lake env comparator config.json` — which includes the sandboxed solution
build's Lean diagnostics. This is not a false-ACCEPT vector (the `and` only *tightens*: without the
sentinel a comparator-accepted build is demoted to provisional), but it is fragile: an entry that
can keep the sentinel out of the log (or a comparator version that changes the wording) turns a valid
certificate provisional (honest harm), and the pattern invites confusion. Prefer the comparator's
exit code alone, or a machine-readable result file written by the comparator to a path the solution
build cannot write, rather than a substring of a shared log.

### RB-m3 (minor). `evaluate.py cert` is run with `|| true` and its status read back by a second parse; a crash before `cert.json` is written yields an empty status that does not equal `'reject'`.
`evaluate.yml:81-83`: `python3 … evaluate.py cert … || true` then
`status=$(python3 -c '… json.load(open("cert.json"))["status"]')`. If `cert_job` raises outside its
`Reject`/`TimeoutExpired` handlers (a harness bug, or `cert.json` never created), the inner parse
fails, `status` is empty, and `benchmark.if: needs.certificate.outputs.status != 'reject'` is true,
so the benchmark runs against a missing/partial certificate. It then errors on `cert["badge_dir"]`
⇒ ERROR (fails closed, not a false ACCEPT), but the intent is lost. Default `status` to `reject` on
any parse failure and drop `|| true` (let the step fail and surface it).

### RB-m4 (minor). `T_V` is silently unenforced if a benchmark job's `--parts` omit `calibrate`.
`tv_cap_ns` starts `None` and is set only in `calibrate()`; `check()` enforces only
`if self.p.tv_enforce and self.tv_cap_ns is not None` (`bench.py:148`). The CI matrix always
prefixes `calibrate` (`evaluate.yml:98`), so this is latent, but a hand-run `--parts tree` would
measure outputs with no cap and still report pass. Guard it: when `tv_enforce` and any of
`tree`/`stream` run without a cap, abort as a harness error.

### RB-m5 (minor, hardening). `--insecure-test-keys` is compiled into the production service binary.
`service/src/main.rs:18-20,251-254` accepts fixed keys and prints `INSECURE`. The runner refuses a
service that prints `INSECURE` (`rfh/service.py:56-58`) and controls argv, so this is not reachable
in deployment; still, a trusted-runtime binary that can run with attacker-chosen keys should gate
that path behind `#[cfg(debug_assertions)]` or a non-default cargo feature so it cannot exist in the
release artifact whose hash is attested.

### RB-m6 (minor). The calibration column reports `compressions_per_s = calls_per_s`.
`bench.py:186-188` sets `compressions_per_s` equal to `calls_per_s` with the comment "a 64-byte
keyed query is one compression after the cached key block" — true only for the fixed 64-byte probe
used here. The field name implies a size-independent compression rate (C-m8 wanted compressions/s as
a calibration unit). Either rename it to make the 1-block basis explicit or derive it from the probe
size, so a reader comparing seasons is not misled.

### RB-m7 (minor, cross-ref to stage A / RA-M2). The contract `acc` still omits `tr.length ≤ S.qV`.
`Contract/Certificate.lean` `Submission.acc` and `Library/Fast.lean` `accF` enforce `proofCap`, the
per-query `queryCap`, `SigOk` and `runSeq`, but not a bound on the number of trace entries, while
`KS` is stated with `S.qV`. RA-M2 (quoted in FORMAT.md and RESULT §6) already scheduled this for the
contract. For stage B this is not a defect — the badge mirrors `acc` through `accF` and needs no
change when the conjunct lands (I confirmed both read the same four conjuncts) — but the stage should
state that the harness's query accounting currently rests on the service's `MAX_SIGN_COUNT=2^16` cap
rather than on `acc`, until RA-M2 is merged.

### RB-m8 (minor, acknowledged). SROM liveness is exercised only at `r=1, n=16`.
The authentic-log extractor check (`tree_repeat(..., liveness_log=…)`) runs only in the dedicated
`liveness` repeat at `live_r=1, live_n=16` (`season.toml [liveness]`); the three season tree repeats
start the service without `--log`, so the composition/extraction smoke never runs at the season
shape. RESULT open-question 4 and V4-A8 own this; keep it stated in the design as a known gap (the
security claim is the proved `Computes`, not the smoke).

### RB-m9 (minor). The canary set mutates a trace *answer* but never a trace *query*.
`checks.py:canaries` flips an answer byte (`trace-answer`), adds a trace entry (`trace-extra`) and
mutates `π`/`idx`/`ots`, but never flips a byte of a query `q_i`. A query mutation is caught by the
crypto (it changes `traceDigest` ⇒ `SigOk` fails, or breaks `runSeq`), so this is not a hole, but a
`trace-query` canary would make the non-vacuity of the query binding explicit alongside the others.

### RB-m10 (minor). Declaring `fuel > 2^36` makes liveness report "ok not run", hiding a broken extractor from the smoke.
`badge/Liveness.lean.in` throws `not run` (reported as `ok`) when `declaredFuel t > stepCap = 2^36`.
An entry can set `fuel_base`/`fuel_per_word` so the cap is always hit, so the liveness smoke never
actually runs `ext`. Security rests on the proved `Computes S.ext S.E S.fuel` with
`fuel ≤ extractorBudget` (checked by the certificate), so this does not admit a wrong proof; note it
so the smoke's silence is not read as evidence.

### RB-m11 (minor, small bias). Stream input-writing latency is inside the timed window.
`request()` sets `t0` *before* `write_atomic` of the inputs and the `go` line (`rfh/prover.py:199-204`).
For `node`, `child1.bin`/`child2.bin` can be ~`proofCap` (1 MiB) each, so a few ms of the runner's
own write time is charged to the prover's `t_merge`. Negligible at season sizes but a systematic
bias against the prover; write the inputs (or at least the large child files) before starting the
clock, or subtract the measured write time.

### RB-m12 (housekeeping). Stray directories in the shared read-only package tree.
RESULT open-question 7: `VCVio/.lake` and `leansqlite/.lake` were created in the shared package tree
by a `lake build gate` on 2026-10-22 and could not be removed. These must be cleaned by the user;
until then `olean-manifest.py` scope and any future `org-setup.sh` on that tree should be checked
against them.

---

## Checks that passed (no finding)

- **Sandbox.** `--unshare-user --disable-userns` blocks nested user namespaces via *any* syscall
  (the kernel's `max_user_namespaces`, not just the seccomp `unshare`/`setns` denials), so the
  `clone3`-userns path the hostile test does not exercise is still closed; `--unshare-pid` + non-host
  `/proc` hide the service pid; `PR_SET_DUMPABLE=0` + seccomp block same-uid memory reads; outputs
  read with `O_NOFOLLOW`, regular-file-only, size-capped (`files.read_output`); `--die-with-parent`
  + pid-ns + killed scope stop survivors. The "no separate uid" deviation (§5.1) is adequately
  compensated.
- **Clock.** T run timed exec→exit under `--block-fd`/`--json-status-fd` (no pre-ready or
  post-exit work counted); stream clock starts after `ready`, before inputs, and stops at `done`
  then kills the sandbox (no post-`done` child work). No way found to move timed work outside the
  window.
- **No free oracle / no cross-request state.** Every oracle answer comes from the service (secret
  keyed PRF; a prover cannot compute it offline) and is logged; no per-query memo; a fresh sandbox
  per request; the only cross-request channel is the observable 16-bit index, which carries no
  proving state.
- **Service DoS.** Body ≤ 2^24, query ≤ 2^20, items ≤ 2^18 (QUERY)/2^16 (SIGN), ≤ 64 connections,
  ≤ 2^16 signatures, own 2 GB cgroup, prover `oom_score_adj=1000`: no unbounded alloc, no path for a
  prover to kill the service by memory pressure. Refusals return no answers.
- **CI trust anchor (V4-A1/A2).** `pull_request_target`+label / `workflow_dispatch`; base-branch
  workflow; fork fetched by SHA as data (no `actions/checkout` of the fork, no
  `allow-unsafe-pr-checkout`, no persisted credentials, read-only `contents`); entry code
  (Lean build, gate, badge, prover) only in the sandbox; result attested and verified by
  `--signer-workflow`. ACCEPT requires a comparator certificate; PROVISIONAL never ranks. nanoda's
  absence is recorded (`second_kernel`).

---

## Verdict

**Accept with fixes.** One major (RB-M1: single-shot wall-clock `T_V` enforcement against a
best-of-N cap, with `fail-fast`, rejects correct entries) must be fixed before the rules are run on
GitHub; it is a measurement-robustness/honest-harm defect, not a soundness hole. The minors are
hardening and clarity. I found no path to a false ACCEPT, a key or seed leak, a sandbox escape,
cross-request persistence, or code execution with the job's token; the service crypto and the
badge/FORMAT bytes are faithful to the stage-A contract and independently tested.
