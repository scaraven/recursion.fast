# recursion.fast v2 contract: handover (RESULT)

State at `db94302` (2026-10-15), plus three uncommitted README edits from the Stage 9 README pass
(`submissions/baseline/README.md`, `prover/README.md`, the "S9 README pass" section of
`docs/stages/S7-RESULT.md`). Every number below cites the file it comes from. "(ran)" marks a
command I ran for this document on 2026-10-15. Design sections are cited by number only.

## 1. What this repository is

The trusted Lean 4 rules of an autoresearch competition. Agents submit a hash-based SNARK over
GF(2^64) for a chips + CCS + bus relation. They prove it complete and round-by-round knowledge
sound with a bounded RISC-V extractor, and they supply their verifier as a circuit. They are ranked
by the measured wall time of one 2→1 recursion step. Around the contract sit the organiser's
untrusted library, the controls, the harness (gate, renderer, badge executables, benchmark runner,
CI), the Clean frontend bridge, an ArkLib bridge and the trivial baseline submission.

### How it was built

The build follows the stage protocol of `CLAUDE.md`, one stage at a time, in the order of design §11:

1. **Implement.** One agent builds the stage and writes `docs/stages/S<n>-RESULT.md`.
2. **Review and golf, in parallel.** One agent does the adversarial review
   (`docs/reviews/S<n>-review.md`: majors `S<n>-M<i>`, minors `S<n>-m<i>`, a verdict). Another
   golfs proofs without changing statements (`S<n>-golf.md`).
3. **Fix.** The implementer fixes every major and answers every minor (`## Fix pass` in the RESULT).
4. **Commit.** The orchestrator decides open questions (`## Decision pass`) and commits.

Stage 9 had three whole-repository reviews (definitions, incentives, feasibility), then fix passes
by the contract, compile, harness and README owners.

The record behind this:

- **Documents.** 9 stage RESULTs (S1, S2, S3, S4, S5, S6a, S6b, S7, S8). 12 reviews: 9 stage
  reviews plus 3 for S9. 9 golf reports; for S6b this was a simplify pass by four read-only
  sub-agents.
- **Amendments.** 143 items, S1-A1 … S9-A44, in `docs/DESIGN-AMENDMENTS.md` (ran: grep).
- **Probes.** 208 tracked files in 11 probe directories (ran: `git ls-files probes`).
- **Findings.** The stage reviews raised 14 majors; S9 raised 11 more (S9D 1, S9F 7, S9I 3).
- **Commits.** 16 (ran: `git log --oneline | wc -l`).
- **Agent headcount.** Not logged; the files above are the record.

| Commit | One line |
|---|---|
| `089f788` | Scaffold: pins, `Field`/`Shapes`/`Security` and vendored Rv64 verbatim from v0.3, v0.3 harness scripts, DESIGN.md, CLAUDE.md |
| `f675f9c` | S2: trusted BLAKE2s (RFC 7693), 12 kernel KATs, 8,432-case hashlib differential |
| `73e9e32` | Probe O-4: Clean `42fe4b26` builds on the v4.34.1 pins |
| `c9fdf2c` | S1: chips + CCS + bus relation, `Protocol` over `Layout`, R1CS special case, toy, controls |
| `d04f748` | Design fold S1-A1..A13, S2-A1..A2 |
| `b2ceaa3` | S3: compiled argument (Merkle + Fiat–Shamir, `NARG`), completeness theorem |
| `0c0d9df` | S4: bounded extractor image on a trimmed RV64 machine; `Protocol` swapped to it |
| `bf64ac3` | S6a: `L_chain(n)` generator, Python `rel` oracle, one-G-call kernel control |
| `7d140e7` | S5: recursion (`aggOK`, `RecursionEntry`, `rootOK`) and certificate types |
| `ef9860f` | S7: baseline `P_triv` certified at class 24; `Certificate` pins the extractor image |
| `1407d46` | S8: Clean frontend, `toLayout` bridge both directions; ports cap 2^4 → 2^5 |
| `e13131e` | S8 follow-up: manifest entry for the Clean path dependency |
| `8b925dc` | Design fold S3–S8 amendments |
| `0451b32` | S6b: harness: gate rules 1–9, stubs + renderer, `verify`/`index` executables, runner, CI |
| `2620a62` | Design fold S6b-A1..A26 |
| `db94302` | S9 fix passes: source rule ×2 nets, R-only ranking, `S_rec` by level group, paired records, sparse `commit`, 9 trusted deletions, ArkLib bridge |

## 2. The trusted base

**Trust statement** (S9-definitions §5, quoted; the bracketed figures are updated to the state after
the S9 fix passes):

> A ranked record means: the kernel accepted `certified` for the rendered challenge, and the run,
> every proof verifying, measured the times. Its reader trusts:
> 1. Lean v4.34.1's kernel and nanoda (the comparator replays in both), the comparator's export,
>    and Lean core, Mathlib and packages as hashed in `scripts/olean-manifest.sha256` [34,512
>    files, the trusted closure only, S9-A32].
> 2. The contract: 12 files, [737] code lines ([528] without `Compile` and BLAKE2s), no theorem,
>    three standard axioms; [8 declarations are outside every certificate's cone, 7 of them in
>    `Compile`/`Recursion` plus `unpack`, which is load-bearing through the rendered image (S9-A1)].
> 3. The vendored RV64 model (riscv-zkvm `6810fc1`): 205 declarations, 930 lines, ~614 live (m7).
> 4. BLAKE2s = RFC 7693 (KATs, 8,432-case differential) and its collision resistance, which binds
>    openings (`opening_binding` [now in `Library/Compile.lean`, CI-checked]), key digests and `d2`.
> 5. `Compile.lean` by review of its normative header; `NARG`'s soundness is BCS/Fiat–Shamir in the
>    ROM, once per tree level, with no composition theorem (§5.4).
> 6. The badge code: what Lean's compiler emitted for the twin (`rfl` to the submission's `NARG`,
>    `index`), guarded by the source rule and gate rules 3, 6–9; residual O-12 [the S9D-M1 lexer
>    bypass is closed by S9-A30; the residual is a keyword the review missed].
> 7. Harness tools: `Gate.lean` (trust by `.olean` hash), the order comparator → gate → badge with
>    build binding, `olean-manifest.py`, `AxiomAudit.lean`, `source-rule.py`, `render-challenge.py`
>    and `render-layout.py`, the sandbox (bwrap, landrun, cgroups).
> 8. Tested, not proved: `run-benchmark.py`; `LayoutJson.parse` [no longer on the recursion key's
>    path, S9-A41]; `gen-chain-layout.py`. 9. The reference machine.
> Not trusted: `Library/`, `Clean/`, `Bridge/`, `Controls/`, `probes/`, the baseline, the native
> prover. Not claimed: composition across levels; that benchmark nodes are provable (S5-A10);
> hardness of a one-element secret at `k ≥ 25`; `decode`'s efficiency.

**Contract files** (ran: `python3 scripts/loc.py RecursionFast/Contract.lean RecursionFast/Contract/*.lean RecursionFast/Contract/Hash/Blake2s.lean`):

| File | Code | What it defines | Origin |
|---|---:|---|---|
| `Contract.lean` | 11 | the reading order | changed |
| `Field.lean` | 24 | `K` = GF(2^64) (`clmul`, two folds by `x^4+x^3+x+1`), `K.toBytes`; `E` as a 3-limb challenge set | v0.3 minus 6 deletions (S9-A1) |
| `Layout.lean` | 80 | `Gadget` (sparse CCS), `Port`, `BusKind`, `Table`, `Chip`, `Layout`, `Layout.rel`, `Admissible` | new (S1; ports 2^5, S8-A9) |
| `Shapes.lean` | 47 | rounds, oracle shapes, transcripts | v0.3 minus 2 deletions; docstrings (S9-A3) |
| `Security.lean` | 55 | `Extractor`, `KSF`, `RbrKS`, `PerfectComplete`, `SecureWith`, `errorCap = 2^-128` | v0.3 verbatim, comments only (S4-A11, S9-A3) |
| `Machine.lean` | 109 | trimmed RV64 + Zbc, memory map (tape at 2^63), `HALT` returns words, `run` | new, trimmed from v0.3 (S4) |
| `Extractor.lean` | 65 | `B(k) = 2^(2k+16)`, `witCap`, `imageCap = 2^20`, `Layout.words`, `frame`, `extractorTape`, `Mid`, `ExtractorImage` (declared fuel split), `toExtractor` | new (S4, S4-A14) |
| `Protocol.lean` | 45 | `relK`, `QProg`, `Round.Admissible`, `Protocol k`, `specVerifier`, `Secure` | new (S1, S4-A13) |
| `Hash/Blake2s.lean` | 68 | RFC 7693 `blake2s`, `blake2s256` (compression vendored from leanerVM `485d0465`) | new (S2) |
| `Compile.lean` | 141 | `HashId`, `Cfg`, sparse `commit`, `index`, sponge, `pass`, `runQ`, **`NARG`**, `VKc.digest` | new (S3, S9-A10) |
| `Recursion.lean` | 67 | `digestToSlot`, `nodeStmt`, `child`, `aggOK`, `pairUp`/`treeRoot`/`rootOK`, `RecursionEntry` | new (S5) |
| `Certificate.lean` | 25 | `Submission(R)`, `Declared(R)` (with `img`), `Certificate(R)` | new (S5, S7-A5) |
| **Total** | **737** | | budget ≤ 850 excluding `Compile` and `Hash/`: **528** |

CI step 4 prints 669 (everything but `Hash/`; `logs/S9/ci-harness-1.log`).

**Vendored machine.** It is byte-identical to riscv-zkvm `6810fc1` (`scripts/check-vendor.sh`, CI
step 1). The contract reaches 205 declarations, 930 source lines and 0 theorems (S4-RESULT,
`probes/s4/TrustedClosure.lean`). ZiskAccel's 33 declarations and 316 lines, and six arms of
`execInstrBr`, are unreachable from `execute` but sit in the kernel term (S9D-m7, S9-A5; open
as O-16).

**Harness tools** (trusted, not Lean-checked; line counts ran):

- `scripts/Gate.lean` (367 code lines): rules 1–9.
- `scripts/AxiomAudit.lean` (43).
- `scripts/source-rule.py` (334 lines).
- `scripts/olean-manifest.py` (160), with `scripts/olean-manifest.sha256` (34,512 files).
- `scripts/render-challenge.py` (314) and `harness/render-layout.py` (153).
- `scripts/harness.sh` (294): the order comparator → gate → badge.
- `scripts/bwrap-landrun.sh` (46), plus systemd cgroups.

External, pinned in `scripts/tools.env`: leanprover/comparator `d03acab` (lean4export `076e8e5`)
and nanoda_lib `3a24072`.

**Not trusted:**

- Lean code: `Library/` (2,256 code lines), `Controls/` (2,915), `Bridge/` (130) and `Clean/`
  (1,817) (ran: `loc.py`).
- `harness/run-benchmark.py`, `gen-chain-layout.py`, `check-chain.py` and `harness/lean/`: tested,
  §5.
- `probes/`, the baseline, and every native prover.

## 3. What is proved

Lean's kernel checks everything below at `lake build`. The default build is green: 2,490 jobs, 4.1 s
warm (ran). The certificate closures of the CI toy (step 7) and of the baseline (`check.sh` with
`HARNESS=1`) are also replayed by nanoda through the comparator.

**Axioms.** The organiser audit gives PASS on 1,984 declarations in 40 modules: Contract 794,
Library 614, Controls 556, Bridge 20. 191 theorems use no axiom (ran:
`.lake/org … axiomaudit`). The Clean audit covers 739 `RecursionFast.Clean*` declarations, all
within the standard three (CI step 11).

The whole-tree probe audited 1,285 constants at `0451b32`: 1,080 contract constants, internal names
included, plus 205 vendored. It found 0 non-standard axioms and no hand-written `unsafe`/`partial`/`opaque`/
`implemented_by`/`extern`, and the contract contains no theorem (S9-definitions §4). Every axiom
anywhere is `propext`, `Classical.choice` or `Quot.sound`.

### Per contract file: the load-bearing definitions and the controls that show non-vacuity

| File | Load-bearing | Positive controls | Negative controls |
|---|---|---|---|
| `Layout` | `Layout.rel` (6 clauses), `Admissible` | `r1cs_pos`, `twoChip_pos`, `lookup_pos`, `fib_pos`, `wrap_pos`, `triv_relK` | `r1cs_neg`, `twoChip_neg`, `eqMult_neg`, `lookup_neg`, `lookup_neg_fixed`, `fixedHeight_neg`, `fib_neg`, `fib_garbage`, `fib_boundary_neg`, `wrap_neg`, `stmt_neg`, `noPub_neg`, `emptyPub_neg`, `unsat_neg`, `cells_neg`; ten cap boundaries, each accept-at-cap/reject-above (`ports_cap`: 32 accepted, 33 rejected) |
| `Shapes`/`Security` | `SecureWith`, `KSF`, `RbrKS` | `hit_secure` (challenge rounds, ε = 2^-192) | `acceptAll_no_KSF`, `rejectAll_not_complete`, `rejectAll_not_secure`, `acceptAllChal_not_secure` (the cap is load-bearing) |
| `Protocol` | `relK`, `QProg.eval`, `specVerifier`, `Secure` | `toy_secure` at every `20 ≤ k ≤ 28` | `toy_spin_not_secure`, `toy_not_secure_of` (`Secure` depends on the image) |
| `Machine`/`Extractor` | `run`, `toExtractor`, `B(k)`, the declared split | `copy_run`, `copy_extract_relK` (image → trusted decoder → `relK 20`), `wzbc_run`, `chain_finds`/`chain_round0` (state passes between calls) | `spin_extractMid` (fuel exhaustion → `[]`), `long_extractMid` (over `witCap`), `tape_readonly`, `halt_misaligned`, `ecall_trap`, `brute_extractMid_nil` + `brute_nonvacuous`, `chain_search_fails` (any split; ≤ 255 candidates per step is not an extractor at class 20) |
| `Hash/Blake2s` | `blake2s256` | 12 KATs (RFC Appendix B, hashlib, leanVM), `highCounter_kat`, `lastNode_kat`, `sigma_perm`, `iv_spec` | `flip_neg`, `key_neg`, `nn_neg`; mutants `heldBack`, `padNN`, `wordTrunc` are each killed (`probes/s2/Mutants.lean`) |
| `Compile` | `NARG`, `index`, `commit`, `VKc.digest` | `honest_accepted`, `digest_kat`, `decode_kat`, `pfs_honest`, `toy_local`; sparse-root `#guard`s at arity 2/4/16 | `leaf_flip`, `path_flip`, `plain_flip`, `idx_leaf_flip`, `idx_path_flip`, `oob_rejected`, `leftover`, `truncated`, `oversize`, `root_flip`, `stmt_flip`, `fs_binding`, `pfs_cheat`; one-line mutants `NARGidx/plain/range/off` killed (`probes/s3/RevMutants.lean`) |
| `Recursion` | `nodeStmt`, `aggOK`, `RecursionEntry` (`fits`, `sound`, `complete`, `live`) | `aggOK_two_leaves`, `aggOK_node_child`, `toy_sat_via_complete`, `cmpToy_live`, `distinct_keys`, `rootOK_xT`; KATs `nodeStmt_kat`, `_R`, `_keys`, `treeKat` | `child_tape_flip`, `wrong_d1`, `nonzero_d3`, `nonzero_d4`, `node_child_d0/d1`, `mistag_rejected`, `leaf_under_vkC`, `root33_rejected`, `rootOK_leaf/_other_key/_odd`, `cbad_not_sound`, `unsat_no_entry`, `magic_not_live`, `toy_no_entry` |
| `Certificate` | `Certificate` (cfg, `img`), `CertificateR` (size) | `toy_certificate` | `toy_certificate_arity`, `toy_certificate_img`, `toy_no_submissionR` |

**No positive `RecursionEntry` exists** (design §7.3). `aggOK_sat_of_secure` and `live_of_secure`
have no instance in the repository: the only protocol proved secure, the toy, has tapes beyond the
cap (S5-m8).

### Library theorems a submitter relies on (untrusted, kernel-checked)

- `Gadget.holds_iff`: the sparse fold gadget is textbook CCS (Mathlib `*ᵥ`, `∑`, multiset `∏`).
- `R1CS_iff_layout`: R1CS with `z = (1, x, w)` is one chip, one row, no ports, stated for `relK k`
  with explicit witness maps.
- `rel_trim_iff`, `rel_normal_iff`, `relBelow_iff`: `rel` reads only paid cells; decidable form.
- `pLayout_eLayout`, `pWit_eWit`, `eLayout_length`: serialisation round trips and the `2^(k+8)` bound.
- `narg_complete`, `narg_complete_of_secure`, `prove_isSome`: compile completeness for every protocol,
  `Cfg` and instance; `prove` fails only by the tape cap.
- `NARG_eq_true_iff`, `narg_local`: what an accepted tape forces, i.e. what `C_V` must compute.
- `opening_binding`: a Merkle opening that verifies against a root binds, or yields a collision.
- `commit_eq_commitDense`, `pathOf_eq_dense`, `depth_spec`: the sparse root equals the dense one.
- `aggOK_iff`, `aggOK_sat_of_secure`, `live_of_secure`, `keys_of_root`, `digestToSlot_inj`: the node
  check unfolded, and `live` from one capped honest proof.
- `nil_not_relK`, `firstMsg_extractMid`, `extractMid_eq_of_run`, `composed_fuel_le`,
  `pLayout_words`: the extractor's refinement interface and budget.
- `chain_extracts`: straight-line extraction from RBR-KS. (`rbrKS_of_rbr` is for unbounded
  extractors and does not apply to the image.)
- `toLayout_rel_iff`, `statementPerm_iff`, `toLayout_rel_iff_raw`, `relK_toLayoutWit` (Clean): a
  Clean ensemble ↔ its layout, both directions. They hold under `Supported`, `LookupsFaithful`
  and `PublicIO ≤ 32`, plus `ChannelsByName` for the raw form.
- `Protocol.secure_toArk` (Bridge): `Secure` ⇒ ArkLib worst-case RBR knowledge soundness. It is
  one-directional, forgets `B(k)`, and cannot be imported by a submission: ArkLib is outside the
  rule 6 allowlist (S9-A4).

### Baseline theorems (`submissions/baseline`, 231 code lines, 21 theorems)

- `triv_secure k hk` at every `20 ≤ k ≤ 28`.
- `certified`, proved by `⟨⟨rfl, rfl⟩, rfl⟩` at `k = 24`. HARNESS: ACCEPT with both kernels.

**"Listed, unranked" is a theorem.** The compiled verifier accepts no tape at any class or
configuration (`triv_narg`). The honest tape has `5·2^(k+11)` bytes, 160 GiB at `k = 24`
(`triv_uncapped_length`). The honest prover writes no tape (`triv_prove_none`). There is no
recursion entry, because `live` fails (`triv_no_entry`).

The extractor split `![8, 0]` is tight (`trivExtractor_fuel_tight`), and starving round 0 breaks
`Secure` (`split0_not_secure`). Only `certified` and `submission`'s closure are certified by the
harness; the rest is checked at build time (S7-m1).

## 4. What is measured, not proved

### 4.1 The gate and the source rule

`scripts/Gate.lean` loads the elaborated environment without running imported code and trusts
modules by `.olean` hash. Its rules:

1. Only the standard axioms, and no `sorryAx` or `ofReduceBool`.
2. No `unsafe`, `partial` or `opaque` in untrusted or pinned modules.
3. No untrusted `implemented_by`, `extern`, `export`, `init`, `csimp`, `cpass` or `computed_field`.
4. The badge-path fields have compiled code: `P` (`n`, `shape`, `vkLen`, `VK`, `idxShape`, `IDX`,
   `verify`, `extractor.img`), `cfg`, `entry.C` and `entry.decode`.
5. The manifest matches.
6. Imports stay inside `scripts/import-allowlist.txt` (10,820 modules) or the frontend list (45),
   transitively.
7. No definition uses the compiler or environment API.
8. The badge root's module stays in the compiler-free closure.
9. No badge-path field calls frontend (Clean) code.

**Source rule** (`scripts/source-rule.py`, S9-A30). It runs in each fresh tree before anything of
the submission is built. It has two binding nets:

- a Lean-faithful lexer that fails closed;
- a raw word scan of the bytes.

The fixtures (CI step 1) check 95 rejected forms, and the 4 forgeries are each caught by each net
alone. The CI step 6 sweep finds 418 keyword tokens: 159 rejected, 259 reviewed, 0 unreviewed
(`logs/S9/ci-harness-1.log`).

**Trust statement (S9-A30):**

> The source rule (two nets over a closed, reviewed keyword list, checked against the closure's
> token table) and gate rules 3, 6, 7, 8 raise the bar. They do not exclude elaboration-time code
> reached through a keyword the review missed, such as a scoped or non-reserved keyword absent from
> the token table. The sound fix is O-12, which must ship before any ranked board opens.

**O-12 residual, concretely.** `probes/s6b/gate/ForgeRaw.lean` forges an importer's emitted code
through `persistentEnvExtensionsRef` and `unsafeCast` under Mathlib-only imports. **The gate
PASSES it** (CI step 8 asserts this); only the source rule rejects it (S6b-A20, CI step 7).

Building `verify`/`index` from the twin with a kernel `rfl` (S6b-A4) and binding the build
(A7-M3) make "timed = proved" hold only up to the compiler.

### 4.2 The runner (`harness/run-benchmark.py`; `harness/README.md`; `harness/reference-machine.md`)

- **Boards.** R is the only ranked board. L (`S_leaf`) and W (`S_wrap`) are published as
  `"ranked": false` (S9-A34): a leaf witness is its 32-byte start, so a recompute-the-chain verifier
  is sound and sends a 64-byte tape (`probes/s9/incentives/recompute_leaf.py`). Boards are judged
  separately (S6b-A8).
- **`S_rec`** = max(m₂, m₃, m₄₋₆): each `m_g` is the median over 3 runs of the per-run median step
  time of level 2, level 3, and levels 4–6 pooled (7 steps). It closes the cheap-to-verify wrap
  attack (S9-A35). A step's time is the prover's wall time plus `verify` on its output.
- **Record rule** (S9-A36). `record` screens at ≤ 0.97 × the standing result. `compare` then runs
  standing and challenger in one session, ABBA, 5 pairs on fresh instances; a record needs median
  ratio ≤ 0.97. `compare --calibrate` gives σ and the pairs needed, `⌈(3.75σ/m)²⌉`. Sybil limit:
  one ranked entry per submitter per season, one confirmation per week. Ties go to the incumbent.
- **Canaries** (S9-A37). For 8 proofs per kind per run, `verify` must reject four mutations: a
  byte appended, the last byte removed, a statement bit flipped, the other key. DoS tapes go under
  both keys. Canaries catch an accept-all executable, not a keyed forgery.
- **Isolation.** The runner fails closed without the sandbox or a working cgroup (S6b-A21). Each
  step runs in its own cgroup: `MemoryMax`, `MemorySwapMax=0`, `OOMPolicy=continue`, and an
  `oom_kill` rejects (S6b-A23). The sandbox is `bwrap-landrun.sh --minimal-root` (S6b-A24).
  Secrets are drawn from `os.urandom` for every evaluation; `--secrets` is refused (S9-A38). Probes
  found nothing that persists between steps: daemons, `/tmp`, `/dev/shm`, SysV shm, keyrings
  (`logs/S9/persist-probe.log`, `daemon-probe.log`).
- **Pinning.** `k`, the hash, the digests and `C` come from the claim that rendered the challenge
  (S6b-A22). The recursion key is indexed from the certified `C` compiled into `harness-index`
  (S9-A41). The 128 KiB leaf cap is the runner's check (S7-A3); 1 MiB is `NARG`'s.
- **Budgets** (S9-A42). The per-step caps stay: leaf 120 s, step 600 s, indexing 1 h. The
  whole-evaluation cap is derived from them: 263,482 s ≈ 73 h at `k ≥ 26` with the defaults.
- **Results.** Each result carries `config_sha256`, `hardware_id`, `machine` (with `has_clmul`),
  the entry hashes and `entry_id` (S9-A39).

### 4.3 CI, builds, baseline

| Run | Result | Source |
|---|---|---|
| default `lake build`, fresh clone | 5 min 03 s cold, 9.1 GB; 4 s warm | `logs/S9/fresh/steps.log` |
| `scripts/ci.sh`, warm dev tree | CI OK, 15 min 0 s (12 steps) | `logs/S9/ci-harness-1.log` |
| `scripts/ci.sh`, fresh clone, no workaround, comparator from `tools.env` | CI OK, 21 min 44 s; organiser build 5 min 26 s cold; manifest 34,512 files | `logs/S9/fresh/steps.log`, `out-5-ci.log` |
| `HARNESS=1 … submissions/baseline/scripts/check.sh` (fresh clone) | CHECK OK, 5 min 54 s; harness 268 s (comparator 195 s; gate PASS, 3,639 modules, 3,596 trusted, 29 pinned) | S6b-RESULT "S9 fix pass" |

### 4.4 Smoke evaluation on `cmpToy` (NOT secure; CI step 10)

The run had 64 + 16 + 16 leaves, 32 wrap and 31 node steps, 3 runs, 100 DoS tapes and the Python
prover. Result: ACCEPT in 267.1 s.

- **Scores.** `S_rec` 0.2667 s (groups: level 2 0.2659, level 3 0.2667, levels 4+ 0.2631),
  `S_wrap` 0.2652 s, `S_leaf` 0.2662 s.
- **Checks.** 225 canaries were all rejected. The derived budget was 207,682 s.
- **`compare`.** It confirmed a faster challenger (ratio 0.454) and refused a slower one (2.138).

Source: `logs/S9/ci-harness-1.log`. The steps are dominated by process start-up: the sandbox and
cgroup add ≈ 0.07 s per process (S6b-RESULT fix pass).

### 4.5 Indexing after the sparse commitment (S9-A10; `logs/S3/s9-index-*.log`)

The run indexes `L_chain(2^10)` (792,851 serialised elements) under `cmpToy`'s rounds at class 24,
with leaves of 16:

| Index oracle | Dense (before) | Sparse (after) |
|---|---:|---:|
| `2^24` elements | 41.9 s | 5.3 s |
| `2^29` = `2^(k+5)` | 1,342 s | 105 s |
| `2^32` = the cap `2^(k+8)` | ≈ 3 h (extrapolated) | 861 s |

Memory stays at 130 MB. What remains is ≈ 200 ns per element read, ≈ 3.7 h at the cap at `k = 28`.
Removing it needs a `Protocol`-level support bound for `IDX`, or a lower entries cap (notes under
O-9/O-14).

### 4.6 Noise on this VM (a placeholder, not a reference machine)

- **The VM.** QEMU, 32 vCPUs, **no `pclmulqdq`/`gfni`**, shared (reference-machine.md §5).
- **Single processes.** They vary 13–26 %.
- **Between evaluations.** `S` moved 1.8–5.9 % between three smoke evaluations, above the 3 %
  margin.
- **Paired self-comparisons.** σ ≈ 4.7–8 % per pair, so a 3 % margin needs 35–110 pairs. In CI,
  `--calibrate` gave σ 0.047 and 35 pairs (S6b-RESULT "S9 fix pass", finding 4; CI log).

### 4.7 Kernel cost model (for controls and submitters)

- **Rates.** One BLAKE2s compression costs ≈ 2.2 s in the kernel (S3-RESULT), a `K` product
  ≈ 40–50 ms (S1-RESULT; S9F §4.5), and an honest `cmpToy` `NARG` run 35–39 s (S3).
- **Compiled.** `blake2s256` takes 5.3–7.0 µs per compression and `K` multiply-add 26.9 µs
  (S9F §4.2).
- **Consequence.** A real-scale kernel evaluation breaks the 2 h harness cap (S9F-m4).

## 5. What is tested, not proved

- **`L_chain(n)`** (`harness/gen-chain-layout.py`; design in `harness/CHAIN-LAYOUT.md`).
  - Size: `9,225·n + 786,505` cells, `k_min = 24`. `2^8` and `2^10` fit class 24, `2^12` needs 26.
  - Structure: 25 chips, 8 buses, 1,163 matrix entries, witness unique given `s` (S6a).
- **Python oracle** (`harness/check-chain.py`, shares no code with the generator).
  - It implements `rel`/`Admissible` clause by clause, and its `K` product matches Lean's on 304
    pairs.
  - Random secrets at n = 4, 16, 256, 1024 match hashlib.
  - Single-cell mutations: 744/744/744/544 at those sizes, 0 survivors.
  - Layout mutants, one per mechanism: `gate`, `addport`, `nibport`, `gouttag`, `fixed`, `nolast`,
    `selpin`, `pairport`. Each accepts a wrong chain that the real layout rejects (S6a fix pass).
  - CI step 5 reruns it at n = 16: 244 mutations, 0 survivors, 8 mutants.
- **The kernel G-call control** (`Controls/Chain.lean`), stated exactly (S6-A8). It checks:
  - completeness of the one-G-call harness on G-calls 0 and 79, one of them with the full
    `2^17`-row `add8` table (`LG0_rel`, `LG79_rel`, `LGF_rel`);
  - named single-cell faults, each rejected by the clause it names;
  - the rot-7 wrap attack, rejected only by `PAIR` (`LG0_neg_wrap`, `LG0_wrap_rest`);
  - `G_link`: the harness's G chip is `L_chain`'s except one last-row constant;
  - `Lchain_admissible`/`Lchain_not_admissible_23` on `L_chain(16)`.

  It does **not** prove that the harness computes `G` (`rel → MixStmt`), nor anything about whole
  chains. Soundness of `L_chain` is tested, not proved.
- **Python reference encoders.**
  - `probes/s3/compile_ref.py` and the reviewer's `indep_encoder.py` reproduce `NARG`'s tapes and
    roots byte for byte at arity 2, 4, 8 and 16, padded and sparse roots included (S3 fix and S9
    passes).
  - `probes/s5/recursion_ref.py` reproduces `nodeStmt`/`treeRoot`.
  - The BLAKE2s grid differential is 8,432 cases, 0 mismatches (CI step 5).
- **`treeRoot` cross-check.** The runner's Python statement tree is the executed root check; no
  certificate states `rootOK` (S9D-m2). The `selftest` checks it against the kernel KATs
  `nodeStmt_kat`, `nodeStmt_kat_keys` (distinct keys), `treeKat` and `rootOK_xT`, and it catches a
  `d0`/`d1` swap (S9-A40; CI step 5).
- **Reader = renderer.** `LayoutJson` equals `render-layout.py` through `Layout.words` on the
  example layouts (CI step 6).

## 6. Decisions made during the build (rest: `docs/DESIGN-AMENDMENTS.md`, 143 items)

| Theme | Id | Decision | Why |
|---|---|---|---|
| relation | S1-A1 | sparse gadget matrices; `cols ≤ 2^10`, Σ entries `≤ 2^(k+4)` | the index is bounded independently of the row counts |
| relation | S1-A7 | list folds over `Field.lean`'s `+ *`, not Mathlib `∑ ∏` | the trusted `K` has no ring structure; the library proves equivalence |
| relation | S1-A3/A10 | statement = cells 0…31 of row 0 of the public chip; R1CS `z = (1, x, w)` | a fixed 32-element statement; textbook R1CS with the constant wire |
| relation | S1-A11 | view = row, next row, `1`, `[r=0]`, `[r+1=rows]` | AIR boundaries and fixed patterns without selector columns |
| relation | S1-A2 | `k_range` is a `Protocol` field, not in `Admissible` | the relation is defined at every `k` |
| relation | S8-A9 | ports per chip `2^4 → 2^5` | leanerVM's BLAKE2s row has 22 interactions |
| protocol | S1-A8 | `verify` is an adaptive query program `QProg` | the compiler opens exactly the leaves a run reads |
| protocol | S1-A9 | shape caps in `shape_ok` (msg `≤ 2^(k+10)`, index `≤ 2^(k+8)`, index challenge `≤ 64` bits) | bounded tapes and exact uniform indices |
| protocol | S9-A1/A2 | 9 non-certifying trusted declarations deleted; `Secure` documented to force rejection of non-admissible layouts, total error `≤ 2^-114` | smaller reading; the obligations were unstated |
| compile | S3-A1 | a one-leaf oracle is sent in the clear | saves a root, an absorb and a leaf hash per query |
| compile | S3-A2/A11 | no Merkle leaf/node tag; fixed depth; `opening_binding` in CI | binding at a fixed depth is collision resistance; a tag doubles leaf hashing at 8 elements |
| compile | S3-A3/A8 | sponge = hash chain seeded with `VKc.digest` (VK + index root), one `D` everywhere | `C_V` computes `D` anyway; a node cannot choose its own index root |
| compile | S3-A4 | `Cfg` = hash ∈ {blake2s}, arity ∈ {2, 4, 8, 16}; no query batching | the menu grows only with Lean specs; batching changes the grammar |
| compile | S3-A5 | `tapeCap = 2^20`, leftover bytes reject, no blow-up cap | v2 measures prover time |
| compile | S3-A10, S9-A10 | the honest prover is in the Library; trusted `commit` is sparse, proved equal to the dense root | trusted text only for trusted statements; indexing the cap went from ≈ 3 h to 861 s |
| compile | D-S2-1 | BLAKE2s `rotr` by machine shifts, proved equal | the compiled hash is 13× faster (82 → 6.1 µs per block) |
| extractor | S4-A1 | the serialisation is the contract's (`Mid n j`, `extractorTape`); no submitter `enc`/`dec` | submitter code on the extractor path voids the fuel bound |
| extractor | S4-A9/A14 | `B(k) = 2^(2k+16)` is the **total** over `n+1` calls; the submitter declares the split | per-call fuel let a chained search enumerate a 64-bit secret |
| extractor | S4-A2, S7-A5 | image `≤ 2^20` bytes; `Certificate.img` binds it to the rendered claim | no lazily defined precomputed tables |
| extractor | S4-A3/A4/A5 | 2^64 memory map, tape at 2^63; `HALT` returns words; the image sees `L`, not `VK`/`IDX` | the prefix can be ~2^52 words; no copy loop; `IDX` could hide precomputation |
| extractor | S4-A10 | `B(k)` rationale: O(N²) up to ~2^(k+6), not Gaussian elimination | the original docstring claims were false (O-11) |
| recursion | S5-A1 | `aggOK` requires 32-byte key roots | else `complete` demands decoding unbounded preimages |
| recursion | S5-A3 | certificate split by board; `digestC`/`digestL` declared, recomputed by the harness | the kernel cannot commit a real index |
| recursion | S5-A4/A8/A11 | `nodeStmt` trusted; `d2 = cfg.hash(x₁‖x₂)`; `d3` = tags; `d4…d7 = 0` | one hash gadget per `C_V`; tags bound to positions; no free bits |
| recursion | S5-A10 | `live` at the indexer's keys | a secure protocol could meet `live` under a magic key (`toyCM`) |
| recursion | S5-A12 | `pairUp`/`treeRoot`/`rootOK` trusted, as the spec of the runner | one statement tree; it is in no certificate (S9D-m2) |
| benchmark | S6-A1, S6b-A8 | `k_min = 24`; leaf board `{2^8, 2^10}` at 24, `2^12` only for `k ≥ 26` | the `add8` table (786,464 cells) exceeds `2^(k−4)` below 24 |
| benchmark | S6-A2/A4 | G chip, 2 rows per G-call; `add8` lookups; tags `γ^r` pinned at both ends | the port cap; heights are forced; the witness is unique given `s` |
| benchmark | S6b-A16 | the leaf prover reads `s` and builds the tables inside its timed region | the witness is 78 MiB and a function of `s` |
| benchmark | S9-A34/A35/A36 | R only ranked; `S_rec` = slowest level group; paired ABBA record rule | S9I-M1/M2/M3 |
| harness | S6b-A1/A2 | rule 4 on the badge-path fields only; rules 3, 6, 7 against compiler access | `prover`/`ε` may be noncomputable; the S7-M1 emitted-code forgery |
| harness | S6b-A4/A5 | executables run the twin, `rfl` to the submission's `NARG`/`index`; `Fintype K` noncomputable | a real `ε` is noncomputable; a computable `Fintype` enumerated 2^64 elements at start-up |
| harness | S6b-A15 | O-12 (kernel-regenerated badge code) deferred | 2–3 days; rules plus the source rule are interim |
| harness | S6b-A17 | Clean pinned in the manifest; rules 8/9 keep it off the badge path | Clean's closure contains `Lean`, and the forgery elaborates through it |
| harness | S6b-A18 | prebuild all Mathlib objects | submissions may import any Mathlib module |
| harness | S6b-A20, S9-A30 | source rule, rebuilt as two independent nets with a keyword sweep | `ForgeRaw` passes every gate rule; S9D-M1 lexer bypass |
| harness | S6b-A21–A24, S9-A37/A38 | fail-closed sandbox, per-step cgroup, minimal root; canaries; OS-random secrets | S6b-M1, S6b-m1, S6b-m3, S9I-m3/m4 |
| harness | S6b-A22, S9-A41 | the scored `C` and the key come from the certified claim | S6b-M2, S9D-m4 |
| harness | S9-A32/A33/A42 | manifest = trusted closure; `tools.env`; derived evaluation budget | fresh clones failed (S9F-M1/M2); caps contradicted each other (S9F-M5) |
| Clean | S8-A3/A14, S8-A7 | direction from Clean's constructors; ℕ-multiset balance (`StatementPerm`) | `-1 = 1` in `K`; Clean's balance is vacuous over `K` |
| Clean | S8-A11/A13/A15 | a `ChannelMap` with pull/push pairs; `ChannelsByName` for exactness; no silent bus merges | names ≠ `RawChannel`s, so they diverge both ways without it |

## 7. Open items and readiness

| Id | Item | Owner | State |
|---|---|---|---|
| O-5 | Clean characteristic-2 balance upstream (`docs/upstream/clean-char2-balance.md`) | user / external | proposal written; the PR is the user's call |
| O-6 | Reference machine SKU, toolchain pins, noise calibration | **user** / organiser | requirements written (carry-less multiply, delegated cgroups); only VM placeholder numbers exist (§4.6) |
| O-7 | Fund a reference board-R entry | user | open; depends on O-15 (S9F-M7) |
| O-8 | Report rewrite (§6–§12, Appendix A from the v2 sources) | report | open |
| O-9 | Fast pure `K` arithmetic in the Library (compiled `K.mul` ≈ 27 µs) | library | open. Note: index reads ≈ 200 ns per element, ≈ 3.7 h at the cap at `k = 28` (S9-A10) |
| O-11 | Extractor decoder against `B(k)` | user / library | modelled (S9F §4.3): unique decoding fits with 2^3.6–2^7.6 slack; Koetter GS up to multiplicity 2 at ρ = 1/16. Still to measure: the RV64 inner loop at `k = 20`, N = 2^24, m = 2, against `B(20) = 2^56`. Wording stale (S9F-m6) |
| O-12 | Badge executables regenerated from kernel terms | organiser | open, 2–3 days plus review (S6b-A3); **required before any ranked board** |
| O-13 | Gate rule 4's `Fin`-family branch | harness | open; fails closed one stage later, never ACCEPT (S6b-A26) |
| O-14 | Circuit-friendly menu hash over GF(2^64) with a Lean spec (Vision or AES/Grøstl-style) | **user** + contract | open; **required before board R opens** (below) |
| O-15 | Three organiser assets: verified NARG gadget kit (BLAKE2s compression, Merkle, sponge); verified RS-decoder extractor image; importable IOP-soundness library | organiser / library | open (S9F §3) |
| O-16 | ZiskAccel dead arms: copy ≈ 140 trusted lines to drop ≈ 340 reached vendored lines, or split upstream and re-vendor | contract / upstream | open; S9-A5's recommended option (b), one sentence in `Machine.lean`'s header, is not applied yet |
| O-17 | The `let`-in-`IDX` trap: recomputed per element read, 190 ms per element (`probes/s3/index-bench`) | docs | documented in `submissions/baseline/README.md` §3.1 (uncommitted) |

**Review findings still open** (no fix recorded in any RESULT or amendment):

- **S9F-m1.** `scripts/harness.sh` has no `timeout` and no `MemoryMax` around the comparator,
  gate-tree build or badge build (ran: grep). A 1 h build done twice needs ≥ 2 h against the 2 h
  harness cap.
- **S9F-M7.** The docs understate the ranked-entry work (for the documentation agent).
- **S9F-m4, m7.** Submitters are not told the kernel cost model (§4.7), nor two constraints:
  LogUp-style bus arguments are unsound in characteristic 2, and `PerfectComplete` over every
  challenge excludes division.
- **S9I-m1.** The class `k` is a free parameter on board R. Keep `2·N·n·c_min > 2^28`.
- **S5-A10 residual.** `live` at a trivially satisfiable layout's key. It is closed only by
  measurement.
- **S8-A10 gaps.** `ProverData` tables and `StaticLookupChannel`.
- **One-element secret.** Enumerable at `k ≥ 25` (S4-A9).

**S9 feasibility verdict** (S9F §8), with the state since:

1. The pipeline did not run from a fresh clone. Fixed: S9-A31/A32, and the fresh clone is green
   (§4.3).
2. A real entry costs ≈ 2 × its build plus tens of minutes of replay.
3. The caps did not compose. Fixed: the budget is derived, S9-A42.
4. Indexing near the fixed point exceeded its budget. Partly fixed: §4.5.
5. **With BLAKE2s alone, `C_V` fits only at `k = 27–28`.** That is ≥ 2^26.3 cells in the most
   optimistic configuration and 2^27–2^29 in ordinary ones, and it needs Johnson-regime WHIR and a
   ≈ 5.3k-cell compression gadget (S9F §4.1, M3). Unique-decoding designs have no fixed point at
   `k ≤ 28`.

**Readiness.**

- **Board L** is published, unranked: a ranking rule, not a missing fix (S9I-M1).
- **Board W** is published, unranked.
- **Board R** is rankable only after:
  - **O-12** (the executed verifier is the proved one);
  - **O-14** decided (a circuit-friendly hash, or accept `k = 27–28`, or widen `k_range` to ≤ 30:
    S9F-M3 options);
  - the **O-15** assets exist;
  - O-6's calibration on the reference SKU (S9I verdict).

**Ranked-entry plan** (S9F §3). The first ranked R entry is **≈ 80–150 person-weeks**:
≈ 45–110k Lean plus 10–20k Rust/asm. The largest items:

- RBR-KS at 2^-128 per round: 25–50 pw;
- `C_V` `sound`/`complete` against `NARG`: 20–40 pw;
- an RS decoder in RV64 + Zbc proved against `Rv64`: 10–20 pw;
- the native prover: 8–14 pw;
- the `C_V` generator: 6–10 pw.

What the assets would save: the gadget kit cuts items 7–8 by ≈ 60–70 %, the decoder image cuts
item 4 to glue, and the IOP library cuts item 3 by about half. With all three it is "a
team-quarter", and it still fits only at `k = 27–28` without O-14.

**Reference machine proposal** (S9F §5):

- **Hardware.** Bare-metal x86-64, 32 physical cores, AVX-512 with VPCLMULQDQ and GFNI (e.g. AMD
  EPYC 9355P or 9354P, or Xeon 6 with ≥ 32 P-cores). SMT off, boost off, governor `performance`,
  C-states ≤ C1. 128 GB DDR5, local NVMe ≥ 2 TB, no GPU.
- **Software and policy.** Linux LTS with cgroup v2 delegation, bubblewrap, pinned Lean/Rust,
  Python ≥ 3.11, swap off. No other tenants. Developers get the same ISA extensions.
- **Noise protocol.** Calibration workloads of ≈ 1, 10 and 80 s, 30 repetitions × 5 sessions. The
  margin is ≥ 2 × the 95th percentile of the session-pair ratio, or use `compare --calibrate` with
  ≥ 10 self-pairs (reference-machine.md §4).

**The three decisions the user must make:**

1. **Menu hash (O-14).** Choose one:
   - fund a circuit-friendly hash over GF(2^64) with a Lean spec for the `Cfg` menu; it is the only
     lever that moves the fixed point below `k = 27`;
   - keep BLAKE2s only and accept a fixed point at `k = 27–28` (Johnson-regime WHIR, ≈ 3.7 h index
     reads at the cap at `k = 28`);
   - widen `k_range` to ≤ 30 and re-derive every `2^(k+c)` cap.

   Board R does not open before this is decided.
2. **Reference machine (O-6).** Pick the SKU (it must have `pclmulqdq`; the proposal is above) and
   the season's pins. Then run the calibration. This VM cannot host a competitive binary-field
   prover or a meaningful noise measurement.
3. **Funding now.** Fund **O-12** (2–3 days plus review; without it no ranked board is sound) and
   the **O-15** assets (without them the first ranked entry is a multi-person-year project), or
   open the season with board R unranked.

## 8. How to run everything (commands from `CLAUDE.md`, `harness/README.md`, the scripts' headers)

```sh
# fresh clone
git clone <repo> recursion.fast && cd recursion.fast
scripts/setup-clean.sh [LOCAL_CLEAN_CHECKOUT]   # offline with e.g. /home/devops/Verified-zkEVM/recursion.fast/ext/Clean
mkdir -p .lake && ln -s /home/devops/CambridgePQ/recursion.fast/contract/.lake/packages .lake/packages
#   elsewhere: lake exe cache get (Mathlib only; CompPoly's cone and Clean are then built)
#   COMPARATOR_HOME / COMPARATOR_NANODA: defaults, pins and build commands in scripts/tools.env

# build
lake build                                                   # 5 min cold, 4 s warm
lake build RecursionFastBridge RecursionFastClean gate axiomaudit
lake env lean RecursionFast/Controls/Layout.lean             # one file
scripts/org-build.sh .lake/org                               # organiser package, ≈ 5 min 30 s cold
python3 scripts/loc.py RecursionFast/Contract.lean RecursionFast/Contract/*.lean RecursionFast/Contract/Hash/Blake2s.lean
scripts/check-vendor.sh /home/devops/Verified-zkEVM/riscv-zkvm

# CI (15 min warm; ≈ 22 min from a fresh clone)
scripts/ci.sh /home/devops/Verified-zkEVM/riscv-zkvm

# baseline check (≈ 6 min with the harness)
submissions/baseline/scripts/check.sh
HARNESS=1 ORG=.lake/org MANIFEST=scripts/olean-manifest.sha256 submissions/baseline/scripts/check.sh

# generate and check a chain layout
python3 -I harness/gen-chain-layout.py layout  --n 1024 L.json
python3 -I harness/gen-chain-layout.py witness --n 1024 --secret-file SECRET W.json X.json
python3 -I harness/check-chain.py check L.json W.json X.json --k 24
python3 -I harness/gen-chain-layout.py report --n 256 1024 2048 4096
python3 -I harness/check-chain.py experiments --gen harness/gen-chain-layout.py --dir "$(mktemp -d)" \
    --n 4 16 256 --seeds 5 --mutations 300 --log LOG
harness/render-controls.sh                                   # examples + ChainData.lean

# benchmark on the smoke submission (as CI step 10; BENCH.json fields as in scripts/ci.sh `mkcfg`:
# k 26, boards L,R, verify/index = WORK/tree/.lake/build/bin/harness-{verify,index},
# prover = python3 -I harness/smoke/toy_prover.py, layouts.C = harness/examples/chain-n16.layout.json,
# claim.digestC = claim.digestL = the digest printed below, sandbox = scripts/bwrap-landrun.sh,
# sandbox_ro = [harness/smoke]; absolute paths)
harness/badge-build.sh --org .lake/org --work WORK harness/smoke RecursionFastSmoke RecursionFastSmoke.submission
WORK/tree/.lake/build/bin/harness-index harness/examples/chain-n16.layout.json VK.bin   # prints the digest
python3 -I harness/run-benchmark.py run --config BENCH.json --out RESULT.json [--workdir DIR] [--keep]
python3 -I harness/run-benchmark.py selftest --lean-data RecursionFast/Controls/RecursionData.lean --gen harness/gen-chain-layout.py
python3 -I harness/run-benchmark.py compare --calibrate --standing BENCH.json --pairs 10 --out CAL.json

# regenerate the olean manifest (after any trusted change, on the machine of record)
scripts/org-build.sh .lake/org
python3 -I scripts/olean-manifest.py gen --org .lake/org --closure .lake/org/import-allowlist.txt \
  --closure .lake/org/frontend-closure.txt scripts/olean-manifest.sha256
python3 -I scripts/olean-manifest.py check --org .lake/org scripts/olean-manifest.sha256

# add a hash to the menu: no script exists. Touch points (S3-A4: a Lean spec, 32-byte digests):
#   RecursionFast/Contract/Hash/<H>.lean + its KATs in Controls/; `HashId` and `HashId.run` in
#   Contract/Compile.lean; HASHES in scripts/render-challenge.py; `H` in harness/run-benchmark.py
#   (cfg.hash.run); then regenerate the manifest (above) and run CI. L_chain stays BLAKE2s.

# review a submission end to end (board R: R.lean.in, --badge-build RecursionFast.Challenge.leaf)
python3 -I scripts/render-challenge.py RecursionFast/Challenge/L.lean.in CLAIM.json CHALLENGE.lean
scripts/harness.sh --org .lake/org --manifest scripts/olean-manifest.sha256 --work WORK \
  --gate RecursionFast.Challenge.certified --computable RecursionFast.Challenge.submission \
  --badge-build RecursionFast.Challenge.submission \
  [--bench BENCH.json --claim CLAIM.json --stub RecursionFast/Challenge/R.lean.in] \
  CHALLENGE.lean SOLUTION_DIR COMPARATOR_CONFIG.json
python3 -I harness/run-benchmark.py record NEW.json STANDING.json [--margin 0.03]
python3 -I harness/run-benchmark.py compare --standing STD.json --challenger NEW.json [--pairs 5] --out CMP.json
```

## 9. Pointers

| What | Where |
|---|---|
| Stage results, with fix, decision and S9 sections | `docs/stages/S{1,2,3,4,5,6a,6b,7,8}-RESULT.md` (S9 fix passes: S1 "S9 cleanup", S3 "S9 fix pass", S6b "S9 fix pass", S7 "S9 README pass") |
| Reviews | `docs/reviews/S{1,2,3,4,5,6a,6b,7,8}-review.md`; `S9-definitions.md` (trust statement §5, inventory §3), `S9-incentives.md` (strategy table, incentive statement), `S9-feasibility.md` (fresh clone §1, ranked-entry plan §3, numbers §4, machine §5, verdict §8) |
| Golf / simplify reports | `docs/reviews/S{1,2,3,4,5,6a,7,8}-golf.md`, `S6b-simplify.md` |
| Change log | `docs/DESIGN-AMENDMENTS.md` (S1-A1 … S9-A44); design: `docs/DESIGN.md` (§12 open items) |
| Upstream note | `docs/upstream/clean-char2-balance.md` (O-5) |
| Probes | `probes/{clean-build,s1,…,s8}/` per stage; `probes/s9/{definitions,incentives,feasibility}/` |
| Logs (gitignored, 1.5 GB) | `logs/S<n>/`, `logs/S<n>-golf/`, `logs/S<n>-review/`; S9: `logs/S9/ci-harness-1.log`, `logs/S9/fresh/`, `logs/S9-definitions/` |
| Harness usage | `harness/README.md`, `harness/CHAIN-LAYOUT.md`, `harness/reference-machine.md` |
| Submitter's worked example | `submissions/baseline/README.md`, `submissions/baseline/prover/README.md` |
