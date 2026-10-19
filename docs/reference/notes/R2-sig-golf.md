<!-- Copied verbatim from the design workspace CambridgePQ/recursion.fast/notes/R2-sig-golf.md (research note of 2026-10-10, written against the pinned checkouts it names). Kept here so the repository is self-contained; see docs/reference/neighbouring-competitions.md for the synthesis. -->

# R2: sig.golf (research note for recursion.fast)

Source: `/home/devops/Layr-Labs/sig.golf-dev` (read-only), **HEAD `eaa0c7f97ea24fd61319d19ce1952c66ccef424f`**
(2026-09-30, "Validate submission 97dc1c8b…", a Yukon bot commit). This checkout is the Yukon-hosted
copy ("sig.golf on Yukon"), which vendors the upstream contract at the repository root. The upstream
contract revision recorded in `service/deploy/contract-revision` is `03ba352eccd9…`.

Pinned dependencies (`lakefile.lean`, `lake-manifest.json`):

| Package | Rev | Note |
|---|---|---|
| Lean toolchain | `leanprover/lean4:v4.33.1` | `lean-toolchain` |
| VCVio | `25f26bfee60d6700644eb1a69f091091948f15da` | direct `require` |
| riscv-zkvm | `4634e41b229da4256e4a1f1688b94133fffa4af0` (2026-09-08, "Merge PR #12 feat/sp1-mem-cell") | direct `require` |
| mathlib | `0df444a360ea…` (inputRev `v4.33.1`) | inherited |
| others (inherited) | PolyFun 2348446, loom2 2f65f31, cslib 268b2bb, lean-sail 8d57a8b, Cli, batteries, aesop, Qq, plausible, ProofWidgets, importGraph, LeanSearchClient | pulled in by VCVio / riscv-zkvm |

Label convention: **[V]** = verified by reading the files or running something; **[I]** = my inference.

---

## 1. RULES.md and the trusted Lean contract

### 1.1 Shape of the competition [V]

`RULES.md:3`: "Design a stateless hash-based signature scheme minimizing `S × C`: signature bytes times
maximum honest verification cycles." A submission is four RV64IM images (keygen, sign, expand,
verify), the integers `S, W, K, C`, six buffer offsets, and Lean proofs of the required statements
(`RULES.md:5-10`). Parameters (`RULES.md:12-34`, `SigGolf/Parameters.lean:14-46`): budgets 2^20 / 2^17 /
2^20 compressions for keygen / sign / expand, `FAILURE = 2^-128`, `LIFETIME = 2^32` signing requests,
`SECURITY_BITS = 127`, `CYCLE_LIMIT = 2^32`, `MAX_PROGRAM_BYTES = 2^20`, `K ≤ 128 KiB`, `S ≤ 16 KiB`,
`W ≤ 128 KiB`.

The rules are a short document (199 lines). Every Lean statement is linked from the prose by line
range (for example `RULES.md:108` links `SigGolf/Statements.lean#L21-L24`). The prose is written to
be read by a human; the Lean is the normative version (`site/llms.txt:5`: "the Lean files are the
contract. When they disagree with anything here, they win.").

### 1.2 Trusted files and size [V]

| File | Lines | Non-blank non-comment lines | Role |
|---|---:|---:|---|
| `SigGolf/Parameters.lean` | 95 | 48 | constants, byte types, `Program`, `Sizes`, `Layout`, `witnessCharge` |
| `SigGolf/Oracle.lean` | 55 | 18 | `Query`, `HashSpec`, `World`, lazy RO, counted oracle |
| `SigGolf/Riscv.lean` | 226 | 150 | image, layout validity, decoder extension, step, HASH/HALT, costs, `execute` |
| `SigGolf/Programs.lean` | 130 | 89 | `Submission`, loading, `run`, honest experiment |
| `SigGolf/Security.lean` | 124 | 60 | adversary, signing oracle, forgery game, counted experiment |
| `SigGolf/Statements.lean` | 62 | 35 | six statements and `Certificate` |
| `SigGolf.lean` + `verifier/Challenge.lean.in` | 20 | 12 | root import; challenge template |
| **Total contract** | **712** | **412** | |
| `SigGolfTests.lean` (regression checks, not part of the claim) | 237 | | |

Comments are dense and written for an auditor. Each file opens with a summary paragraph, and
`Oracle.lean:11-19` defines the VCVio vocabulary used later. **Assessment [I]:** a cryptographer who
knows some Lean can audit the 412 code lines in one or two hours. The real trusted base is larger,
because it also includes the transitive *definitions* imported from riscv-zkvm and VCVio (§1.3, §1.5).

### 1.3 How the RISC-V machine is imported [V]

`SigGolf/Riscv.lean:1-4`:

```lean
import SigGolf.Oracle
import RiscvZkvm.Rv64.Execution
import RiscvZkvm.Rv64.StepOn
import RiscvZkvm.Interpreter.Decode
```

At riscv-zkvm `4634e41b`, these three modules transitively import 9 riscv-zkvm modules totalling
**4,281 lines**. The modules are `Rv64.Basic` 739, `Word` 230, `Instructions` 298, `Execution` 1006,
`StepOn` 400, `Sp1Accel` 449, `ZiskAccel` 907, `Backend` 65, and `Interpreter.Decode` 187. They have
no imports outside riscv-zkvm (I computed this from `git show 4634e41b:…`). Many of those lines are
theorems or SP1/ZisK accelerator material that SigGolf never uses. The definitions SigGolf actually
uses are these:

- `MachineState` (`Rv64/Basic.lean:258`). Its fields are `regs : Reg → Word` and `mem : Word → Word`
  (doubleword-addressed: `getByte` reads `getMem (alignToDword addr)`), plus `code`, `pc`, and
  zkVM fields (`committed`, `publicValues`, `privateInput`, …) that SigGolf leaves unused.
  `getReg`/`setReg`/`setMem`/`setPC`/`getByte`/`writeWords`/`writeBytesAsWords` are at
  `Basic.lean:279-375`.
- `Instr` (`Basic.lean:110`), `decode` (`Interpreter/Decode.lean:73`), and `regOfBits` (`Decode.lean:30`).
- `execInstrBr` (`Rv64/Execution.lean:38`), the branch-aware per-instruction semantics.
- `memAccess` (`Rv64/StepOn.lean:116`), which gives the address, width, and store-ness of each of the
  11 load/store forms.

SigGolf builds its own pieces on top of these imports (`Riscv.lean:66-123`):
- The **W-suffixed word ops** `ADDW…REMUW` plus `SRAIW`, because "the upstream decoder … models only
  two of the ten" (`Riscv.lean:66-67`).
- Exact ECALL/EBREAK decoding.
- The memory checks (`rangeValid`, `accessValid`: in range and naturally aligned).
- HASH and HALT, and all pricing.

[I] SigGolf therefore uses riscv-zkvm as a library of per-instruction ALU and load/store semantics.
It does not use riscv-zkvm's `step`/`stepN` or its zkVM syscall model. The organizers wrote their own
small-step driver `execute` and patched the decoder's gaps locally.

### 1.4 Execution, cost, cycles, HASH [V]

Image and memory (`Riscv.lean:20-27`):

```lean
structure Image where
  code : List (BitVec 32)
  data : List Byte
def Image.byteSize (image : Image) : Nat := 4 * image.code.length + image.data.length
def dataBase (image : Image) : Nat := 16 * ((MEMORY_BYTES - image.data.length) / 16)
```

Code lives in a separate immutable space. `fetch` (`Riscv.lean:156-161`) indexes `image.code` at
`(pc - 0x1000)/4` and requires `pc ≥ 0x1000` and `pc % 4 = 0`. `ordinaryStep` (`Riscv.lean:137-147`)
returns `none` (a fault) for ECALL, EBREAK, CSR, and pseudo-instructions. For loads and stores it
requires `memoryArgumentsValid` and then calls upstream `execInstrBr`.

The cycle model (`Riscv.lean:150-154`):

```lean
def instructionCycles : Instruction → Nat
  | .base (.MUL ..) | .base (.MULH ..) | .base (.MULHSU ..) | .base (.MULHU ..)
  | .base (.DIV ..) | .base (.DIVU ..) | .base (.REM ..) | .base (.REMU ..) => 4
  | .word .mul .. | .word .div .. | .word .divu .. | .word .rem .. | .word .remu .. => 4
  | _ => 1
```

HASH arguments (`Riscv.lean:167-177`): `a0`/`a2` 8-byte aligned, `a1` a nonzero multiple of 64, and
both buffers in range. The input becomes a `Query` of `a1/64` blocks.

The driver (`Riscv.lean:204-224`) is a fuel-indexed recursion **in `OracleComp HashSpec`**:

```lean
def execute (image : Image) : Nat → MachineState → OracleComp HashSpec Execution
  | 0, state => pure { exit := .unfinished, state := state, cycles := 0, compressions := 0 }
  | steps + 1, state =>
    match fetch image state with
    | none => pure { exit := .failure, state := state, cycles := 0, compressions := 0 }
    | some (.base .ECALL) =>
      if state.getReg .x5 = 0 && hashArgumentsValid state then do
        let input := hashInput state
        let answer ← HashSpec.query input
        let result ← execute image steps (writeHash state answer)
        return result.charge (8 * input.blocks) input.blocks
      else if state.getReg .x5 = 1 then
        pure { exit := if state.getReg .x10 = 0 then .success else .failure, … cycles := 1, … }
      else pure { exit := .failure, state := state, cycles := 1, compressions := 0 }
    | some instruction => …  result.charge (instructionCycles instruction) 0
```

Observations:

- HASH is an **oracle query in the free monad**. The machine is not given a hash function. The same
  `execute` term is read three ways: against a lazy random oracle (`withRandomOracle`), against a
  fixed function (`evalWithAnswerFn hash`, used for "for every H" statements), and inside the
  counted oracle of the security game. This is the key design trick [V].
- Cost accounting is part of the semantics. HASH costs 8 cycles per 64-byte block and nothing for
  the instruction. A fetch fault costs 0 cycles, while other faults and HALT cost 1
  (`site/llms.txt:40`).
- `Submission.run` (`Programs.lean:78-85`) runs `execute … CYCLE_LIMIT (initialState …)` with fuel
  `2^32` steps and reads outputs from fixed buffers. The output is present iff `exit = .success`.
- Witness charge: `witnessCharge bytes = (bytes + 255) / 256` (`Parameters.lean:93`). It is added only
  to the honest verify cycles (`Programs.lean:117-118`).
- Loading (`Programs.lean:52-59`): data is written at `dataBase` with `writeBytesAsWords`, and inputs
  at their offsets. Offsets must be 8-aligned, because the memory is doubleword-addressed and
  `writeBytesAsWords` writes whole doublewords. `sp := dataBase`, and every other register is 0.

### 1.5 The adversary as a VCVio `OracleComp` [V]

`Oracle.lean:27-53`:

```lean
abbrev Query := (n : Nat) × Bytes (64 * (n + 1))
abbrev HashSpec : OracleSpec Query := Query →ₒ BitVec 256
abbrev Hash := QueryImpl HashSpec Id
abbrev World := unifSpec + HashSpec
def withRandomOracle {α : Type} (program : OracleComp HashSpec α) : ProbComp α :=
  (simulateQ HashSpec.randomOracle program).run' ∅
def countedOracle : QueryImpl World (AddWriterT Nat (StateT (QueryCache HashSpec) ProbComp)) :=
  (unifFwdImpl HashSpec + HashSpec.randomOracle).withAddCost hashCost
```

`Security.lean:46-48`:

```lean
abbrev Adversary (sizes : Sizes) :=
  PublicKey → Bytes sizes.cache →
    OracleComp (World + SigningSpec sizes) (Option (Forgery sizes))
```

The signing oracle (`Security.lean:51-56`) is `QueryImpl.withLogging` around
`submission.run .sign (secretKey, request.cache, request.message)`, so the adversary chooses the
cache. `game` (`Security.lean:104-116`) samples `$ᵗ SecretKey` and runs keygen (keygen failure
returns `false`). It then `simulateQ`s the adversary against forwarding plus the signing oracle,
checks the forgery (`checkForgery`, `Security.lean:89-98`, which handles both the witness and the
signature forms), and returns `decide log.WithinLifetime && forged`. `securityExperiment`
(`Security.lean:120-122`) runs the whole game, honest hashing included, under `countedOracle`, and
returns `(won, calls)`.

Unbounded adversaries: an `OracleComp` is a finite query tree. Strategies that would run forever are
handled by truncation (`RULES.md:186`, `Security.lean:11-15`): "A strategy that could run for ever is
represented by its truncations, which give up where they are cut … so a bound over all adversaries
bounds every adaptive strategy." Local computation is free, and only oracle answers and coins carry
information.

### 1.6 How probabilities and the statements are written [V]

`Statements.lean` (line numbers are the file's own):

- **Admission** (12-19): `sizes.Valid ∧ ∀ program, (image program).Valid sizes layout`, decidable.
- **Completeness** (21-24): for **every message, simultaneously**, under one oracle:

  ```lean
  def Submission.Completeness (submission : Submission) : Prop :=
    ∀ secretKey,
      1 - FAILURE ≤ Pr[= true | withRandomOracle (submission.everyMessageSucceeds secretKey)]
  ```

  `everyMessageSucceeds` (`Programs.lean:122-128`) folds `honest` over
  `(Finset.univ : Finset Message).toList`, which is all 2^256 messages. The docstring calls it "a
  mathematical definition, not something one can execute". The quantifier is ∀ secret key, not an
  average over keys.
- **Compression budgets** (26-31), an **exponential moment**:

  ```lean
  ∀ secretKey program (budget : Nat), program.budget = some budget →
    expectedValue (do let message ← ($ᵗ Message : ProbComp Message)
                      withRandomOracle (submission.honest secretKey message))
      (fun result => (2 : ENNReal) ^ ((result.compressions program : ℝ) / budget)) ≤ 2
  ```

  This gives a tail bound `Pr[N > t·B] ≤ 2^{1-t}` and still permits geometric retry/grinding
  (`site/llms.txt:66`). The `RULES.md:113` remark admits that adaptively chosen messages could cost
  more once H is fixed.
- **Verification cycles** (33-38): the bound is a **worst case over every fixed oracle**, every key,
  and every message, restricted to successful honest runs:

  ```lean
  ∀ (hash : Hash) secretKey message,
    let result := evalWithAnswerFn hash (submission.honest secretKey message)
    result.success = true → result.verificationCycles ≤ C
  ```
- **Security** (40-45): `Pr[fun (won, calls) => won = true ∧ calls ≤ Q | securityExperiment adversary]
  ≤ Q / 2^127` for every adversary and `Q ≥ 1`. The hash count includes honest calls. There is no
  separate q_H/q_S bound beyond `LIFETIME`.
- **Termination** (47-51): `∀ hash program input, (evalWithAnswerFn hash (run program input)).cycles <
  CYCLE_LIMIT`, over all typed inputs including adversarial caches, signatures, and witnesses.
  A run cut off after 2^32 steps has spent at least 2^32 cycles, so it cannot satisfy this; the
  separate "finished" flag is therefore unnecessary. That fact is proved as the regression theorem
  `unfinished_cycles` (`SigGolfTests.lean:56`).
- **Certificate** (53-60):

  ```lean
  structure Certificate (submission : Submission) (C : Nat) : Prop where
    admission : submission.Admission
    completeness : submission.Completeness
    compressionBudgets : submission.CompressionBudgets
    verificationCycles : submission.VerificationCycles C
    security : submission.Security
    termination : submission.Termination
  ```

Probabilities are VCVio `Pr[...]` and `expectedValue` in `ENNReal`. The score is not in Lean. It is
`S × C` computed by the Python checker from `claim.json`, and the Lean challenge pins `S` and `C`
(§2).

### 1.7 Auditability assessment [I]

- Strengths: about 400 code lines; a single semantic object (`execute` in `OracleComp`) serves all
  six statements; prose and Lean are cross-linked by line; and `SigGolfTests.lean` contains
  kernel-checked boundary cases (`witnessCharge 257 = 2`, misalignment, `wordResult .div` overflow,
  and toy adversaries in a fixed world).
- Hidden trust: (a) about 700 to 900 lines of riscv-zkvm *definitions* inside a 4.3k-line import
  closure. (b) VCVio's `simulateQ`, `randomOracle`, `withAddCost`, `withLogging`, `evalDist`, and
  `Pr`. VCVio is a large library, and its semantics, such as how a `StateT` cache interacts with
  `withAddCost` counting cache hits, have to be trusted. (c) Mathlib `ENNReal`. The contract is small
  only because it pushes work into these libraries.
- Changing the contract is expensive for submissions. The accepted submission was written against an
  older contract (70ba436). It carries that contract verbatim (`SigGolfCandidate/Legacy/*`, 590
  lines) plus a 1,225-line `Transfer/` proof that the two machines and runs agree. Freeze the
  contract early.

---

## 2. Verifier (`verifier/`) and scripts (`scripts/`)

### 2.1 Pipeline [V]

`verifier/verify.py:170-242` runs these steps:

1. `tools_env`: requires prebuilt `comparator`, `lean4export`, and `landrun` binaries
   (`setup_tools.sh`). Comparator is pinned at `c0c5a52d…` and built with the project's exact
   toolchain; a different minor version is refused (`setup_tools.sh:6-10,46-51`). Landrun is pinned
   at `811cfff5…`. Comparator's own test suite must pass (`setup_tools.sh:70-73`).
2. `linux_preflight` (`verify.py:63-79`): never run as root; user systemd present; **Landlock** listed
   in `/sys/kernel/security/lsm` with ABI ≥ 3 (checked by syscall 444); a real ELF landrun.
3. The trusted commit must be a canonical SHA, and it is recorded as `contract_commit`.
4. Fetch the PR at a frozen commit with bounded git output and a size check (`fetch.py`), or use
   `--local`.
5. **Source policy** `check_submission.check` (`check_submission.py:105-155`):
   - at most 1000 entries, 8 MiB per file, 16 MiB total; no symlinks or special files;
   - only `Solution.lean`, `claim.json`, and `SigGolfCandidate/**/*.lean` are allowed;
   - imports come only from `SigGolf`, its six modules, your own modules, and `Mathlib`, `ToMathlib`,
     `VCVio`, `RiscvZkvm`, `Batteries`, `Lean`, `Init`, `Std` (`:18-20`);
   - no `prelude` or `module` headers (`:57-58`);
   - `claim.json` (at most 512 bytes) has exactly `S, W, K, C, layout`, with decimal nonnegative
     integers, aligned non-overlapping buffers inside 16 MiB, and `C < 2^32` (`:69-102`).
6. Assemble a fresh project: copy the trusted `lean-toolchain`, `lakefile.lean`, `lake-manifest.json`,
   `SigGolf.lean`, and `SigGolf/`; append `lean_lib Solution`; copy the candidate files; and
   **generate `SigGolf/Challenge.lean` from `Challenge.lean.in`** by substituting
   `{{S}} {{W}} {{K}} {{C}} {{MESSAGE}}…` from the claim (`verify.py:198-213`).
7. Clone the trusted `.lake` with a reflink, then **delete any cached artifacts** for
   `SigGolfCandidate*`, `Solution*`, and `SigGolf/Challenge.*` (`verify.py:214-224`).
8. Run `lake env comparator verifier/comparator.json` inside the sandbox. A run is accepted iff the
   exit code is 0 and the log contains `Your solution is okay!` (`verify.py:235-236`).
   `score = S*C` comes from the claim (`check_submission.py:154`).

The challenge template (`verifier/Challenge.lean.in`):

```lean
noncomputable def submission : SigGolf.Submission := sorry
theorem signature_bytes : submission.sizes.signature = {{S}} := sorry
theorem witness_bytes : submission.sizes.witness = {{W}} := sorry
theorem cache_bytes : submission.sizes.cache = {{K}} := sorry
theorem layout_offsets : submission.layout = { message := {{MESSAGE}}, … } := sorry
theorem certificate : SigGolf.Certificate submission {{C}} := sorry
```

The comparator config (`verifier/comparator.json`) lists the five theorem names, `definition_names:
["SigGolf.Challenge.submission"]`, and `permitted_axioms: ["propext", "Quot.sound",
"Classical.choice"]`, with `enable_nanoda: false`. According to `site/llms.txt:125`, comparator
builds and exports the challenge, then builds and exports the solution, compares statements one by
one, and replays the solution through the Lean kernel. This is the **comparator pattern**: the
organizer's statement with `sorry` against the candidate's proof, so a candidate cannot weaken a
statement by redefining it.

### 2.2 Isolation and limits [V]

`verify.py:30-32`: `WALL_SECONDS = 4 * 3600` and `MEMORY_BYTES = 24 * 1024**3`. The systemd-run
properties (`verify.py:88-98`) are:

- `MemoryMax=24G`, `MemorySwapMax=0`, `RuntimeMaxSec=14400`;
- **`CPUAffinity` = the first 2 CPUs**. The comment reads: "Lake scales its parallel builds to visible
  CPUs; … Keep large independent Lean modules from collectively exhausting that memory limit";
- `TasksMax=512`, `RestrictAddressFamilies=~AF_UNIX`, `NoNewPrivileges`, `ProtectSystem=strict`, and
  only `.lake` writable;
- `PrivateTmp`, `PrivatePIDs`, `ProcSubset=pid`, `InaccessiblePaths=/sys`, `/etc/sig-golf`, and the
  fetched source;
- `PrivateDevices`, a tmpfs `/dev/shm`, `PrivateIPC`;
- a seccomp filter `~@network-io @debug ptrace process_vm_* pidfd_getfd kill tkill tgkill
  pidfd_send_signal`.

`linux_exec.py:20-65` re-checks inside the unit that `/dev` is private, `/dev/shm` is private, the
cwd, home, and script are read-only, the PID namespace is new, `/sys/kernel` is hidden, sockets of
four families cannot be created, and `kill(self,0)` fails. If any check fails, it refuses to run.
Comparator itself uses landrun (Landlock) for its sub-steps. Output is capped at 4 MiB and the
process group is killed at the deadline (`verify.py:116-167`). `site/llms.txt:125` publishes the limits
as "4 hours wall clock, 24 GiB, two CPUs".

The CI path (`.github/workflows/benchmark.yml`, `scripts/blacksmith.sh`) boots a sha256-pinned
Ubuntu 26.04 KVM guest (12 vCPU, 32 GB). The Blacksmith host has no Landlock, so the verifier runs
inside that guest. A trusted `.lake`, elan, and tools cache is exported **before any candidate code
runs**, and only from the default branch. The job timeout is 300 minutes. `scripts/run.py` wraps
`verify.py --local submission` and writes `scripts/score.json` with `score = S*C`. It checks that
the score equals the verifier's and is at most 2^53-1, and that `contract_commit` equals the
repository HEAD.

### 2.3 Image extraction and digests: removed [V]

The task brief assumed that images are extracted and digested. That **was** true, but it was removed
in commit `bb5ae34` (2026-09-29, "Stop extracting and recording the images"):

> "The verifier evaluated the four images with `#eval` after the proof check and published their
> digests. That runs the candidate's compiled Lean, which the candidate controls: `implemented_by`,
> an `#eval` override, or files written during the build could make the digests differ from the
> certified images. The score does not depend on them, and the published source tree already
> determines the images, so the verifier no longer extracts them …; the submission may again be
> noncomputable."

The deleted `verifier/Extract.lean` imported `Solution` and wrote `<program>.code/.data` under
`.lake/images`. Records carried a SHA-256 over the word count (4 bytes LE), the words (LE), and the
data. `README.md:25-27` still says the verifier "evaluates the four images and records their
digests". That line is **stale** [V].

**This matters a great deal for recursion.fast [I].** If the score depends on *running* the verifier
binary on a benchmark (an emulator measuring cycles on fresh R1CS instances), the image bytes must be
obtained without running candidate-controlled compiled code. Options:
(a) Require the image as a raw data file in the submission. A trusted elaborator in the trusted
challenge module reads it at elaboration time (`include_bytes`-style) and binds `submission.image`
to it, and the trusted emulator runs that same file.
(b) Have the kernel or a trusted `whnf`/`Expr` reader extract the literal term from the exported
environment (lean4export output) rather than `#eval`.
(c) Bound cost purely in Lean, as sig.golf does with a proved `C`, which needs no extraction.

### 2.4 Attack classes defended [V unless marked]

| Attack | Defence |
|---|---|
| Restating or weakening the theorem | comparator against the organizer `Challenge` (definitions and theorem names fixed) |
| `sorry`, `native_decide` (`Lean.ofReduceBool`), custom axioms | `permitted_axioms` limited to the three standard axioms; kernel replay |
| Importing hacked modules or shadowing the contract | import allow-list; no `prelude`/`module`; candidate files only under `SigGolfCandidate/` |
| Stale or poisoned build cache | candidate, solution, and challenge artifacts deleted from the cloned trusted `.lake` |
| Elaboration-time side effects (network, reading secrets, signalling the bot, writing outside `.lake`) | systemd sandbox + Landlock (landrun) + seccomp + read-only FS + private PID/IPC/dev/tmp + `InaccessiblePaths` |
| Resource exhaustion | 4 h, 24 GiB, 2 CPUs, `TasksMax=512`, 4 MiB log cap, file-count and size caps |
| Images differing between proof and record | image digests removed entirely (§2.3) |
| Claim/score mismatch | claim values substituted into the challenge; `run.py` re-checks `score == S*C` and the contract commit |
| PR head changed during fetch | `fetch.py` pins the commit and re-checks it |
| `implemented_by`/`unsafe` used inside tactics | allowed (the candidate uses it in `sym_eval`, §3.3), because the kernel re-checks the resulting `Eq.refl` [I: safe because only kernel-checked terms reach the theorem] |

---

## 3. The accepted submission (`submission/`)

### 3.1 Claim and provenance [V]

`submission/claim.json`: `S=6061, W=6348, K=131072, C=11712`, layout `{message 64, secret_key 128,
public_key 160, cache 19200, signature 13056, witness 2048}`. That gives **score 70,986,432**.
`Solution.lean:7-8` gives the breakdown: the verify bound 11,687 plus the witness charge
⌈6348/256⌉ = 25. The scheme is "SPHINCS+ with PORS+FP (forced-pruning single-tree few-time signature)"
(`Solution.lean:5`). `BASELINE.json` still records the earlier upstream baseline (PR #34/#35, S=6404,
C=11573, score 74,113,492). The checked-in submission is a later improvement, landed by Yukon bot
commits on 2026-09-28 to 2026-09-30.

`Solution.lean:27-40` is the whole interface to the challenge:

```lean
def submission : SigGolf.Submission := SigGolfCandidate.submissionNew
theorem signature_bytes : submission.sizes.signature = 6061 := rfl
…
theorem certificate : SigGolf.Certificate submission 11712 :=
  SigGolfCandidate.certificateNew
```

### 3.2 Size and per-directory line counts [V]

The submission has **958 `.lean` files, 154,526 lines, and 11 MiB** of source. That is near the
policy caps of 1000 files and 16 MiB. Every file is in the import closure of `Solution.lean`
(I computed the closure): there is no dead code.

| Directory (under `submission/`) | Lines | Files | KiB | Layer |
|---|---:|---:|---:|---|
| `SigGolfCandidate/SphincsSecurity/` | 90,534 | 734 | 5,428 | abstract SPHINCS+/PORS+FP scheme, SUF-CMA 127-bit proof, completeness |
| &nbsp;&nbsp;`…/Proof/Fts` | 20,605 | 181 | | few-time-signature (PORS+FP) games |
| &nbsp;&nbsp;`…/Proof/Residual` | 14,474 | 105 | | |
| &nbsp;&nbsp;`…/Proof/Forced` | 10,063 | 50 | | forced pruning |
| &nbsp;&nbsp;`…/Proof/Ots` | 10,043 | 126 | | WOTS-style chains |
| &nbsp;&nbsp;`…/Proof/{Hypertree,Reference,Event,Chains,Scheme,Deterministic,Base,Seeded}` | 28,523 | 243 | | |
| &nbsp;&nbsp;`…/Completeness` | 5,047 | 20 | | |
| &nbsp;&nbsp;`Scheme.lean`, `Statement.lean`, misc | 1,779 | 9 | | abstract scheme (1,182) and statement (123) |
| `SigGolfCandidate/Images.lean` | 14,906 | 1 | 1,042 | **generated** image literals (`work/py/export_lean.py`) |
| `SigGolfCandidate/Sign/` | 12,321 | 50 | 706 | sign bytecode refinement |
| `SigGolfCandidate/Verify/` | 9,530 | 61 | 492 | verify bytecode refinement and cycle bound |
| `SigGolfCandidate/Expand/` | 6,177 | 24 | 317 | expand refinement |
| `SigGolfCandidate/Equiv/` | 5,988 | 14 | 297 | refinements to the bridge's implementation equations |
| `SigGolfCandidate/Budget/` | 3,273 | 15 | 149 | exponential-moment compression budgets |
| `SigGolfCandidate/Keygen/` | 3,112 | 12 | 169 | keygen refinement |
| `SigGolfCandidate/Rv/` | 2,289 | 9 | 93 | symbolic executor, soundness, reflection tactics |
| `SigGolfCandidate/Ref/` | 1,794 | 5 | 83 | byte-level reference spec (mirrors `ref.py`) |
| `SigGolfCandidate/Bridge/` | 1,535 | 7 | 72 | abstract security to organizer game |
| `SigGolfCandidate/Transfer/` | 1,225 | 4 | 53 | legacy contract to current contract |
| `SigGolfCandidate/Final/` | 1,043 | 9 | 46 | certificate assembly (`Pending` → certificate) |
| `SigGolfCandidate/Legacy/` | 590 | 6 | 26 | verbatim copy of old contract 70ba436 |
| misc (`Submission`, `CacheBytes`, `Solution`, …) | 209 | 7 | | |

By concern [V, computed from the table]:

| Concern | Lines | Share |
|---|---:|---:|
| Abstract cryptography (scheme, security, completeness) | 90.5k | 59% |
| RISC-V refinement proofs (Rv, Keygen, Sign, Expand, Verify) | 33.4k | 22% |
| Generated image data | 14.9k | 10% |
| Glue (Ref, Equiv, Budget, Bridge, Final) | 13.6k | 9% |
| Contract migration (Legacy, Transfer) | 1.8k | 1% |

### 3.3 Architecture [V]

`Solution.lean:14-22` describes the layers:

1. **RISC-V images** (`Images.lean`). keygen has 175 instructions, sign 2,967, expand 287, and
   verify **145,952**. Of verify's instructions, 285 × 256 = 72,960 are NOPs (`verifyNopChunk =
   List.replicate 256 0x00000013`, `Images.lean:532`). That is about 584 KB of code, under the 1 MiB
   cap. There is no data section. [I] Verify is heavily unrolled and table-dispatched: the
   `tab_c0_*` labels are spaced 256 bytes apart and the code jumps into fixed-pitch slots. This
   trades code size, which is free up to the cap, for cycles.
2. **Byte-level reference** `Ref/Scheme.lean`. "Mirrors `work/py-pors/ref.py` … query for query.
   Every loop is a `List.foldlM` over an index range …". The reference functions are `OracleComp
   HashSpec` programs.
3. **Bytecode refinement**: each program's `run` equals the reference *as an equality of oracle
   computations*, including hash-call counts. For example, `Verify/Main.lean`:

   ```lean
   theorem verify_refines (m : Message) (pk : PublicKey) (w : Bytes 6348) :
       (fun r => (r.value, r.hashCalls)) <$> submission.run .verify (m, pk, w) =
         (fun p => (if p.1 then some () else none, p.2)) <$> countCalls (verifyRef m pk w)
   ```

   Equality of `OracleComp` trees is a strong, oracle-agnostic refinement. It transfers at once to
   the random-oracle, fixed-H, and counted-oracle readings.
4. **Ref ≡ abstract scheme** (`Equiv/`), "up to the oracle input format" (zero-padding to 64-byte
   blocks; `ZeroPadAssumptions`).
5. **Abstract security** (`SphincsSecurity.lean`): `security127_event : ∀ q ≥ 1, ∀ adversary,
   Pr[won ∧ calls ≤ q | experiment adversary] ≤ q / 2^127`. Completeness is per seed, with failure
   probability at most 2^-256 summed over all messages. A `#guard_msgs` on `#print axioms` (lines
   35-55) fails the build if anything beyond the three axioms appears.
6. **Bridge** (`Bridge/`) carries this to the organizer's game. **Final** (`Final/Main.lean`)
   assembles the certificate from a `Pending` record of component statements. **Transfer** moves it
   to the current contract.

The proof was organised as a **multi-agent decomposition** [V]. `Final/Pending.lean:7-25` lists the
component statements with owners ("keygen", "sign", "verify", "abstract security"): "Each is a `def …
: Prop`; the agents working on sign, verify and abstract security must prove them …". This is a
useful template for recursion.fast: the contract's statement is split into named obligations, and
separate agents discharge them.

### 3.4 How the RISC-V refinement is proved [V]

The proofs do not use `bv_decide`, `native_decide`, `grind`, or `aesop` (0 uses each). They use a
**custom verified symbolic executor and proof by reflection**:

- `Rv/Expr.lean`: a symbolic 64-bit expression language `E` over initial-state atoms (`E.reg r`,
  `E.ld a`), with smart constructors that fold constants and normalise addresses into the form
  `base + const`.
- `Rv/Exec.lean`: `symRun cfg code pc fuel : Option Result` symbolically executes straight-line code.
  It stops at ECALL, branches, and jumps, and records side-condition obligations (`Oblig`) such as
  non-aliasing and alignment.
- `Rv/Sound.lean` (599 lines): `symRun_sound`. If `symRun … = some r`, the code is at `pc`, and
  `r.obligs s` holds, then `Steps image s r.steps r.cycles (r.toState s)`. **Cycles are part of the
  executor's output.**
- `Rv/Tactic.lean`: `sym_eval` and the `sym_block` command. The compiled executor computes the
  result through `@[implemented_by evalOptResultUnsafe]`, the result is turned into a literal (with
  DAG sharing, to avoid exponential blow-up), and "the equation is then certified by the **kernel**
  alone (`Eq.refl`, checked in an auxiliary theorem, like `decide +kernel`). No
  `Lean.ofReduceBool`/`native_decide` is involved" (`Rv/Tactic.lean:4-10`). There is also a
  `kernel_theorem` command.
- These are used for keygen, sign, and expand: `sym_block` appears 196 times in 16 files. Several
  files are **generated** by Python scripts that are not shipped (`Sign/gen_code.py`,
  `tools/verify/tab_layers.py`). Example, `Sign/PackC0.lean`:
  `sym_block blk718 := symRun { noAlias := true } seg718 (pcOf 718) 441`, followed by
  `kernel_theorem blk718_words …`. Eighteen files are marked "Generated … Do not edit", and they are
  small apart from `Images.lean`.
- Verify uses **path-guided symbolic execution** (`Verify/Exec.lean`: `pathAux` follows constant
  jumps and takes branch directions from a `dirs` list, recording branch obligations `Br`). Whole
  families of blocks are checked by kernel evaluation of boolean checkers, for example
  `Verify/ChainCheckA00.lean`: `theorem chainCheck_0_0 : chainCheck 0 0 = true := by decide
  +kernel`. The file comment says "the import chain serializes this family to bound parallel build
  memory".
- Composition uses a simulation judgment with cost accounting (`Verify/Judg.lean`):

  ```lean
  def Good (s : MachineState) (N C : Nat) (X : OracleComp HashSpec Obs) : Prop :=
    ∀ F, N ≤ F → obs <$> Riscv.execute F image s = X ∧
      ∀ hash : Hash, (evalWithAnswerFn hash (Riscv.execute F image s)).exit ≠ .unfinished ∧
        (evalWithAnswerFn hash (Riscv.execute F image s)).cycles ≤ C
  ```

  plus `Good.steps` (prefix a `Steps` run) and a counting continuation `cc`. Loop bodies are proved
  once and iterated by induction. Glue is mostly `simp` (about 11k occurrences), `omega` (about 5k),
  and `rfl` (about 4.7k). There are 270 `decide +kernel` and about 1.2k `by decide`.
- **Cycle bound**: `Verify/Top.lean:11-17` defines `cycleBound := 11687` for accepting runs,
  `cycleBoundAll := 16834` for every run, and `fuelBound := 45000`. `main_good` proves
  `GoodQ s fuelBound cycleBoundAll True cycleBound (cc (verifyList …) Kb)` by threading per-segment
  costs (`layersCost 5 = 8691 := by decide`, `cost_vals` by `omega`). The cost is thus an
  arithmetic expression accumulated through the judgment. It is not measured.
- **Admission** for a 145,952-word image: plain `decide` runs out of memory or recursion depth.
  `Submission.lean:71-90` rewrites the code list into its chunks with `delta` and `List.length_append`
  so that "the kernel only counts each chunk", then applies `decide +kernel` with
  `maxRecDepth 200000`.

### 3.5 Build time [V, measured]

The full results are in `probes/sig-golf-build/RESULT.md`. The probe ran in a copy at
`probes/sig-golf-build/repo`, laid out the way `verify.py` lays out a project: `SigGolfCandidate/`
and `Solution.lean` copied in, `lean_lib Solution` appended, `SigGolf/Challenge.lean` generated from
the claim. Steps were `lake env true` → `lake exe cache get` → `lake build SigGolf` →
`lake build Solution` → `lake build SigGolf.Challenge`, each under `/usr/bin/time -v`, on all 32
cores. After that I built the pinned comparator and lean4export with v4.33.1 and ran them with
comparator's `fake-landrun.sh` shim. Go is not installed, so landrun could not be built; this
leaves out the systemd/Landlock sandbox but not the proof checking. Another agent's ArkLib build was running on the same
machine at the same time, so the wall-clock numbers are noisy and probably high.

| Step | Wall (32 cores, shared machine) | CPU | Peak RSS, one process |
|---|---:|---:|---:|
| dependency clone + `lake exe cache get` | 1:36 + 1:17 | – | 1.0 GB |
| **trusted**: `lake build SigGolf` (contract + VCVio, riscv-zkvm, loom2, PolyFun, cslib, Sail; mathlib from cache; 106 modules) | **3:23** | 812 s | 3.2 GB |
| **candidate**: `lake build Solution` (958 modules) | **16:07** | **10,172 s = 2.83 CPU-h** | **5.6 GB** (aggregate PSS peak about 11.3 GB) |
| `lake build SigGolf.Challenge` | 0:09 | 12 s | 3.2 GB |
| **comparator** `c0c5a52d` (export + statement comparison + kernel replay; Lake builds were no-ops; fake landrun shim, unsandboxed) | **23:25** | 1,416 s, single-threaded | 5.1 GB |

The comparator result was "Lean default kernel accepts the solution / Your solution is okay!", so I
confirm [V] that the checked-in submission verifies against this contract.

Elaboration time by area (sum of per-module times, 9,417 s): SphincsSecurity.Proof 58%, Verify 13%,
Sign 10%, Expand 4%, Keygen 3%, Images 2% (a single 183 s module, the slowest). The slowest
proof modules are `Verify.PorsCheckA` (77 s, kernel `decide`) and the
`SphincsSecurity.Proof.Residual.*` modules at about 50 s each.

Extrapolation to the official 2-CPU limit [I]: 2.8 CPU-h / 2 ≈ 1.4 h of elaboration, plus about
0.4 h of single-threaded export and replay, which more cores do not speed up. That is
**about 1.7 to 1.9 h of the 4 h budget**, a margin of roughly 2×. Neither memory figure comes close
to the 24 GiB cap.

---

## 4. Agent-facing guide and baseline mechanism [V]

- `AGENTS.md` (28 lines): solvers edit only `submission/`. They check with `bash scripts/setup.sh`
  and `python3 scripts/run.py`. "`BASELINE.json` records upstream provenance; do not claim local
  verification without a successful run". An optional profile must come "from actual accepting-run
  measurements … Never derive, estimate, or invent profile data." Presentation metadata goes in a
  fenced `sig-golf-presentation` JSON block and does not affect the score.
- `BASELINE.json`: source repository, commit `a28c6e97…`, PR #35 (port of #34), S/W/K/C, and score
  74,113,492, with a note that it was accepted upstream under an older contract and "verification
  against this repository's newer vendored contract is required". The baseline is a recorded
  provenance pointer, not a re-verified artifact.
- `benchmark.json` (Yukon schema v2): one track `full`, `direction: "-"`, `editablePaths:
  ["submission"]`, `setupCommand: bash scripts/setup.sh`, `benchmarkCommand: python3 scripts/run.py`,
  `scorePath: scripts/score.json`, `maxSubmissionBytes: 16777216`, and a GitHub Actions runner
  `benchmark.yml`.
- `records.json`: `{"version":1,"records":{}}`. It is empty here; Yukon does not update it, and the
  upstream bot `service/github.py` publishes records upstream.
- `site/llms.txt` (131 lines) is the **agent guide**: links, the build table, costs, a plain-language
  restatement of the six fields, the condensed game, "**Consequences that bite**" (lines 59-71),
  RISC-V quick reference, submission format with a skeleton `Solution.lean`, policy, and limits
  ("4 hours wall clock, 24 GiB, two CPUs"). The "Consequences that bite" items each "cost real
  submissions": untrusted cache needs a MAC; every signature byte must be checked (malleability is
  a strong forgery); C is a worst case; budgets are exponential moments; "expand adds advice, not
  information"; 16-byte public keys leave one bit of slack; calls versus compressions; termination
  for all inputs; sign is deterministic. [I] recursion.fast should ship an equivalent section from
  day one (for example: the verifier must check every proof byte; Fiat-Shamir transcript must bind
  the statement; termination on adversarial proofs; …).

---

## 5. Known limitations: how they are documented [V]

`RULES.md:190-199` is a flat bullet list. Each bullet names the gap, gives the real-world consequence,
and, where it can, a cheap mitigation or reference. The list:

1. classical-only adversary (NIST L1 needs about 64 quantum bits);
2. single-user security (mitigation: a per-key 16-byte public parameter in the first block, costing
   one compression);
3. MPC/threshold signing cost;
4. trading lifetime for keygen and sign speed (hypertree pruning);
5. **hash cost model** accuracy (exact for BLAKE2s, BLAKE3 up to 1 KiB, and the SHA-256 compression
   function; off for padded SHA-256 and SHA-3);
6. **ISA and metering is one choice** among many and "may not match a given zkVM";
7. delegating hashes of public values;
8. 127 vs 128 bits, with a tightness argument.

Analogues for a SNARK-verifier competition [I]:

| sig.golf limitation | recursion.fast analogue |
|---|---|
| ROM with a 64-byte-block HASH; cost model fits only some hashes | same; plus the gap between the ROM/IOP model and a concrete Fiat-Shamir hash (Poseidon2 vs BLAKE3 have very different costs in a zkVM vs natively). State which hash the cycle cost models. |
| ISA and metering are one choice | same. Also: field arithmetic in RV64IM (no native mod-p multiply, no `clmul`) skews the design space toward 31/64-bit fields. Precompiles (if any) are a policy choice. |
| classical adversaries only | same; plus quantum FS/BCS security is a different theorem (QROM). |
| single-user | multi-instance or batch soundness (many statements, one adversary); preprocessing with an adversarial index. |
| delegating hashes | prover-side grinding/PoW is "free" for the verifier, so prover cost must be bounded (sig.golf bounds sign by an exponential-moment budget; recursion.fast needs a prover budget). |
| 127 vs 128 bits | proven vs conjectured proximity gaps. Only proven regimes are provable in Lean; document the cost of that. |
| (implicit) honest cost is worst-case over oracles | recursion.fast's cost should also be worst-case over honest runs, proved, or measured by a trusted emulator on inputs it fixes. |
| (implicit) heuristic remark on adaptively chosen messages (`RULES.md:113`) | adaptively chosen statements/circuits vs. budgets measured on random ones. |

---

## 6. Implications for recursion.fast [I unless marked]

### 6.1 Reuse more or less verbatim

- **The machine `SigGolf/Riscv.lean`** (226 lines): a separate code space, 16 MiB data memory,
  aligned accesses, local W-op decoding, and fuel-indexed `execute` in `OracleComp`. Its cycle model
  (1 cycle, 4 for mul/div, 1 for HALT, 8 per HASH block) is simple and documented. The pins to reuse
  are riscv-zkvm `4634e41b` and VCVio `25f26bfe`, on Lean `v4.33.1`. Caveat: ArkLib is on v4.34.0
  (PLAN §1.11), so either port this contract (712 + 237 test lines) to v4.34 or skip ArkLib in the
  trusted base.
- **HASH as an oracle syscall** (`t0 = 0`, 64-byte blocks, 32-byte output) with
  `Query := (n : Nat) × Bytes (64 * (n + 1))`. For Fiat-Shamir in the ROM this is exactly what is
  needed. One `execute` can be read against a lazy RO (completeness), against a fixed `Hash`
  (worst-case cost and termination), and against a counted oracle (soundness with query budget Q).
- **Statement styles**: the worst case over all fixed oracles for the cost bound (`VerificationCycles`)
  and termination on all typed inputs. For soundness, a "`Pr[win ∧ calls ≤ Q] ≤ Q·ε`" form over an
  `OracleComp` adversary. Knowledge soundness needs an **extractor**, which sig.golf has no analogue
  for (unforgeability needs none). That is the main new definitional work.
- **Witness charge ⌈W/256⌉**: in recursion.fast the "witness" corresponds to the proof bytes the
  verifier reads, or to an untrusted advice tape produced by an `expand`-like helper. The
  `expand` idea, "advice, not information", maps directly: an untrusted **proof expander** may
  decompress or pre-arrange the proof for the verifier at almost no scored cost. Proof size then
  becomes a separate axis to score or cap (sig.golf scores `S`, the compact form, not `W`).
- **Exponential-moment budgets** `E[2^(N/B)] ≤ 2` for the prover (and batcher). This permits
  grinding and geometric retries while bounding tails, and it is cheap to state.
- **Verifier pipeline**: comparator with a generated `Challenge`, permitted axioms, the import
  allow-list, the policy checker, artifact purging, and the systemd + Landlock sandbox. Copy it
  almost unchanged (about 1k lines of Python and shell).
- **The `Certificate` structure** pattern: one `Prop` structure, one field per obligation, admission
  decidable.

### 6.2 Change

- **Image extraction.** If recursion.fast measures cost by running a trusted emulator on
  organizer-chosen or hidden R1CS instances, which helps against overfitting, it needs image bytes
  without running candidate code (§2.3: sig.golf removed `#eval` extraction for exactly this
  reason). Make the image a raw file read by trusted code, both in the challenge (bound to
  `submission.image`) and in the emulator.
- **Completeness over all messages** becomes completeness over all (instance, witness) pairs in the
  relation, plus a size/shape bound (circuit size up to 2^k). The honest prover can be a Lean
  `OracleComp` specification rather than RISC-V (PLAN §1.5), with its cost bounded by a budget. If
  the prover is a Lean term, the budget has to be stated on its oracle-query count and on some
  abstract op count, because Lean terms have no cycle model.
- **Scale-parameterised statements.** sig.golf has fixed-size inputs (32/16/K/S/W bytes), so every
  statement is about one finite machine. A SNARK verifier must work for every circuit size up to a
  bound, so the statements are parametric in (number of constraints, vk). The verifier image is one
  program, but its correctness proof must be **symbolic in the size**. sig.golf's path-guided
  `decide +kernel` checks over concrete unrolled code do not carry over unchanged.
- **Unrolled code.** sig.golf's best verify image is 146k instructions, half of them NOP padding,
  with costs proved per unrolled block. A size-generic SNARK verifier will have real loops whose
  trip counts depend on the vk or proof. Loop-invariant proofs (as in `Verify/Judg.lean` `Good`
  plus induction) dominate, and the reflection trick applies only to loop bodies.
- **Hard size cap, not a size-weighted score.** sig.golf caps program bytes at 2^20 and does not
  score them. The cap had a real effect: verify uses 57% of it.

### 6.3 Proof-burden and build-time risk (likely larger than SPHINCS+)

- sig.golf's accepted proof is **154.5k lines**, with 59% of it the abstract hash-based security
  argument, all in VCVio. A SNARK knowledge-soundness proof needs (i) RBR knowledge soundness of
  the IOP (sumcheck plus PCS/FRI/WHIR proximity: ArkLib has parts, with `sorry`s; see R4),
  (ii) BCS compilation with Merkle commitments in the ROM, (iii) Fiat-Shamir, (iv) an extractor
  through Merkle trees, and (v) the R1CS-to-IOP reduction. Each of (i)-(iv) is at least the size of
  sig.golf's FTS and hypertree proofs (about 20-30k lines each by analogy). An estimate of
  **2-4× sig.golf's abstract proof**, unless the contract supplies proved library lemmas
  (ArkLib/VCVio) that agents may import.
- RISC-V refinement for a verifier with field arithmetic (Montgomery/Barrett multiplication,
  extension fields) needs `bv_decide`-class bit-vector reasoning per primitive plus loop proofs. A
  Goldilocks or BabyBear mod-mul refinement is a self-contained lemma. sig.golf's refinement layers
  (33k lines for four programs and one simple algorithm per program) are a lower bound.
- **Build-time budget.** sig.golf caps verification at 4 h, 24 GiB, and **2 CPUs**. The measured
  numbers in §3.5 show what a 154k-line proof costs: 2.8 CPU-h of elaboration plus about 23 min of
  single-threaded kernel replay, roughly 1.8 h on 2 CPUs. Assuming cost is roughly linear in
  lines, that is about 1.1 CPU-min per 1k lines plus about 9 s of replay per 1k lines [I]. With
  about 10× build parallelism on this 32-core machine, that works out to roughly 16 s of wall time
  per 1k lines, so a "< 1 h" check allows about 200k lines, and the serial replay is more than half
  of that time. On 2 CPUs it is roughly 42 s per 1k lines, so one hour allows about 85k lines. Recommendation: make
  the MVP baseline well under 20k lines, for example a trivial or near-trivial NP verifier, and give
  the official verifier more CPUs than sig.golf's 2. Any competition-grade submission will need multi-hour budgets like sig.golf's. Memory per
  module is a real risk: the `decide +kernel` families had to be serialised through the import graph
  to stay under 24 GiB.
- **Contract churn is expensive.** The accepted submission carries a 1.8k-line legacy-contract
  transfer. Pin and freeze the recursion.fast contract, toolchain, and library revisions before
  agents start.
