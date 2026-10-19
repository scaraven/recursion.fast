<!-- Copied verbatim from the design workspace CambridgePQ/recursion.fast/notes/R1-ots-golf.md (research note of 2026-10-10, written against the pinned checkouts it names). Kept here so the repository is self-contained; see docs/reference/neighbouring-competitions.md for the synthesis. -->

# R1: ots.golf — structure, trusted contract, verifier pipeline, lessons

Research note for recursion.fast. Author: research subagent R1. Date: 2026-10-10.

## 0. Provenance and conventions

| Object | Location | SHA / version looked at |
|---|---|---|
| ots.golf-dev (core, trusted) | `/home/devops/leanEthereum/ots.golf-dev` | `8b140a99afa5b3e0bc785ab202c7b0a9c1f7fe7c` (2026-09-30 era, HEAD "Label the leanISA DAG line as DAG lower bound") |
| ots.golf-submissions (untrusted proofs) | `/home/devops/leanEthereum/ots.golf-submissions` (cloned for this note) | `30cff1406373fc31dee9be4a3c7c814c50944569`; its `.contract` submodule pins core `8b140a99` |
| riscv-zkvm (RV64IM semantics pinned by the contract) | `/home/devops/Verified-zkEVM/riscv-zkvm`, inspected with `git show` at the pin | `4634e41b229da4256e4a1f1688b94133fffa4af0` (local HEAD is `6810fc1`) |
| leanerVM (leanISA semantics pinned by the contract) | `/home/devops/Verified-zkEVM/leanerVM`, inspected with `git show` at the pin | `8563b05b03434851badc19715f6162fb70ffc093` |
| leanprover/comparator (the judge) | cloned to the scratchpad | `c0c5a52d2aff92b457c3e5ed4a68c1ebc5795809` (pinned in `verifier/setup_tools.sh:19`) |

Toolchain: `leanprover/lean4:v4.33.1` (`formal/lean-toolchain`). Lake dependencies (`formal/lakefile.lean:11-29`): VCVio `25f26bfe`, riscv-zkvm `4634e41b`, leanerVM `8563b05b`, cslib `268b2bb3`, PolyFun `2348446`; Mathlib `0df444a3` (tag v4.33.1) arrives transitively (`formal/lake-manifest.json`).

Paths below are relative to the ots.golf-dev root unless stated; `S:` prefixes paths in the submissions repository; `C:` prefixes paths in the comparator repository. **[V]** marks a fact I read in the cited file; **[I]** marks my inference; **[M]** marks something I measured on this machine. Line counts "total/code" use a comment-stripping counter (code = non-blank lines outside `--` and `/- -/` comments).

---

## 1. Competition structure

### 1.1 Object of the competition

[V] "How cheaply can a hash-based one-time signature be verified?" (`README.md:3`). Every claim is a Lean proof about a pinned contract; the core repo "holds no track proofs" (`README.md:5-8`). Scores are proved bounds, never measurements: there is no trusted emulator in the scoring path (the website's per-instruction tables are owner-maintained display metadata, `tools/submissions_template/RISCV_PROFILES.md:1-12`).

### 1.2 Tracks (`challenges.json:48-183`, `AGENTS.md:36-67`)

| Slug | Direction | What is scored | Model files a root may import (exact) |
|---|---|---|---|
| `lower-generality-1` ("Whole-word DAGs") | `+` (bigger better) | a proved lower bound `c` on the verification cost (compressions) of every secure whole-word DAG OTS | `Model`, `Dag`, `WholeWords` |
| `upper-compressions` | `-` | proved worst-case verification cost in compressions of an arbitrary oracle-algorithm OTS | `Model`, `Dag`, `OracleAlgorithm` |
| `upper-riscv` | `-` | proved bound on cycles of **every** execution (accepting or rejecting) of a fixed RV64IM image that exactly refines the Lean verifier | + `RiscvMachine`, `Riscv` |
| `upper-leanisa` | `-` | proved bound on cycles of every **completing** execution of a leanISA bytecode over every prover-committed memory, + 120-cycle surcharge | + `LeanIsaMachine`, `LeanIsa`, nine pinned `LeanerVM.*` modules |
| `upper-riscv-hint` | `-` | proved bound on cycles of every **accepting** execution of the same RV64IM machine over every prover-chosen "view" | + `RiscvMachine`, `Riscv`, `RiscvHint` |

[V] `Mathlib.*` and `VCVio.*` are importable by prefix on every track (`challenges.json:62-182`, `verifier/check_submission.py:149-153`).

[V] Records: lower needs `claim ≥ record + 1`, upper needs `claim ≤ record − 1` (`AGENTS.md:84-86,110,128`). Current records at submissions SHA `30cff14` (`S:records.json`): lower 90, compressions 86, RISC-V 341, hinted RISC-V 310, leanISA 1088.

[V] The cost model shared by all upper tracks: one random oracle on bit strings, one compression per started 512-bit block, at least one (`AGENTS.md:72-77`, `formal/OptimalOTS/Model.lean:70`). `challenges.json:7`: `"cost_model": "one compression per started 512-bit block of the input"`. RISC-V track: `"cycles_per_compression": 1` (`challenges.json:102`). leanISA: `BLAKE2S` = 10 cycles (`formal/OptimalOTS/LeanIsaMachine.lean:59-65`). An open maintainer note proposes "RiscV: 4 cycles instead of 1 for every hash compression (ideally find the correct cost)" (`NEXT_COMPTETION.md:1`).

### 1.3 Limits (`challenges.json:40-47`, `AGENTS.md:239-249`)

| Limit | Value |
|---|---|
| wall clock (whole comparator run) | 1200 s |
| memory | 25,769,803,776 B = 24 GiB |
| files per root | 200 |
| bytes per file | 8 MiB |
| bytes per root | 16 MiB |
| `max_claim` | 1,000,000 |
| combined stdout+stderr | 4 MiB, truncated beyond (`AGENTS.md:244-246`, `verifier/verify.py:53`) |
| `NOTES.md` read | 64 KiB (`verifier/verify.py:144`); admission receipt 48 KiB (`AGENTS.md:300-302`) |
| permitted axioms | `propext`, `Quot.sound`, `Classical.choice` (`challenges.json:9-13`) |

Track-specific size limits are *proved theorems*, not measurements: RISC-V `image_size : submission.image.byteSize < 1048576` (`AGENTS.md:130-135`), leanISA `seeded_rows : submission.seededRows < LeanIsa.maxSeededRows` (`AGENTS.md:203-210`).

### 1.4 Protected files and contract pin

[V] `challenges.json:14-39` lists 24 protected files: `challenges.json`, `formal/lean-toolchain`, `formal/lakefile.lean`, `formal/lake-manifest.json`, `formal/OptimalOTS.lean`, every `formal/OptimalOTS/*.lean` model file, every `Challenge/*.lean.in` stub template and every `verifier/comparator-*.json`. Their SHA-256 digests are pinned in `verifier/protected.sha256` (24 lines); the **contract id** is the SHA-256 of that pin file (`verifier/pin_contract.py:7-9,49-50`). Every record in `S:records.json` carries a `contract` id and a `contract_commit`.

[V] Not in the protected list: `verifier/*.py`, `verifier/Measure*.lean`, `formal/scripts/*.lean`. These are trusted by construction because `verify.py` always runs from, and copies from, the trusted checkout (`verifier/verify.py:507-520`). [I] The pin therefore defines "what statement a score refers to", not "what software checked it"; the checking software is identified by the core commit recorded per verdict (`contract_commit`).

### 1.5 Dev vs submissions repository split (`docs/repositories.md`, `AGENTS.md:274-336`)

- **ots.golf-dev** (trusted): model, stubs, verifier, website, tools; "no track proofs" (`docs/repositories.md:5`).
- **ots.golf-submissions** (untrusted): proof PRs; `main` holds the current record root per track, `records.json`, contributor files and a `.contract` git submodule pinned to a core commit for local checking (`docs/repositories.md:6,23-27`; `S:.gitmodules`).
- One way in: a PR that "creates or changes only your admitted track's submission root" (`AGENTS.md:283-285`). The bot fetches the head commit, **keeps only that root**, verifies it against the trusted core, and reports with a commit status and comment (`AGENTS.md:285-288`). Draft PRs are not queued (`AGENTS.md:287`).
- PRs are **never merged or closed**; after a durable verdict the bot copies the checked root and its registry entry into submissions `main` in a separate commit (`AGENTS.md:321-331`, `docs/repositories.md:40-47`).
- Durability: before verification, the exact head is retained under a creation-only tag `refs/tags/ots-source/<submission-id>`; receipt and verdict comments on GitHub are "the durable record"; the server is disposable and can be rebuilt from GitHub (`AGENTS.md:311-319`, `README.md:52-62`, `service/deploy/README.md` "Rebuilding the server from nothing").
- Record rule: first verified head whose claim strictly improves the record when its verification **finishes**; "a later identical or copied claim never takes a record" (`AGENTS.md:321-324`).
- Attribution: PR author plus optional `Assisted by:` and `Co-authors:` lines, frozen at admission (`AGENTS.md:292-302`).
- Knowledge sharing: each root carries a `NOTES.md` ("the idea, the result, what did not work and why, and what you would try next"), published at `ots.golf/notes.md` as untrusted text whatever the verdict (`AGENTS.md:304-310`, `llms.txt:84-86`).
- Contract changes: the website syncs the submissions `.contract` pin to the deployed core (`docs/repositories.md:71-75`); records on old contracts are ported by maintainers and listed in `service/record-revalidations.json` with `original_*` and `check_*` provenance (`S:README.md` "When a maintainer ports an existing proof ... does not transfer credit").

[V] Activity: submissions history spans 2026-09-18 to 2026-09-30 with 105 commits, 7 "Sync contract with deployed verifier" commits (`git log` of `S:`); the core has 46 commits touching `verifier/protected.sha256` between 2026-09-16 and 2026-09-25 (`git log -- verifier/protected.sha256`). leanISA records went 49335 → 33843 → 1598 → ... → 1088 within a week (`S:` git log, PRs #36-#67). [I] The contract churned heavily for ~10 days after launch; a recursion.fast contract should expect the same and budget for re-pinning and porting.

---

## 2. The trusted contract (`formal/OptimalOTS/`)

### 2.1 Size of the trusted base

[M] Lines (total / code) of every protected Lean file, and of the external semantics they import:

| File | Total | Code | Role |
|---|---:|---:|---|
| `OptimalOTS.lean` | 2 | 2 | root import |
| `Model.lean` | 126 | 56 | constants, oracle, costs, `probTrue` |
| `OracleAlgorithm.lean` | 129 | 61 | `Scheme`, `Adversary`, `experiment`, `Secure`, `Admissible` |
| `Dag.lean` | 288 | 150 | DAG model (lower track only) |
| `WholeWords.lean` | 48 | 20 | whole-word class (lower track only) |
| `RiscvMachine.lean` | 130 | 79 | loader, HASH/HALT, `execute` with cycle count |
| `Riscv.lean` | 47 | 22 | `Submission`, `Implements`, `CyclesAtMost`, `Certificate` |
| `RiscvHint.lean` | 217 | 57 | hinted loader, `Sound`, `Faithful`, `Expands`, `CyclesAtMost` |
| `LeanIsaMachine.lean` | 342 | 101 | leanISA weights, BLAKE2S-as-oracle, loop, caps, loader |
| `LeanIsa.lean` | 206 | 46 | leanISA `Submission`, `Sound`, `Faithful`, `CyclesAtMost` |
| `Challenge/*.lean.in` (5) | 90 | 29 | stubs with `{{CLAIM}}` |
| **Contract total** | **1,625** | **623** | |
| riscv-zkvm `RiscvZkvm.Rv64` import closure at `4634e41b` | 4,343 | — | 11 files: `Basic` 739, `Execution` 1006, `ZiskAccel` 907, `Sp1Accel` 449, `StepOn` 400, `Instructions` 298, `Word` 230, `Program` 142, `Bytes` 92, `Backend` 65, root 15 |
| of which the semantics actually reached by `execute` (`Basic`, `Word`, `Instructions`, `Execution`) | 2,273 | 1,498 | `Execution.lean` also contains lemmas |
| leanerVM `LeanerVM.Semantics.Execution` closure at `8563b05b` | 1,342 | — | 9 files; reaches Mathlib and `CompPoly.Fields.Binary.BF64` |

[V] The model files are unusually comment-heavy: `LeanIsa.lean` is 206 lines with 46 of code; `RiscvHint.lean` 217/57. Docstrings explain why each clause exists and what it does *not* say (e.g. the vacuity explanation in `OracleAlgorithm.lean:51-62`, the load-bearing-cap explanation in `LeanIsaMachine.lean:200-216`). [I] For the RISC-V track alone, a reader must audit about 220 code lines (450 total lines) of contract (`Model` 56, `OracleAlgorithm` 61, `RiscvMachine` 79, `Riscv` 22, stub 6) plus about 1,500 code lines of riscv-zkvm semantics, plus the relevant part of VCVio (`OracleComp`, `IsQueryBound`, `randomOracle`, `simulateQ`, `support`, `Pr[...]`), which is not small.

### 2.2 `Model.lean`: one oracle, one cost, two semantics

Load-bearing definitions (verbatim):

```lean
abbrev Query := Σ k : ℕ, BitVec k                                   -- Model.lean:61
abbrev hashSpec : OracleSpec Query := Query →ₒ BitVec hashBits      -- :64
abbrev Spec := unifSpec + hashSpec                                  -- :67
def blockCost (k : ℕ) : ℕ := max 1 ((k + blockBits - 1) / blockBits) -- :70
def CostAtMost {α : Type} (oa : OracleComp Spec α) (B : ℕ) : Prop :=
  oa.IsQueryBound B (fun t b => queryCost t ≤ b) (fun t b => b - queryCost t)   -- :78-79
def Deterministic {α : Type} (oa : OracleComp Spec α) : Prop :=
  oa.IsQueryBound () (fun t _ => t.isRight = true) (fun _ u => u)              -- :95-96
def probTrue (oa : OracleComp Spec Bool) : ℝ≥0∞ :=
  Pr[= true | (simulateQ oracleImpl oa).run' ∅]                                -- :114-115
```

- [V] No labels or domain separation: "equal strings share an answer. Explicit prefixes are part of the input and incur their full query cost" (`Model.lean:58-62`). Uniform sampling is free (`queryCost (.inl _) = 0`, `Model.lean:73-75`).
- [V] `CostAtMost` is **pathwise**: VCVio's `IsQueryBound` requires every continuation, on every answer, to fit the remaining budget, "including branches with negligible probability" (`docs/AUDIT.md:33-37`).
- [V] `oracleImpl` is a lazily sampled, cached random oracle shared by the whole experiment (`Model.lean:106-111`).
- [V] Two semantics coexist and the distinction is load-bearing: `support oa` (no cache; each query ranges independently over all answers) versus `probTrue` (cached). `probTrue oa = 0 ↔ true ∉ support ((simulateQ oracleImpl oa).run' ∅)` is proved in `formal/scripts/check-leanisa.lean:250` and `check-riscv-hint.lean:71`, so `probTrue … = 0` means "on no coherent path", not "with negligible probability" (`docs/upper-leanisa.md:36-49`).

### 2.3 `OracleAlgorithm.lean`: the security game

```lean
structure Scheme where                                   -- OracleAlgorithm.lean:24-28
  SecretKey : Type
  keygen : OracleComp Spec (PublicKey × SecretKey)
  sign : SecretKey → Message → OracleComp Spec (Option Signature)
  verify : PublicKey → Message → Signature → OracleComp Spec Bool

def experiment (S : Scheme) (A : Adversary) : OracleComp Spec Bool := do   -- :39-45
  let (pk, sk) ← S.keygen
  let (m₁, st) ← A.choose pk
  let σ₁ ← S.sign sk m₁
  let (m₂, σ₂) ← A.forge st σ₁
  let ok ← S.verify pk m₂ σ₂
  return ok && decide (σ₁.map (fun s => (m₁, s)) ≠ some (m₂, σ₂))

def Secure : Prop :=                                                        -- :63-65
  ∀ (A : Adversary) (B : ℕ), CostAtMost (experiment S A) B →
    probTrue (experiment S A) < (B : ℝ≥0∞) / 2 ^ securityBits
```

- [V] Concrete security, not asymptotic: for every adversary and every pathwise budget `B` of the **whole** experiment (adversary, honest keygen, signing and final verify), success `< B / 2^127` (`OracleAlgorithm.lean:51-65`). The adversary's non-oracle computation is unbounded and free (`docs/AUDIT.md:235`).
- [V] `Admissible` (`OracleAlgorithm.lean:117-125`) bundles: perfect `Correct` (rejection probability exactly 0 for every message chosen as a function of `pk`, `:94-101`), `VerifyDeterministic`, signing failure `≤ 2^-128`, signature size `≤ 5504` bits, `RejectsOversized`, and pathwise budgets `2^20` for keygen, sign **and verify**.
- [V] The verify budget exists only to keep `Secure` non-vacuous: "Without the verification cap the statement is vacuous — a verifier that hashes a `2 ^ 137`-bit input costs `2 ^ 128` on every path, so every valid `B` gives `B / 2 ^ 127 ≥ 2 > 1`" (`OracleAlgorithm.lean:57-62`). See §5.1 for how this was found.

### 2.4 `RiscvMachine.lean`: the RISC-V machine

**Own model or import?** [V] Both: the instruction semantics are imported from riscv-zkvm (`import RiscvZkvm.Rv64`, `RiscvMachine.lean:2`; `step` and `execInstrBr` from `RiscvZkvm/Rv64/Execution.lean:38,402` at the pin), while the competition wraps them in its **own** 130-line driver that fixes the loader, the syscalls, the admitted subset and the cycle count. The design credits Derek Sorensen's `xmss-verify-asm` (`RiscvMachine.lean:16`, `docs/upper-riscv.md:152-159`).

- [V] Machine shape: "A subset of RV64IM with the pinned `riscv-zkvm` semantics and two system calls, selected by `t0` … Harvard-style: the code is an instruction list in its own address space, separate from data memory, so a program cannot modify its code" (`RiscvMachine.lean:7-13`). riscv-zkvm's `MachineState` has `regs : Reg → Word`, doubleword-addressed `mem : Word → Word`, `code : Word → Option Instr`, `pc` (`RiscvZkvm/Rv64/Basic.lean:258-272` at the pin).
- [V] Admitted subset (`RiscvMachine.lean:37-42`): every riscv-zkvm `Instr` except pseudo-instructions `LI`, `MV`, `NOP`, the ZisK accelerator `CSRS` and `EBREAK`; branch/jump offsets must be even. The riscv-zkvm `Instr` type at the pin has 60 constructors: RV64I ALU/immediate ops, loads/stores, branches, `JAL/JALR`, `LUI/AUIPC`, `FENCE`, `ECALL`, the M extension (`MUL, MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU`) and only five W-ops (`ADDIW, SUBW, SRLW, SLLIW, SRLIW`) (`RiscvZkvm/Rv64/Basic.lean:110ff`). [I] So it is a strict subset of RV64IM (no `ADDW`, `SLLW`, `SRAW`, `SRAIW`, `MULW`, `DIVW`, ...), which a SNARK-verifier competition doing 31-bit field arithmetic would notice.
- [V] Image (`RiscvMachine.lean:45-54`):
  ```lean
  structure Image where
    code : List Instr
    data : List Byte
  def Image.byteSize (image : Image) : ℕ := 4 * image.code.length + image.data.length
  def Image.Valid (image : Image) : Prop :=
    image.code.length ≤ 262144 ∧ image.data.length ≤ 1048576 ∧
      ∀ i ∈ image.code, admittedInstruction i = true
  ```
  The program is a Lean term `List Instr`, not an ELF; there is no decoder in the trusted path. [I] The submission's image is whatever term `submission.image` reduces to; it is bound to the theorem because the theorem is *about that term* (see §3.3).
- [V] Memory layout and loader (`RiscvMachine.lean:25-30,70-80`): code at `0x1000`, data at `0x200000`, pk at `0x400000`, message at `0x400010`, signature at `0x400030`, `sp = 0x1000000`; `a0..a2` point to pk/message/signature; `a3` holds the signature bit length "capped at `maxSignatureBits + 1` to distinguish every oversized input"; only the first 5504 bits are loaded; "no parsing or scheme-specific preprocessing by the loader". Memory validity zones (`MEM_START = 0x20` … `MEM_END = 0x78000000` etc.) come from riscv-zkvm `Word.lean:86-103`; invalid accesses trap (`step` returns `none`).
- [V] Cost model per instruction: "Each instruction, including HALT, costs one cycle; HASH costs `blockCost` of its input length" (`RiscvMachine.lean:9-10`). The whole cost model is the 22-line `execute` (`RiscvMachine.lean:107-128`):
  ```lean
  def execute : ℕ → MachineState → OracleComp Spec Outcome
    | 0, _ => pure none
    | fuel + 1, s =>
      match s.code s.pc with
      | none => pure none
      | some instruction =>
        if !admittedInstruction instruction then pure none else
        match instruction with
        | .ECALL =>
          if s.getReg .x5 = 0 then
            if s.getReg .x10 = 0 then pure (some (false, 1)) else
            if s.getReg .x10 = 1 then pure (some (true, 1)) else pure none
          else if s.getReg .x5 = hashCall then
            if hashArgumentsValid s then do
              let input := hashInput s
              let answer ← hash input.2
              addCycles (blockCost input.1) <$> execute fuel (writeHash s answer)
            else pure none
          else pure none
        | _ => match step s with
          | none => pure none
          | some next => addCycles 1 <$> execute fuel next
  ```
  `Outcome := Option (Bool × ℕ)`; `none` is a trap or exhausted fuel (`:101`). Fuel "only witnesses termination; the score is the cycle count" (`:105-106`).
- [V] Hash syscall: `HASH` (`t0 = 1`) reads `a1` bits at byte pointer `a0`, LSB-first per byte (`hashInput`, `:83-86`), checks the input range and four aligned output doublewords (`hashArgumentsValid`, `:89-92`), queries the competition's single oracle on the exact bit string, writes the 256-bit answer as four little-endian doublewords at `a2` and advances `pc` ("Input is read before output is written, so buffers may overlap", `:94-98`). No dispatch fee; repeated queries are charged again (`docs/upper-riscv.md:33-43`). Kernel-checked boundary tests in `formal/scripts/check-riscv.lean:28-105` pin this behaviour by `rfl`/`decide` (e.g. `execute 1 (state [.ECALL]) = pure (some (false, 1))`, `blockCost 513 = 2`, pseudo-instructions and `CSRS` trap).
- [V] The machine is deterministic given oracle answers; riscv-zkvm's own `ECALL` semantics (SP1 `WRITE`, `HINT_READ`, etc.) are never reached because `execute` intercepts `ECALL` before `step` (`RiscvMachine.lean:115-125` vs `RiscvZkvm/Rv64/Execution.lean:402-470`). [I] The riscv-zkvm `privateInput`/`HINT_READ` machinery exists upstream but is deliberately unused.

### 2.5 `Riscv.lean`: the deterministic certificate (47 lines)

```lean
structure Submission where                                    -- Riscv.lean:18-21
  scheme : OracleAlgorithm.Scheme
  image : Image
  fuel : PublicKey → Message → List Bool → ℕ

def Submission.Implements (S : Submission) : Prop :=           -- :31-33
  S.image.Valid ∧ ∀ pk m signature,
    Option.map Prod.fst <$> S.run pk m signature = some <$> S.scheme.verify pk m signature

def Submission.CyclesAtMost (S : Submission) (c : ℕ) : Prop := -- :36-37
  ∀ pk m signature b cycles, some (b, cycles) ∈ support (S.run pk m signature) → cycles ≤ c

structure Submission.Certificate (S : Submission) (c : ℕ) : Prop where  -- :41-45
  admissible : S.scheme.Admissible
  secure : S.scheme.Secure
  implements : S.Implements
  cycles : S.CyclesAtMost c
```

[V] `Implements` is an **equality of two free-monad trees**: it forces the same query sequence and the same decision on every raw input, and the always-`some` right-hand side excludes traps and fuel exhaustion (`docs/upper-leanisa.md:52-62`). Derived (not protected) theorems in `check-riscv.lean:113-151` show that the machine-as-verifier scheme equals the specification and inherits `Secure` and `Admissible`.

### 2.6 `RiscvHint.lean`: hints (non-deterministic advice)

**What a hint is.** [V] The machine is unchanged; "what changes is the **third input**": the loader places a *view*, "a bit string chosen by whoever runs the machine", in place of the raw signature (`RiscvHint.lean:11-19`). Up to `maxViewBits = 1048576` bits are loaded, `a3` capped at `maxViewBits + 1` (`:59,68-77`). The submitter supplies a pure `compress : View → Signature` and an honest oracle computation `expand : PublicKey → Message → Signature → OracleComp Spec View` (`:97-107`). The alternative, a hint syscall or read-only hint region (SP1 `hint_read`, RISC Zero `env::read`), was rejected because it changes the machine and every theorem about `execute` (`docs/upper-riscv-hint.md:90-97`).

**How it is made sound.** Four clauses replace `Implements` (verbatim, `RiscvHint.lean:128-184`):

```lean
def Submission.Sound (S : Submission) : Prop :=
  ∀ (pk : PublicKey) (m : Message) (view : View) (n : ℕ),
    probTrue (do
      let outcome ← S.exec n pk m view
      let accepted ← S.scheme.verify pk m (S.compress view)
      pure (decide (decision outcome = some true) && !accepted)) = 0

def Submission.Expands (S : Submission) : Prop :=
  ∀ (pk : PublicKey) (m : Message) (σ : OracleAlgorithm.Signature) (view : View),
    view ∈ support (S.expand pk m σ) → S.compress view = σ

def Submission.Faithful (S : Submission) : Prop :=
  ∀ (pk : PublicKey) (m : Message) (σ : OracleAlgorithm.Signature),
    probTrue (do
      let outcome ← S.honestRun pk m σ
      let accepted ← S.scheme.verify pk m σ
      pure (decide (outcome ≠ some accepted))) = 0

def Submission.CyclesAtMost (S : Submission) (c : ℕ) : Prop :=
  ∀ (pk : PublicKey) (m : Message) (view : View) (n cycles : ℕ),
    some (true, cycles) ∈ support (S.exec n pk m view) → cycles ≤ c
```

- `Sound`: **no** view and no fuel make the machine accept unless the verifier accepts `compress view`, on every coherent oracle assignment (the cached semantics is essential: "the machine and the verifier must see the same answer for the same query", `:121-126`).
- `Faithful` + `Expands`: the honest view of every signature drives the machine to exactly the verifier's decision (completeness, both directions, absolute rather than probabilistic).
- `CyclesAtMost`: over every view and every fuel, so neither `expand` nor `fuel` can lower the score ("Quantifying over every view is what stops a program whose honest run is short but whose view-controlled loop admits an arbitrarily long accepting run", `:177-180`). Rejecting and faulting runs are not charged.
- Adaptive provers: views are quantified "plainly"; `check-riscv-hint.lean:227` proves `Submission.sound_adaptive` (soundness against a prover that queries the oracle before choosing its view) by **cache weakening**, proved in the script because "VCVio ships only the forward direction" (`docs/upper-leanisa.md:353-357`).
- Port theorem: `Riscv.Submission.hinted_certificate` (`check-riscv-hint.lean:613`) turns any deterministic certificate into a hinted one with the identity view, given that the image rejects views longer than a signature.
- Explicitly documented non-guarantee: "`Sound` constrains acceptance under a shared oracle, not compression counts. A repeated query in the specification can reuse an answer in the machine" (`docs/AUDIT.md:200-202`; `docs/upper-riscv-hint.md:462-472`). Hint delivery is free (trust item T3, `docs/upper-riscv-hint.md:499-509`).

[I] This is precisely the "verifier with untrusted advice" pattern a SNARK verifier competition needs: `Sound` is a soundness statement for the RISC-V program relative to a Lean specification, `Faithful` is completeness for an honest advice generator, and the split between `probTrue` (cached, coherent) and `support` (uncached, all paths) is the key modelling device.

### 2.7 `LeanIsaMachine.lean` and `LeanIsa.lean`: the leanISA model

- [V] leanISA is "the six-instruction ISA of leanVM-b" with semantics taken from leanerVM `8563b05b`; the contract "changes exactly two things" (`LeanIsaMachine.lean:7-8`): memory is a prover-committed immutable image `MemImage κ = Fin (2 ^ κ) → E`, κ ∈ [16, 32], and `BLAKE2S` queries the competition oracle on the exact 896 bits it consumes instead of computing RFC 7693 (`:10-24`). The other five opcodes are a catch-all arm calling `LeanerVM.Semantics.execute`, "so they cannot drift from the pinned formalisation" (`:151-176`, theorem `execute_eq_leanerVM`).
- [V] Weights: `xor, mulNative, setConstant, deref, jump` = 1, `blake2s` = 10 (`:59-65`). Ten is "a competition parameter, not a measurement"; the doc lists two rejected alternatives (bus-flush counting giving 10/10/6/10/12/22, and `blockCost 896 = 2`) (`:46-58`, `docs/upper-leanisa.md:146-176`).
- [V] Acceptance is existential ("Acceptance is the existence of a committed image that drives the run to the sentinel counter", `:14-16`), so the certificate has `Faithful` and `Sound` (`LeanIsa.lean:111-140`) like the hinted track; `Sound` quantifies over every κ in range and every image.
- [V] Anti-gaming caps: `maxProgramLogSize = 18` because `Program.code` is a *function* and `κ_bc ≤ 32` "would let a submission commit a four-billion-slot bytecode for free" and tabulate every non-hash computation (`:200-217`); `maxSeededRows = 2^20` bounds `2^κ_bc + 2^κ_mem`, a prover cost "the cycle score is blind to" (`:219-238`); `BytecodeValid` forbids `JUMP` in the halt slot (`:244-259`).
- [V] Public boundary idealised and priced: leanVM's public input is 256 bits, but the loader pins the 6016-bit statement into 47 cells; routing it through a digest "makes soundness a *cryptographic* statement … `Submission.Sound` is a `probTrue … = 0` … so it would become unsatisfiable for every program"; `boundaryCycles = 12 · 10 = 120` is added to every claim instead (`:264-318`).
- [V] Proof consequence: "Expect everything to be noncomputable. `gLog?` is `Classical.choose`-based, so no run reduces in the kernel" (`docs/upper-leanisa.md:315-320`).
- [V] Import hygiene: only nine leanerVM modules are admitted, as exact imports, because `LeanerVM.Arithmetization.*` reaches `Clean`, which "carries a sorried `Fact (Nat.Prime BN254_PRIME)` instance that typeclass synthesis could pick up with no syntactic trace" (`docs/AUDIT.md:153-156`, `docs/upper-leanisa.md:296-311`, test `verifier/tests/test_verifier.py:357`).

### 2.8 Challenge stubs

[V] Each stub is a `.lean.in` template with `{{CLAIM}}`, rendered by `verifier/render_challenge.py:20-32` from the canonical integer in `claim.txt`. Example, `Challenge/UpperRiscv.lean.in:1-18`:

```lean
import OptimalOTS.Riscv
namespace OptimalOTS.Challenge.UpperRiscv
noncomputable def submission : Riscv.Submission := sorry
theorem certificate : submission.Certificate {{CLAIM}} := sorry
theorem image_size : submission.image.byteSize < 1048576 := sorry
end OptimalOTS.Challenge.UpperRiscv
```

`submission` is a comparator **definition hole** (`definition_names` in `verifier/comparator-upper-riscv.json`); `certificate` and `image_size` are theorem targets.

### 2.9 Readability and auditability (assessment)

- [V] Strengths: every clause has a docstring stating what it guarantees and what it does not; the audit doc enumerates trusted components (`docs/AUDIT.md:10-18`) and per-track trust tables (e.g. T1-T8, `docs/upper-riscv-hint.md:482-496`); vacuity is addressed by kernel-checked companion facts (`cyclesAtMost_of_no_completion`, `sound_of_never_completes`, `boundaryCycles_le` in `check-leanisa.lean:260-468`; `sound_of_never_accepts` etc. in `check-riscv-hint.lean:78-86`); `check-axioms.lean` audits 106 contract declarations (`formal/scripts/check-axioms.lean:20-80`) and rejects any `axiom` declared in an `OptimalOTS.*` module (`:84-98`).
- [I] Weaknesses for a domain auditor: the security statement leans on VCVio's `IsQueryBound`, `simulateQ`, `randomOracle` and `Pr[...]`, and on the `support`/`probTrue` distinction, which is subtle (the docs need several paragraphs to explain it). The riscv-zkvm semantics (≈1,500 code lines, plus ZisK/SP1 accelerator files in the import closure) are pinned and trusted, not re-audited by the competition. The docstring-to-code ratio (≈2.6:1) makes the files readable but long.

---

## 3. What a submission must prove, and how vacuity and image binding are handled

### 3.1 Statements per track

| Track | Exports (statement must match rendered stub exactly) |
|---|---|
| compressions | `scheme`, `admissible : scheme.Admissible`, `secure : scheme.Secure`, `cost : scheme.VerifyCostAtMost c` (`AGENTS.md:92-99`) |
| RISC-V | `submission`, `certificate : submission.Certificate c` (= admissible ∧ secure ∧ implements ∧ cycles), `image_size` (`AGENTS.md:112-118`) |
| hinted RISC-V | `submission`, `certificate` (= admissible, secure, valid, expands, faithful, sound, cycles), `image_size` (`AGENTS.md:137-143`, `RiscvHint.lean:200-215`) |
| leanISA | `submission`, `certificate` (= admissible, secure, valid, faithful, sound, cycles), `seeded_rows` (`AGENTS.md:167-174`, `LeanIsa.lean:191-204`) |
| lower | `candidate : LowerBoundGenerality1 c` (`AGENTS.md:87-90`) |

### 3.2 Anti-vacuity devices (all [V] unless noted)

1. **Security is bundled with correctness and resource bounds.** `Secure` alone is satisfied by a scheme that accepts nothing; `Admissible.correct` forces acceptance of honest signatures, and `Faithful`/`Implements` force the machine to accept them too: "`Admissible.correct` forces `scheme.verify` to accept something, `faithful` forces an accepting honest run there, and `secure` forces that run to hash" (`RiscvHint.lean:192-195`, `LeanIsa.lean:184-186`).
2. **Budgets on honest parties**, so that the concrete-security bound `B/2^127` cannot be inflated (`verifyBudget`, §5.1).
3. **Two-sided machine ↔ spec ties.** "`Sound` alone would be satisfied by a program with no valid execution at all … `Faithful` alone would be satisfied by an under-constrained program" (`LeanIsa.lean:29-33`).
4. **Score clauses quantify over all adversarial witnesses** (every view/image, every fuel/step count) so prover-side witnesses cannot lower the score (`RiscvHint.lean:94-96`, `LeanIsa.lean:47-48`).
5. **Size caps proven, not measured**, to block free lookup tables: `Image.Valid` and `image_size` (RISC-V), `maxProgramLogSize` and `seeded_rows` (leanISA). "`valid` bounds the image, without which a free lookup table would absorb every non-hash cost" (`RiscvHint.lean:192-193`).
6. **Loader length sentinel** (`a3` capped at max+1) so oversized inputs are distinguishable (`RiscvMachine.lean:65-69`).
7. **Machine-checked statements of non-guarantees** in `formal/scripts/` (vacuity on programs that never complete or never accept), so reviewers can see exactly when each clause bites.
8. [V] Strong unforgeability is stated once, on signatures; for hints, "a second accepted view of the honest signature is not a forgery" (`RiscvHint.lean:33-40`, `docs/upper-riscv-hint.md:398-411`). [V] The general quantitative transfer of security from spec to hinted machine "is not a Lean theorem here" (`docs/upper-riscv-hint.md:428-431`): it is a prose argument.

### 3.3 How the exact program image is bound to the theorem

- [V] The image is a field of the submitted term (`Riscv.Submission.image : Image`, `Riscv.lean:20`), and every clause (`Implements`, `CyclesAtMost`, `image_size`) is a statement about `submission.image`. The comparator checks the *statement* of `certificate : submission.Certificate c` and that `submission` is a definition of type `Riscv.Submission` with matching name/type/universes/safety; it then replays the solution's definitions, including `submission`'s value, in the kernel (`C:Comparator/Compare.lean:63-108`, `C:Main.lean:199-212`). [I] Hence the program that the theorem is about is exactly the closed Lean term `submission.image`; there is no separate binary whose correspondence must be trusted.
- [V] The verifier optionally extracts the image size *from the kernel-replayed export*, never from candidate output: `verifier/MeasureRiscv.lean:43-64` re-runs comparison and axiom checks, replays the export into a fresh environment, then `Kernel.whnf`s the two list fields to count instructions and data bytes. This is display metadata only ("A failure here leaves an already verified certificate and its score unchanged", `verifier/verify.py:331-335`).
- [V] A submission's own NOTES report an "independent generator reproduces the Lean-exported … record image (canonical JSON sha256 …)" and 16,330 byte-memory executions on an external harness (`S:formal/Submissions/UpperRiscv/NOTES.md` "Validation"), i.e. agents test outside Lean before proving.
- [I] Gap for a deployment: nothing exports the image to an ELF or binary for a real zkVM; a recursion.fast competition that wants a deployable RISC-V verifier would need a trusted, audited Lean-to-bytes emitter or an in-Lean encoder/decoder pair.

---

## 4. Verifier pipeline

### 4.1 Steps (`verifier/verify.py:1-24`, `401-628`)

1. **Preflight** (Linux): refuse to run as root, require `systemd-run`, Landlock in `/sys/kernel/security/lsm`, a real compiled `landrun` ELF, Landlock ABI ≥ 3 (`verify.py:265-288`); dedicated bounded work volume (`verifier/linux_storage.py`, `service/deploy/README.md:17-20`: "at most 64 GiB … Memory and time limits do not prevent a submission from filling a disk"). macOS runs unsandboxed and is documented as development only (`README.md:40-42`).
2. **Export only the submission root** from the PR head: flat regular files only (modes 100644/100755), no symlinks/FIFOs/subdirectories/submodules, sizes checked before reading, blobs read directly so attacker-controlled `export-ignore`/`export-subst` are ignored, commit argument cannot inject options (`verify.py:156-262`).
3. **Lay it over a copy of the trusted tree**, allowlisted (only `challenges.json`, `verifier/`, `formal/` minus `.lake`, the submission root and the rendered challenge) (`verify.py:507-520`).
4. **Policy**: `pin_contract.py check` (protected files match the pin) then `check_submission.py` (flat root, `Solution.lean` and `claim.txt` present, canonical claim, header imports restricted to allowed prefixes/exact modules/siblings, no `prelude`/`module`/modified imports, comments cannot hide header commands, quoted identifiers cannot escape prefixes) (`verify.py:521-537`; `check_submission.py:30-162`; `contract.py:9-55`).
5. **Warm cache**: clone the trusted prebuilt `.lake` with reflinks, then delete this track's build products and all `OptimalOTS/Challenge` oleans so the submission is compiled for the first time inside the sandbox (`verify.py:538-546`). Mathlib/VCVio are prebuilt; "No network" (`AGENTS.md:246`).
6. **Render** the stub with the claim (`verify.py:548`).
7. **Run comparator** under a transient systemd *user service*: `MemoryMax`, `MemorySwapMax=0`, `RuntimeMaxSec`, `KillMode=control-group`, `TasksMax=512`, `RestrictAddressFamilies=~AF_UNIX`, `NoNewPrivileges`, `ProtectSystem=strict` with only the job's `.lake` writable, `PrivatePIDs`, `ProcSubset=pid`, `InaccessiblePaths=/sys /etc/ots …`, `PrivateDevices`, private `/dev/shm`, `PrivateIPC`, and a syscall filter denying `@network-io @debug ptrace process_vm_* pidfd_getfd kill tkill tgkill pidfd_send_signal`; the environment is cleared to `PATH`, `HOME`, `LANG` and tool paths ("the worker's carries the GitHub token and the webhook secret") (`verify.py:291-326,549-574`). A launcher (`verifier/linux_exec.py`) re-checks that the restrictions are effective before starting comparator, and `verifier/check_linux_sandbox.py` is a host probe (`service/deploy/README.md:112-135`).
8. **Verdict**: `verified` iff exit 0 and output contains "Your solution is okay!"; else `rejected` / `policy_rejected` / `timeout` / `failed` (`verify.py:602-625`). For RISC-V/leanISA tracks, the optional size measurement then runs in its own 300 s sandbox (`verify.py:329-386,606-616`).

### 4.2 What comparator checks (`C:README.md:29-62,157-180`, `C:Main.lean`, `C:Comparator/*.lean`)

- Build `Challenge` and `Solution` with `lake build` inside landrun (read whole FS, write only `.lake`), then export each with `lean4export` in a sandbox with no writable paths (`C:Main.lean:115-151`, `273-288`). "We generally adopt a policy of not loading olean files" into the judge (`C:README.md:157-160`).
- **Statement comparison** (`C:Comparator/Compare.lean:37-108`): for each theorem target, the solution's type must equal the challenge's; then *every constant transitively used by those statements* must be identical (`ConstantInfo` equality, values included) between the challenge export and the solution export. Definition holes match on name, type, universe levels and safety only; their value is not compared. Kernel primitives (`Nat.add` … `eagerReduce`) are always included (`C:Main.lean:214-239`).
- **Axiom audit** (`C:Comparator/Axioms.lean:52-70`): the transitive closure of every target (theorems and definition holes) may use only permitted axioms.
- **Kernel replay** (`C:Main.lean:199-212`): the solution export is replayed into `Lean.mkEmptyEnvironment` (optionally also nanoda; disabled in every ots.golf config, e.g. `verifier/comparator-upper-riscv.json`).
- Toolchain policy: comparator is built with the project's exact toolchain (minor version must match; only the patch digit is overridden) and its own test suite must pass (`verifier/setup_tools.sh:6-10,46-54,70-73`).
- Comparator's own caveat: definition holes "can be gamed without additional oversight … all definition hole solutions **must** always be checked with an additional (potentially human) verifier" (`C:README.md:70-92`). [I] ots.golf neutralises this by design: the theorems pin the hole so completely that "any term of the stated type is admissible" (`AGENTS.md:101`); any `submission` satisfying `Certificate c` is a legitimate win. A recursion.fast contract must have the same property.

### 4.3 Attack classes and the defence for each

| Attack | Defence | Evidence |
|---|---|---|
| `sorry` | `sorryAx` fails the axiom audit | `AGENTS.md:240-242` [V] |
| `native_decide` / `Lean.ofReduceBool` / `ofReduceNat` | non-permitted axiom; refused | `AGENTS.md:241-242` [V] |
| new `axiom` declarations | axiom audit; `check-axioms.lean` additionally rejects axioms declared in protected modules | `formal/scripts/check-axioms.lean:84-98` [V] |
| `implemented_by`, `@[extern]`, `@[csimp]` | only affect compiled code; kernel replay checks declared values (an `opaque` cannot be unfolded by the kernel) | [I] not discussed explicitly in the repo; follows from kernel replay. Submissions use none (`grep` of `S:formal/Submissions/UpperRiscv`: 0 occurrences) [M] |
| environment manipulation by metaprograms (adding unchecked declarations, `debug.skipKernelTC`, rewriting contract constants in the environment) | export via `lean4export` and replay into an empty environment; challenge built separately; all statement dependencies compared constant-by-constant | `C:README.md:157-180`, `C:Compare.lean:37-59` [V] |
| import shadowing / redefining a contract module | lakefile globs `Submissions.*` for submitted code (`formal/lakefile.lean:35-37`); only the admitted root is copied; contract modules are exact imports; protected files pinned; comparator's transitive constant equality catches any changed dependency | `check_submission.py:149-160`, `verify.py:507-526` [V] |
| sorried **instances** in transitive dependencies (Clean's BN254 `Fact`) | exact-module import allowlist (not prefix) plus axiom audit | `docs/AUDIT.md:153-156`, `docs/upper-leanisa.md:296-311` [V] |
| stale or planted build products | delete track oleans and challenge oleans from the cloned cache before building | `verify.py:543-546` [V] |
| header tricks (`prelude`, `module`, `meta import`, comments hiding commands, BOM, quoted module names) | `check_submission.header_imports` and tests | `check_submission.py:30-83`; `verifier/tests/test_verifier.py:148-199` [V] |
| runtime module loads by metaprograms | **not** restricted; documented as such; soundness rests on comparator | `docs/AUDIT.md:23-29`, `AGENTS.md:234-237` [V] |
| claim injection | canonical-integer regex, bounded read, stub rendering | `verifier/contract.py:9,39-55` [V] |
| sandbox escape, exfiltration of tokens, network | systemd + Landlock + syscall filter + cleared env; GitHub credentials only in the web service | `verify.py:291-326`; `service/deploy/README.md:58-63` [V] |
| resource exhaustion (memory, time, output, disk, PIDs) | MemoryMax, RuntimeMaxSec, 4 MiB log cap, dedicated ≤ 64 GiB volume, TasksMax | `verify.py:53,296-301`; `service/deploy/README.md:17-20` [V] |
| git-level tricks (symlinks, submodules, attributes, nested trees, option injection) | blob-level export with mode checks | `verify.py:204-262`; tests `test_git_*` [V] |
| record sniping / copied claims | first strict improvement by finish order | `AGENTS.md:321-324` [V] |
| semantic gaming of the contract (vacuous security, lookup tables, unbounded memory, hint-controlled loops, fuel) | contract-level clauses of §3.2 | §5.1 [V] |

[V] Not used: SafeVerify, lean4checker; nanoda is available in comparator but disabled (`enable_nanoda: false` in all five configs). [I] A second kernel (nanoda) is a cheap hardening option for recursion.fast if replay time allows.

---

## 5. Documentation: lessons learned and proof techniques

### 5.1 Lessons from `docs/AUDIT.md` and the git history

1. **A vacuity bug shipped and was found after launch.** Commit `30e33a7` (2026-09-21) "Cap verification cost so Secure is not vacuous": a verifier hashing one `2^137`-bit input costs `2^128` on every path, so no `B < 2^128` is a valid budget and `Secure` becomes `probTrue < B/2^127 ≥ 2`; "A scheme with a fixed public key, an empty signature for every message and that one query is admissible and secure under the old definition, and is forged with probability 1. This was checked in Lean against the previous contract." Exposure was the leanISA track only, because RISC-V's `Implements` equates oracle computations and so charges the verifier's hashing in cycles (`git show 30e33a7`; `docs/AUDIT.md:76-84`). [I] Lesson: in concrete-security statements where the budget covers honest parties, every honest party needs an explicit cost cap; and decision-only ties (Sound/Faithful) do not transfer costs.
2. **Decision agreement does not transfer compression costs** (`docs/upper-riscv-hint.md:462-472`, commit `705419a` "remove the unproved hinted lower-bound reference"): a spec querying `H(x)` twice and a machine querying once decide identically under a cache. [I] For recursion.fast: a soundness statement relative to a spec does not bound the machine's cost; costs must be measured on the machine itself.
3. **Free lookup tables** must be bounded by proved size caps (RISC-V image < 1 MiB added in commit `b38f3c5` on 2026-09-21; leanISA `maxProgramLogSize`). The record RISC-V image is 15,616 instructions / 62,552 bytes, mostly jump tables (`S:formal/Submissions/UpperRiscv/NOTES.md` "341-cycle candidate"; `Solution.lean:16`).
4. **Prover-side costs invisible to the score** must be capped separately (`seeded_rows`, `docs/AUDIT.md:158-164`), and `expand`/`prover` carry no cost bound — an acknowledged open question (`docs/upper-riscv-hint.md:522-530`).
5. **Cryptographic soundness vs `probTrue = 0`.** Binding a long statement through a digest makes an "on every coherent path" soundness statement unsatisfiable (collisions exist on some assignment); the contract idealised the boundary and priced it (`LeanIsaMachine.lean:264-286`). [I] Directly relevant: recursion.fast soundness statements over Merkle/FS hashing must be *probabilistic*, not `= 0`.
6. **Trusted upstream gaps are stated, not hidden**: `run` vs arithmetization closed walks, a blocked leanerVM Layer 9 (`docs/AUDIT.md:139-143`, `docs/upper-leanisa.md:222-235`).
7. **Retiring tracks** with "an exact contract compatibility mapping" to preserve history (`792ac43`); strengthening `Admissible` "is not a pure addition", so results were audited per track (`30e33a7`).
8. **VCVio findings**: only the forward cache-monotonicity lemma exists upstream; `QueryCache` `≤` elaborates to the wrong instance silently (`docs/upper-leanisa.md:351-362`).

### 5.2 Proof techniques used for RISC-V programs

- [V] **Hand-built refinement calculus with symbolic execution by rewriting**, written by the submitters inside their root. `S:formal/Submissions/UpperRiscv/Refines.lean:14-17` defines `Refines fuel s q c := observe fuel s = q ∧ ∀ b cycles, some (b, cycles) ∈ support (execute fuel s) → cycles ≤ c`, with composition rules for straight-line blocks (`Refines.steps`, `Refines.linear` via `List.foldl execInstrBr`), hash calls (`execute_hash`) and halts. Programs are proved region by region (`IndexPhase`, `ChainPhase` by induction over chains, `RootPhase`) and composed (`docs/upper-riscv.md:136-146`).
- [V] **riscv-zkvm's proof tooling is not used and cannot be imported**: submissions may import only `Mathlib.*`, `VCVio.*`, exact contract modules and siblings, and `RiscvZkvm.Rv64.Logic.*` (separation logic, WP, `SymStep`, `RunBlock` tactics) is outside the `RiscvZkvm.Rv64` closure. Across all five record roots the only non-sibling imports are Mathlib, VCVio, contract modules and two `LeanerVM` modules [M] (`grep "^import"` over `S:formal/Submissions/*/*.lean`).
- [M] Tactic profile of the 341-cycle RISC-V root (100 files, 20,660 lines): `simp` 1,376, `rfl` 827, `omega` 785, `decide` 362 (`by decide` 201), `norm_num` 228; `bv_decide` 0, `grind` 0, `native_decide` 0 as a tactic (1 mention in a comment); `maxRecDepth` raised 15 times, `maxHeartbeats 4000000` twice. Kernel-evaluated `decide` is used for concrete facts (counts such as `comp 32 160 = 44383521204130784290044027201113527 ≥ 2^115`, `docs/upper-riscv.md:84-89`), and `check-riscv.lean` tests machine behaviour by `rfl` on hand-built states.
- [V] Programs are generated by Lean functions over tables of offsets, not written as literal instruction lists (`S:formal/Submissions/UpperRiscv/MixedProgram.lean:22-60`).
- [V] Agents pair each Lean proof with **external differential testing** (16,000+ byte-level executions per candidate against a reference, exhaustive over relevant parameter ranges) before proving (`S:.../UpperRiscv/NOTES.md`).
- [V] leanISA proofs cannot `decide` an execution; they peel runs with `run_succ_of_ne`, `run_intermediate`, `run_prefix` (`docs/upper-leanisa.md:315-320`); the record root is 175 files / 102,529 lines / 6.5 MB, dominated by generated data tables (`FreeLastLayoutData.lean` 31,305 lines, `SplitTables.lean` 13,672) [M].
- [V] Security proofs (compressions and all upper tracks reuse them) are VCVio game-hopping proofs: lazy-oracle keygen analysis, identical-until-bad (`IUB.lean`), potentials and a row inequality (`docs/upper-bound-proof.md:56-70`).

### 5.3 Reported proof sizes, check times and limits

[M] Submission sizes at `S:30cff14`:

| Root | Files | Lines | Bytes | Claim |
|---|---:|---:|---:|---:|
| `LowerGenerality1` | 26 | 3,814 | 163,952 | 90 |
| `UpperCompressions` | 44 | 26,403 | 1,162,023 | 86 |
| `UpperRiscv` | 100 | 20,660 | 924,559 | 341 |
| `UpperRiscvHint` | 90 | 21,838 | 984,616 | 310 |
| `UpperLeanIsa` | 175 | 102,529 | 6,520,901 | 1088 |

[V] Reported check times (submitter NOTES; local unless "hosted"):

- RISC-V 358-cycle record: **836.1 s hosted** (`S:.../UpperRiscv/NOTES.md:473`). Standalone export+compare+replay of ≈22,250 declarations: 186-226 s, peak PSS ≈ 8 GB (`:97-98,193-194,403`); full local run 291 s (`:529`).
- Hinted RISC-V: export+compare+replay 98-241 s, peak PSS 5-10 GiB; 22,928-23,094 exported declarations (`S:.../UpperRiscvHint/NOTES.md:305,424,491,545`).
- Compressions 86: clean build 254 s, solution export 138 s (export file **463 MB**), kernel replay of 103,046 declarations 320 s, total 772 s, peak PSS 10.2 GiB; a predecessor took 1035 s locally and **timed out hosted at 1230.6 s** (`S:.../UpperCompressions/NOTES.md:220-246`).
- leanISA 1088: original head "compiled successfully on the hosted runner but timed out during the full verification pipeline"; its 1102 s local check "provided insufficient runtime margin"; the revision refactored proofs to reduce check time (`S:.../UpperLeanIsa/NOTES.md:75-80`).
- A hinted submission was rejected because local elaboration used default `autoImplicit` while the pinned project sets it false (`S:.../UpperRiscvHint/NOTES.md:67-81`). [I] Agents must check through the exact pinned Lake project.

[M] My own measurement on this machine (32 cores, 62 GB): see §8.1.

---

## 6. `AGENTS.md`: the submission specification for agents

[V] Summary of `AGENTS.md` (353 lines): layout (`:20-34`); frameworks/tracks (`:36-70`); oracle model (`:72-77`); exact exports per track with the stubs' declarations (`:79-210`); root rules (`:212-249`: flat directory of identifier-named `.lean` files plus `claim.txt`, optional `NOTES.md`/`README.md`; `Solution.lean` required; one plain `import` per line; allowed imports table; canonical claim ≤ 1,000,000; axioms; limits 200 files / 8 MiB / 16 MiB, 20 min, 24 GiB, 4 MiB output, no network, prebuilt Mathlib/VCVio; exact toolchain); local check commands (`:251-272`); submission workflow, attribution, NOTES journal, retention tags, record rule, bot snapshot (`:274-336`); website maintenance rules for maintainers (`:338-353`). `llms.txt` (144 lines) is the agent-facing quick guide served at `ots.golf/llms.txt`; it repeats the rules and tells agents to read the notes journal and treat notes "as untrusted" (`llms.txt:84-86`).

[V] Notable agent-facing statements: "a `decide` over large naturals can exceed the budget" (`AGENTS.md:246-247`); "This list restricts explicit source-header imports … It does not restrict runtime module loads by Lean metaprograms or certify where a proof was obtained" (`:234-237`).

---

## 7. Reusability for a SNARK-verifier competition

### 7.1 Directly reusable

- **The RV64IM wrapper** (`RiscvMachine.lean`, 79 code lines): Harvard image as `List Instr` + `List Byte`, raw-input loader with length sentinel, `HALT`/`HASH` syscalls, fuel-indexed `execute` returning `Option (Bool × ℕ)` in `OracleComp Spec`, one cycle per instruction and `blockCost` per hash. A recursion.fast machine could keep this shape and add syscalls (e.g. field-op or `clmul` precompiles) as further `ECALL` arms with explicit prices. [I]
- **The hinted certificate pattern** (`RiscvHint.lean`): `Sound` (no advice makes the machine accept what the spec rejects, cached oracle), `Faithful` + `Expands` (honest advice reaches the spec's decision), `CyclesAtMost` over all advice and all fuel, and the adaptive-prover lemma via cache weakening. A SNARK verifier reading a serialized proof is exactly "a machine reading prover-chosen bytes". [I]
- **Cost model as a Lean definition** (no trusted emulator), proved worst-case bounds, `support`-based cycle clauses. [I]
- **Verifier pipeline**: comparator (pinned to the toolchain minor), definition holes for the submitted artifact, rendered claim stubs, protected-file pin with contract id, root-only export, header policy, warm-cache clone with stale-artifact removal, systemd+Landlock sandbox, durable GitHub receipts, never-merge PRs, bot record snapshots, NOTES journal. Almost all of `verifier/` is generic. [I]
- **Audit practice**: per-track trust tables, machine-checked vacuity facts in unprotected scripts, `check-axioms.lean` over contract declarations, exact-module import allowlists to avoid sorried instances in transitive dependencies (ArkLib has `sorry`s; R4 should confirm which modules). [I]

### 7.2 What would not scale (or needs redesign)

- **Proof-checking time is already the binding constraint for OTS-sized programs.** The 358-cycle RISC-V record (an image of the same family as the current 341-cycle, 15,616-instruction one) needed 836 s hosted against a 1,200 s limit; two submissions on other tracks timed out after successful builds; kernel replay alone is 190-320 s for 22k-103k exported declarations, with 8-10 GB peak memory and a 463 MB export file. A SNARK verifier (Merkle path checks over many queries, sumcheck rounds, field arithmetic in RV64IM) is one to three orders of magnitude more code and cycles. [I] Proof architecture must be compositional with loop invariants (not unrolled symbolic execution), and the time budget, kernel-replay strategy (comparator replays every transitively used declaration, including Mathlib/VCVio pieces) and memory limit must be re-derived from measurements.
- **No reusable RISC-V proof automation** is admitted to submitters; each team rebuilt a refinement calculus (`Refines.lean` etc.). [I] recursion.fast should ship a vetted, importable, *untrusted-but-sound* proof library (e.g. riscv-zkvm's `Logic/` WP and separation-logic tactics, R6) as an allowed import, since anything elaborated still passes through the kernel.
- **`probTrue … = 0` soundness** works for OTS hint checking because the hint relation is checked exactly against oracle answers; for SNARKs, soundness is inherently probabilistic (Schwartz-Zippel, proximity gaps, Merkle collisions), so the clause shape must change to a bound (e.g. RBR knowledge soundness error) and the machine-to-spec bridge must be exact (decision agreement on every coherent path) while the error lives entirely in the spec. [I]
- **The subset of RV64IM** lacks most W-ops; 32-bit field arithmetic in RV64 commonly uses `ADDW`/`MULW`. [I] Check R6 for later riscv-zkvm revisions.
- **Idealised hash** (`HASH` is the random oracle, priced at 1 cycle per block, with an open note that 4 may be right) is fine for a ROM-based argument but the price strongly influences design rankings (hash-heavy vs arithmetic-heavy verifiers). [I]
- **Hint delivery and `expand` are unpriced**; a SNARK prover cost must be constrained (PLAN §1 item 5), which ots.golf leaves open (`docs/upper-riscv-hint.md:522-530`).

---

## 8. Measurements on this machine

### 8.1 Building the contract and checking one RISC-V submission

Setup [M]: a fresh `git clone` of core `8b140a99` into the session scratchpad (the read-only checkout was not touched); comparator `c0c5a52d` built with the project toolchain (17 s); landrun could not be built (no Go on this host), so comparator ran with its `fake-landrun.sh` shim (**not a sandbox**), wrapped in a `systemd-run --user` unit with `MemoryMax=24 GiB`, `MemorySwapMax=0`, IPv4/IPv6 sockets denied. Before running I scanned the record root for metaprogramming (`run_cmd`, `#eval`, `IO.`, `initialize`, `unsafe`, `import Lean`, `elab`/`macro` commands, `extern`, `implemented_by`): none present. The machine (32 cores, 62 GB) was **shared with other agents' concurrent Lean builds** (load average 6-10), so the times below are upper-bound-ish and not hosted-equivalent.

| Step | Wall time | Notes |
|---|---:|---|
| `lake exe cache get` (clone VCVio, Mathlib, ArkLib, ... and fetch 8,689 Mathlib oleans) | 254 s | network-bound |
| `lake build OptimalOTS` (VCVio, riscv-zkvm, leanerVM semantics, CompPoly, contract; 2,869 jobs) | 341 s | one-off warm-cache cost |
| `pin_contract.py check` | <1 s | "contract ok: ots-v1-draft 2e8ba38cb5cfb50d" (matches the record's contract id in `S:records.json`) |
| `check_submission.py upper-riscv` | <1 s | "ok: upper-riscv submission, claim 341, 103 files, 971225 bytes" |
| **comparator on `S:formal/Submissions/UpperRiscv` (claim 341)**: build challenge, export, build solution (100 modules), export, compare, axiom audit, kernel replay | **1,516 s (25 min 15 s)** | "Lean default kernel accepts the solution / Your solution is okay!"; user 2,665 s + sys 438 s CPU (204 % average, i.e. little parallelism); peak RSS of one process 12.9 GB |
| `lake env lean scripts/check-axioms.lean` | 13 s | "ok — 106 contract declarations use only propext/Classical.choice/Quot.sound" |

Breakdown inside the comparator run [M]: the solution build accounted for roughly 1,230 s (export of the solution was in progress at t = 1,231 s); export + statement comparison + axiom audit + kernel replay took the remaining ≈ 285 s, consistent with the submitter-reported 186-226 s standalone replay. Per-module build times sum to 2,130 s over 100 modules; the critical path is dominated by `Payload.lean` (472 s alone), then `CappedCost.lean` (171 s) and `PairCount.lean` (92 s). [I] On an idle host the check would likely land near the hosted figures of 14 min (836 s for the 358-cycle predecessor); under contention it exceeded the 20-minute production limit, i.e. **the current RISC-V record has less than 2x headroom against the time limit** and single heavy modules set the critical path. [V] The 472 s module `S:.../UpperRiscv/Payload.lean` is only 176 lines; its cost is four `decide +kernel` proofs quantifying over all 5,328 signature-bit positions (`Payload.lean:41-44`, e.g. `∀ i < 5328, coindex' (index' i) = i := by decide +kernel`). [I] Kernel-evaluated exhaustive checks are the agents' substitute for `native_decide`, and their cost grows linearly with table size: a SNARK verifier with large constant tables (Merkle layouts, twiddle factors, round constants) would hit this immediately. The task's 30-minute cap was respected.

---

## Implications for recursion.fast

- Adopt the ots.golf architecture wholesale for the plumbing: trusted dev repo + untrusted submissions repo, PR-only intake of one flat root, never-merge, retention tags, durable verdict comments, bot record snapshots, `NOTES.md` journal, canonical `claim.txt` rendered into the stub, comparator with definition holes, protected-file pin and contract id, systemd+Landlock sandbox with cleared environment, warm `.lake` clone with stale-artifact deletion.
- Make the submitted artifact a **definition hole whose type bundles program image, specification and witnesses**, and make the certificate pin it so completely that *any* term satisfying it is a legitimate win (comparator explicitly warns that definition holes are otherwise gameable).
- Reuse the RISC-V wrapper design (`List Instr` image, raw-input loader with length sentinel, syscall arms with explicit prices, fuel-indexed `execute` in `OracleComp`) on top of the pinned riscv-zkvm semantics; check whether the needed RV64IM ops (W-ops, any field/`clmul` precompile) exist at the chosen pin.
- Use the **hinted pattern** for the verifier: the proof is prover-chosen input; state `Sound` (machine accepts ⇒ spec accepts, on every coherent oracle path), `Faithful` (honest prover's proof ⇒ machine reaches spec's decision) and a cycle bound over **all** proofs and all fuel. Put all cryptographic soundness error in the spec-level (ArkLib) statement; keep the machine-to-spec bridge exact.
- Do not state SNARK soundness as `probTrue … = 0`: Merkle/FS hashing makes such statements unsatisfiable (ots.golf's leanISA boundary lesson). Use an explicit error bound, and keep the cached (`probTrue`) vs uncached (`support`) semantics distinction explicit in the contract docs.
- Budget every honest party (verifier, prover, batcher) inside any concrete-security statement whose budget counts them, or the statement can become vacuous (ots.golf shipped exactly this bug, fixed in `30e33a7`). Ship machine-checked "this clause is vacuous when …" facts and a non-vacuity witness (a baseline submission) with the contract.
- Prove, do not measure, every size cap that blocks lookup tables (image bytes, data bytes, proof length, advice length), and cap prover-side costs the score cannot see.
- Costs must be read off the machine, not transferred from the spec: decision agreement does not preserve query counts.
- Plan for **check time as the binding constraint**: OTS-sized RISC-V proofs already take 3-14 minutes and 8-10 GB, with timeouts at 20 minutes; my own check of the 341-cycle record took 25 min on a contended 32-core host, dominated by one 176-line module of `decide +kernel` over 5,328 cases. Measure baseline check time early (P3), consider raising limits, and provide an admitted, vetted RISC-V proof library (WP/separation logic, loop rules) so that proofs scale by invariants rather than unrolling.
- Restrict imports by exact module where upstream libraries contain `sorry`s or sorried instances (ArkLib, Clean); keep the axiom audit as the backstop; consider enabling nanoda as a second kernel.
- Expect heavy contract churn after launch (ots.golf: 46 pin changes in 10 days, 7 submissions-side contract syncs); design record porting/revalidation (`record-revalidations.json`) from day one.
- Keep the contract small and heavily documented: ots.golf's RISC-V path is ≈220 code lines (≈450 total) of contract over ≈1,500 code lines of pinned ISA semantics plus VCVio; recursion.fast will add ArkLib security definitions, so the auditable surface must be budgeted explicitly.
