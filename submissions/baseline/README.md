# Baseline submission `P_triv`: a worked example of what a submitter proves

`P_triv` is the organiser's trivial baseline for the recursion.fast v2 contract (DESIGN §7.3). Its
proof is the witness itself: the prover sends the witness tables, and the verifier reads all of them
and decides the relation.

- It is **proved secure at every class `20 ≤ k ≤ 28`**.
- It is **certified at `k = 24`**, the recursion tree's `k_min` (`L_chain(2^10)` fits class 24).
  - A board-L entry must declare the class of its largest leaf layout. With the runner's default
    leaf board `{2^8, 2^12}` that is 26, since `L_chain(2^12)` needs class 26.
  - A class-24 entry that requests board L fails every default evaluation (S7-M2, open with the
    orchestrator and Stage 6b).
- It is **listed, unranked**. The compiled verifier accepts no tape at any class, because the
  rounds section alone exceeds the tape cap (`triv_narg`). So the entry cannot run the badge path
  (O-10).

This file is written for a submitter.

- Section 3 goes through every field of `Protocol`, `ExtractorImage`, `Submission` and
  `Certificate`: what it means, what `P_triv` puts there, and who checks it.
- Section 4 says what the kernel, the comparator, the gate and the runner each check, and how the
  harness builds a solution.
- Sections 6 and 7 give the tape-size arithmetic and the extractor's fuel split.

## 1. Files

| Path | What |
|---|---|
| `RecursionFastCandidate/Protocol.lean` | `P_triv k`, its verifier, its extractor (`trivExtractor`) and the security proof `triv_secure`. It is adapted from the organiser's `RecursionFast/Controls/Toy.lean`, which it does not import. By convention a submission imports only the contract and the organiser's `Library`. Nothing enforces this: the organiser package also exposes `Controls` and `Bridge`. That is harmless, since they are untrusted, kernel-checked and subject to the gate like the `Library`. |
| `RecursionFastCandidate/Compiled.lean` | What the organiser's compilation makes of `P_triv`. The honest tape has `5 · 2^(k+11)` bytes, so the honest prover writes no tape. The verifier accepts none, because the rounds section alone exceeds the cap. There is no recursion entry. |
| `RecursionFastCandidate/Submission.lean` | `cfg`, `submission k`, the declared record `⟨24, blake2s, 2, firstMsgImg⟩` and its `certificate`. |
| `RecursionFastCandidate/Negative.lean` | The negative control `split0_not_secure`: the same protocol, with the call before round 0 starved of fuel, is not secure. |
| `RecursionFastCandidate.lean` | The library root. The repository's lakefile entry is `RecursionFastCandidate` (`srcDir = "submissions/baseline"`, not a default target). The production harness ignores it (§4). |
| `extractor/extractor.S`, `build.sh`, `extractor.bin`, `extractor.data` | The extractor image as submitted files: 8 code words and no data. It reassembles byte-identically to the library's `firstMsgImg`. |
| `claim.json` | The claim: `k`, `hash`, `arity` and the extractor image files (`image`). |
| `audit/BaselineChallenge.lean` | The rendered challenge: the organiser's `RecursionFast/Challenge/L.lean.in`, rendered from `claim.json` by `scripts/render-challenge.py`. It is organiser data, with two `sorry` placeholders. |
| `audit/BaselineSolution.lean` | The solution, made by `scripts/make-solution.py`. |
| `audit/comparator{,-nanoda}.json` | The comparator configurations. |
| `scripts/check.sh` | Every check below. `HARNESS=1 ORG=… MANIFEST=…` also runs the production harness. |
| `scripts/tape-size.py` | The arithmetic of §6. |
| `prover/README.md` | What a real entry's native prover must produce. There is none for this entry. |

## 2. The protocol in one paragraph

**Index.** `VK L` is one element: `1` if `L` is admissible at class `k`, else `0`. The index
oracle `IDX L` holds `L`'s serialisation (`Library/Codec.lean`, `eLayout`) in one leaf of `2^(k+8)`
elements, padded with zeros.

**Prover.** In its one round, the prover sends the serialised tables (`eWit`) in one leaf of
`2^(k+10)` elements. There are no challenges.

**Verifier.** The verifier is a query program. It reads leaf 0 of oracle 0 (the index) and leaf 0
of oracle 1 (the message). It parses the layout and the tables, and accepts iff the key says the
layout is admissible and the tables satisfy `rel` (`triv_accepts_iff`).

**Extractor.** The extractor image outputs round 0 in place. Before round 0, the contract decodes
that output as exactly the tables the verifier checked (`triv_extractMid`).

## 3. The objects, field by field

### 3.1 `Protocol k` (`Contract/Protocol.lean`)

| Field | Meaning | `P_triv k` | Checked by |
|---|---|---|---|
| `k_range` | `20 ≤ k ≤ 28` | the argument `hk` | kernel (type) |
| `n`, `n_le` | number of rounds, at most `roundCap = 2^14` | `1` | kernel (`decide`); gate (`n` compiled) |
| `shape` | the rounds: `msg ⟨logLen, logLeaf⟩` or `chal nE idx` | `msg ⟨k+10, k+10⟩` (one leaf) | kernel; gate (compiled) |
| `vkLen`, `vkLen_le`, `VK` | the verification key, at most `2^10` elements | `1`; `trivVK` | kernel; gate (`vkLen`, `VK` compiled) |
| `idxShape`, `IDX` | the index oracle (oracle 0) | `⟨k+8, k+8⟩`; `toOracle (k+8) (eLayout L)` | kernel; gate (compiled) |
| `shape_ok` | the shape caps: messages `logLeaf ≤ logLen ≤ k+10`, index `≤ k+8`, index challenges `≤ 64` bits | at the caps exactly | kernel |
| `prover` | the honest prover: a Lean specification, never executed, may be noncomputable | sends `eWit L w` | kernel (completeness) |
| `verify` | the verifier: a query program from `VK L`, `x` and the challenges | `trivVerify` | kernel; gate (compiled) |
| `extractor` | the extractor image and its fuel split (§3.2) | `trivExtractor k` | kernel; gate (`img` compiled); `Certificate.img` binds `img` to the claim |
| `ε` | the declared error of each challenge round | `fun _ => 0`, a function on an empty type (no challenge rounds) | kernel (`RbrKS` at `ε`, and `cap`: `ε ≤ 2^-128`) |

**`verify` is executed and timed.** The executed code is what the Lean compiler emits for the
submission's module. The comparator and the gate check the kernel term of `verify`, not that
code. A module can overwrite its own compiled code at elaboration time without any attribute
(S7-M1, open with Stage 6b). So "the thing timed is the thing proved" holds only up to that check.

`Protocol.Secure` is `SecureWith (relK k) Set.univ P.prover P.specVerifier
(P.extractor.toExtractor P.shape) P.ε`. It has three fields:

- **`complete`** (perfect completeness): on every instance of `relK k` and every challenge vector,
  the verifier accepts the honest transcript.
- **`sound`**: a knowledge state function (`KSF`) for the named extractor with the counting bound
  `RbrKS` at `ε`. The `KSF` laws are `empty`, `next` and `full`.
- **`cap`**: `ε c ≤ 2^-128`.

The proof, in the order a submitter writes it:

1. **`trivDecide_iff`**: the decision on the parsed leaves is `L.Admissible k ∧ L.rel k x (tables)`.
   It uses the layout round trip `pLayout_eLayout`, the bound `eLayout_length ≤ 2^(k+8)` (this is
   where the index shape cap matters), `relBelow_iff` (the decidable form of `rel`) and
   `rel_normal_iff`.
2. **`triv_accepts_iff`**: `specVerifier` accepts iff the tables parsed from the message are a
   witness in `relK k`.
3. **`triv_extractMid`**: the image's run before round 0 decodes to exactly those tables. It
   follows from `Library/Extractor.lean`'s `firstMsg_extractMid` with the declared fuel of 8.
4. **`trivKSF`**: before round 0 the state is "`w` is a witness"; after round 0 it is "the parsed
   tables are a witness". `next` is item 3, and `full` is item 2.
5. **`triv_secure`**.
   - `complete` is item 2 together with the witness round trip `pWit_eWit`, the bound
     `eWit_length ≤ 2^(k+10)` (the message shape cap), `rows_le_of_rel` and `rel_trim_iff`.
   - `sound` is `trivKSF`. Its counting bound `RbrKS`, like `cap`, is vacuous here for every `ε`:
     there are no challenge rounds (`triv_noChal`), so `ε` is a function on an empty type, and
     `fun _ => 0` and `fun _ => errorCap` are the same.
   - The knowledge content is in the `KSF` laws (items 3–4). A starved extractor breaks them
     (`split0_not_secure`, §7).

### 3.2 `ExtractorImage k n` (`Contract/Extractor.lean`)

| Field | Meaning | `trivExtractor k` | Checked by |
|---|---|---|---|
| `img` | a RISC-V image (code words, data words) | `firstMsgImg`, 8 instructions | gate (compiled); the certificate's `img` field states that it equals the claim's rendered image (§3.4) |
| `img_le` | `img.byteSize ≤ imageCap = 2^20` | 32 bytes | kernel (`decide`) |
| `fuel` | the submitter's split of the budget over the `n + 1` calls, indexed by the round before which each call's witness lives; specification data, not compiled | `![8, 0]` | kernel |
| `fuel_le` | `Σ fuel ≤ B(k) = 2^(2k+16)` | `8 ≤ 2^(2k+16)` | kernel |

The extractor is **defined** as running `img` on the contract's input tape with the declared fuel
and decoding the output (`toExtractor`). There is no separate agreement theorem.

A fault, a trap, running out of fuel, or an output longer than `witCap k = 2^(k+12)` words gives
the empty witness. The empty witness fails `relK` before round 0 (`nil_not_relK`). The `KSF` laws
are therefore what force the image to work.

### 3.3 `Submission k`, `Declared`, `Certificate` (`Contract/Certificate.lean`)

| Object | Field | Here |
|---|---|---|
| `Submission k` (board L) | `P : Protocol k`, `cfg : Cfg`, `secure : P.Secure` | `⟨P_triv k hk, cfg, triv_secure k hk⟩` |
| `Cfg` | `hash ∈ {blake2s}`, `arity ∈ {2, 4, 8, 16}` | `⟨blake2s, 2⟩` |
| `Declared` | `k`, `hash`, `arity`, `img` (rendered from the claim) | `⟨24, blake2s, 2, firstMsgImg⟩` |
| `Certificate D S` | `cfg : S.cfg.hash = D.hash ∧ S.cfg.arity = D.arity`; `img : S.P.extractor.img = D.img` (S7-A1) | `⟨⟨rfl, rfl⟩, rfl⟩` |

The class is pinned by the type: the challenge asks for `submission : Submission declared.k`.

**Why `cfg = ⟨blake2s, 2⟩`.**

- The hash menu has one entry.
- For the arity: every oracle of `P_triv` has one leaf, so its Merkle tree has depth 0 at every
  arity (`triv_depth`). There are no authentication paths, and the index root is the hash of the
  one leaf. The arity therefore changes neither the tape nor the verifier's work.
- 2 is the design's default. For a real multi-leaf design, arity 2 also gives the shortest paths
  (§6, item 3).

**A computable `submission`.** `P_triv`'s `submission` compiles as a whole, because its `ε` and its
specification prover are computable. That is not the usual case.

- A real submission typically has `ε := fun _ => errorCap`, which is noncomputable. It is then
  written `noncomputable def submission`; the comparator ignores `noncomputable`.
- The gate then checks the badge-path fields one by one (§4).

**Board R.**

- **What the entry adds.** `SubmissionR` (`entry : RecursionEntry P cfg`); `DeclaredR` (also the
  chips and entries of `C_V`, and the key digests `digestC`, `digestL`); and `CertificateR`
  (also `C_V`'s size).
- **What the R stub adds.** It binds `submission.entry.C` to the rendered layout `C`.
- **The digests** are compared by the runner with the compiled indexer's. They are not proved
  (S5-A3, S5-A13).
- **This entry.** `P_triv` has no recursion entry: `triv_no_entry` proves that none exists at any
  class (its `live` field fails, S5-A10).

### 3.4 The claim, the challenge and the solution

`claim.json` is the claim:

```json
{"k": 24, "hash": "blake2s", "arity": 2,
 "image": {"code": "extractor/extractor.bin", "data": "extractor/extractor.data"}}
```

**Claim rules** (`scripts/render-challenge.py`):

- The key set equals the stub's placeholder set exactly.
- `image.code` is little-endian 32-bit words and `image.data` little-endian 64-bit words, together
  at most `2^20` bytes.
- Paths are plain relative paths inside the claim's directory, with no `..` and no symbolic link.
- Floats and duplicate keys are rejected.

**Rendering.** The renderer renders the claim into the leaf-board stub
`RecursionFast/Challenge/L.lean.in`, giving `audit/BaselineChallenge.lean`. Everything in that file
is organiser data except the two placeholders, `submission` and `certified`. The image is rendered
from the submitted files into the packed `unpack` form, and becomes `declared.img`. The statement
is

```lean
theorem certified : Certificate declared submission
```

**The solution.** `scripts/make-solution.py` copies the challenge and fills in the placeholders:
`submission := RecursionFastCandidate.submission 24 h24`, and the proof `⟨⟨rfl, rfl⟩, rfl⟩`.

For a large image, `rfl` against the packed form can be expensive. Two cheap routes:

- define the candidate's image in the same packed `unpack` form;
- or prove the equation chunk by chunk.

v0.3 measured 80 s and 9 GB per word lookup in a 1 MiB image done naively.

**What the comparator checks.**

- **The targets.** `certified` must be a theorem whose type equals the challenge's.
  `submission` (`definition_names`) must be a definition of the same type, with a free value.
- **Everything reachable.** Every other constant reachable from those two types must equal the
  organiser's value for value. That covers `declared`, `image`, `Certificate`, `Submission`,
  `Protocol.Secure` and the whole security cone.

So what is kernel-checked is the challenge's statement: the submission's class (by its type), hash,
arity and extractor image equal the rendered claim's, and its protocol is secure. It is not
vacuous. A claim with arity 4, or with one image bit flipped, fails to elaborate at `certified`
(`logs/S7/negative-claims.log`). The contract control is `toy_certificate_img`
(`Controls/Certificate.lean`).

## 4. Who checks what

**How the harness builds a solution** (`scripts/harness.sh`):

- It ignores the submitter's lakefile. Every `*.lean` file under the solution directory becomes a
  root of one generated library, with no `leanOptions` and no `moreLeanArgs`.
- Module roots must be fresh: not `RecursionFast`, not `Mathlib`, not any package root.
- The challenge and solution modules are the comparator config's `challenge_module` and
  `solution_module`.

**Caps outside Lean** (DESIGN §6.5): the build takes at most 1 h and 48 GB; the harness at most 2 h.

| Checker | What it checks | For this entry |
|---|---|---|
| **Kernel** (Lean, at build time) | Every field above has its type: the caps (`n_le`, `vkLen_le`, `shape_ok`, `img_le`, `fuel_le`, `k_range`), `Secure`, and the certificate's fields. `check.sh` also runs `leanchecker` on the solution's whole closure. The organiser's harness does not. | All pass. Axioms: `propext`, `Classical.choice`, `Quot.sound` only. |
| **Comparator** (`harness.sh` stage 1, fresh sandboxed tree) | The challenge is built and exported before the solution. `certified` has the challenge's type, the axioms are permitted, and only `submission`'s value may differ (§3.4). The closure of `certified` and `submission` is exported and replayed by nanoda and the Lean kernel. | "Your solution is okay!": nanoda and the Lean kernel accept. |
| **Gate** (stage 2, second fresh tree, byte-identical build) | Trust is by `.olean` hash. It rejects `sorryAx` and non-standard axioms in the closure, `unsafe`/`partial`/`opaque` constants from untrusted modules, and `implemented_by`/`extern`/`export`/`init`/`csimp` registered by untrusted modules. The badge-path fields must have compiled code: `Submission`: `P`, `cfg`; `Protocol`: `n`, `shape`, `vkLen`, `VK`, `idxShape`, `IDX`, `verify`, `extractor`; `ExtractorImage`: `img`; `SubmissionR`: `toSubmission`, `entry`; `RecursionEntry`: `C`, `decode`. A `submission` with compiled code as a whole passes outright. Otherwise the fields are checked one by one. It does **not** check that compiled code agrees with kernel terms (S7-M1). | PASS: `RecursionFast.Challenge.submission` has compiled code as a whole. |
| **Benchmark runner** (`harness/run-benchmark.py`, DESIGN §6.2–§6.3) | It indexes the benchmark layouts with the Lean-compiled indexer (untimed, ≤ 1 h). It runs the native prover on each instance and `harness-verify` (`NARG`) on each proof; every proof must verify. Board L is scored on prover + verifier wall time, medians of 3 runs. **The 128 KiB board-L proof cap is enforced here** on every measured leaf tape (S7-A3). `NARG` itself enforces only `tapeCap = 2^20`, and the certificate states nothing about proof sizes. In Stage 6b's current runner, requesting board L also applies the 128 KiB cap to the recursion tree's leaves, and the leaf board's largest layout fixes the class an entry needs (S7-M2). | **Nothing runs.** No tape is accepted (`triv_narg`), and the honest prover writes none (`triv_prove_none`). The entry is listed, unranked. |

## 5. What is proved, what is declared, what is measured

- **Certified by the harness** (comparator: both kernels; then the gate): `certified` at
  `k = 24`. It says that the configuration and the extractor image are the declared ones, and,
  through `submission`'s value, that `triv_secure 24 h24 : (P_triv 24 h24).Secure`.
- **Kernel-checked at build time** (and by `leanchecker` in `check.sh`), documentation rather than
  certified claims, because the comparator exports only the closure of `certified` and
  `submission`:
  - `triv_secure` at every `20 ≤ k ≤ 28`;
  - the compilation facts `triv_depth`, `triv_uncapped_length`, `triv_prove_none`, `triv_narg`
    and `triv_no_entry`;
  - `trivExtractor_fuel_tight` and `split0_not_secure`.
- **Declared:** the claim (`k = 24`, BLAKE2s, arity 2, the image files), all of it certified.
  - The leaf-board record has **no key digests**. Only `DeclaredR` has `digestC` and `digestL`,
    which the runner recomputes and does not certify (S5-A3).
  - So `D (index cfg (P_triv 24) (L_chain 2^10))` is neither needed nor computed. The kernel could
    not evaluate it anyway: it is one BLAKE2s over the 2^35-byte index leaf (32 GiB), of which the
    layout is 6.0 MiB and the rest is zero padding.
- **Measured:** nothing. There is no proof to time.

## 6. Why it is listed, unranked: the tape-size arithmetic

The tape grammar is in `Contract/Compile.lean`'s header: `tape ::= rounds openings`.

`P_triv`'s shapes are static, so its tape does not depend on the instance:

- **Rounds section.** The message has one leaf, so it is **plain**: all of its `2^(k+10)` elements,
  8 bytes each. That is `8 · 2^(k+10)` bytes.
- **Openings.** Query `(0, 0)` opens the index oracle, which is always Merkle-committed. That is
  1 leaf of `8 · 2^(k+8)` bytes plus a path of depth 0, so 0 bytes. Query `(1, 0)` reads the plain
  message and opens nothing.
- **Total.** In "leaves × (leaf + path)" form: `1 × (8 · 2^(k+8) + 0) + 8 · 2^(k+10) = 5 · 2^(k+11)`
  bytes. This is kernel-checked (`triv_uncapped_length`).

| k | tape | × 1 MiB (boards R, W) | × 128 KiB (board L) |
|---|---:|---:|---:|
| 20 | 10 GiB | 10,240 | 81,920 |
| **24** | **160 GiB** (171,798,691,840 B) | **163,840** | **1,310,720** |
| 28 | 2,560 GiB | 2,621,440 | 20,971,520 |

`NARG` checks `|tape| ≤ tapeCap = 2^20` first. The rounds section alone is `8 · 2^(k+10) ≥ 2^33`
bytes, so **no tape is accepted at any class** (`triv_narg`).

Shrinking the shapes would not help. On `L_chain(2^10)` at `k = 24` (measured:
`logs/S7/lchain1024-sizes.log`, `chain-report-1024.log`):

- **The witness** is 25 heights + 10,232,905 cells, i.e. 81,863,440 B = 78.1 MiB.
  - It includes the fixed `ADD8`/`NIB` tables: 786,464 cells, 6.0 MiB, which the index already
    determines.
  - The part the prover chooses is 72.1 MiB.
- **The layout** is 792,851 elements (6.0 MiB). It holds the `add8` table too, so adding it to the
  witness counts that table twice.
- **Witness and layout are 0.05 % of the compiled tape**; the rest is zero padding.
- **The prover-chosen part alone is 72× the 1 MiB cap and 577× the 128 KiB cap.** Any protocol
  whose proof contains the witness is excluded, whatever its shapes. This is the role DESIGN §6.2
  gives the proof-size cap.
- **A Merkle variant (a model, `scripts/tape-size.py`).** Take leaves of `2^l` elements, and let an
  adaptive verifier open only the occupied leaves. The minimum over `l` and the arity is 84.5 MiB
  (arity 2; message leaves `2^14`, index leaves `2^13`).
- **Arity 2 gives the shortest paths.** With leaves of `2^10` elements the tape is 89.2 / 92.2 /
  96.1 / 104.6 MiB at arity 2 / 4 / 8 / 16 (`logs/S7/tape-size.log`).

**The badge path fails before any proving.** The Lean-compiled indexer commits the index oracle by
hashing its one leaf, and building that leaf is already infeasible:

- `IDX L = toOracle (k+8) (eLayout L) = fun p => (eLayout L).getD p 0`;
- `Oracle.leaf` builds the leaf with `List.ofFn` over all `2^(k+8)` positions.

At `k = 24` there are `2^32` lookups. Every lookup past the end walks the whole 792,851-element
list. That is `3.4 · 10^15 ≈ 2^51.6` list steps before any hashing, beyond the 1 h indexing
budget at any plausible speed. The review's "about `2^63`" assumed lookups that walk `p` steps.
`scripts/tape-size.py` prints this count.

## 7. The extractor budget split

`P_triv` has `n = 1` round, so its extractor makes two calls:

1. **`extractMid 0`, before round 0.** The `next` law requires its output to be a witness in
   `relK k` whenever the message parses to one. `firstMsgImg` halts after its 8 instructions:
   `run` with fuel `f + 8` halts (`run_firstMsgImage`), and fuel 7 does not, on one small tape
   (`trivExtractor_fuel_tight`).
2. **`extractOut`, after round 0.** `trivKSF` at the last state does not read the witness, so the
   output is irrelevant and the fuel is 0.

So the declared split is `fuel = ![8, 0]`. The total is 8 steps, against `B(24) = 2^64`.

**What the kernel checks about the split.**

- **8 steps suffice** on every tape the protocol produces. This is `triv_extractMid`, inside
  `triv_secure`.
- **Starving the call before round 0 is fatal.** `split0_not_secure` takes the same image and the
  same total 8, moved to the output call (`![0, 8]`), and shows the protocol is not secure at any
  class:
  - the starved call returns `[]`, and `[]` is never in `relK` (`nil_not_relK`);
  - completeness gives an accepted transcript on which the `next` law needs that call's output.
- **The contract bounds only the total** (S4-A14). Nothing else checks the split: `Secure` is
  stated about the extractor with it.
- **When a call may have 0.** Any call other than the one before round 0 may get 0 exactly when the
  submitter's own state function ignores its output, as `trivKSF` does at the last state.

The library also offers `firstMsgImage k n = atZero …`, which puts all of `B(k)` on the call before
round 0; the organiser's toy uses it. Either split proves `Secure`. The tight split is the more
informative declaration.

## 8. Measurements

From `scripts/check.sh` and its harness run; logs are in `logs/S7/`.

| Item | Result |
|---|---|
| `lake build RecursionFastCandidate` (its 5 modules; contract and library warm) | 19.8 s wall, 2.7 GB (`build-candidate.log`) |
| `scripts/check.sh` with `HARNESS=1` | 6 min 22 s, CHECK OK (`check.log`) |
| Production harness (`scripts/harness.sh`: comparator with nanoda and the Lean kernel, then the gate) on a private organiser build | **HARNESS: ACCEPT**, 293 s wall, 3.5 GB; comparator (nanoda and the Lean kernel) 203 s; gate PASS (Stage 6b's v2 gate) (`harness-L.log`) |
| `leanchecker BaselineSolution` | OK, 24 s, 2.3 GB (`leanchecker.log`) |
| Axioms of every theorem of the package, and of `certified` | within `[propext, Classical.choice, Quot.sound]` (`axioms.log`) |
| Hygiene (no `sorry`/`admit`/`native_decide`/`implemented_by`/`extern`/`csimp`/`axiom`/`noncomputable`) | OK (`hygiene.log`) |
| Size (`scripts/loc.py`) | 231 code lines, 21 theorems: `Protocol` 111, `Compiled` 53, `Negative` 33, `Submission` 14, root 4, solution 16 (`loc.log`) |
