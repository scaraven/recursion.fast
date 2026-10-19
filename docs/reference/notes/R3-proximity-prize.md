<!-- Copied verbatim from the design workspace CambridgePQ/recursion.fast/notes/R3-proximity-prize.md (research note of 2026-10-10, written against the pinned checkouts it names). Kept here so the repository is self-contained; see docs/reference/neighbouring-competitions.md for the synthesis. -->

# R3: proximity-prize (ArkLib-based autoresearch competition)

Research note for recursion.fast. Author: R3 subagent, 2026-10-10.

Source checkout (read-only): `/home/devops/proximity-prize/proximity-prize`
- HEAD `ed2b68c4a330d76dc4ab6693eec81b685b493270` (2026-10-01, "Validate submission ae343732-..."),
  127 commits; initial commit `a36cdb6a` (2026-08-20).
- Toolchain `leanprover/lean4:v4.32.2` (`lean-toolchain`).
- ArkLib pinned at `e65197892890b8fd9b0dc05b8980273cf1d595cc` (2026-08-20, "feat: formalize the
  ABF26 toy problem (#754)"), in both `lakefile.toml:15-18` and `lake-manifest.json`. ArkLib's own
  `lean-toolchain` at that commit is also v4.32.2. That commit is 419 commits behind the local ArkLib
  HEAD `db7005f` (`/home/devops/Verified-zkEVM/ArkLib`). ArkLib sources quoted below were read with
  `git show e651978:<path>` from that local clone.
- Transitive pins (manifest): VCVio `446baa7` (inputRev v4.32.2), CompPoly `6416946`
  (zksecurity fork, inputRev `rabin-explicit-q`, inherited from ArkLib), mathlib `905b958`
  (inputRev v4.32.2), plus doc-gen4, checkdecls, leansqlite, Cli, UnicodeBasic, BibtexQuery, MD4Lean,
  PolyFun, loom2, plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq, batteries,
  cslib (21 packages in all).

Legend: **[F]** = verified fact (read in source or measured), **[I]** = my inference.

---

## 1. Overall structure

### 1.1 What is being scored [F]

`README.md:7-23`:

```text
epsilon* = 2^-128
q(delta) = (1 - delta)^128
b = B / 100
```

| Track | Certificate | Score |
|:--|:--|:--|
| `irs-reduction-threshold-lower` | At `delta = P/Q`, `certifiedGammaError(delta) <= epsilon*` and `q(delta) <= 2^-b` | maximize `B` |
| `irs-reduction-threshold-upper` | For every admissible `delta >= delta* = i/2^18`, `winningSetDensity(delta) > epsilon*`, and `2^-b <= q(delta*)` | minimize `B` |

README is explicit that "The score is the spot-check quantity induced by a certified threshold
radius. It is not `-log2(WSS)` and is not a full-protocol security claim." (`README.md:15-16`).

So the competition is a two-sided bracket on one threshold radius `δ*` of one fixed IOP instance:
lower-track submitters push the largest radius they can prove *safe* (combination-round error
≤ 2^-128), upper-track submitters push the smallest radius from which they can prove the protocol
*unsafe* (winning-set density > 2^-128). In both, the claimed `B` (centibits) is bound by the
spot-check term at that radius: lower requires `(1-δ)^128 ≤ 2^(-B/100)` (so `B ≤ -100·log2(1-δ)^128`),
upper requires `2^(-B/100) ≤ (1-δ*)^128` (so `B ≥ -100·log2(1-δ*)^128`).

The fixed instance (`ProximityPrize/Benchmark/IRSProfile.lean:25-32`): field `KoalaBear.Ext6`
(sextic extension of the 31-bit KoalaBear prime; |F| ≈ 2^186), domain size n = 2^18 (an NTT
subgroup of the base field embedded into Ext6), total message length k = 2^20, interleaving s = 8,
base RS dimension 2^17 (rate 1/2), t = 128 spot-check repetitions.

### 1.2 Protected target files [F]

The entire trusted Lean contract in this repository is three files, 290 lines including
comments/copyright (`wc -l`):

| File | Lines | Contents |
|---|---:|---|
| `ProximityPrize/Benchmark/IRSProfile.lean` | 177 | concrete code profile: field, domain, encoder, `code`, `baseCode`, sanity theorems (dimension, rate 1/2, min distance 131073, relative distance 131073/262144), `parameters : FixedRadiusParameters`, Merkle size estimate |
| `ProximityPrize/Benchmark/TargetLower.lean` | 59 | `claimedRadius`, `claimedError`, `reductionTarget`, `structure ProtocolClaim` |
| `ProximityPrize/Benchmark/TargetUpper.lean` | 54 | `epsilonStar`, `claimedUnsafeRadius`, `structure ProtocolClaimUpper` |

These three files are byte-identical between the initial commit `a36cdb6a` and HEAD `ed2b68c`
(`git diff --stat a36cdb6a HEAD -- ProximityPrize/Benchmark lakefile.toml lake-manifest.json
lean-toolchain` is empty; only CI/scripts changed). I.e. the contract was frozen for 6 weeks and
~125 validated submissions [F].

The lower target, verbatim (`TargetLower.lean:28-57`, comments trimmed):

```lean
noncomputable def claimedRadius (numerator denominator : Nat) : ℝ≥0 :=
  (numerator : ℝ≥0) / (denominator : ℝ≥0)

noncomputable def claimedError (centiBits : Nat) : ℝ≥0 :=
  (2 : ℝ≥0) ^ (-((centiBits : ℝ) / 100))

noncomputable def reductionTarget : ℝ≥0 :=
  (ProximityGap.prizeThreshold : ℝ≥0)

structure ProtocolClaim
    (centiBits radiusNumerator radiusDenominator : Nat) : Prop where
  admissible : claimedRadius radiusNumerator radiusDenominator ∈
    Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance
  reduction :
    ToyProblem.Impl.IRS.certifiedGammaError IRSProfile.totalDimension
        IRSProfile.interleaving IRSProfile.domain
        (claimedRadius radiusNumerator radiusDenominator) ≤
      reductionTarget
  score :
    (1 - claimedRadius radiusNumerator radiusDenominator) ^
        IRSProfile.repetitions ≤
      claimedError centiBits
```

The upper target (`TargetUpper.lean:32-52`):

```lean
noncomputable def epsilonStar : ℝ≥0 :=
  (ProximityGap.prizeThreshold : ℝ≥0)

noncomputable def claimedUnsafeRadius (unsafeIndex : Nat) : ℝ≥0 :=
  ProximityGap.gridPt (ι := IRSProfile.Index) unsafeIndex

structure ProtocolClaimUpper (centiBits unsafeIndex : Nat) : Prop where
  admissible : claimedUnsafeRadius unsafeIndex ∈
    Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance
  unsafeAbove : ∀ δ ∈ Set.Ico (claimedUnsafeRadius unsafeIndex)
      IRSProfile.minRelativeDistance,
    epsilonStar < winningSetDensity IRSProfile.encoder δ
  score :
    (2 : ℝ≥0) ^ (-((centiBits : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius unsafeIndex) ^ IRSProfile.repetitions
```

Design points worth copying [F unless marked]:
- The claim is a `structure ... : Prop` with *named fields* (`admissible`, `reduction`, `score`),
  each a single readable inequality. The score parameter is a `Nat` argument of the structure.
- Upper track certifies the whole suffix `[δ*, minRelDist)` "because no monotonicity theorem for
  `winningSetDensity` is assumed" (`README.md:31-34`, `TargetUpper.lean:21-23`). A contract that
  avoids needing an unproved monotonicity lemma by quantifying over the range.
- The upper radius is pinned to the `1/n` grid (`claimedUnsafeRadius` via `gridPt`), the lower
  radius is an arbitrary exact fraction P/Q.

### 1.3 Submission layout and candidate rules [F]

`README.md:52-93`, `AGENTS.md:1-43`, enforced locally by `scripts/check-submission-imports.sh`
(194 lines) and authoritatively by the remote service's "source policy" (`AGENTS.md:177-181`:
"the manifest wins and this file is stale").

```text
ProximityPrize/SubmissionLower/          ProximityPrize/SubmissionUpper/
  Solution.lean                            Solution.lean
  score.txt          # centibits B         score.txt
  radius.txt         # exact P/Q           unsafe-index.txt   # i in [1, 131072]
```

Exported theorem: `theorem ProximityPrize.Benchmark.candidate : ProtocolClaim B P Q` (lower),
`theorem ProximityPrize.Benchmark.Upper.candidate : ProtocolClaimUpper B i` (upper).

Rules (`README.md:88-93`): "a candidate may import only its own protected target and flat helper
`.lean` files beside `Solution.lean` in the same submission root. Cross-challenge imports and
subdirectories are rejected. The benchmark binds the scalar files to the exact theorem type and
permits only `propext`, `Classical.choice`, and `Quot.sound` in the candidate's axiom closure."

`check-submission-imports.sh` enforces:
- no symlinks, no subdirectories (`:87-117`), only `*.lean`, `score.txt`, claim file admitted (`:111`);
- comments and string interiors are blanked before scanning (`:33-85`) so prose cannot cause false
  positives and string tricks cannot hide code;
- reject Lean module system headers (`module`, `public/private/meta import`, `:133-137`);
- reject `run_cmd|run_elab|initialize|implemented_by|extern|#eval|#exit|debug.skipKernelTC`
  (`:141`) and metaprogramming `run_tac|elab|macro|syntax|...|importModules|setEnv|modifyEnv|addDecl`
  (`:145`) ("Custom elaborators, macros, and run_tac can execute after the audited import block and
  dynamically load another challenge");
- one module per `import` line in a leading import block (`:152-168`);
- imports allowed: own target, `Mathlib*`, `ArkLib*`, `CompPoly*`, own submission modules (`:170-193`).
  `AGENTS.md:13`: "**`Mathlib`, `ArkLib` and `CompPoly` may be imported freely**, at any depth."

Resource limits (deployment-side, `AGENTS.md:17-23,47-49,120-122,136-138,163-165`): ≤1000 files,
≤8 MiB/file, ≤16 MiB total; 24 GiB memory; 4 h wall; 4 vCPU `r8i.xlarge` (~3.9 GHz); 31.9 GiB disk.
`AGENTS.md` is a remarkably detailed performance guide (kernel `decide` cost model, "split generated
tables into small per-row definitions", "Do not split modules to gain parallelism": each concurrently
built module loads "the challenge's import closure independently — about **3 GiB and five seconds
each**").

### 1.4 Scalar binding of score.txt / claim file to the theorem type [F]

`benchmark.sh:41-47`:
```bash
bash scripts/check-submission-imports.sh "${profile}" "${submission_dir}"
centibits="$(python3 scripts/benchmark_contract.py read-scalar "${score_path}")"
claim="$(python3 scripts/benchmark_contract.py read-scalar "${claim_path}")"
python3 scripts/render-benchmark-challenge.py \
  "${profile}" "${centibits}" "${claim}" "${challenge_path}"
```
`render-benchmark-challenge.py:30-53` generates the *challenge* file Comparator compares against:
```lean
import ProximityPrize.Benchmark.TargetLower
namespace ProximityPrize.Benchmark
theorem candidate : ProtocolClaim {centibits} {numerator} {denominator} := by
  sorry
```
Comparator then checks that the solution module's `candidate` has *exactly* that type with
permitted axioms (`benchmark/comparator.json`: `"theorem_names": ["ProximityPrize.Benchmark.candidate"],
"permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]`). The scalars are parsed
strictly (`benchmark_contract.py:24-103`): canonical ASCII decimal, bounded (`MAX_CENTIBITS =
100_000`, numerator/denominator ≤ 2^63-1, `0 < P < Q`, unsafe index in [1, 131072]), single
printable-ASCII line ≤128 bytes, NUL/control bytes rejected ("benchmark.sh transports this value
through command substitution, which silently drops NUL bytes"). The score is thus a *parameter of
the theorem statement*, not a value computed by trusted code: the trusted side only renders a
`Nat` literal into the type.

The score written to Yukon (`write-verifier-score.py`) re-reads `score.txt`/claim file and requires
equality with the service's verified value, challenge slug, challenge version, and commit SHA.

### 1.5 Axiom policy [F]

- Candidate: closure ⊆ {`propext`, `Classical.choice`, `Quot.sound`} (Comparator config). This
  excludes `sorryAx` and `Lean.ofReduceBool` (so `native_decide` is out; `decide` is in, and the
  current lower submission uses ~13k `by decide`).
- Protected path: `scripts/check-axioms.lean` (66 lines) imports `ProximityPrize`, (a) rejects any
  module in the environment whose top-level prefix is not in a reviewed list (`:11-14`), (b)
  rejects any `axiom` declared in a `ProximityPrize.*` module (`:30-40`), (c) checks
  `collectAxioms` of 13 protected declarations (encoder facts, `claimedRadius`, `ProtocolClaim`,
  `ProtocolClaimUpper`, …) against the whitelist (`:44-66`).
- ArkLib at e651978 has 263 `sorry` tokens in 82 files [F, `git grep -c -w sorry`]; these are
  harmless only because the candidate's axiom closure is checked. ArkLib's ToyProblem docs say the
  admit-backed capacity bounds are "deliberately outside this file's import cone"
  (`Leaderboard.lean:20-26`) and "the live downstream consumer ... enforces a transitive axiom
  closure of exactly `propext`, `Classical.choice`, `Quot.sound`" (`Impl/IRS.lean:52-56`).

### 1.6 Pipeline: setup.sh / benchmark.sh / scripts [F]

`setup.sh` (78 lines):
1. install elan if missing;
2. clone Comparator at `777e7f5...` and Landrun at `811cfff...`, verifying exact HEAD and clean tree;
3. copy `lean-toolchain` into Comparator, apply `benchmark/comparator-leanchecker.patch`, build
   `lean4export comparator`;
4. build Landrun with Go (Linux, unless `BENCHMARK_INSECURE_LOCAL=1`);
5. `lake exe cache get || true` (mathlib cache only);
6. `lake build ProximityPrize` (protected targets + their dependency closure; "The submitted
   solution is intentionally not built here; Comparator must be the first process to compile it",
   `setup.sh:66-68`);
7. `lake env lean scripts/check-axioms.lean`.

The Comparator patch (63 lines) replaces Comparator's fresh-environment kernel replay with a
sandboxed `leanchecker` over the untrusted module prefix. Reason (`setup.sh:41-46`):
"Comparator's fresh-environment replay ignores declaration-local recursion limits and cannot replay
CompPoly's checked KoalaBear.Ext6 irreducibility certificate. Keep Comparator's structural/axiom
export checks, but recheck every untrusted submission module with Lean's kernel against the already
audited imports in a read-only Landrun sandbox." [Lesson: heavy computational certificates in
the trusted import closure (Ext6 irreducibility) broke the standard Comparator replay.]

`benchmark.sh lower|upper` (80 lines): import audit → scalar read → render challenge → run
Comparator inside `systemd-run --user ... RestrictAddressFamilies=~AF_UNIX` with Landrun
(`benchmark.sh:56-68`) → `write-benchmark-score.py` writes `.yukon/<track>-score.json` with
`"verified": False, "independentVerified": False, "launchEligible": False,
"verificationAuthority": "local-comparator-diagnostic"`, plus `arklibRev` read from the manifest.

Authoritative path (`.github/workflows/benchmark.yml`, 125 lines): GitHub job does **not** build
Lean. `scripts/submit.py` POSTs `{repository, commit, challenge[@version]}` to
`https://proximity-prize.zksecurity.xyz` with a GitHub OIDC token (re-minted every 240 s), polls
`/v1/submissions/{id}` to a terminal state (`verified|rejected|failed|source_failed|timeout|cancelled`),
`verdict-gate.py` separates proof rejections from infrastructure failures, `write-verifier-score.py`
cross-checks score/claim/commit/version. Job timeout 360 min. So the real verifier is an external,
autoscaled (≤3 hosts) service fetching the commit itself; the repository holds the statement and
a local diagnostic replica: "The one cheap check kept when the heavy Lean CI was removed"
(`.github/workflows/check-versions.yml:2`).

Versioning: `challenges.json` is the single source of truth for the immutable challenge version
(`proximity-prize-reduction-lower @ irs-reduction-threshold-v17`, upper `-v15`);
`scripts/check-versions.py` fails CI if any other file hardcodes a version. (README still says
`v10`, `README.md:127-130`: stale doc [F].)

### 1.7 Yukon integration [F]

`benchmark.json` (schemaVersion 2): two tracks, each with `category: "lean"`, `direction` `+`/`-`,
`editablePaths: ["ProximityPrize/SubmissionLower"]` (resp. Upper), `setupCommand ./setup.sh`,
`benchmarkCommand ./benchmark.sh lower|upper`, `scorePath .yukon/<track>-score.json`,
`runner: {provider: github-actions, workflow: benchmark-irs-reduction-threshold-<x>.yml}`.
`editablePaths` is what makes the protected targets protected from the agent's point of view;
`yukon switch <track>; yukon run` (`README.md:113-121`).

---

## 2. How ArkLib is used

### 2.1 Imports [F]

`IRSProfile.lean:6-10` (the only ArkLib imports in the trusted base):
```lean
import ArkLib.ProofSystem.ToyProblem.Codegen
import ArkLib.ProofSystem.ToyProblem.Leaderboard
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.UniqueDecoding
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
import CompPoly.Univariate.NTT.KoalaBear
```
`TargetUpper.lean` additionally imports `Mathlib.Data.Nat.Choose.Central`, `Mathlib.Data.Set.PowersetCard`.

`ToyProblem.Leaderboard` → `Impl/FRS`, `Impl/IRS`, `Spec/SimplifiedIOR` → `Spec/General`, which
imports `ArkLib.OracleReduction.Security.RoundByRound`, `ArkLib.OracleReduction.Security.RbrGame`,
`ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ`, `ProximityGap.Errors`, `ListDecodability`.
So the full `OracleReduction` framework (ProtocolSpec, Prover/Verifier/OracleVerifier,
security definitions, VCVio's `OracleComp`/`simulateQ`) *is* in the trusted import closure, even
though the target statements themselves never mention a security game (see 2.4).

ToyProblem directory sizes at e651978 [F]: Definitions 53, SoundnessBounds 1373, Spec/General 1438,
Spec/KnowledgeSoundness 477, Spec/Completeness 383, Spec/SimplifiedIOR 629, Spec/ErasureDecoder 294,
Impl/IRS 1127, Impl/FRS 432, ConstrainedCode 320, Leaderboard 124, Codegen 98 lines.

### 2.2 The toy IOP (ABF26 Construction 6.2) in ArkLib terms [F]

Paper: Arnon–Boneh–Fenzi, "Open Problems in List Decoding and Correlated Agreement" [ABF26], §6.
Relation (`ToyProblem/Definitions.lean:33-51`):
```lean
def RelationFor {k ℓ : ℕ} (encode : (Fin k → F) →ₗ[F] (ι → A))
    (v : Fin k → F) (μ : Fin ℓ → F) (W : Fin ℓ → ι → A) : Prop :=
  ∃ M : Fin ℓ → Fin k → F, (∀ i, W i = encode (M i)) ∧
    ∀ i, ∑ j, M i j * v j = μ i

def RelaxedRelationFor {k ℓ : ℕ} (encode : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0)
    (v : Fin k → F) (μ : Fin ℓ → F) (W : Fin ℓ → ι → A) : Prop :=
  ∃ Wstar : Fin ℓ → ι → A, RelationFor encode v μ Wstar ∧
    ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
      ∀ i, ∀ j ∈ S, W i j = Wstar i j

def winningSetFor {k : ℕ} (encode : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0)
    (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → A) : Set F :=
  {γ | RelaxedRelationFor (ℓ := 1) encode δ v
    (fun _ ↦ μ₁ + γ * μ₂) (fun _ j ↦ f₁ j + γ • f₂ j)}
```
Note "The encoding map is part of the data: replacing it by an existentially chosen map with the
same range would change the constrained relation" (`Definitions.lean:15-16`), and
`Spec/General.lean:269-272`: "with an existentially quantified encoder ... honest completeness is
false". [Lesson: pin the encoder, not just the code.]

Protocol (`Spec/General.lean:220-222`, 3-round `ProtocolSpec`):
```lean
@[reducible]
def pSpec : ProtocolSpec 3 :=
  ⟨!v[.V_to_P, .P_to_V, .V_to_P],
   !v[F, Fin k → F, Fin t → ι]⟩
```
(γ ← F; prover sends g ∈ F^k; spot-check positions x ∈ ι^t). Oracle statements are two words
`f₀, f₁ : ι → A` (`OracleStatement ι A : Fin 2 → Type := fun _ ↦ ι → A`, `:184`).
Decision predicate (`:253-257`):
```lean
def Accepts (encode : (Fin k → F) → (ι → A))
    (stmt : Statement (F := F) k) (f : ∀ i, OracleStatement ι A i)
    (γ : F) (g : Fin k → F) (xs : Fin t → ι) : Prop :=
  (∑ j, g j * stmt.1 j = stmt.2.1 + γ * stmt.2.2) ∧
  ∀ j : Fin t, encode g (xs j) = f 0 (xs j) + γ • f 1 (xs j)
```
`OracleVerifier` (`:512-532`), monadic, acceptance = no `guard` failure, output `Unit`:
```lean
def oracleVerifier (encode : (Fin k → F) → (ι → A)) :
    OracleVerifier []ₒ (Statement (F := F) k) (OracleStatement ι A)
      OutputStatement OutputOracleStatement (pSpec (ι := ι) (F := F) k t) where
  verify := fun stmt challenges ↦ do
    let γ : F := challenges ⟨⟨0, by decide⟩, by rfl⟩
    let xs : Fin t → ι := challenges ⟨⟨2, by decide⟩, by rfl⟩
    let g : Fin k → F ← liftM <| queryMessage (ι := ι) (F := F) (k := k) (t := t)
    guard (∑ j, g j * stmt.1 j = stmt.2.1 + γ * stmt.2.2)
    for j in (List.finRange t) do
      let f₀ : A ← liftM <| queryOracleStatement (ι := ι) (A := A) 0 (xs j)
      let f₁ : A ← liftM <| queryOracleStatement (ι := ι) (A := A) 1 (xs j)
      guard (encode g (xs j) = f₀ + γ • f₁)
    pure ()
  ...
```
`OutputStatement := Unit`, `OutputOracleStatement : Fin 0 → Type := nofun`, `OutputWitness := Unit`
(`:197-208`): this is literally a reduction from the relation to the trivial relation, i.e. a
proof system, with "accept" encoded as non-failure of the `OptionT` computation. Input relation
`inputRelationFor` (exact, `:274-278`) and relaxed `outputRelationFor encode δ` (`:289-294`).
Doc caveats (`:94-97`): "extraction **time** ... is outside ArkLib's cost-free model, and the
verifier's query complexity (`2t + 1`) is documented, not enforced (`OracleVerifier.numQueries` is
upstream-sorried)."

The IRS instance (`Impl/IRS.lean`): `encoder k s hdvd domain` (`:116`), `oracleReduction`
(`:273`), executable `transitionExtractor` (`:245-252`: erasure-decode both words on the maximal
post-γ agreement set), named `rbrExtractor` (`:358`) and `straightlineExtractor` (`:377-384`):
```lean
def straightlineExtractor (k s t : ℕ) (hdvd : s ∣ k) (domain : ι ↪ F) :
    Extractor.Straightline []ₒ ... (Spec.pSpec (ι := ι) (F := F) k t) :=
  fun stmtIn _ tr _ _ ↦ pure <|
    transitionExtractor k s hdvd domain stmtIn
      (tr ⟨0, Nat.zero_lt_succ _⟩)
      (tr ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)
```
`ToyProblem/Codegen.lean` (98 lines) adds an `assert_toy_ir` command that fails elaboration unless
each named declaration (encoder, decoders, extractors, prover, oracleVerifier, oracleReduction, ...)
has compiler IR, i.e. is genuinely executable (`Codegen.lean:23-26`, used at `:78-96`):
```lean
elab "assert_toy_ir " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
    throwError "expected compiler IR for `{name}`"
```
Because `IRSProfile` imports `Codegen`, the protected build itself fails if any of these objects
became `noncomputable`. [Lesson: an "executability gate" in the trusted import closure.]

### 2.3 Security definitions used [F]

ArkLib `OracleReduction/Security/Basic.lean` at e651978:
- `Extractor.Straightline` (`:218-224`): `StmtIn → WitOut → FullTranscript pSpec → QueryLog oSpec
  → QueryLog oSpec → OptionT (OracleComp oSpec) WitIn`.
- `Verifier.knowledgeSoundnessWith relIn relOut verifier extractor knowledgeError` (`:269-291`):
  the extractor is a *parameter* ("keeps the extractor's identity in its type. This is the
  appropriate public contract when a caller needs to name, execute, or audit the exact extractor").
  Event: `(∀ extractedWitIn ∈ extractedWitIn?, (stmtIn, extractedWitIn) ∉ relIn) ∧ (stmtOut, witOut)
  ∈ relOut`, probability `≤ knowledgeError`, quantified over all `stmtIn`, `witIn`, `prover`.
- `knowledgeSoundness` (`:314-…`) = `∃ extractor`, same game. Its docstring records a past
  vacuity bug class: running the extractor inside the outer `OptionT` would let "the always-failing
  extractor `fun _ _ _ _ _ => failure` ... drive the game's event probability to `0`, vacuously
  discharging knowledge soundness (at error `0`!)". Also: "failures of the reduction execution
  itself (e.g. the verifier aborting) are still excluded from the event".
- RBR: `rbrKnowledgeSoundness` / `rbrKnowledgeSoundnessWith` / `rbrKnowledgeSoundnessWorstCase`
  (`Security/RoundByRound.lean:413, 440, 531`), with `KnowledgeStateFunction` and
  `Extractor.RoundByRound`.

Toy-problem headline theorems (all sorry-free, axioms ⊆ {propext, choice, Quot.sound} per
`Spec/General.lean:116-120`):
- `Spec.oracleReduction_perfectCompleteness` (`Spec/Completeness.lean:111`);
- `Spec.oracleVerifier_rbrKnowledgeSoundnessWorstCase` (`Spec/General.lean:1375`) (L6.8);
- `Spec.oracleVerifier_knowledgeSoundness_winningSetUpperBound` (`Spec/KnowledgeSoundness.lean:461-472`):
  ```lean
  (oracleVerifier (k := k) (t := t) (encode : (Fin k → F) → (ι → A))).knowledgeSoundness
      (WitOut := OutputWitness) init impl
      (outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ)
      (Set.univ : Set ((OutputStatement × ∀ i, OutputOracleStatement i) × OutputWitness))
      (winningSetUpperBound encode δ t)
  ```
  i.e. relIn = relaxed relation, relOut = `Set.univ` ("verifier accepted").
- `Impl.IRS.oracleVerifier_knowledgeSoundnessWith_straightlineExtractor` (`Impl/IRS.lean:1063-1088`):
  same game with the *named* executable extractor and error `certifiedExtractorError k s t domain δ`,
  under hypotheses `hfull : k / s ≤ Fintype.card ι` and `hδ : δ < minRelHammingDistCode (RS code)`.

### 2.4 Error quantities and their connection to the score [F]

`SoundnessBounds.lean:1271-1277`:
```lean
noncomputable def certifiedGammaError
    (C : ModuleCode ι F A) (δ : ℝ≥0) : ℝ≥0 :=
  ENNReal.toNNReal <|
    mcaError (AffineLineGenerator F) C (δ : ℝ) +
      ((Code.Lambda
        ((C ^⋈ (Fin 2) : ModuleCode ι F (Fin 2 → A)) : Set (ι → Fin 2 → A))
        (δ : ℝ)).toNat : ENNReal) / (Fintype.card F : ENNReal)
```
with `mcaError G MC δ := ⨆ U, Pr_{x ←$ S}[IsMCA G MC x U δ]` (`ProximityGap/ProximityGenerators.lean:152-154`)
and `Code.Lambda C δ := ⨆ f, (closeCodewordsRel C f δ).encard` (`ListDecodability.lean:139-140`).
`Impl.IRS.certifiedGammaError k s domain δ := ToyProblem.certifiedGammaError (irsCode domain k s) δ`
(`Impl/IRS.lean:662-664`).

`SoundnessBounds.lean:1134-1148, 1347-1356`:
```lean
noncomputable def winningSetRatio ... (x : ViolatingInstance enc δ) : ℝ≥0 :=
  ((winningSetFor enc δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard : ℝ≥0) / (Fintype.card F : ℝ≥0)

noncomputable def winningSetDensity {k : ℕ}
    (enc : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0) : ℝ≥0 :=
  ⨆ x : ViolatingInstance enc δ, winningSetRatio x

noncomputable def winningSetUpperBound ... (δ : ℝ≥0) (t : ℕ) : ℝ≥0 :=
  (1 - δ) ^ t + winningSetDensity enc δ * (1 - (1 - δ) ^ t)

noncomputable def certifiedExtractorError (C : ModuleCode ι F A) (δ : ℝ≥0) (t : ℕ) : ℝ≥0 :=
  (1 - δ) ^ t + certifiedGammaError C δ * (1 - (1 - δ) ^ t)
```
Bridge: `winningSetDensity_le_certifiedGammaError` (`SoundnessBounds.lean:1293`), and
`winningSetUpperBound_le_certifiedExtractorError` (`:1360`). ArkLib explicitly does *not* prove
the converse (winning-set density = optimal adversary's game error): "the matching
optimal-adversary/lower-coupling theorem needed to identify it with a minimal game error is not
asserted here" (`:1142-1145`).

How the score relates to protocol security [F/I]:
- The trusted *target* states only numeric facts about `certifiedGammaError` (lower) or
  `winningSetDensity` (upper) plus the spot-check inequality. It never mentions
  `knowledgeSoundness`. The link "certifiedGammaError bounds the combination-round KS error of the
  executable straight-line extractor" is an ArkLib theorem in the trusted import closure, audited
  once by the organisers, not re-proven per submission. [F]
- Hence a lower-track certificate implies, via ArkLib, KS error of the full IOP
  ≤ `(1-δ)^128 + 2^-128·(1-(1-δ)^128)` ≤ `2^-b + 2^-128`, but this implication is *not* restated in
  the contract and is not what is scored [I, from the definitions]. The README is honest that the
  score "is not a full-protocol security claim".
- The upper track is a *combinatorial attack lower bound* on a quantity that ArkLib only proves to
  upper-bound the game error, so an upper certificate does **not** construct an attacking prover
  ("This threshold certificate does not construct an end-to-end attacking prover",
  `TargetUpper.lean:258-259`). [F]

`Leaderboard.lean` (124 lines) is a "neutral fixed-radius reference interface" that ArkLib keeps
for the downstream prize: `FixedRadiusParameters` (`:38-44`: `k, t, code, encoder,
encoder_injective, encoder_range`), projections `winningSetUpperBound`, `certifiedExtractorError`,
and the warning (`:105-110`): "**The carrier is directional, and inhabitation alone asserts
nothing.** ... *every* weaker `bound` qualifies ... Any downstream policy layer must therefore
compare the numerals". `IRSProfile.parameters` instantiates it but the targets don't use it.

### 2.5 Division of labour ArkLib vs. prize repo [F]

ArkLib (upstreamed via PR #754 specifically for the prize; `lakefile.toml:10-13` comment) owns the
generic protocol, games, extractors, error definitions and bridge theorems, all parametric. The prize
repo owns only "the concrete downstream choices which intentionally do not live in ArkLib: the field,
smooth evaluation domain, code dimensions, repetition count, and the public argument-size estimate"
(`IRSProfile.lean:15-17`), plus the scoring structures. ArkLib's `Leaderboard.lean:65-72`
deliberately has "no in-tree interleaved-RS inhabitant" to avoid forking the protected profile.

---

## 3. Trusted base: size, readability, non-vacuity

Size [F]:
- In-repo Lean: 290 lines (177 + 59 + 54), of which the scored statements are ~30 lines of Lean.
  Plus `scripts/check-axioms.lean` (66).
- Trusted scripts: `check-submission-imports.sh` 194, `benchmark_contract.py` 193,
  `render-benchmark-challenge.py` 61, `write-*-score.py` 120/192, `benchmark.sh` 80, `setup.sh` 78,
  Comparator patch 63, workflows ~150. Plus Comparator, Landrun, leanchecker, and the remote service
  (not in repo).
- ArkLib definitions an auditor must read to understand the statements: `Definitions.lean` (53),
  `SoundnessBounds.lean` `ViolatingInstance`/`winningSetRatio`/`winningSetDensity`/
  `certifiedGammaError` (~60 lines), `ProximityGenerators.lean` `IsMCA`/`mcaError`/
  `AffineLineGenerator` (~50), `ListDecodability.lean` `Lambda`/`closeCodewordsRel` (~30),
  `ReedSolomon.code`, `ReedSolomon.Interleaved.irsCode`, `Code.minRelHammingDistCode`, interleaving
  `^⋈`, `GrandChallenges.gridPt`/`prizeThreshold`, CompPoly `KoalaBear.Ext6` and the NTT domain.
  [I] Roughly 300-500 lines of ArkLib definitions, all coding-theoretic; no game semantics needed
  to read the statement. To understand *why* the number matters you need the KS theorem and the
  `OracleReduction` stack (VCVio `OracleComp`, `simulateQ`, `runWithLog`), which is far larger.
- Trusted import closure size: see §4 measurements (number of modules built).

Readability [I]: very high for the statements. Each field is one inequality between named
quantities; docstrings map each to a paper definition/lemma (ABF26 Def 6.11, Lemma 6.10). Every
nontrivial number is a `Nat` literal in the theorem type.

Non-vacuity / binding executable objects [F]:
1. **Sanity theorems in the protected file** pin the profile's meaning: `encoder_injective`,
   `encoder_range : Set.range encoder = code`, `dimension = 2^20`, `alphabetRate = 1/2`,
   `minDistance = 131073`, `minRelativeDistance_eq` (`IRSProfile.lean:72-152`). These are checked
   at setup and their axioms audited by `check-axioms.lean`.
2. **Executability gate**: `assert_toy_ir` in `ToyProblem.Codegen` (imported by the profile)
   ensures the encoder, erasure decoder, transition/RBR/straight-line extractors, prover, verifier
   and reduction compile to IR, so "executable straight-line extractor" is a checked claim, not a
   comment. The KS theorem names `straightlineExtractor` in its type (`knowledgeSoundnessWith`).
3. **Admissibility field** `δ ∈ (0, minRelativeDistance)` rules out degenerate radii; scalars are
   range-checked (`0 < P < Q`) before rendering.
4. **Directional carriers documented**: ArkLib's `FixedRadiusCertificateBound.self` docstring
   flags that a `≤ bound` carrier is trivially inhabited; the target compares to a fixed numeral
   (`2^-128`) instead.
5. **`ENNReal → ℝ≥0` truncation guarded**: `certifiedGammaError` uses `ENNReal.toNNReal` and
   `Lambda.toNat`, both of which send `⊤` to `0` (a classic vacuity trap). ArkLib proves
   `coe_certifiedGammaError` (sum is never ⊤, `SoundnessBounds.lean:1279-1290`) and
   `Code.Lambda_ne_top [Finite F]` (`ListDecodability.lean:468-470`, via `Lambda_le_card`), so
   `toNat` is faithful for the finite alphabets used here. Auditors of recursion.fast should
   watch for the same pattern (a `toNat`/`toNNReal` of a possibly-infinite quantity silently
   becomes 0).
6. **Encoder pinned** in the relation (see 2.2).
7. **Upper track quantifies over the whole suffix** instead of assuming monotonicity.

---

## 4. Baseline candidates and build/check times

### 4.1 Baselines (initial commit a36cdb6a) [F]

| Track | Files | Lines | Score | Claim | Proof method |
|---|---|---:|---|---|---|
| lower | `Solution.lean` | 198 | 5300 (53.00 bits) | radius `1/4` | unique-decoding regime: `RS_correlatedAgreement_affineLines_uniqueDecodingRegime` (BCIKS20, in ArkLib) gives MCA ≤ n/|F|; `mcaError_interleaved_le` transports to IRS; `Lambda(C^2, 1/4) ≤ 1` from unique decodability; so `certifiedGammaError(1/4) ≤ (2^18+1)/|F| ≤ 2^-160`; spot-check `(3/4)^128 ≤ 2^-53` by `norm_num` |
| upper | `Solution.lean`, `IRSHalfRadius.lean`, `HalfRadiusCollision.lean` | 52+211+369 = 632 | 12800 (128.00 bits) | index 131072 (δ*=1/2) | "half-radius interpolation attack": `winningSetSoundness_eq_one` on `[1/2, minRelDist)`; spot-check `(1/2)^128 = 2^-128` |

### 4.2 Current HEAD submissions [F]

| Track | Files | Lines / bytes | Score | Claim |
|---|---:|---|---|---|
| lower | 153 `.lean` | 149,662 lines, 14.67 MB (cap 16 MiB) | 6815 (68.15 bits) | radius 331366399/1073741824 ≈ 0.30861 |
| upper | 5 `.lean` | 2,256 lines, 94 KB | 11613 (116.13 bits) | index 122369 (δ* ≈ 0.46680) |

Current lower: ~31.9k declarations, ~13.1k `decide` uses, largest file `LowerFoundation.lean`
1.75 MB importing 111 Mathlib modules (and no ArkLib module beyond the target) (function fields, Dedekind domains, RatFunc), i.e. a
generated, table-driven kernel computation at the edge of the byte budget. Current upper:
`score_nat : 2^218787 ≤ 139775^12800 := by decide` with `exponentiation.threshold 300000`,
plus an "orbit pencil" window attack and a "prescribed-top" attack.
[I] The bracket after 6 weeks: safe at δ ≈ 0.3086 (68.15 bits), unsafe from δ ≈ 0.4668 (116.13 bits).

### 4.3 Build measurements (probe)

Probe dir: `/home/devops/CambridgePQ/recursion.fast/probes/proximity-build/` (copy of the repo
without `.git`; baselines copied to `ProximityPrize/Baseline{Lower,Upper}/` with module paths
renamed; script `run.sh`, log `build.log`, summary `timings.txt`). Comparator/Landrun were *not*
built; this measures `lake` builds only. Machine: 32 cores, 62 GB, **shared with other concurrent
build probes** (load average 6-12 during the run), so wall clocks are upper bounds.

All on lean v4.32.2, mathlib from `lake exe cache get` (8639 files, 84 s), everything else built
from source. `/usr/bin/time` max-RSS is the largest single descendant process.

| Step | Cores | Wall | Peak RSS | Notes |
|---|---|---:|---:|---|
| `lake exe cache get` | - | 84 s | - | mathlib only; network-bound |
| `lake build ProximityPrize` (protected targets + closure) | 32 (shared) | **615 s** | 4.07 GB | builds ~464 non-Mathlib modules from source: VCVio 219, ArkLib 81, PolyFun 76, CompPoly 48, ToMathlib 23, Loom 9, Cslib 4, ProximityPrize 4 |
| `lake env lean scripts/check-axioms.lean` | 1 | 12 s | 4.06 GB | both "ok" lines printed |
| baseline lower (`a36cdb6a`, 198 lines) | 4 (`taskset`) | **15 s** | 4.08 GB | module itself 7.0 s |
| baseline upper (`a36cdb6a`, 632 lines) | 4 (`taskset`) | **33 s** | 4.11 GB | modules 13 + 7.9 + 6.2 s |
| `leanchecker ProximityPrize.BaselineLower` | 4 | 29 s | 3.69 GB | kernel re-check (as in the Comparator patch) |
| `leanchecker ProximityPrize.BaselineUpper` | 4 | 37 s | 6.17 GB | |
| `leanchecker ProximityPrize.Benchmark` (protected targets) | 4 | 35 s | 7.19 GB | |
| current upper (HEAD, 2256 lines) | 32 (shared) | **126 s** | 8.65 GB | `OrbitPencil` 68 s, `PrescribedTop` 25 s |
| current lower (HEAD, 14.7 MB, 153 files) | 32 (shared) | **>3000 s (timed out, partial)** | 7.19 GB | 92/153 submission modules built when the 50-min cap hit (job 4291/4351); summed per-module time of those 92 = 9,910 s; `LowerFoundation.lean` alone 1,094 s, `MergedWidePack6815_{0..7}` 421-904 s each. The deployment allows 4 h on 4 vCPU, so this submission presumably runs near its ceiling [I]. |

Import closure of `import ProximityPrize` (measured with
`probes/proximity-build/extra/ImportStats.lean`): **5398 modules, 495,846 constants**; Mathlib
3134, Lean 719, Init 601, Std 215, VCVio 219, Aesop 132, Batteries 82, ArkLib 81, PolyFun 76,
CompPoly 48, ToMathlib 23, Qq 14, Plausible 13, ImportGraph 10, ProofWidgets 10, Loom 9, Cslib 4,
LeanSearchClient 4, ProximityPrize 4. Loading it takes ~8.7 s and **4.05 GB RSS** per process
(consistent with AGENTS.md's "about 3 GiB and five seconds each"). Every protected/baseline module
costs ≥5-7 s just to import. On disk: mathlib build 6.4 GB, VCVio 468 MB, ArkLib 206 MB.

Notable: VCVio's Fiat–Shamir, Fischlin, Fujisaki–Okamoto, UC, Birthday modules are compiled and
loaded because they are in the transitive closure of `ArkLib.ProofSystem.ToyProblem.*` [F: they
appear in the build log and in the 219 VCVio modules of the closure]; the slowest from-source modules
were `ArkLib...BCIKS20.AffineLines.BWMatrix` (57 s), `VCVio...FiatShamir.Sigma.Stateful.Chain`
(41 s), `ArkLib.OracleReduction.Security.RoundByRound` (32 s). The ToyProblem modules themselves
build in 6-24 s each.

[I] Implications: (1) setup cost is dominated by building ArkLib+VCVio from source (~10 min on a
wide machine; on the prize's 4-vCPU hosts it is pre-baked into the verifier image); (2) a baseline
submission checks in well under a minute; (3) agent-optimised submissions grow to the resource
ceilings (current lower: >50 min here, >2.7 CPU-hours of module time for 60% of its modules), so
the ceilings, not the contract, determine check time.

---

## 5. Lessons: what makes an ArkLib-based contract auditable and fast

1. **Score a closed-form quantity, not a game.** The prize's statements are ~30 lines of numeric
   inequalities about named coding-theory quantities. All game semantics (OracleReduction, VCVio
   probability, extractors) sits in ArkLib behind *one* bridge theorem that the organisers audit
   once. Submitters never touch `knowledgeSoundness`. This is why the contract is tiny and stable
   (unchanged for 6 weeks) [F]. Cost: the score is a proxy, honestly labelled as such [F].
2. **Upstream the generic part into ArkLib, keep the profile downstream.** ArkLib PR #754 was
   written for this prize; the prize repo pins its squash-merge commit [F]. ArkLib keeps "no score
   format, ranking direction, submission metadata, or chosen operating radius"
   (`Leaderboard.lean:17-18`).
3. **Name the executable object in the theorem type** (`knowledgeSoundnessWith ...
   straightlineExtractor`) and gate executability (`assert_toy_ir`) in the trusted closure [F].
4. **Pin the encoder/representation, not just the set** (existential encoder breaks completeness and
   attack statements) [F].
5. **Scalars are parameters of the statement**, rendered from strictly parsed files into the
   Comparator challenge; trusted code never computes the score [F].
6. **Axiom closure, not sorry-freeness of dependencies.** ArkLib has 263 `sorry`s; the contract is
   safe because candidate and protected declarations are checked against {propext, choice,
   Quot.sound}, and admit-backed ArkLib files are kept out of the protected import cone by
   construction [F].
7. **Textual import/metaprogramming audit with comment stripping**, plus Comparator export check,
   plus sandboxed `leanchecker` kernel re-check [F].
8. **Resource ceilings are first-class rules** (files, bytes, RAM, time, disk, cores), with a
   long performance guide for agents [F]. Agents *will* use the whole byte budget (14.7/16 MiB) and
   `decide`-heavy tables [F].

Pitfalls observed:
- **Heavy trusted import closure.** Importing `ToyProblem.Leaderboard`/`Codegen` pulls the whole
  OracleReduction + VCVio stack and CompPoly's KoalaBear Ext6 (irreducibility certificate), costing
  "about 3 GiB and five seconds" per module load and forcing a full ArkLib source build at setup
  (no ArkLib cache): measured 615 s on a shared 32-core box, 5398-module closure, ~4 GB RSS per
  process just to import [F, §4.3].
- **Comparator incompatibility.** Ext6's checked irreducibility certificate and declaration-local
  recursion limits broke Comparator's fresh-environment replay; they had to patch Comparator to use
  sandboxed `leanchecker` instead (`setup.sh:41-46`) [F].
- **Dependency bloat from ArkLib's lakefile**: doc-gen4 (and transitively leansqlite, Cli, MD4Lean,
  BibtexQuery, UnicodeBasic) and checkdecls are build-time requirements of ArkLib and thus of the
  contract [F]. 
- **Toolchain pinning couples everything**: the prize is on v4.32.2 because ArkLib e651978 is;
  recursion.fast faces the same with ArkLib (v4.34.0) vs riscv-zkvm (v4.33.1) [F for prize; PLAN §1.11].
- **Two verifiers can drift**: local `benchmark.sh` vs. remote service source policy; AGENTS.md
  declares the manifest authoritative and the README already has a stale version string [F].
- **ENNReal/ℕ∞ truncations** (`toNNReal`, `toNat`) in error definitions are vacuity traps unless
  finiteness is proven [F/I].

---

## 6. Implications for recursion.fast

1. **The prize does not let submitters supply the protocol; recursion.fast must.** In the prize the
   IOP (verifier, prover, extractor) is fixed in ArkLib and only a *number* is contested. In
   recursion.fast the verifier itself is the submission, so the knowledge-soundness *game* must be in
   the trusted statement. Emulate the prize by keeping the statement shape small:
   `structure Claim (costParams : Nat ...) : Prop` with fields `completeness`, `knowledgeSound`
   (`OracleVerifier.rbrKnowledgeSoundness` / `knowledgeSoundnessWith` against a *fixed* trusted R1CS
   relation, relOut = `Set.univ`, error ≤ fixed `2^-λ`), `refines` (RISC-V program ↔ Lean verifier),
   and `cost ≤ claimed`, with scalars rendered from `score.txt` into the type. [I]
2. **Reuse ArkLib's games as-is, with the extractor named when possible.** The toy problem shows
   ArkLib's `knowledgeSoundness`/`rbrKnowledgeSoundness` are usable end-to-end for a real IOP with
   relIn = relation, relOut = `Set.univ`, `OutputStatement = Unit`, acceptance = `guard`
   non-failure. recursion.fast's "reduce R1CS to Unit" is exactly this shape [F for the pattern].
   Note the caveats ArkLib itself records: extractor *time* and query complexity are not modeled
   (`numQueries` is sorried) [F]. If cost or succinctness matter they must be enforced separately
   (e.g., by the RISC-V cost measurement), not inferred from the ArkLib theorem.
3. **Keep proximity-gap numerics out of the trusted cone, but let submitters prove them.** The prize
   shows proven bounds in the unique-decoding regime are available in ArkLib (BCIKS20 affine lines),
   Johnson-range MCA is an external admit, and agents can push beyond with massive `decide` proofs.
   recursion.fast's axiom policy (no `sorryAx`) will force proven regimes; expect agents to choose
   unique-decoding radii or to submit very large table-driven proofs. Budget files/bytes/time
   accordingly. [F/I]
4. **Contract-level hygiene to copy verbatim**: flat submission dir, no cross imports, allowlisted
   imports (Mathlib/ArkLib/CompPoly/riscv model), comment-stripped textual audit of
   metaprogramming, axiom whitelist via Comparator, sandboxed kernel recheck, strict scalar parser,
   `challenges.json` single source of version truth, `editablePaths` in `benchmark.json`. [F]
5. **Build-time budget.** Any trusted import of ArkLib's OracleReduction stack implies building
   ArkLib from source at setup (no Mathlib-style cache) and ~3 GiB RAM per concurrently built
   module. A recursion.fast contract that also imports a RISC-V semantics library will be heavier.
   Mitigations: (a) import only the minimal ArkLib modules (`OracleReduction.Security.Basic`,
   `RoundByRound`, the R1CS relation), not proof-system directories; (b) provide a prebuilt image
   (as the prize's service does: "built ahead of time in the verifier image"); (c) avoid heavy
   computational certificates (like Ext6 irreducibility) in the trusted closure, or verify them once
   and ship oleans. Measured for the prize (§4.3): closure 5398 modules / ~4 GB / ~9 s to load;
   setup 615 s (32 shared cores); baseline candidates 15-33 s on 4 cores. A recursion.fast MVP
   baseline that imports a similar ArkLib cone plus a RISC-V model will be at least this heavy
   (to be measured in probe P1); baseline checking in the minute range is realistic only if the
   RISC-V refinement proof is not a large kernel-evaluated symbolic execution. [F for the prize
   numbers, I for recursion.fast]
6. **Pin one toolchain and one ArkLib commit, ideally an ArkLib commit created for the competition**
   (as PR #754 was), and record `arklibRev` in every score artifact. [F/I]
7. **Separate safe/unsafe tracks are a useful pattern** for recursion.fast's security parameter
   choices: e.g., a side track where agents certify attacks (lower bounds on soundness error) for
   proposed parameter sets, keeping the main track honest. [I]
8. **Honesty labels in the README** ("not a full-protocol security claim") are a good norm:
   recursion.fast should state precisely what its theorem buys (IOP KS in ArkLib's model, not
   Fiat–Shamir/BCS security of a deployed NARG) [I].
