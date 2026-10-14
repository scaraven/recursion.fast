# Probe O-4: building Clean (commit 42fe4b26) on our pins

Date: 2026-10-14. Machine: 32 cores, 62 GiB RAM, otherwise idle (load average 0.5 to 3.5 during runs, see per-run
rows). Toolchain: Lake 5.0.0-src+5045d00, Lean 4.34.1. Nothing outside `probes/clean-build/` was modified (checked:
no file in the shared packages tree or in leanerVM is newer than the probe manifest). Nothing was committed.
Note: the repo `.gitignore` contains `logs/` and `.lake/`, so `probes/clean-build/logs/` and all build outputs are
git-ignored; use `git add -f` if the logs should be kept.

## Verdict (short)

* `import Clean.Air.FlatEnsemble` works as a plain `require` on our pins and coexists with Mathlib v4.34.1,
  CompPoly 572f997, ArkLib 7653a90, VCVio, PolyFun in one file. No root option is needed for Clean's
  `requiresModuleSystem := true`. Lake printed no toolchain/manifest/version-mismatch warning at all.
* The FlatEnsemble cone (39 Clean modules, 15.6k lines) builds from scratch in **2 min 18 s wall, 4 min 26 s user CPU,
  1.5 GiB peak RSS (largest single process)**, 2 deprecation warnings, 0 errors. Reproduced twice (2:19.0 / 2:17.8).
* The **full `Clean` library does not build as-is on Lean/Mathlib 4.34.1**: 63 of 160 modules fail, from 3 root causes
  (one removed Mathlib module and two proofs that broke). With 3 small patches (about 20 lines, in
  `logs/clean-4.34-patch.diff`) all 160 modules build: 4 min 02 s wall (709% CPU) plus a 32 s incremental rebuild.

## Setup (exact files)

`probes/clean-build/lean-toolchain`: `leanprover/lean4:v4.34.1`

`probes/clean-build/lakefile.toml`:

```toml
name = "CleanBuildProbe"

[leanOptions]
autoImplicit = false
relaxedAutoImplicit = false

[[require]]
name = "mathlib"
scope = "leanprover-community"
git = "https://github.com/leanprover-community/mathlib4"
rev = "v4.34.1"

[[require]]
name = "CompPoly"
git = "https://github.com/Verified-zkEVM/CompPoly"
rev = "572f997390aa4fc131ef30b1186fa1dcf292ca10"

[[require]]
name = "Clean"
path = "Clean-src"
```

`probes/clean-build/lake-manifest.json`: a copy of the repo root `lake-manifest.json` (so Arklib, VCVio, PolyFun,
cslib, aesop, ... stay listed) with `"name": "CleanBuildProbe"` and this entry inserted first (the format of a Lake
path package; leanerVM instead records Clean as `type: git`, `inputRev` = rev 42fe4b26, `inherited: false`):

```json
{ "type": "path", "scope": "", "name": "Clean", "manifestFile": "lake-manifest.json",
  "inherited": false, "dir": "./Clean-src", "configFile": "lakefile.lean" }
```

Lake did not rewrite the manifest in any run (`diff` against `logs/lake-manifest.before.json` is empty).
`.lake/packages` is a symlink to `/home/devops/CambridgePQ/recursion.fast/contract/.lake/packages` (Mathlib, CompPoly,
ArkLib etc. prebuilt; the shared tree also contains its own Clean checkout at 42fe4b26 with 40 prebuilt oleans for
4.34.1, which these runs deliberately do not use, since the root requires Clean by path).

`Clean-src/` = `Clean/`, `Clean.lean`, `lakefile.lean` copied from `leanerVM/.lake/packages/Clean` (183 `.lean`
files under `Clean/`; no `.git`, `.lake`, `lean-toolchain`, `lake-manifest.json`). Clean's lakefile is untouched:
it still says `require "leanprover-community" / "mathlib" @ git "v4.33.1"` and `require CompPoly from git ...@"v4.33.1"`.
Those are silently overridden by the root's requires (root requires are resolved first); Lake gave no warning.

`requiresModuleSystem`: it is a `lean_lib` option inside Clean's own lakefile (Lake 5.0 / Lean 4.34.1 accepts it)
that only asserts every Clean file starts with `module`. The root needs nothing; leanerVM's lakefile has no such
option either. Consumers that are not `module` files (our `Probe.lean`) can import module-system files.

Other variants (all under this directory): `variant-patched/` (own copy of Clean with the three 4.34 patches),
`variant-fullrepo/` (lakefile = all six `[[require]]` of the repo's `lakefile.toml` + Clean by path, `Clean-src`
symlinked to `../Clean-src`). `sample.sh` is a 2 s sampler of load average and process RSS (the summed RSS it logs
over-counts the shared mmap of .olean files, so do not read it as real memory; peak single-process RSS comes from
`/usr/bin/time -v`).

## Measurements

All wall/user/sys/RSS values are from `/usr/bin/time -v` (logs: `logs/NN-*-time.txt`). "Jobs" is Lake's count,
`Build completed successfully (N jobs)`; most of them are up-to-date checks of prebuilt Mathlib/dependency modules,
only the modules in the "compiled" column were actually run.

| # | Command (from `probes/clean-build/` unless noted) | Result | Wall | User | Sys | CPU | Peak RSS (max process) | Jobs | Compiled | Load avg before / peak sampled |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 | `lake build Clean.Air.FlatEnsemble --no-build` (dry run) | exit 3: 6 targets "out-of-date" (expected, nothing built yet); no warnings; manifest unchanged | 5.5 s | 5.7 s | 2.2 s | | | 1765 | 0 | n/a |
| 1 | `lake build Clean.Air.FlatEnsemble` from scratch, run 1 | success, 2 warnings | **2:18.97** | 265.67 s | 42.47 s | 221% | 1,585,248 KB (1.51 GiB) | 1765 | 39 | 0.46 / 2.22 |
| 1b | same, run 2 (deleted `Clean-src/.lake`, `.lake/build`) | success, same 39 modules | 2:17.81 | 264.25 s | 42.39 s | 222% | 1,582,036 KB | 1765 | 39 | 1.55 / 3.50 |
| 1c | same, no-op rebuild | success | 2.53 s | | | | 895,660 KB | 1765 | 0 | |
| 2 | `lake build Clean` (full library, unpatched), from scratch except cone modules already built from run 1 | **FAILED**, exit 1, 64 failed jobs | 1:27.86 | 682.57 s | 73.36 s | 860% | 1,822,404 KB | 1889 | 58 (+39 replayed) | 1.75 / 8.52 |
| 3 | `lake build Clean` in `variant-patched/` (patch 1 of 3 only: Primes import), from scratch | FAILED, exit 1, 2 root failures + 3 not built | 4:02.55 | 1525.74 s | 195.44 s | 709% | 1,887,956 KB | 1888 | 155 | 2.71 / 13.69 |
| 4 | same dir after patches 2 and 3 (Gates `rfl`, Or8 reproof), incremental | **success** (all 160 modules) | 0:32.33 | 60.53 s | 8.39 s | | 1,587,464 KB | 1888 | 5 | n/a |

Cone, run 1: critical path dominated; slowest modules were `Clean.Circuit.Loops` 22 s, `Clean.Air.Balance` 17 s,
`Clean.Circuit.Operations` 15 s, `Clean.Circuit.Theorems` 12 s, `Clean.Circuit.Explicit` 10 s,
`Clean.Utils.Tactics.ProvableStructDeriving` 8.4 s, `Clean.Air.FlatEnsemble` 5.7 s. At most 13 lean processes ran
concurrently. The cone has 39 modules and 15,562 lines (the brief said 37 modules / 15.4k lines; the closure computed
from the `import` lines by script gives 39 / 15,562; Lake compiled exactly 39). The cone does not import CompPoly;
only `Clean/Specs/Poseidon.lean` does (`CompPoly.Fields.BN254`), and it is outside the closure of `Clean.lean`.
The full closure of `Clean.lean` is 160 modules, 43,655 lines.

Estimated CI cost with Mathlib cache fetched (`lake exe cache get`) and the other packages prebuilt: cone about 4.5 CPU
minutes, so about 2.3 min wall on a many-core box (critical-path bound), likely 3 to 4 min on a 4-core runner. The full
patched library is about 26 CPU minutes (about 8 min on 4 cores at best). The cone alone is what the repo needs.

### Import time (`lake env lean X.lean`, warm page cache, 2 reps each, files in this directory)

| File | Imports | Wall (rep1 / rep2) | User | Peak RSS |
|---|---|---|---|---|
| `ProbeMathlibOnly.lean` | `Mathlib.LinearAlgebra.Matrix.Defs` | 3.67 / 3.67 s | 2.14 s | 1.57 GB |
| `ProbeCleanOnly.lean` | `Clean.Air.FlatEnsemble` | 5.95 / 5.61 s | 3.5 s | 2.79 GB |
| **`Probe.lean`** | `Clean.Air.FlatEnsemble` + `Mathlib.LinearAlgebra.Matrix.Defs` | **5.63 / 5.26 s** | 3.4 s | **2.80 GB** |
| `ProbeFullMathlib.lean` | `Mathlib` | 12.13 / 11.15 s | 7.0 s | 6.86 GB |
| `ProbeCleanFullMathlib.lean` | `Clean.Air.FlatEnsemble` + `Mathlib` | 11.96 / 11.42 s | 7.0 s | 7.22 GB |
| `variant-fullrepo/ProbeArkOnly.lean` | `ArkLib.OracleReduction.Execution` + Matrix.Defs | 7.44 / 7.42 s | 4.0 s | 3.37 GB |
| `variant-fullrepo/ProbeAll.lean` | Clean cone + `ArkLib.OracleReduction.Execution` + Matrix.Defs | 8.59 / 8.41 s | 4.8 s | 3.84 GB |

`Probe.lean` elaborates with no error; `#check @Air.Flat.Ensemble` prints
`Air.Flat.Ensemble : (F : Type) → [FiniteField F] → (PublicIO : TypeMap) → [ProvableType PublicIO] → Type 1`
(the namespace is `Air.Flat`, not `Clean.Air.Flat`) and a `decide` example about `Matrix.of` also passes, so
Clean's cone and Mathlib's `Matrix` coexist in one environment. The marginal import cost of the Clean cone over a
small Mathlib import is about +1.7 s and +1.2 GB; over `import Mathlib` it is about +0.3 s and +0.35 GB. Adding it to
an ArkLib import costs about +1.2 s and +0.5 GB. (`variant-fullrepo/ProbeAll.lean` first also imported
`CompPoly.Fields.BN254`, which failed with "object file ... does not exist": that module is simply not prebuilt in the
shared tree, unrelated to Clean; see `logs/07-ProbeAll.*` for the final run.)

`variant-fullrepo`: with all six repo requires plus Clean (path), `lake build Clean.Air.FlatEnsemble --no-build`
reported `All targets up-to-date (1765 jobs)`, exit 0, manifest unchanged (`logs/06-fullrepo-resolve.log`).

## Warnings and mismatches (verbatim)

Lake emitted none about toolchain, manifest, or dependency versions (grep over every log for
toolchain/mismatch/incompatible/manifest/requested outside `trace:` lines is empty). Clean's own `lean-toolchain`
(v4.33.1) and its `mathlib`/`CompPoly` `v4.33.1` requires are ignored silently. The only warnings are Lean deprecations:

Cone (2, both in `Clean.Gadgets.Conditional`):

```
warning: Clean/Gadgets/Conditional.lean:81:21: `if_false` has been deprecated: Use `ite_false` instead
warning: Clean/Gadgets/Conditional.lean:86:15: `if_true` has been deprecated: Use `ite_true` instead
```

Full library (patched, 18 warnings, `logs/04-patched-build.log`): `dif_pos` (11) -> `dite_eq_left`, `dif_neg` (2) ->
`dite_eq_right`, `if_neg` -> `ite_eq_right`, `if_true`, `if_false`, `cond_true` -> `Bool.cond_true`,
`cond_false` -> `Bool.cond_false`; plus a few `info: Try this: rwa [...]` linter suggestions in
`Clean/Gadgets/ByteDecomposition/Theorems.lean`. Clean sets no `warningAsError`; the repo's `warningAsError`
settings (leanerVM has `warningAsError = true` at its root) would not apply to a dependency's modules.

## What fails on 4.34.1 (full library, unpatched: 63 of 160 Clean modules, plus 1 missing Mathlib job)

Root causes (first lines of the errors, `logs/03-full-build.log`):

1. Removed Mathlib module (61 modules fail by "bad import" cascade): Mathlib v4.34.1 moved `Mathlib/Logic/Basic.lean`
   to `Mathlib/Basic/Logic/Basic.lean`. `Clean/Utils/Primes.lean:8` has `public meta import Mathlib.Logic.Basic`.
   ```
   error: no such file or directory (error code: 2)
     file: .../packages/mathlib/Mathlib/Logic/Basic.lean
   error: Clean/Utils/Primes.lean: bad import 'Mathlib.Logic.Basic'
   error: Clean/Types/U64.lean: bad import 'Clean.Utils.Primes'
   ```
   Cascades to `Types.U32/U64`, all Keccak, Rotation32/64, ByteDecomposition, Xor32/64, SHA256, BLAKE3 gadgets etc.
   The FlatEnsemble cone does not import `Clean.Utils.Primes`, which is why leanerVM could build "the affected import
   cone" on 4.34.1.
2. `Clean/Circomlib/Gates.lean:840:8: error: No goals to be solved` (a now-redundant `rfl` after `convert this`).
3. `Clean/Gadgets/Or/Or8.lean:57:52: error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats
   (200000) has been reached` (a `repeat rw [Nat.mod_eq_of_lt] at h_u16 <;> try omega` loop in
   `or_times_two_sub_xor` no longer terminates cheaply), then `(kernel) unknown constant
   '_private.Clean.Gadgets.Or.Or8.0.Gadgets.Or.Or8.or_times_two_sub_xor'` at lines 69, 76, 92.
   Dependents of the last two: `Or32`, `BLAKE3.FinalizeChunk`, and the root module `Clean`.

Patches that make all 160 modules build (statement-preserving; diff in `logs/clean-4.34-patch.diff`, applied in
`variant-patched/Clean-src` only; `Clean-src/` stays pristine):

1. `Primes.lean`: `Mathlib.Logic.Basic` -> `Mathlib.Basic.Logic.Basic` (one line).
2. `Gates.lean`: delete the `rfl` at line 840 (one line).
3. `Or8.lean`: reprove `or_times_two_sub_xor` (about 15 lines): `bv_decide` on `BitVec 16`, then `congrArg BitVec.toNat`,
   `simp only [BitVec.toNat_mul, ..._add, ..._or, ..._xor, ..._ofNat]`, `omega`.

I did not run `CleanTests` or audit axioms/`sorry` in Clean; the claim is only that the modules compile.

## Recommendation

Clean can be a `require` of this repo's untrusted library as-is **if the library only imports the
`Clean.Air.*` / `Clean.Circuit.*` cone** (we measured `Clean.Air.FlatEnsemble`; other Air/Circuit modules not in
the full-library failure set should behave the same). The root's pins win silently over Clean's v4.33.1 requires, no
manifest edit beyond the new `Clean` entry is needed, `requiresModuleSystem` needs nothing in our lakefile, and the
import cost on top of Mathlib is small (+1.7 s, +1.2 GB per Lean process; about 5.5 s total for a Clean+Matrix file).
Expected CI cost: about 2.3 min wall (4.5 CPU min) for a cold build of the cone once Mathlib and the other packages are
cached, 2.5 s for a no-op; mind that `lake build` of the whole repo default target must not pull `Clean` (the full
`Clean` library) or CI will fail on the 63 modules above. Pin Clean by `git` + `rev = 42fe4b26...` exactly as leanerVM
does (with root requires for mathlib v4.34.1 and CompPoly 572f997 so they override Clean's), and build only the
needed modules (`lake build RecursionFast.Library` will build exactly the imported cone). If the full Clean library
(Keccak, BLAKE3, SHA256, Poseidon gadgets) is ever needed, either wait for a Clean revision that targets 4.34 or
fork Clean with the three patches above (about 20 lines); the cost then is about 4 min wall / 26 CPU min cold. Not
tested: a `git` require against the shared packages tree (its Clean checkout is at the same rev and already has 40
prebuilt oleans for 4.34.1, but pointing Lake at it risks Lake re-validating/cloning inside the read-only tree).

## Logs

`logs/00-resolve-dryrun.log`, `01-cone-*` (run 1), `08-cone-run2-*`, `09-noop-*`, `02-*` (import timings),
`03-full-*` and `03-failed-modules.txt` (unpatched full library), `04-patched-*` (import patch only),
`05-patched2-*` (all three patches), `06-fullrepo-resolve.log`, `07-*` (ArkLib joint import), `clean-4.34-patch.diff`,
`lake-manifest.before.json`, and `*-samples.txt` (2 s load/RSS samples; summed RSS over-counts shared mmaps).
