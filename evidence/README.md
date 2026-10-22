# Evidence archived with the v3 contract

This folder keeps the kernel probes and interim harness tools that the v3 design record cites. Until
2026-10-22 they lived only on the development VM: in gitignored log folders, in untracked scratch
files, or on local-only branches. They are copied here verbatim, with the logs that were recorded
when they ran. None of this is built by `lake build`; the paths are outside every `lean_lib` glob.

Each probe was checked against the contract named in its row, not necessarily against this
branch's head (`6202402` and later): the S2R stage removed `ImageComputes` and the RISC-V machine,
so probes written against `15e4ae5` or `05fde28` do not compile here unchanged. To re-run one,
check out the commit named in its row and run it with `lake env lean <file>`.

## Kernel probes (`probes/`)

| file | checked against | what it shows | cited as |
|---|---|---|---|
| `LiteralTrigger.lean`, `.log` | `15e4ae5` (the S1 pin) | the O-25 backdoor with a hard-coded 32-byte trigger: the verifier equals `Controls/Backdoor.lean`'s and is certified by the same proof, yet its constant closure contains neither `blake2sOracle`, `tagRO` nor `Submission.Vb`, so the gate rejection proposed by the S1 review does not fire | ADV-M5, the comment on issue #4 |
| `CountingForm.lean`, `.log` | `15e4ae5` | two ROM-sound verifiers with no knowledge state at a useful error. `Product` (k fixed queries, answers in a set `T`): ROM error `(|T|/2^256)^k`, but every `Bounded ε` state has `ε ≥ |T|/2^256` (`product16_not_capped`; the shape of a multi-squeeze query phase). `Collision`: no state is bounded at `errorCap` (`collision_not_capped`, `collision_no_bound`), because `Bounded` quantifies over logs of every length | ADV-M2, ADV-M3, issue #5 |
| `TaskRfl.lean`, `.log` | `15e4ae5` | `Task.spawn`/`Task.get` are kernel-transparent: a parallel `V` is provably equal to the sequential one by `rfl` (`spawn_get`, `all_par`) | ADV-M1, issue #6 |
| `fastchain.log`, `refchain.log`, `build.log` | `15e4ae5` | measured BLAKE2s chain throughput in compiled Lean: the reference implementation (about 5.6–6.1 µs per compression) against an unrolled one (151 ns per compression sequential), with `Task.spawn`; the basis of the 37–43 ms against 20.9 s root-check comparison | ADV-M1, issue #6 |
| `Shallow.lean`, `.log` | `05fde28` plus the S2R draft | a step monad whose bind takes a Lean continuation charges one step for a `2^k` search, so the extractor's cost language must be deep | V3-S2R-H-M1 |
| `Review.lean`, `.log` | `4b3356a` | P1 `B(2^64) = 2^80 + 2^48`; P2 extractor memory was a constant (at most about `2^48` words); P3 a non-constructive extractor beyond `2^64` tape words; P4 a certified submission whose deployed `Vb` rejects every proof | V3-S2R-M1, m1–m3 |
| `P1_interface.lean` | `05fde28` | Candidate E (parametric `V`): `idxOf_full` (a width-chosen index map returns the whole answer) is a theorem. `cmpNat`, `encodeF`/`cmpF` and `pinned` are type-checked **definitions** (plus an `#eval`), not theorems | O25-M1, O25-M2 |
| `P2_hatches.lean` | `05fde28` | the digest-side escape hatches of Candidate E are closed (noncomputable, no instance, or a type mismatch), while `Nat.cast : ℕ → F` compiles | O25-m1 |
| `T1_pub_sees.lean`, `.log` | `05fde28` | Candidate T: `pubTau_eq_challenge` (a `pub` of T's type computes the first challenge), `evil_Vb`, a submitter-set `wf` flag, and `postHoc_iff` (the post-hoc check as plain data) | O25T-M1, O25T-M2, O25T-m1 |

## Interim harness tools (`interim-harness/`)

The S2/S3 interim organiser tools that produced both `HARNESS: ACCEPT` results (S2a against the
pin, and the honest entry `spartan-chain` against the amended contract). They were never pushed.
They are kept here as `git format-patch` series; apply them with `git am` on top of the base
shown in each row.

| series | source branch (local clone `rf-core-s2a`) | base | commits |
|---|---|---|---|
| `v3-s2-interim-harness/` | `v3/s2-interim-harness` | `15e4ae5` | `2a4588b`: v3 challenge stub, renderer, local proof-half harness, scratch setup |
| `v3-ks-interim-harness/` | `v3/ks-interim-harness` | `05fde28` (PR #11's commits are omitted here; they are in this branch's history) | `2464e97`, `26c3b23`, `9d5b26a`: the same tools on the amended contract; `09668b5`: the CompPoly `BF64`/`Ext3` allowlist and the olean manifest (most of the series' size); `4a1a1ed`: gate rule 4 over `V`, `P`, `E`, `img` |
