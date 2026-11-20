# Mutation testing of the trusted contract

The contract (`RecursionFast/Contract/**/*.lean`) is trusted: nothing proves that it says what its
module headers say. Its controls (`RecursionFast/Controls/`) and the library's proofs about it
(`RecursionFast/Library/`) are what would notice a wrong definition. This directory measures how
much they notice: each **mutant** is one small change of a contract definition, applied to a
scratch copy of the repository, and a mutant is **killed** when some check of the organiser fails
on it.

* `mutants.toml`: the mutants. Each has an `id`, the contract `file`, the exact `original` text
  (it must occur exactly once), its `replacement`, the property it `breaks` and the check it was
  `expect`ed to be killed by. `calibrate = "survive"` marks a mutant expected to survive when it was
  written (an equivalent change, or a constant no check pinned); `equivalent = true` one that
  changes no meaning.
* `accepted.toml`: survivors accepted as such, each with its reason (an equivalent mutant).
* `run.py`: the runner; `results.json` and `results.md`: the last results (generated). **Pending:**
  the committed `results.*` and `targeted.*` are the last full run's, over the earlier seed leaf
  (99 mutants, base `377b489`); the committed-data leaf replaced its six leaf mutants by fifteen
  (`rel-leafcap-2^21` … `rel-leaf-count-zero`) and added `ext-leaf-one-block` and
  `rel-datanode-no-tag` (a data node without its tag, added after review) and `ext-tape-no-log` (a
tape without the log, which `Controls/MaskedLeaf.lean`'s log-reading extractor kills), and the run
over all 111
  and the targeted re-run of the `rel-*` mutants (`--targets RecursionFast.Controls.Relation
  --every`) are still to be made (their slots need `systemd-run --user` scopes);
  `targeted.json`, `targeted.md`: the controls added by this suite, each run alone against its
  mutant (`--targets <control module> --every`).

## The pipeline

For each mutant, cheapest first, stopping at the first kill:

1. `lake build RecursionFast.Contract`. A failure is **INVALID**: the mutant is not a contract
   (for example, a 31-byte Keccak output breaks `keccakDigest`'s length proof); it is recorded
   with the failing contract module.
2. `lake build RecursionFast`: the library and the controls. The first Lean file that fails
   **kills** the mutant (stage `proofs`), recorded by module and line. With `--every` the build
   runs to its end and every failing module is recorded (modules that import a failed one are not
   built, so this lists independent failures only).
3. With `--harness`, for a mutant that survived stage 2: the organiser tests of the core CI that
   run *compiled* contract code: `lake -f scripts/speed/lakefile.toml build extract signer`, then
   `.lake/build/bin/extract` (the compiled extractor interpreter on the witness-sending entry),
   `tests/service/test_lean_signer.py` (the Lean signer against the service) and
   `tests/harness/accprobe/run.py` (`acc` on a signed `2^16`-query trace and the organiser's
   canaries), each run only if the service's binaries are built in this checkout
   (`cd service && cargo build --release`, and `--features insecure-test-keys --target-dir
   target/test-keys` for the signer test). The gate fixtures (`tests/gate/check.sh`) are not a
   stage: they regenerate the olean manifest from the mutated build, so they check the gate, not
   the contract.

A mutant that passes every stage **SURVIVES**. A surviving mutant that changes the meaning is a
gap: it gets a control (in the matching `RecursionFast/Controls/*.lean`) and is run again; an
equivalent one is listed in `accepted.toml` with the reason.

A kill by a library proof can be incidental, a proof that unfolds a constant or closes by `rfl`
(the `rel-dataroot-empty-one` mutant breaks `Library/Tree.lean`'s `dataRoot_nil`, proved by
`rfl`, before any control is built). Where the property is load-bearing, a control states it directly, and
`--targets RecursionFast.Controls.X --every --out DIR` checks that the control alone kills the
mutant (`targeted.md`). Many kills are by `Library/Fast.lean`, `Library/KeccakFast.lean` and
`Library/Words.lean`, whose word-level twins restate the contract's layouts independently and are
proved equal to them: a change of the contract alone breaks that proof, and a change of both
would then meet the controls' known answers, which are decided on the twins.

In the harness stage, a build failure without a Lean error, or a test that times out or is killed
(exit 124 or 137), is ERROR, not a kill; so is any stage-1 or stage-2 failure without a Lean error
(for example an out-of-memory kill).

## Running it

From the repository root, after `lake build` (the runner checks `lake build --no-build
RecursionFast` first, since every slot starts from this checkout's `.lake/build`):

```
python3 -I tests/mutation/run.py --check                 # every original text occurs exactly once
python3 -I tests/mutation/run.py                         # all mutants, 3 in parallel
python3 -I tests/mutation/run.py --only rel-no-leafcap,sig-root-swap
python3 -I tests/mutation/run.py --file Signature.lean --harness
python3 -I tests/mutation/run.py --only rel-leafcap-2^21 --targets RecursionFast.Controls.Relation \
  --scratch /path/to/other/scratch --out /path/to/other/out --jobs 1
```

Each job works in its own slot `<scratch>/s<k>` (default scratch `$RF_MUTATION_SCRATCH`, else
`<this checkout>-mutation` beside it; about 0.5 GB per slot), reused from mutant to mutant: a copy of the working tree without
`.lake` and `.git`, its `.lake/packages` a symlink to this checkout's package tree (read only:
nothing in it is rebuilt) and its `.lake/build` copied from this checkout before every mutant. The
runner never deletes anything and never writes into this checkout except `--out` (default this
directory). Every command runs as `systemd-run --user --scope -p MemoryMax=16G taskset -c <cores>
timeout 1500 …` with `LEAN_NUM_THREADS=4`; the default cores are `16-20`, `21-25` and `26-31`, one
range per job (`--cores`, `--jobs`, `--threads`). Build logs are in `<scratch>/logs/`.

A run of every mutant (109; 99 before the committed-data leaf) takes about 30 minutes with 3 jobs on 16 cores (77 minutes of build
time in all, median 32 s per mutant): most are killed within a minute (the first failing module is
reached early and the build is stopped), and a survivor costs a rebuild of everything that imports
its file (about 3 to 4 minutes). It is not part of the CI (too slow
for every pull request, and it needs `systemd-run --user` scopes and 16 free cores): run it locally
before changing the contract or its controls, and commit the regenerated `results.md` and
`results.json`.
