# S9 review (definitions lens): the trusted base as one object

Whole-repository adversarial review, Stage 9, reviewer 1 of 3 (definitions; the other two cover
incentives and feasibility). Date 2026-10-15. Repository `/home/devops/Verified-zkEVM/recursion.fast`
at `0451b32` (all stages committed; working tree clean apart from this report and `probes/s9/`).
Nothing outside `docs/reviews/S9-definitions.md` and `probes/s9/definitions/` was edited. Logs:
`logs/S9-definitions/` (gitignored). Skills used: `adversarial-review` (findings), `lean4:review`
(construct audit), `human-review-audit` (inventory format).

**Read.** `CLAUDE.md`; `docs/DESIGN.md` §1–§5, §8; `docs/DESIGN-AMENDMENTS.md` in full; the
verdicts, majors and "remaining gap"/"not claimed" sentences of every `docs/reviews/S*-review.md`.
In full, in reading order: `RecursionFast/Contract.lean` and `Field`, `Layout`, `Shapes`, `Security`,
`Machine`, `Extractor`, `Protocol`, `Hash/Blake2s`, `Compile`, `Recursion`, `Certificate`; the
reached part of the vendored machine (`execInstrBr`, `decode`, `MachineState` and its memory
helpers); `scripts/Gate.lean`, `scripts/AxiomAudit.lean`, `scripts/source-rule.py`,
`scripts/render-challenge.py`, `scripts/olean-manifest.py`, the header of `scripts/harness.sh`;
`RecursionFast/Challenge/{L,R}.lean.in`; `harness/lean/{Main.lean.in, RecursionFastHarness/Driver.lean}`;
the statement functions, `tree` and `selftest` of `harness/run-benchmark.py`. Library and Controls
as evidence only.

## Verdict

**The contract, read as one object, says what the design says; the harness's interim guard does
not.** Every seam the brief lists holds:

- `Protocol.Secure` is exactly perfect completeness on `relK k` plus round-by-round knowledge
  soundness with the image's bounded extractor at `ε ≤ 2^-128` per challenge round. No field or
  hypothesis makes it easier than the design says. One clause makes it *stronger* than the design
  text says: soundness ranges over non-admissible layouts too (S9D-m3, kernel-checked).
- `NARG`, `VKc.digest`, `nodeStmt`, `aggOK` use one `cfg`, one digest function and one byte
  convention end to end.
- The runner's Python statement tree agrees with `nodeStmt`/`pairUp`/`treeRoot` clause by clause.
- The rendered R certificate asserts `SubmissionR` with `fits`, `sound`, `complete` and `live`, at
  one `k` throughout.
- The extractor tape serialises every round of the prefix, injectively for admissible statements.
- The `2^(k+4)` entry cap fits the `2^(k+8)` index oracle at 3 words per entry, at every class.

The axiom audit of the whole trusted tree is clean: 1,285 constants (1,080 contract, internal names
included, plus 205 vendored), no non-standard axiom, no user `unsafe`/`partial`/`opaque`/
`implemented_by`/`extern`/`@[irreducible]`, no `decide`-closed proof inside a trusted definition,
and no theorem in the contract.

**One major finding (S9D-M1).** `scripts/source-rule.py`, which the S6b fix pass made the binding
interim guard against the raw compiler-state forgery (S6b-M3), tokenises differently from Lean.
Two edits, each invisible to it, reopen S6b-M3 end to end:

- a two-line prefix `def r : Nat := 0` / `example : Nat := r#check r`;
- a string literal inside an interpolation.

With the first edit, `ForgeRaw` gets 0 source-rule findings, the current gate binary says PASS,
and its importer's emitted code is `acceptAll`.

**Seven minor findings (S9D-m1 … m7).**

- **Non-load-bearing trusted text.** Sixteen trusted declarations, `E`'s arithmetic and the
  `rootOK` family among them, are outside the cone of every certificate.
- **Runner selftest blind spot.** The selftest cannot see a `d0`/`d1` swap.
- **Undocumented clause.** The rejection of non-admissible layouts is not documented.
- **Second layout reader.** The recursion key is indexed from a second reading of the layout JSON.
- **Binding theorem outside CI.** The binding theorem behind `Compile.lean`'s review lives in a
  probe.
- **Stale docstrings.** These are in the carried-over files.
- **Dead vendored reach.** A third of the vendored reach is dead on the extractor's path.

| ID | Severity | One line |
|---|---|---|
| S9D-M1 | major | the source rule's lexer diverges from Lean's (`r#…`, a string inside `s!"{…}"`): ForgeRaw passes source rule + gate, importer runs `acceptAll` |
| S9D-m1 | minor | 16 trusted declarations certify nothing: 12 are dead or conveniences (E's `+ * 0 1`, `K`'s `-`/`neg`, `E.toBytes`, `Round.decode`, `FullTranscript.tapeWords`, …), 4 are the `rootOK` family (m2) |
| S9D-m2 | minor | `pairUp`/`treeRoot`/`rootOK` are a specification of Python, not a certified statement; the runner selftest uses `dC = dL` |
| S9D-m3 | minor | `Secure` obliges the verifier to reject non-admissible layouts and bounds the error per round; neither is said |
| S9D-m4 | minor | the recursion key is indexed from `LayoutJson.parse`'s reading of the JSON, not from the certified `C` |
| S9D-m5 | minor | `opening_binding` (Merkle binding ⇒ collision) is a review probe outside CI |
| S9D-m6 | minor | stale/misleading docstrings: Shapes header (`Agrees`, QUERY), "reductions", "DESIGN §5", `NARG`'s key, Protocol's computable list |
| S9D-m7 | minor | 316 of the 930 vendored lines reached (ZiskAccel) and six arms of `execInstrBr` are dead on the contract's path; §8 overstates the reading |

---

## 1. Findings

### S9D-M1 (major): the source rule does not lex like Lean, and S6b-M3 is open again

- **Declaration.** `scripts/source-rule.py`, `tokens` (lines 54–121). It is the TRUSTED harness tool
  that S6b-A20 made "interim and binding": the only layer that rejects the raw forgery
  `probes/s6b/gate/ForgeRaw.lean`, which no gate rule can see (CI asserts the gate PASSES it).
- **Problem 1 (raw strings).** Line 71 treats any `r` at a token start followed by `#` as a raw
  string opener `r#"…"#`. It then searches for `"#` and, if there is none, skips to the end of the
  file (line 78, `end = n`). Lean opens a raw string only for `r` + `#…#` + `"`. So `r#check r` is
  two things to Lean: the identifier `r`, then the allowed command `#check r`. To the rule it is
  the start of a string that swallows the rest of the file.
- **Problem 2 (interpolation).** Lines 84–89 close an interpolation `s!"{…}"` at the first `}` by
  counting braces, blind to string literals inside the interpolant. In `s!"{ "}" }"` the rule
  closes at the `}` inside `"}"`, and from there its string/code parity is inverted. The next
  line's command is read as string content. Every literal can be terminated (end the file with
  `-- "`), so failing closed on unterminated literals would not catch this one.
- **Evidence (all logs under `logs/S9-definitions/`).**

  | Probe | What it shows | Log |
  |---|---|---|
  | `probes/s9/definitions/srcrule/RawHash.lean` | Lean runs two `#eval`s written after `r#`; the rule reports 0 findings | `source-rule-bypass.log`, `source-rule-rawhash.log` |
  | `probes/s9/definitions/srcrule/Interp.lean` | importing only `RecursionFast.Contract`, Lean runs a `run_cmd` hidden by the interpolation; the rule reports 0 findings | `source-rule-interp.log` |
  | `probes/s9/definitions/srcrule/ForgeRawR.lean` | the S6b forgery `ForgeRaw.lean` with the two prefix lines after its imports: 0 findings (the original gets 5); it elaborates; its importer `UseRawR.lean` emits `l_useDec = List_beq(msg, msg)`, the `acceptAll` CI greps for | `source-rule-bypass.log` |
  | the current gate binary (`.lake/org/.lake/build/bin/gate`, built 07:11, after `Gate.lean`'s last edit at 07:09) on `ForgeRawR` | the manifest, allowlists, `--computable S7Raw.submission` and `--badge-root S7Raw.submission` all match CI's; result `gate: badge-root-module ForgeRawR … gate: PASS` | `forgerawr-gate2.log` |

  So a submission passes the source rule and the gate. The comparator replays kernel terms, which
  the forgery leaves untouched (S7-M1; not run here). Its badge `verify` runs code the kernel
  never saw.
- **Fix (precise).**
  1. **Lex like Lean.** Raw strings: `re.match(r'r(#*)"', src[i:])` only, else `r` is an
     identifier. Interpolations: scan the interpolant with the full tokenizer (recursive, string
     and char literals and comments inside), not by counting braces.
  2. **Fail closed.** Any literal or comment still open at end of file is a finding.
  3. **Add a lexer-free second pass.** Scan the raw bytes, comments and strings included, with
     word-boundary regexes for the banned words (`run_\w+`, `#[A-Za-z]\w*` minus the allowed
     four, `\bunsafe\w*`, `\bpartial\b`, `persistentEnvExtensionsRef`, `envExtensionsRef`,
     `\binitialize\b`, `\belab\b`, `\bmacro\b`, `\bsyntax\b`, …). Reject any hit. The cost is false
     positives in comments, which a submitter can reword. This pass cannot be desynchronised.
  4. **Add the regression fixtures.** Put `r#check r`, `s!"{ "}" }"` and ForgeRawR into
     `tests/source-rule/` and into CI step 7.
  5. **Correct the trust statement.** The statement of S6b-A20 ("the source rule rejects the
     commands such code needs") is false today. It holds again only after 1–4. O-12 stays the sound
     fix, and this finding is one more reason to ship it before any ranked board.

### S9D-m1 (minor): trusted declarations that no certificate states

- **Probe.** `probes/s9/definitions/CertificateCone.lean` (`certificate-cone.log`). This probe
  takes the cone of the six certificate structures (types, values, constructors and projections).
  The cone holds 294 of the 311 non-internal, non-auxiliary contract declarations. The other 17
  are outside it. One of them, `unpack`, is load-bearing anyway, through the rendered image
  literal. The other 16 certify nothing:
  - `E.instZero`, `E.instOne`, `E.instAdd`, `E.instMul`, `E.toBytes`;
  - `K.instSub`, `K.instNeg`;
  - `Round.decode`, `FullTranscript.tapeWords`, `instInhabitedOracle`, `instReprHashId(.repr)`;
  - `pairUp`, `treeRoot`, `treeRoot.go` and `rootOK` (S9D-m2).
- **Meaning.** `E` enters the trusted statements only as a *set*: `Round.Ty (chal nE _)` is
  `Fin nE → E`, three 64-bit limbs. `RbrKS` counts bad challenges over that set. Nothing trusted
  multiplies two `E` elements. The modulus `y^3 + y + 1`, which `Field.lean` presents as "the
  challenge field", therefore binds no submission. A verifier may use any arithmetic on its
  192-bit challenges, and its proof is about whatever it uses. This is harmless for soundness,
  since the counting is over all `2^192` triples. But a human auditor spends time on 10 lines that
  carry no weight. `Round.decode` is dead: `NARG` uses `Round.decodeK`.
- **Fix.** Move `E`'s instances, `E.toBytes`, `K.instSub`, `K.instNeg`, `Round.decode`,
  `FullTranscript.tapeWords` and the two instances to `Library/` (the controls and the Library
  import them from there). Alternatively, mark each "convenience; no certificate depends on it".
  In `Field.lean`'s header, replace "E is the only challenge field" by the rewrite in §7.

### S9D-m2 (minor): the statement tree is a specification of Python, and its KATs cannot see a key swap

- **Declarations.** `pairUp`, `treeRoot`, `rootOK` (`Contract/Recursion.lean:124–149`), against
  `harness/run-benchmark.py` `node_stmt`/`pair_up`/`tree_root`/`tree` (lines 97–135, 480–507) and
  `cmd_selftest` (626–665).
- **What holds.** Clause by clause the Python agrees with the Lean:
  - `d0 = dC`, `d1 = dL`, `d2 = H(stmtBytes x₁ ‖ stmtBytes x₂)`, `d3 = (tag₁, tag₂, 0, 0)`,
    `d4…d7 = 0`;
  - `struct.unpack("<4Q")` is `digestToSlot` on 32 bytes;
  - `pair_up` returns `None` on odd counts;
  - `tree_root` gives level 1 over leaves and levels above over nodes, and `None` unless there are
    `2^d` leaves (`d = 0` and the empty list included);
  - the runner verifies every node proof under `vkC` and every leaf proof under `keys[tree_n]`.

  I found no divergence.
- **Problem (a), no certificate states it.** No certificate states `rootOK`: it is outside the cone
  (S9D-m1). The organiser's root check is the Python. Moreover, the runner computes every node
  statement itself, so its final `tree_root(...) != xr` comparison (line 504) is a tautology.
  `rootOK`'s docstring calls it "The organiser's root check" without saying so.
- **Problem (b), a key swap passes the selftest.** `cmd_selftest` checks `nodeStmt_kat`, `xR`,
  `treeKat` and `rootOK_xT`, always with `dC = dL = D(vkc2)`. A `node_stmt` with `d0` and `d1`
  swapped passes every check. The failure is closed: honest `C_V` proofs would not verify, so the
  evaluation rejects. But it is a regression-net hole on the one function that defines what the
  ranked tree means.
- **Fix.**
  1. Add a kernel KAT with two different keys, for example `nodeStmt cfg2 vkK vkc2 .leaf .leaf
     x0 x1` (`vkK : VKc 1`, `Controls/RecursionData.lean:172`, is `cmpToyK`'s key, element
     `0x1235`). Today every `rootOK` control has `C = L = L0` and one protocol, so `dC = dL` there
     too. Export its words in `Controls/RecursionData.lean` and check them in `cmd_selftest`.
  2. Docstring of `rootOK`/`treeRoot`: "No certificate states this; it is the specification of the
     runner's root check (`harness/run-benchmark.py`, `tree_root`), tested against it by
     `run-benchmark.py selftest` in CI."

### S9D-m3 (minor): what `Secure` asks of the verifier on layouts it never proves anything about

- **Declarations.** `relK` (`Protocol.lean:27`), `KSF.empty` (`Security.lean`), and `Protocol.Secure`
  with its docstring (`Protocol.lean:97–102`). DESIGN §3.1 and §4 items 1–2 describe the same
  objects.
- **What the Lean says.** Admissibility is a conjunct *inside* `relK k`. `KSF.empty` ties the
  state before round 0 to `relK k` for **every** statement `(L, x)`, and `RbrKS` quantifies over
  every statement. For a non-admissible `L` no witness is in `relK k`, so an accepted transcript
  must contain a bad challenge.
  - With no challenge rounds, a secure protocol accepts **no** transcript of a non-admissible
    layout (`probes/s9/definitions/NonAdmissible.lean`, `nonadmissible_rejected`, axioms standard;
    `nonadmissible.log`).
  - The obligation is not vacuous: a layout can be satisfiable and not admissible (the
    `entries_neg` shape). So the verifier, which sees `L` only through `VK L` and `IDX L`, must
    learn admissibility from the key. The toy and `P_triv` do exactly that (`toyVK`,
    `trivVK = if L.Admissible k then 1 else 0`).
- **Assessment.** This is stronger, not weaker, than "knowledge soundness for admissible layouts",
  and cheap: one key element. But the design and the docstrings say only "RBR knowledge soundness
  for `relK k`". A first submitter who reads §4 will not know that the honest indexer must encode
  admissibility.
- **A second unstated point.** `ε ≤ 2^-128` is per **challenge round**. The knowledge error of
  the whole protocol is at most `Σ_c ε c ≤ 2^14 · 2^-128 = 2^-114` (union bound over rounds,
  `Library/RbrSound.lean` `chain_extracts` is the straight-line case). DESIGN §1 and §4 never state
  the total.
- **Fix (wording only).** Add to `Protocol.Secure`'s docstring and to DESIGN §4 item 2 (rewrite in
  §7): "Soundness ranges over every statement `(L, x)`, admissible or not: a secure verifier
  rejects non-admissible layouts, which it can learn only through `VK L`; the toy keys one element
  `[L.Admissible k]`. `ε c` bounds each challenge round; the protocol's knowledge error is at most
  `Σ_c ε c ≤ 2^-114`."

### S9D-m4 (minor): the recursion key is indexed from a second reading of the layout file

- **Seam.** Two different programs read `C_V`'s layout JSON. The certified `C` is
  `render-layout.py`'s Lean literal, and `certified` binds `submission.entry.C = C`. The key that
  the runner uses everywhere (`digestC`, every node's `NARG`, the root check) is
  `index cfg P (LayoutJson.parse file)`, from `harness/lean/RecursionFastHarness/LayoutJson.lean`.
  Their agreement is a CI test on `harness/examples/` (`probes/s6b/layout/check.sh`, through
  `Layout.words`). The submitted `C_V` is not cross-checked at run time.
- **Why it matters.** If the two readers disagree on some layout, the benchmark proves nodes of
  `C' = parse(file)` while `sound`, `complete` and `live` are theorems about `C`. Every link of the
  §5.3 extractor chain then needs `C'.rel = C.rel`. A reader bug that a submitter can trigger is
  the only route, so this is minor. The same holds for `L_chain(n)`, which exists only as JSON.
  There, the trusted-by-test claim is the one DESIGN §7.2 already makes: fidelity tested, not
  proved.
- **Fix.** Render `C` into its own organiser module (data only, no `sorry`). The rendered
  challenge and the badge `index` executable both import it, and `index` indexes that constant
  instead of parsing the JSON. The cheaper alternative: at run time, have `harness-index` print
  `Layout.words` of its parse, plus the fixed tables and the bus kinds below `2^8`, and compare
  that with the same dump of the compiled rendered `C`.

### S9D-m5 (minor): the theorem behind "Merkle binding is collision resistance" is not in CI

- `Compile.lean` is "trusted by review" (§8). Of the review's arguments, only completeness and
  locality are CI-checked (`Library/Compile.lean`). Binding of openings to roots is
  `opening_binding`, which lives in the S3 review probe `probes/s3/RevBinding.lean`. No CI step
  builds that file. It still checks against today's contract (`revbinding.log`: `opening_binding`
  on standard axioms, 15 s), but nothing would notice if a later edit to `climb`, `readOpening` or
  `node` broke it.
- **Fix.** Move `Collision`, `LevelOK` and `RevBinding.lean` lines 31–149 (`climb_binding`,
  `verifyPath_binding`, `readOpening_shape`, `opening_binding`) into `Library/Compile.lean`, and cite
  them from `Compile.lean`'s header.

### S9D-m6 (minor): stale and misleading docstrings in the trusted files

- **The carried-over files** (`Shapes`, `Security`, `Field`) were kept "verbatim" from v0.3, and
  their text names objects v2 deleted:
  - `Shapes.lean` header: "`Agrees` (∀ transcripts) covers every string an adversary can commit
    to", "read by QUERY";
  - `Oracle.get`: "QUERY never reads there";
  - `roundCap`: "every protocol and reduction";
  - `SecureWith`: "shared by protocols and reductions";
  - `errorCap` "DESIGN §5" and `roundCap` "DESIGN §3/§5": the cap now lives in §4.
- **Two v2 docstrings mislead.**
  - `NARG`: "`vkc` is the indexer's output (`index`)". `aggOK` runs `NARG` on the node witness's
    keys, and `complete` ranges over every key.
  - The `Protocol.lean` header: computability is checked "in the closure of `VK`, `IDX`, `verify`
    and the image". Gate rule 4 (S6b-A1) also requires `n`, `shape`, `vkLen` and `idxShape`.
- **Fix.** Use the rewrites in §7. The olean manifest must be regenerated after any edit to a
  trusted file (CLAUDE.md, A6-G0). That is the only cost of editing "verbatim" files.

### S9D-m7 (minor): what a human must read of the vendored machine is smaller than §8 says

- `probes/s9/definitions/TrustedAudit.lean` reproduces Stage 4's count: **205** reached vendored
  constants, 930 source lines. Of these, `RiscvZkvm.Rv64.ZiskAccel` contributes 33 declarations
  and 316 lines. They are reached only through `execInstrBr`'s `CSRS` arm (`execCsrs`,
  `ZiskAccel.lean:787`).
- The contract never executes that arm:
  - `decodeInstruction` intercepts opcode `0x73` before upstream `decode` and returns only an exact
    `ECALL`;
  - `ordinaryStep` refuses `.base (.CSRS _ _)`, `ECALL`, `EBREAK`, `LI`, `MV` and `NOP`.
- So the auditor must read about 614 vendored lines: `execInstrBr` without those six arms,
  upstream `decode` without opcode `0x73`, and the `MachineState` helpers. 316 lines are dead
  weight inside the kernel term.
- **Fix.** Add one sentence to `Machine.lean`'s header and to DESIGN §8: "of the 930 reached lines,
  ZiskAccel's 316 and `execInstrBr`'s `ECALL`/`EBREAK`/`CSRS`/`LI`/`MV`/`NOP` arms are unreachable
  from `execute`, since `decodeInstruction` never produces them and `ordinaryStep` refuses them".

---

## 2. Seam checks across stages

Each stage review read one file. These are the joints between files, checked against the brief's
list (a)–(f).

### (a) `Secure` = Security + Protocol + Extractor

The composed object is `SecureWith (relK k) Set.univ P.prover P.specVerifier
(P.extractor.toExtractor P.shape) P.ε`. Unfolded:

1. **Completeness.** For every `((L, x), w) ∈ relK k` (an admissible layout at class `k`, a witness
   of at most `2^k` cells satisfying it) and **every** challenge vector, `specVerifier` accepts the
   honest transcript. Admissible layouts only, as designed.
2. **Soundness.** There is a state function `KSF` for this verifier and **this** extractor
   (the extractor is a parameter of `KSF`'s type, so it is the image's, not chosen inside `∃`) with `#bad ≤ ε c · #challenges`
   for every statement, challenge round and prefix. The challenge types are finite (`2^192` per `E`
   element, `2^b` per index), so `Nat.card` is the true count and the bound is not vacuous. Their
   `Fintype` instances are in `Library/Field.lean`; the trusted statement relies on finiteness, not
   on the instances. `chain_extracts` (`Library/RbrSound.lean:145`) turns it into straight-line
   extraction into `relK k` when no challenge is bad.
3. **Cap.** `ε c ≤ 2^-128` for every challenge round.

The hypotheses one might suspect:

| Item | Effect | Easier than the design? |
|---|---|---|
| `k_range : 20 ≤ k ≤ 28` | a field the submitter proves; no statement assumes it | no |
| `shape_ok` | restricts the submitter's shapes; `b ≤ 64` makes index challenges exactly uniform and their tape words injective | no |
| admissibility inside `relK` | completeness only on admissible layouts (designed); soundness on **all** layouts (S9D-m3) | no: stronger |
| `Mid n j` | fixed by the contract: tables before round 0 (`eqIn := rfl`), words after; the submitter's `KSF` interprets words | no: S4-A1's reason holds, since no submitter code runs on the extractor's path |
| default `[]` | a failed call (fault, trap, fuel, output over `witCap`) yields `[]`; before round 0 `[]` ∉ `relK` (`nil_not_relK`: an admissible layout has a chip); after round 0 `[]` is a word list like any other, and the submitter's laws decide | no |
| `extractOut` ignores `wOut` | `WitOut = Unit` | no |
| `prover` may be noncomputable | completeness is about the Lean strategy; the executed prover is measured, not proved | as designed |

One `k` throughout: `relK k`, `Round.Admissible k`, `ExtractorImage k n` (`B(k)`, `witCap k`) and
`P.n = n` are forced by the types. **Conclusion:** exactly "perfect completeness for admissible
layouts + RBR knowledge soundness with the bounded image extractor at `ε ≤ 2^-128` per round",
plus the unstated rejection of non-admissible layouts (S9D-m3).

### (b) `NARG`/`VKc`/`D` (Compile + Recursion)

| Use | Function | Byte convention |
|---|---|---|
| sponge seed | `seed cfg vkc x = absorb cfg (vkc.digest cfg) (stmtBytes x)` | `VKc.toBytes` = `K.bytes` of each `VK` element, then the root; `stmtBytes` = 32 × `K.bytes` |
| `d0`, `d1` | `digestToSlot (vkC.digest cfg)`, `digestToSlot (vkL.digest cfg)` | `digestToSlot` = `K.ofBytes` of bytes `8j…8j+7` (LE), the inverse of `K.bytes` (`K.ofBytes_bytes`, `digestToSlot_inj` on 32 bytes) |
| `d2` | `digestToSlot (cfg.hash.run (stmtBytes x₁ ++ stmtBytes x₂))` | same `H` as `D` and the sponge (S5-A8) |
| child verification | `NARG cfg P vkC x π` / `NARG cfg P vkL x π`, with `aggOK`'s `cfg` = the entry's `cfg` = the submission's | the same key whose digest is in `x'` |
| leaves, elements | `leafHash` over `K.bytes`; `kList` reads 8-byte LE words back | the machine's tape word is `bits` (LE in memory), the same 8 bytes |
| badge I/O | `parseVKc` (exactly `8·vkLen + 32` bytes, round trip), `parseStmt` (256 bytes, round trip), `index` writes `vkc.toBytes` and prints `vkc.digest cfg` | the runner hashes `vkc.bin` with `hashlib.blake2s` and compares |

There is one `cfg`, one digest function (`VKc.digest`, never restated) and one encoding
(`K.toBytes` LE). `NARG` and `aggOK` both require 32-byte roots. **No seam.**

### (c) `aggOK`/`rootOK`/`treeRoot` against `harness/run-benchmark.py`

The Python agrees with the Lean, clause by clause (S9D-m2 lists the checks). Two caveats are filed
as S9D-m2:

- **The tree is the runner's, not a certificate's.** The organiser accepts exactly the tree the
  runner builds itself. Every node statement is the runner's `node_stmt`, so the final root check
  is a tautology, and the trusted `rootOK` is the specification the Python is tested against.
- **The KATs cannot see a key swap.** They use one key for both `dC` and `dL`.

The runner never evaluates `aggOK`. It relies on `NARG` accepting each node's output under `vkC`
for its own `nodeStmt`, and on `sound` (via KS of `P` on `C_V`, in the ROM) for what the children
were. **No divergence found.** A divergence of the `d0`/`d1` kind would fail closed: honest
`C_V` proofs cannot be produced.

### (d) `RecursionEntry` with `Certificate`/`Declared` and the R stub

The rendered R challenge (`Challenge/R.lean.in`) states:

- `submission : SubmissionR declared.k`, whose type carries `secure : P.Secure` and `entry :
  RecursionEntry P cfg` with **all four** proofs `fits`, `sound`, `complete` and `live`;
- `certified : CertificateR declared submission ∧ submission.entry.C = C ∧ submission.toSubmission
  = leaf`, where `CertificateR` extends `Certificate`: `cfg` (hash, arity), `img` and `size`.

`k` is `declared.k` everywhere: in the type of `leaf` and of `submission`; in `Protocol k`, hence
`relK k`; in `ExtractorImage k n`, hence `B(k)`; and in `RecursionEntry`'s `C.Admissible k` and
`C.rel k` (implicit from `P`). The runner takes the same `k` from the claim (S6b-A22).
`digestC`/`digestL` are rendered and **in no conjunct**: declared, not certified, by design.
`fuel` is not declared: it is part of `P`, and `fuel_le` is kernel-checked. **No seam.** The only
joint outside Lean is the JSON-reader pair of S9D-m4.

### (e) The extractor's input tape against the transcript types

`extractorTape j (L, x) rounds w = frame ([j] :: L.words :: x :: rounds ++ [w])`.

- **Coverage.** `extractMid m` serialises rounds `0 … m` (the prefix it is given), and
  `extractOut` all `n` rounds. Each message round appears as its `2^logLen` element words. Each
  challenge round appears as its `E` limbs (`c0, c1, c2`), then its indices, zero-extended
  (`Round.words` = `Round.tapeWords`).
- **What is not on the tape, by design (S4-A5).** `VK L` and `IDX L` are absent, and the extractor
  sees `L` itself. The shapes are absent too: the image is per protocol.
- **Distinctness.** Two different prefixes of one protocol give two different tapes:
  - `frame`'s directory recovers the sections whenever the tape is shorter than `2^64` words
    (`unframe_extractorTape`). A prefix of `2^14` rounds of `2^(k+10)` elements is under `2^52`
    words at `k ≤ 28`. The addressable tape is `2^60` words.
  - `j` and the section count separate `extractMid (n−1)` from `extractOut`: they have equal
    section counts and different `j`.
  - Message words are the elements; `E` limbs are the elements; and `setWidth 64` is injective
    on `BitVec b` for `b ≤ 64`, which `shape_ok` guarantees.
  - The layout section parses back to `L.normal 2^8` for admissible `L` at `k ≤ 28`
    (`pLayout_words`), that is, up to what `rel` does not read (bus kinds at or above `2^8`, table
    cells outside `rows × cols`). Two layouts with the same tape therefore have the same relation,
    and the extractor owes both the same witnesses.
- **Non-injective cases, harmless.** Non-admissible layouts can collide (`toWord` truncates).
  There `relK` is empty, so nothing is extracted, and the verifier must reject (S9D-m3).

**No seam.**

### (f) `Layout.Admissible` against what `IDX`/`VK` can commit (`shape_ok`: index `≤ 2^(k+8)`)

In words of the contract's own layout encoding (`Chip.words`), an admissible layout costs:

| Part | Words |
|---|---|
| header | `2 + 2^8` (bus kinds) |
| per chip, apart from its entries and fixed table | 4 (`cols`, `cons`, `t`, `q`) + `t ≤ 64` lengths + `q·(1 + len (S i)) ≤ 2^8·9` + `q ≤ 2^8` coefficients + 1 + ports `≤ 2^5·(4 + 2^4)` + 2, i.e. **≤ 3,300 words per chip** |
| per matrix entry | **3 words** (row, column, value) |
| per fixed cell | 1 word (plus one height per table) |

Total: `≤ 258 + 2^8·3,300 + 3·2^(k+4) + 2^(k−4) < 2^(k+6) + 2^20 ≤ 2^(k+8)` for every `k ≥ 20`.
The Library proves this for this encoding (`Codec.eLayout_length`, `Layout.words_length`:
`L.words.length ≤ 2^(k+8)` for admissible `L`, `20 ≤ k`). **Consistent.**

Remark for the feasibility reviewer, not a definitional finding: `idxShape` is one shape for all
layouts. So every layout's index oracle, `L_chain`'s included, is as long as the largest
admissible layout's. Soundness at every admissible layout forces `(VK, IDX)` to determine the
relation, so the oracle holds at least the `2^(k+4)` 64-bit values plus their positions (about 19
bits each). That is `2^(k+5)` elements after rounding to a power of two, and `2^(k+6)` at 2
elements per entry: `2^29`–`2^30` elements (4–8 GiB) at `k = 24`. The contract's `commit` hashes
every leaf of it (`node` does not share all-zero subtrees), for each layout the runner indexes,
inside the 1 h indexing budget.

---

## 3. Load-bearing inventory

### 3.0 Header

- **Scope.** The trusted contract (`Contract.lean` and the 11 files it imports, 739 code lines by
  `scripts/loc.py`), the challenge stubs, and the four trusted harness tools. The vendored machine
  is summarised (S9D-m7).
- **Pins.** Lean v4.34.1, Mathlib v4.34.1, riscv-zkvm `6810fc1` (vendored byte-identical), leanerVM
  `485d0465` (the BLAKE2s source), RFC 7693.
- **Claim.** A ranked record certifies three things:
  - a holographic public-coin IOP for the chips + CCS + bus relation over GF(2^64) is perfectly
    complete and round-by-round knowledge sound, with a bounded RISC-V extractor;
  - on board R, a layout `C_V` is the organiser's specification "two children accepted by the
    compiled verifier", exactly, at the protocol's own class;
  - the submission is the declared one.

  Wall times, proof sizes and "every proof verifies" are measured, not certified.
- **Category.** Mostly specifications of intent. The exceptions are `Hash/Blake2s.lean`, a
  transcription of RFC 7693 that is wrong if it deviates, and `Compile.lean`, whose header grammar
  is normative.
- **Sits between.** Below it are Lean core and Mathlib (`Multiset`, `Nat.card`, `ℝ≥0`, `Fin`,
  `BitVec`, `Vector`, `UIntN`) and the vendored RV64 model. Above it are the rendered challenge
  (`certified`), the gate, and the badge executables (`NARG`, `index`).
- **Index.** 139 numbered lines in 13 groups. `○` marks a declaration outside every certificate
  (S9D-m1). `⚑` marks a docstring that disagrees with the Lean, is stale or is vague (S9D-m6, §7).
  `◇` marks a declaration used only by the rendered data. Constructors and auto-generated declarations
  (matchers, `_proof_i`, `injEq`, `sizeOf_spec`, recursors, `_unsafe_rec`) are not shown: 769 of
  the 1,080 contract constants.

### 3.1 Vocabulary (borrowed objects, in dependency order)

- **`BitVec n`, `UInt8/32/64`** (Lean core): `n`-bit words with wrapping arithmetic. `K` is a
  `BitVec 64` read as polynomial coefficients. BLAKE2s works on `UInt32` words and `UInt8` bytes.
- **`Fin n`, `List.ofFn`, `Fin.cases`** (core): indices below `n`; the list `f 0, …, f (n−1)`; the
  definition by "case 0 / case successor" that makes `Mid n 0` tables and `Mid n (j+1)` words.
- **`Multiset`** (Mathlib): lists up to order. `Table.msgs` and `traffic` are multisets of
  messages, compared with `=` (`eq` bus, multiplicities counted in ℕ) or `∈` (`sub` bus).
- **`Nat.card`** (Mathlib): the number of elements of a finite type (`0` for an infinite one).
  Every challenge type is finite, so `RbrKS`'s counting form is the uniform probability.
- **`ℝ≥0`** (Mathlib `NNReal`): non-negative reals, the type of `ε` and of `errorCap = 2^-128`.
- **`Vector α n`** (core): arrays of length `n`; BLAKE2s's state, block and schedule.
- **Vendored `MachineState`, `Instr`, `execInstrBr`, `decode`** (riscv-zkvm `6810fc1`): RV64
  registers, doubleword memory `Word → Word` accessed at aligned addresses, the instruction type,
  one-instruction semantics, the upstream decoder. The arms S9D-m7 lists are unreachable.

### 3.2 What a rendered certificate asserts, conjunct by conjunct

The R stub's `submission : SubmissionR declared.k` and `certified` together assert every row below.
The L stub asserts the rows not marked R.

| Conjunct | Source | Says, in domain words |
|---|---|---|
| type index | `Submission declared.k` | the protocol is at the declared class `k` |
| `P.k_range` | `Protocol` | `20 ≤ k ≤ 28` |
| `P.n_le`, `P.vkLen_le` | `Protocol` | at most `2^14` rounds; a key of at most `2^10` elements |
| `P.shape_ok` | `Protocol` | message oracles `≤ 2^(k+10)` elements, index oracle `≤ 2^(k+8)`, leaves no longer than their oracle, index challenges `≤ 64` bits |
| `P.extractor.img_le`, `fuel_le` | `ExtractorImage` | the image has `≤ 2^20` bytes; the declared fuels of the `n + 1` calls sum to `≤ 2^(2k+16)` |
| `cfg.arity_ok` | `Cfg` | Merkle arity `∈ {2, 4, 8, 16}` |
| `secure.complete` | `SecureWith` | for every admissible layout, statement and satisfying witness of `≤ 2^k` cells, and every challenge vector, the verifier accepts the honest transcript |
| `secure.sound` | `SecureWith` | there is a state function for **this** verifier and **this** extractor (`toExtractor` of the image) whose laws hold; at every statement (admissible or not, S9D-m3), challenge round and prefix, at most an `ε c` fraction of challenges is bad |
| `secure.cap` | `SecureWith` | `ε c ≤ 2^-128` in every challenge round (total `≤ 2^-114`) |
| `certified.cfg`, `.img` | `Certificate` | hash and arity are the declared ones; the extractor image is the rendered literal |
| R: `entry.fits` | `RecursionEntry` | `C_V` is admissible at the same `k` |
| R: `entry.sound` | `RecursionEntry` | every satisfying witness of `C_V` at `k` decodes to a node `aggOK` accepts |
| R: `entry.complete` | `RecursionEntry` | every node `aggOK` accepts, under any keys, is decoded from a satisfying witness of `≤ 2^k` cells |
| R: `entry.live` | `RecursionEntry` | some node keyed by the indexer (`index cfg P C`, `index cfg P L` for some `L`) is accepted |
| R: `.size` | `CertificateR` | `C_V`'s chip and matrix-entry counts are the declared ones |
| R: `entry.C = C` | R stub | `C_V` is the layout rendered from the submitted JSON |
| R: `toSubmission = leaf` | R stub | the badge executables' protocol is the certified one |

Declared and **in no conjunct**: `digestC` and `digestL` (harness-compared). **Not declared**: the
fuel split, which is part of `P` and kernel-checked.

### 3.3 Oneline index

```
RecursionFast/Contract/Field.lean                       (K is load-bearing; E only as a set)
  [01] abbrev Word                      a 64-bit word: machine word, tape word, a K element's bits
  [02] struct K                         GF(2^64) element as its 64 coefficient bits (x^i = bit i)
  [03] def    K.clmul a b               carry-less 64×64→128-bit product; also Zbc's semantics
  [04] def    K.fold t                  one reduction step hi·x^64 ↦ hi·(x^4+x^3+x+1)
  [05] def    K.reduce t                two folds: the residue mod x^64+x^4+x^3+x+1
  [06] inst   Zero/One/Add/Mul K        0, 1, xor, reduced carry-less product: the relation's arithmetic
  [07] inst   Sub/Neg K              ○  xor / identity; no certificate uses them
  [08] def    K.toBytes a               the 8 little-endian bytes of the coefficient word
  [09] struct E                         a challenge: three K limbs c0 + c1·y + c2·y² (2^192 values)
  [10] inst   Zero/One/Add/Mul E     ○⚑ arithmetic mod y^3+y+1; nothing trusted multiplies in E
  [11] def    E.toWords a               limbs c0, c1, c2 as three tape words
  [12] def    E.toBytes a            ○  24 bytes, limbs little-endian; unused by every certificate
RecursionFast/Contract/Layout.lean                      (the relation; docstrings match the Lean)
  [13] struct Gadget F width            CCS row gadget: t sparse cons×width matrices; terms c_i·∏_{S_i} M_j·z
  [14] struct Port                      rows whose sel cell is 1 put the msg cells on a bus, sending or receiving
  [15] ind    BusKind                   eq: sent = received as multisets; sub: every received message was sent
  [16] struct Table F                   a table: height rows, cells ℕ → ℕ → F (read inside rows × cols)
  [17] struct Chip F                    cols; a gadget over 2·cols+3 view cells; ports; optional fixed table
  [18] struct Layout F                  the index: chips in order, bus kinds, which chip is public
  [19] abbrev Stmt                      a statement: 32 elements of K, 8 digest slots of 4 limbs
  [20] def    rowDot M z r              row r of the sparse product M·z, entries at one position adding up
  [21] def    Gadget.holds g z          every constraint row r: Σ_i c_i·∏_{j∈S_i}(M_j·z)_r = 0
  [22] def    view C T r                row r, row r+1 mod rows, then 1, [r = 0], [r + 1 = rows]
  [23] def    Table.msgs T p            port p's messages: one per row whose sel cell is exactly 1
  [24] def    traffic L w b send        all messages sent (or received) on bus b, over all chips
  [25] def    BusKind.Balanced          eq: equal multisets (ℕ counts); sub: received ⊆ sent
  [26] def    Layout.rel L k x w        THE RELATION: tables per chip, fixed tables, gadgets, buses, x, ≤ 2^k cells
  [27] def    Chip.Admissible C         1≤cols≤2^10; t≤2^6, cons≤2^8, q≤2^8, degree≤8; ≤2^5 ports, own columns
  [28] def    Chip.entries/fixedCells   matrix entries of a chip / cells of its fixed table
  [29] def    Layout.Admissible L k     ≤2^8 chips, all admissible; public ≥32 cols; Σentries≤2^(k+4); fixed≤2^(k−4)
  [30] inst   Decidable Admissible      admissibility is decided by evaluation
RecursionFast/Contract/Shapes.lean                      (v0.3 verbatim; header stale, S9D-m6)
  [31] def    roundCap               ⚑  2^14 rounds ("every protocol and reduction": reductions are gone)
  [32] struct OShape                    an oracle of 2^logLen elements read in leaves of 2^logLeaf
  [33] abbrev OVal o                    an oracle's contents, Fin 2^logLen → K
  [34] ind    Round                     msg o (prover sends an oracle) | chal nE idx (nE E's, one b-bit index per b)
  [35] def    Round.Ty                  a round's value: the oracle, or (E-vector, indices)
  [36] def    Round.isMsg               whether the prover speaks in the round
  [37] abbrev Transcript/FullTranscript the values of rounds 0 … m−1 / of every round
  [38] def    Transcript.empty/concat   the empty prefix / the prefix extended by round m's value
  [39] abbrev MessageIdx/ChallengeIdx/Challenges  prover rounds / challenge rounds / a choice of every challenge
  [40] struct Oracle                    a shape and its contents
  [41] inst   Inhabited Oracle       ○  unused
  [42] def    Oracle.get o p         ⚑  element p, 0 beyond the length ("QUERY never reads there": stale)
  [43] def    OShape.leaves             2^(logLen − logLeaf)
  [44] def    Oracle.leaf o l           the 2^logLeaf elements of leaf l
  [45] def    Round.oracles             a msg round's one oracle; none for a challenge round
  [46] def    Round.tapeWords           a challenge as words: E limbs, then indices zero-extended
  [47] def    FullTranscript.oracles    the prover's oracles in round order (oracles 1, 2, …)
  [48] def    FullTranscript.tapeWords ○ unused
RecursionFast/Contract/Security.lean                    (v0.3 verbatim; one header sentence S4-A11)
  [49] def    errorCap               ⚑  2^-128 ("DESIGN §5": now §4)
  [50] struct Strategy                  deterministic prover: messages from (input, prefix); output from transcript
  [51] abbrev PureVerifier              a total function of statement and transcript; none = reject
  [52] def    Strategy.prefixes/transcript  the honest transcript on challenge vector ρ
  [53] def    PerfectComplete           every (s, w) ∈ relIn and every ρ: accepted, output in relOut
  [54] struct Extractor                 RBR extractor: extractMid (after round m ↦ before it), extractOut, eqIn
  [55] struct KSF                       state function: empty ↔ relIn; next on prover rounds; full on acceptance
  [56] def    KSF.Bad                   a challenge after which some witness is good but the extracted one is not
  [57] def    RbrKS kSF ε               #bad ≤ ε c · #challenges at every statement, challenge round, prefix
  [58] struct SecureWith             ⚑  complete ∧ (∃ KSF, RbrKS) ∧ ε ≤ 2^-128 ("and reductions": stale)
RecursionFast/Contract/Machine.lean                     (the extractor's machine; vendored reach S9D-m7)
  [59] def    CODE_BASE/TAPE_BASE       code at 0x1000 in its own space; the read-only tape from 2^63
  [60] struct Image                     32-bit code words and 64-bit data words
  [61] def    unpack w k x           ◇  k w-bit words packed in a natural (the rendered image literal)
  [62] def    Image.byteSize            4·|code| + 8·|data|
  [63] ind    WordOp/ClOp/Instruction   W-ops, Zbc ops, and upstream base instructions
  [64] def    decodeInstruction         exact ECALL; Zbc; OP-32 and OP-IMM-32 W-ops; otherwise upstream decode
  [65] def    wordResult/clResult       W-op results (RISC-V ÷0 rules); clmul low / high / reversed
  [66] def    memAccess/ordinaryStep    aligned loads anywhere, aligned stores below 2^63; anything else faults
  [67] def    fetch                     pc 4-aligned and ≥ CODE_BASE: the image's word, decoded
  [68] def    readOut/execute           HALT (t0 = 0, a0 8-aligned) returns a1 words at a0; fault/trap/fuel: none
  [69] def    initState                 data from 0, tape from 2^63, zeros beyond; sp = 2^63; pc = CODE_BASE
  [70] def    run img input fuel        THE MACHINE: the output at HALT within fuel steps, else none
RecursionFast/Contract/Extractor.lean                   (Q1; the contract's serialisation)
  [71] def    extractorBudget k         B(k) = 2^(2k+16) steps, the total over every call of one extraction
  [72] def    witCap k                  2^(k+12) words: the longest output that counts
  [73] def    imageCap                  2^20 bytes
  [74] def    toWord a                  a natural's low 64 bits
  [75] def    Table/Chip/Layout.words   the layout as words: counts, gadget entries, ports, fixed table, bus kinds 0..255
  [76] def    Round.words               a round's value as words: oracle elements / challenge tape words
  [77] def    frame secs                a directory (count; start and length per section), then the sections
  [78] def    extractorTape j s rs w    [j], L, x, one section per round, w, behind the directory
  [79] def    Mid n j                   the witness before round j: tables if j = 0, words after
  [80] def    decTables/decMid          tables read back from words (missing words 0) / words unchanged
  [81] struct ExtractorImage k n        image ≤ 2^20 bytes; a fuel per call; Σ fuel ≤ B(k)
  [82] def    ExtractorImage.call       run with the call's fuel; [] on failure or output over witCap
  [83] def    ExtractorImage.toExtractor  extractMid m on ⟦m, s, rounds 0..m, w⟧; extractOut on ⟦n, s, all, []⟧
RecursionFast/Contract/Protocol.lean                    (the proved object)
  [84] def    vkCap                     2^10 key elements
  [85] def    relK k                    ((L, x), w): L admissible at k and L.rel k x w
  [86] ind    QProg α                   adaptive query program: done a | query j l cont
  [87] def    QProg.eval                run on oracles; an out-of-range oracle or leaf rejects
  [88] def    chalOf tr                 the challenges of a full transcript
  [89] def    Round.Admissible k        msg: logLeaf ≤ logLen ≤ k+10; chal: every index ≤ 64 bits
  [90] struct Protocol k             ⚑  k_range, n, shapes, VK, IDX, shape_ok, prover, verify, extractor, ε
  [91] def    Protocol.specVerifier     accept iff verify(VK L, x, challenges) on IDX L :: prover oracles is true
  [92] def    Protocol.Secure        ⚑  SecureWith (relK k) univ prover specVerifier (image's extractor) ε
RecursionFast/Contract/Hash/Blake2s.lean                (transcription of RFC 7693; provenance in header)
  [93] def    iv/sigma                  RFC 7693 §2.6 IV and §2.7 message schedule
  [94] def    rotr/mix/round/initialState/compress  G, the rounds of F, F with counter and flags
  [95] def    block/compressInput       64-byte little-endian blocks; the §3.3 block loop
  [96] def    blake2s key nn msg        keyed BLAKE2s of RFC 7693 §3.3
  [97] def    blake2s256 msg            unkeyed 32-byte BLAKE2s: the contract's H
RecursionFast/Contract/Compile.lean                     (trusted by review; header grammar normative)
  [98] ind    HashId/HashId.run         the menu {blake2s} and its function
  [99] struct Cfg                       hash and Merkle arity ∈ {2, 4, 8, 16}
 [100] abbrev Tape/Digest; tapeCap/zeroDigest   byte strings; 2^20 bytes; 32 zero bytes
 [101] def    K.bytes/wordOfBytes/K.ofBytes/kList  element ↔ 8 LE bytes; bytes → elements
 [102] def    stmtBytes x               a statement's 256 bytes
 [103] abbrev VKc; def VKc.toBytes/digest   compiled key (VK L, index root); its bytes; D = H(bytes)
 [104] def    OShape.plain/msgLen       a one-leaf oracle is sent in the clear / bytes per prover round
 [105] def    Cfg.logArity/Cfg.depth    log₂ A; depth ⌈(logLen − logLeaf)/log₂ A⌉
 [106] def    leafHash/node/commit      the Merkle tree: leaf hashes, zero-digest padding, A-ary nodes, root
 [107] def    climb/verifyPath          an authentication path climbs to the root
 [108] def    index cfg P L             THE INDEXER: (VK L, root of IDX L) under cfg
 [109] def    absorb/squeeze/seed       hash-chain sponge; seed = absorb(D, x)
 [110] def    Round.chalLen/decodeK     24·nE + 8·|idx| bytes; E from limbs; index = low b bits
 [111] def    Round.decode           ○  dead: NARG uses decodeK
 [112] def    takeN/readMany/readOpening  exact-length reads; an opening = leaf, then depth levels of A−1 digests
 [113] def    pass                      FS pass: read and absorb prover rounds, squeeze challenge rounds
 [114] def    chals                     the challenges from the pass's bytes
 [115] ind    View; def roundViews/views  root or plain view per oracle; the index root first
 [116] def    runQ                      the query program against the openings; leftover bytes reject
 [117] def    NARG cfg P vkc x t     ⚑  THE COMPILED VERIFIER: cap, 32-byte root, rounds parse, accept, no leftovers
RecursionFast/Contract/Recursion.lean                   (§5; docstrings match the Lean but for rootOK)
 [118] def    digestToSlot/Stmt.slot/ofSlots  32-byte digest ↔ 4 limbs; slot d_i = elements 4i..4i+3
 [119] ind    Tag; def tagK/tagSlot     leaf ↦ 0, node ↦ 1; d3 = (t₁, t₂, 0, 0)
 [120] struct NodeWitness               vkC, vkL, the two tags, statements and proofs
 [121] def    nodeStmt                  d0 = D vkC, d1 = D vkL, d2 = H(x₁‖x₂), d3 = tags, d4..d7 = 0
 [122] def    child                     node child: same d0, d1, NARG under vkC; leaf child: NARG under vkL
 [123] def    aggOK cfg P x' nw         x' is the node statement, both roots 32 bytes, both children accepted
 [124] def    pairUp/treeRoot/rootOK ○⚑ the statement tree and root check: the spec of the runner's Python
 [125] struct RecursionEntry P cfg      C, fits, decode (computable), sound, complete, live (see 3.2)
RecursionFast/Contract/Certificate.lean                 (what a record certifies)
 [126] struct Submission k              a protocol at class k, its cfg, and Secure
 [127] struct SubmissionR k             a Submission and its RecursionEntry
 [128] struct Declared/DeclaredR        rendered claim: k, hash, arity, image (+ chips, entries, two digests)
 [129] struct Certificate D S           cfg and image are the declared ones
 [130] struct CertificateR D S          a Certificate, and C_V's chip and entry counts are the declared ones
RecursionFast/Challenge/{L,R}.lean.in                   (rendered organiser data + the solver's terms)
 [131] def    image/declared            the rendered image literal (via unpack) and claim
 [132] def    C                  (R)    the rendered recursion layout, with helpers kx, tabOf, add8
 [133] def    leaf               (R)    the badge-root Submission, in a Clean-free module
 [134] def    submission                the solver's Submission / SubmissionR at declared.k
 [135] thm    certified                 L: Certificate; R: CertificateR ∧ entry.C = C ∧ toSubmission = leaf
scripts/ (trusted harness tools; not Lean-checked)
 [136] Gate.lean                        rules 1–9: axioms; unsafe/partial/opaque; code attrs; computability; manifest; imports; compiler API; badge root; frontend refs
 [137] AxiomAudit.lean                  every RecursionFast.* constant within propext, Classical.choice, Quot.sound
 [138] source-rule.py                ⚑  token scan for elaboration-time code; its lexer diverges from Lean's (S9D-M1)
 [139] render-challenge.py              claim + files → the literals `certified` speaks about (strict schema)
```

**Where the docstring and the Lean disagree (⚑), in one place.**

- **Stale v0.3 vocabulary.** [31] [42] [49] [58] and the Shapes header refer to `Agrees`, the
  QUERY syscall, reductions, and v0.3 section numbers.
- **[10] `E`.** "E is the only challenge field" is true as a set, but its arithmetic carries no
  weight (S9D-m1).
- **[90] `Protocol` header.** Its computable list is shorter than gate rule 4's (S9D-m6).
- **[92] `Secure`.** The docstring is silent on non-admissible layouts and on per-round versus
  total error (S9D-m3).
- **[117] `NARG`.** "`vkc` is the indexer's output" does not hold under `aggOK` (S9D-m6).
- **[124] `rootOK`.** Its docstring says "the organiser's root check" without saying that the
  executed check is Python and that no certificate states it (S9D-m2).

No ⚑ in `Layout`, `Extractor`, `Hash/Blake2s`, `Certificate`.

**Questions for the author** (not findings).

1. `RecursionEntry.decode` must be computable (gate rule 4), but computable does not mean explicit.
   With 32-byte roots and `tapeCap`, the set of accepted nodes for a statement is finite, so a
   brute-force `decode` (enumerate keys, statements and tapes, return the first accepted node) is
   computable. §5.3 item 7 already says `decode` need not be efficient. Should §5.3's "decode names
   them (no existential), so the extractor chain is explicit" say "computable, not necessarily
   feasible"?
2. `KSF`'s `next` law is stated only for prover rounds, and challenge rounds are covered by
   `Bad`. Is it intended that an **empty** challenge round (`chal 0 []`, one possible value) must
   have zero bad challenges (forced by `ε ≤ 2^-128 · 1`)? It is, as far as I can tell, and
   `padShape` relies on it. A sentence in `RbrKS`'s docstring would help a reader.

---

## 4. Axiom and construct audit of the whole trusted tree

The repository's audit only reaches `RecursionFast.*` modules and skips internal names. So
`probes/s9/definitions/TrustedAudit.lean` (log `trusted-audit.log`, 22 s) roots at every constant
declared in a `RecursionFast.Contract*` module, internal names included: 1,080 constants. It adds
the 205 vendored constants they reach.

| Check | Result |
|---|---|
| axioms (`collectAxioms` per constant, 1,285 constants) | only `propext` (481), `Quot.sound` (307), `Classical.choice` (101); **0 non-standard**, no `sorryAx`, `ofReduceBool`, `trustCompiler` |
| repository audit `lake exe axiomaudit` (Contract + Library + Controls + Bridge) | `PASS`; 190 theorems use no axiom (`axiomaudit.log`, 7 s) |
| `unsafe` / `partial` / `opaque` declarations | none written by hand; the 15 `*._unsafe_rec` are the compiler's auxiliaries for the structurally recursive `runQ`, `node`, `pass`, `decTables`, `squeeze.go`, `readMany`, `unpack`, `compressInput`, `pairUp`, `treeRoot.go`, `QProg.eval`, `takeN`, `climb`, `execute`, `kList.go` (no kernel term refers to them) |
| `noncomputable` | `errorCap` only (a real; never executed) |
| `implemented_by`, `extern`, `csimp`, `export`, `init` | none |
| `@[irreducible]` | none (S4-A6's `extractorFuel` is gone with S4-A14) |
| `@[reducible]` | abbrevs (`Word`, `Stmt`, `OVal`, `Transcript`, `FullTranscript`, `MessageIdx`, `ChallengeIdx`, `Challenges`, `PureVerifier`, `Tape`, `Digest`, `VKc`), structure projections, auto-generated eliminators; none changes a meaning (an abbrev unfolds to its body) |
| `unseal`, `set_option`, `native_decide`, `macro`, `attribute` in trusted sources | none (grep of the 12 files) |
| `decide`-closed proofs inside trusted definitions (`of_decide_eq_true`/`ofReduceBool` in a value) | **0**; the proofs inside definitions are `by omega` (`Stmt.slot`, `Stmt.ofSlots`), `by simpa` (`Strategy.prefixes`) and `get_elem_tactic` bounds in BLAKE2s, none of which can change a value |
| `decide` as Boolean evaluation in definitions | `aggOK`, `child`, `rootOK`, `NARG`: `decide p` of a decidable `p`, equal to `p` by `decide_eq_true_iff` |
| theorems in the contract | none; the 24 theorem-kind constants with user names are 23 `Prop` fields of structures (3.2's, `KSF`'s laws, `Extractor.eqIn`, `CertificateR.toCertificate`) and the auto-generated `QProg.brecOn.eq` |
| manifest freshness | the 12 contract `.olean`s match `scripts/olean-manifest.sha256` byte for byte |

---

## 5. The complete trust statement (for DESIGN §8 and the report)

> A ranked record means: the kernel accepted `certified` for the rendered challenge, and the run,
> every proof verifying, measured the times. Its reader trusts:
> 1. Lean v4.34.1's kernel and nanoda (the comparator replays in both), the comparator's export,
>    and Lean core, Mathlib and packages as hashed in `scripts/olean-manifest.sha256` (35,223 files).
> 2. The contract: 12 files, 739 code lines (543 without `Compile` and BLAKE2s), no theorem, three
>    standard axioms; 16 of its declarations certify nothing (S9D-m1).
> 3. The vendored RV64 model (riscv-zkvm `6810fc1`): 205 declarations, 930 lines, ~614 live (m7).
> 4. BLAKE2s = RFC 7693 (KATs, 8,432-case differential) and its collision resistance, which binds
>    openings (`opening_binding`, m5), key digests and `d2`.
> 5. `Compile.lean` by review of its normative header; `NARG`'s soundness is BCS/Fiat–Shamir in the
>    ROM, once per tree level, with no composition theorem (§5.4).
> 6. The badge code: what Lean's compiler emitted for the twin (`rfl` to the submission's `NARG`,
>    `index`), guarded by the source rule and gate rules 3, 6–9; residual O-12, and today the
>    source rule is evadable (S9D-M1).
> 7. Harness tools: `Gate.lean` (trust by `.olean` hash), the order comparator → gate → badge with
>    build binding, `olean-manifest.py`, `AxiomAudit.lean`, `source-rule.py`, `render-challenge.py`
>    and `render-layout.py` (they fix what `certified` says), the sandbox (bwrap, landrun, cgroups).
> 8. Tested, not proved: `run-benchmark.py` (Python statement tree, m2; digests; L cap; budgets);
>    `LayoutJson.parse` (the indexed `C_V`, `L_chain`, m4); `gen-chain-layout.py` (`L_chain(n)` is
>    blake2s^n(s) = y by `check-chain.py` and one-G-call kernel controls). 9. The reference machine.
> Not trusted: `Library/` (`narg_complete`, `live_of_secure`, `chain_extracts`, …), `Clean/`,
> `Bridge/`, `Controls/`, `probes/`, the baseline, the native prover (only its tapes are checked).
> Not claimed: composition across levels; that benchmark nodes are provable (S5-A10); hardness of a
> one-element secret at `k ≥ 25`; `decode`'s efficiency.

---

## 6. Readability: can a cryptographer who does not read Lean audit it from the docstrings?

Three sentences per file.

- **`Contract.lean`.** It is the reading order and nothing else, and the order is the dependency
  order. The 5-line header names the three carried-over files and the eight new ones. It could
  add one line per file saying which certificate conjunct each file feeds (3.2's table).
- **`Field.lean`.** The header and the `K` docstrings let a reader check the arithmetic against
  `x^64 ≡ x^4 + x^3 + x + 1 = 0x1B` without Lean: shift-and-xor, then two folds. The `E` product
  docstring gives the two identities it folds by. The reader is not told that `E`'s arithmetic is
  never used by a certificate (S9D-m1), so they will audit 10 lines for nothing.
- **`Layout.lean`.** It is the best-documented file: the header states the relation in prose,
  `Layout.rel`'s docstring lists its six clauses in the order of the code, and
  `Chip.Admissible`/`Layout.Admissible` match DESIGN §2.2 number for number. The two traps, a
  selector other than `1` is silent and the view's next row wraps modulo the height, are both
  stated. A cryptographer can audit it fully from the docstrings.
- **`Shapes.lean`.** The round menu (`msg`, `chal`) is clear and its docstrings are accurate. The
  header and three docstrings speak of v0.3 objects (`Agrees`, the QUERY syscall, reductions,
  DESIGN §3/§5/§7 of the old design), which a new reader cannot resolve (S9D-m6). `Transcript sh m`
  as a dependent function through `Fin.castLE` is the one line that needs Security's reading
  guide.
- **`Security.lean`.** The header's reading guide ("prefix of *length* `m`", "`castSucc`/`succ` =
  before/after round `m`", "`Bad`'s `∃ w` is the next-stage witness") is what makes `KSF` and `Bad`
  auditable. `RbrKS`'s docstring says why `Nat.card` is the count, though the finiteness it relies
  on is in the Library. "Protocols and reductions" and "DESIGN §5" are stale.
- **`Machine.lean`.** The header lists what was kept, changed and removed against v0.3 and gives
  the memory map and the HALT convention, so the extractor's machine is auditable as a delta. A
  reader still needs the vendored `execInstrBr` for the base semantics. Nothing says which of its
  arms are dead (S9D-m7).
- **`Extractor.lean`.** The header is a model docstring: what the bound guarantees, why the
  serialisation is the contract's, what a failed call yields, and the thresholds in §4's quote.
  Every definition says which words go where, so the tape layout can be re-implemented from the
  text. `Mid` via `Fin.cases` needs the translation "tables before round 0, words after", which
  the docstring gives.
- **`Protocol.lean`.** The field docstrings say what each field is and which are executed. The
  `Secure` docstring is a fair one-line summary, but it omits the two things a submitter most needs:
  soundness covers non-admissible layouts, and `ε` is per round (S9D-m3). The header's list of
  computable fields predates gate rule 4 (S9D-m6).
- **`Hash/Blake2s.lean`.** It is exemplary. Every definition cites its RFC 7693 section, the header
  gives provenance (leanerVM commit, line ranges, the RFC text's SHA-256) and every change from the
  source. A cryptographer can audit it line by line against the RFC.
- **`Compile.lean`.** The header's byte grammar is complete enough that S3 wrote an independent
  encoder from it alone, and every definition's docstring is a sentence of that grammar.
  `NARG`'s "`vkc` is the indexer's output" misleads a reader who comes from `aggOK`, and
  `Round.decode` is dead code a reader will try to place.
- **`Recursion.lean`.** The header explains statements as digests, the VK cycle and why roots are
  32 bytes. `RecursionEntry`'s field docstrings say what each field buys, the `live` residual
  included. `rootOK`'s docstring should say that no certificate states it (S9D-m2).
- **`Certificate.lean`.** It is clear about what is certified (configuration, image, static size),
  what is declared but harness-checked (the digests) and what is measured. The class being pinned
  "by its type" is the one Lean-ism a reader needs explained, and the docstring does explain it.
- **Challenge stubs.** The header comments say which definitions are organiser data and which are
  the solver's, and what the comparator and the gate check. The R stub's three conjuncts each carry
  a sentence.
- **Vendored machine.** It has no contract-level docstrings, as it must stay byte-identical.
  `Machine.lean`'s header is the only guide, so S9D-m7's sentence belongs there.

### The five worst docstrings, with rewrites

1. **`Shapes.lean` header, first bullet**. Now: "`msg o`: the prover sends a raw vector `Fin
   2^o.logLen → K` (an oracle, read by QUERY in leaves of `2^o.logLeaf` elements). No submitter
   types, no serializer: every raw vector is a possible message, so `Agrees` (∀ transcripts)
   covers every string an adversary can commit to."
   Rewrite: "`msg o`: the prover sends a vector of `2^o.logLen` elements of `K` (an oracle). The
   verifier reads it only through `QProg.query`, a leaf of `2^o.logLeaf` elements at a time. Every
   vector of that length is a possible message: there is no submitter type and no serialiser, so
   the security statements quantify over every string an adversary can commit to." Also drop
   "(DESIGN §7: …)" for "(DESIGN §3.1)", and in `Oracle.get` replace "QUERY never reads there" with
   "`QProg.eval` reads only leaves below `leaves`, so never there".
2. **`Protocol.Secure`**. Now: "**Security of a protocol**: perfect completeness for `relK k`,
   worst-case RBR knowledge soundness with the extractor of the image (`B(k)` steps in all over its
   `n + 1` calls) at the declared errors, and `ε ≤ 2^-128` in every round (…)".
   Rewrite: "**Security of a protocol.** (1) Perfect completeness: on every admissible layout at
   class `k`, every statement and satisfying witness (`relK k`), and every challenge vector, the
   verifier accepts the honest transcript. (2) Round-by-round knowledge soundness with the image's
   extractor (`B(k)` steps in all over its `n + 1` calls), at **every** statement `(L, x)`,
   admissible or not. A secure verifier therefore rejects non-admissible layouts, which it sees only
   through `VK L` and `IDX L`. (3) Each challenge round's error is at most `2^-128`, so the
   protocol's knowledge error is at most `n · 2^-128 ≤ 2^-114`. The round cap, the key cap and the
   shape caps are fields of `Protocol`."
3. **`NARG`**. Now: "… `vkc` is the indexer's output (`index`)."
   Rewrite: "… `vkc` is any compiled key. On the badge path it is the indexer's output (`index`).
   In `aggOK` it is a key from the node's witness, bound to the statement only by its digest."
4. **`rootOK`** (and `treeRoot`). Now: "**The organiser's root check** (DESIGN §5.1, §6.3 step 5):
   `x` is the root of the statement tree … It pins `d0`, `d1`, `d2`, `d3`."
   Rewrite: "**The root check, as a specification.** `x` is the root of the statement tree of depth
   `d` over the leaf statements `xs`, keyed by the indexer for `C` and `L`. It pins `d0`, `d1` (the
   keys), `d2` (the children, by collision resistance, level by level) and `d3` (the tags, by
   position). No certificate states it. The organiser's runner computes the tree in Python
   (`harness/run-benchmark.py`, `tree_root`), and CI tests that against the kernel KATs of
   `Controls/RecursionData.lean` (`run-benchmark.py selftest`)."
5. **`SecureWith`, `roundCap`, `errorCap`** (one family). Now: "The security clause shared by
   protocols and reductions …", "every protocol and reduction has at most `2^14` rounds", "Contract
   error cap (DESIGN §5)".
   Rewrite: "The security clause of a protocol: perfect completeness, an RBR knowledge-soundness
   state function for the named extractor at errors `ε`, and the cap `ε c ≤ 2^-128` (DESIGN §4)."
   For `roundCap`: "every protocol has at most `2^14` rounds (DESIGN §3.1)". For `errorCap`:
   "Contract error cap (DESIGN §4): every challenge round's error is at most `2^-128`."

Honourable mention: the `extractorBudget` sentence "It excludes enumerating `2^128` candidates" is
true but beside the point. The threshold a reader needs is §4's: a one-element secret is
enumerable only if `2^(2k+16) ≥ 2^64 · c`, never for `k ≤ 23`.

---

## 7. Probes and logs

All probes run from the repository root with `lake env lean <file>`. Logs are in
`logs/S9-definitions/`.

| Probe | What it shows | Log |
|---|---|---|
| `probes/s9/definitions/TrustedAudit.lean` | axioms and constructs of all 1,080 contract constants (internal names included) and the 205 vendored constants they reach; theorem-kind constants; `decide`-closed proofs in definitions | `trusted-audit.log` |
| `probes/s9/definitions/CertificateCone.lean` | the cone of the six certificate structures: 294 of 311 declarations; the 17 outside, `unpack` (rendered data) and 16 that certify nothing (S9D-m1, m2) | `certificate-cone.log` |
| `probes/s9/definitions/NonAdmissible.lean` | `nonadmissible_rejected`: a secure protocol without challenge rounds accepts no transcript of a non-admissible layout (S9D-m3); standard axioms | `nonadmissible.log` |
| `probes/s9/definitions/srcrule/RawHash.lean` | Lean runs `#eval` after `r#`; `source-rule.py` reports 0 findings (S9D-M1) | `source-rule-bypass.log`, `source-rule-rawhash.log` |
| `probes/s9/definitions/srcrule/Interp.lean` | a `run_cmd` hidden by a string inside `s!"{…}"`, with only the contract imported: it runs, 0 findings (S9D-M1) | `source-rule-interp.log` |
| `probes/s9/definitions/srcrule/ForgeRawR.lean`, `UseRawR.lean` | S6b's `ForgeRaw` with a two-line `r#` prefix: 0 source-rule findings (original: 5); compiled in `/tmp/s9def-srcrule`, the importer's `l_useDec` is `List_beq(msg, msg)` (`acceptAll`); compiled in `/tmp/s9def-a4` against `.lake/org`, the current gate binary says `PASS` with CI's options (S9D-M1) | `source-rule-bypass.log`, `forgerawr-gate2.log` |
| `lake exe axiomaudit` (existing tool) | `PASS` over Contract, Library, Controls, Bridge | `axiomaudit.log` |
| `probes/s3/RevBinding.lean` (existing S3 probe) | `opening_binding` still checks against today's contract (S9D-m5) | `revbinding.log` |

Commands to reproduce S9D-M1 against the harness's own tools:

```sh
R=$(pwd); D=/tmp/s9def-a4; mkdir -p $D; cp probes/s9/definitions/srcrule/ForgeRawR.lean $D/
python3 -I scripts/source-rule.py probes/s9/definitions/srcrule          # 0 finding(s)
python3 -I scripts/source-rule.py probes/s6b/gate | grep -c ForgeRaw     # 5 (the original)
(cd .lake/org && lake env bash -c "LEAN_PATH=$D:\$LEAN_PATH lean --root=$D -o $D/ForgeRawR.olean $D/ForgeRawR.lean")
(cd .lake/org && lake env bash -c "LEAN_PATH=$D:\$LEAN_PATH .lake/build/bin/gate ForgeRawR S7Raw.certified \
  --manifest $R/scripts/olean-manifest.sha256 --allowed-imports $R/scripts/import-allowlist.txt \
  --frontend-imports $R/scripts/import-frontend.txt --computable S7Raw.submission --badge-root S7Raw.submission")
```

(The gate is the organiser build's binary, `.lake/org/.lake/build/bin/gate`, 07:11. The root's
`.lake/build/bin/gate` (03:48) predates `Gate.lean` (07:09) and rejects the v2 options.)
