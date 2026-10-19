# V3-S2-KS RESULT: the potential knowledge state and the log-length guard

One implementing agent, 2026-10-19, on branch `v3/ks-potential` of a scratch clone of the core at
`15e4ae5`. A contract amendment requested from the submissions repository's S2 (SNARK baseline)
work: `docs/snark-baseline/notes/F1-ks-feasibility.md` §1, §2, §4 there, confirmed by
`notes/ADV1-rules-review.md` ADV-M2, ADV-M3 (probes in its `logs/adv-probes/`). Amendments:
V3-KS-A1 … A5 in `docs/DESIGN-AMENDMENTS.md`. Logs: the submissions repository's
`logs/ks-amendment/` (gitignored there).

## Headline

- **The contract's `KState` is a potential.** `μ : Log → ℝ≥0`, `μ [] = 0`; below `1` and within
  `logCap = 2^64` entries, a fresh query raises the average of `μ` over its `2^256` answers by at
  most `ε`; below `1` and within `logCap`, every accepted proof is extracted. `KS` is
  `Nonempty (KState R V E ε)` plus the query bound. The paper theorem is unchanged in form,
  `(Q + qV)·ε`, now for `Q + qV ≤ logCap`, by a stopped supermartingale and Markov (header of
  `Contract/Security.lean`, V3-KS-A2).
- **Contract: 331 code lines** (`scripts/loc.py`; S1 fix pass 328; budget 500).
  `Contract/Security.lean` 23 → 26. No other trusted file changed. `Certificate.lean` elaborates
  unchanged.
- **Nothing a submitter could do before is lost**: the S1 structure is `BoolKState` in the
  library and embeds (`KState.ofBool`, kernel-checked), from a bound on short logs only.
- **Two separating controls, kernel-checked**: `twoLucky` (a challenge over two answers, ROM
  error `2^-192`) has a potential at `2^-192` and no boolean state below `2^-96` even on short
  logs; `Vcol` (collisions, the binding half of a Merkle commitment) has no boolean state at
  `errorCap` over unbounded logs and one at `2^-192` within the guard.
- **Builds** (`logs/ks-amendment/`): `lake build` 2 min 07 s cold (own build directory removed;
  the shared package tree prebuilt), 4.15 GB peak; 3.0 s warm. Unamended `15e4ae5` in the same
  clone: 2 min 36 s cold (first build, `build-baseline-15e4ae5.log`). `lake build gate
  axiomaudit` 12.9 s; `lake exe axiomaudit` PASS (763 declarations), 5.4 s.
  `scripts/ci.sh /home/devops/Verified-zkEVM/riscv-zkvm`: CI passed (vendor, hygiene, source-rule
  fixtures, build, audit, line budget 331/500), 14 s warm (`ci.log`).

## Files

Code lines from `scripts/loc.py` (`loc-contract.log`, `loc-library-controls.log`; before:
`loc-before-15e4ae5.log`).

| File | Before | After | Change |
|---|---:|---:|---|
| `Contract/Security.lean` (TRUSTED) | 23 | 26 | `instance : Fintype Digest` (3 lines), `logCap`, `KState R V E ε` with `μ`, `empty`, `step`, `final`; `KState.Bounded` removed; `KS` with `Nonempty`. Header rewritten: the laws, the paper theorem, why a potential, why the guard. |
| `Library/Security.lean` | 35 | 107 | `digestEquiv`, `fintype_card_digest`, `card_digest`, `errorCap_lt_one`; `BoolKState`, `Bounded`, `BoundedBelow`, `Bounded.below`, `bounded_of_not_bad`, `Bounded.mono`, `one_le_of_bounded`; `step_of_hits`; `KState.ofBool`, `ofBool_μ_eq_zero`, `KState.zero`, `KState.mono`, `KState.one_le_of_jump`; `no_kstate_of_empty`, `acceptAll`, `acceptAll_kstate_iff` (now per error) |
| `Library/WitnessSending.lean` | 175 | 170 | `kstate := KState.zero 0 …` |
| `Controls/Security.lean` | 63 | 74 | ported (table below); `jump`, `jump_step`, `mono_control` new |
| `Controls/Potential.lean` | — | 297 | **new**: `twoLucky`, `Vcol` (table below) |
| `Controls/Backdoor.lean` | 113 | 115 | `boolState` (the S1 state, unchanged), `kstate := KState.ofBool boolState bounded.below` |
| `Controls/Certificate.lean` | 48 | 48 | `acceptAll_no_certificate` reads `h.secure.1.some` at `S.ε` |
| `Controls.lean` | | | imports `Controls.Potential` |
| `docs/DESIGN-AMENDMENTS.md` | | | section V3-KS, A1 … A5 |

### The new contract text (verbatim, without docstrings)

```lean
instance : Fintype Digest :=
  Fintype.ofSurjective (fun f : Fin 32 → Fin 256 => Vector.ofFn fun i => UInt8.ofFin (f i))
    fun d => ⟨fun i => d[i].toFin, by ext i hi; simp⟩

def logCap : ℕ := 2 ^ 64

structure KState (R : Digest → Wit → Prop) (V : Digest → Proof → OProg Bool)
    (E : Digest → Proof → Log → Option Wit) (ε : ℝ≥0) where
  μ : Log → ℝ≥0
  empty : μ [] = 0
  step : ∀ L q, L.length < logCap → μ L < 1 → q ∉ L.map Prod.fst →
    ∑ a : Digest, μ (L ++ [(q, a)]) ≤ (μ L + ε) * Fintype.card Digest
  final : ∀ L c π, L.length ≤ logCap → μ L < 1 → (V c π).runLog L = some true →
    ∃ w, E c π L = some w ∧ R c w

def KS (R : Digest → Wit → Prop) (V : Digest → Proof → OProg Bool)
    (E : Digest → Proof → Log → Option Wit) (ε : ℝ≥0) (qV : ℕ) : Prop :=
  Nonempty (KState R V E ε) ∧ ∀ H c π, ((V c π).queries H).length ≤ qV
```

## Controls and what each shows

Ported (F1 §4.6's table; meaning kept):

| Control | Now | Shows |
|---|---|---|
| `ws_ks`, `ws_kstate_trivial`, `ws_complete` | `μ = fun _ => 0` (`rfl`) | the witness-sending argument is KS at `0`, `qV = 0`; positive control of every law |
| `mono_control` (new) | `kstate.mono` to `errorCap` | `KState.mono` is inhabited |
| `rejectAll_ks`, `rejectAll_not_complete` | `KState.zero 0` | reject-all is KS and not complete: completeness is needed |
| `acceptAll_kstate_iff` (example), `acceptAll_no_kstate_empty`, `acceptAll_no_kstate_none` | at every `ε` | accept-all has a state iff every statement has a witness; none for the empty relation or a `none` extractor |
| `badAll`, `jumpAll_ge_one`, `badAll_not_capped` | potential `1` off `[]` (`jump`), at `ε = 1` | a potential that jumps to `1` on every answer needs `ε ≥ 1`, above the cap; one exists |
| `queryThenAccept_ge_one`, `ks1` | `final` forces `μ = 1` on every `[(q, a)]`, `one_le_of_jump` | the `step` law charges the verifier's own query (V3-S1 M2); exercises `step`, `final` and the `μ < 1` hypothesis; a state exists at `ε = 1` |
| `oneQuery_not_KS` | unchanged | the query conjunct of `KS` binds |
| `Certificate` controls (`ws_certificate`, `acceptAll_no_certificate`, `error_one_no_certificate`, …) | unchanged but one line | the certificate clauses |
| `Backdoor.backdoor` | `KState.ofBool` of the S1 state | the O-25 gap is unchanged |

New (`Controls/Potential.lean`):

| Control | Shows |
|---|---|
| `card_lucky` | `2^160` digests start with 12 zero bytes |
| `twoLucky_kstate`, `twoLucky_ks` | a potential at `ε = 2^-192` for the two-query verifier (the chance of acceptance given the answers so far, `0` before either), so KS at the cap with `qV = 2` |
| `twoLucky_bool_ge`, `twoLucky_no_bool_kstate` | every boolean state bounded at `ε` on logs shorter than `logCap` has `ε ≥ 2^-96`; none at the cap. The guard does not help; the potential does (ADV-M3, F1-2) |
| `collision_no_bound`, `collision_no_bool_kstate` | the ADV1 probe, ported: over unbounded logs, no boolean state of `Vcol` is bounded at `errorCap` (ADV-M2, F1-1) |
| `colBool`, `colBool_below`, `colBool_not_bounded`, `colState`, `collision_ks` | the boolean state "answers distinct" is bounded at `2^-192` within the guard but not at the cap without it; through `ofBool` it is a potential, so `Vcol` is KS at the cap with `qV = 2`. The guard is load-bearing |

## Deviations from the request and from F1 §4.2

- **`Fintype.card Digest` instead of `2 ^ 256`** in `step` (the request allowed either). No
  constant to trust; the library proves the value.
- **The instance is `Fintype.ofSurjective`, not F1's `Fintype.ofEquiv`**: three lines instead of
  four, and the instance's content is irrelevant to trust (subsingleton). The summing-over-
  `Fin 32 → Fin 256` alternative was not chosen: `step` would carry `Vector.ofFn` and
  `UInt8.ofFin` and stop reading as an average over answers.
- **`merkleToy` simplified to `Vcol`** (V3-KS-A4). F1 §1.2's full toy needs the dangling-root
  argument over a `2^136`-entry log with a pigeonhole over `2^128` answer classes (a 16-byte
  check makes a class exactly as large as a bad set, so the pigeonhole is over roughly `2^256`
  steps and several statements); `Vcol` is its collision half, already kernel-checked by the ADV1
  probe. Not kernel-checked: that a *potential* (as opposed to a boolean state) for `Vcol` needs
  the guard at `errorCap` (F1 §4.1, third row, which is a paper argument).
- **`ofBool` takes `BoundedBelow`** (a bound on logs shorter than `logCap`), more general than
  the request's `Bounded`; `Bounded.below` converts. This is ADV-M2's one-line fix, as a library
  notion.
- **Design text not edited**: the core records agreed changes in `docs/DESIGN-AMENDMENTS.md` and
  keeps `docs/DESIGN-v3.md` in sync with its master in the design workspace, which this agent
  must not edit. The ledger entries carry the replacement wording for §4.1, §4.2, §4.5, §6.6, §8.

## Observations

- **A failing unification can unfold the `Fintype Digest` instance.** Two proof attempts that
  mismatched a goal containing `Fintype.card Digest` failed with "maximum recursion depth" instead
  of a type mismatch (Lean tried to evaluate the instance, a `Finset.image` over `256^32`
  functions). Rewriting with `fintype_card_digest` first, or using `gcongr`, avoids it. A
  submitter will meet this; the library's lemmas are stated so that it does not arise. Marking the
  instance irreducible would add an attribute to the trusted base; not done.

## Open questions for the orchestrator

1. Accept `Fintype.card Digest` (as built) or the literal `2 ^ 256` in `step`?
2. `logCap = 2^64` (F1) or `2^58`, under the extractor tape's `2^60` words (F1 §4.3 notes either)?
   The paper bound at the caps is `2^-64` either way.
3. Should a control kernel-check that a *potential* for a Merkle-type verifier needs the guard
   (F1 §4.1 row 3), or is the boolean witness (`collision_no_bool_kstate`) enough?
4. The pin move in the submissions repository, and its `AGENTS.md` §4 and `BASELINE-TASK.md` §0,
   §5 (V3-KS-A5), follow this branch's merge.
