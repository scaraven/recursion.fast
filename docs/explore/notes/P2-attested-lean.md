# P2: Lean probes for the attested oracle (D4)

Probe author: Lean implementer agent, 2026-10-20. Code: `RecursionFast/Explore/Attested/*.lean`,
aggregated by `Attested/All.lean`, imported from `RecursionFast/Explore.lean`. Design formalised:
`W2-attested-oracle.md` §A. All claims are **kernel** unless marked otherwise. Namespace
`RecursionFast.Explore.Attested` is omitted below.

## Conclusions

1. **Attestation escapes "the parent must re-ask".** P1 showed that in the pure ROM a node verifier
   that judges its children against answers it did not ask is unsound (`lazy_no_kstate`), and that
   a sound one re-asks them (`deferState`, `|Q|` queries per node). With the attested oracle, a
   node verifier that makes **one** call, `attest (hashList xs)`, and judges its children reading
   the carried list `xs` has an attested knowledge state whenever its child verifier has one, with
   the same potential and error (`attState`). Its calls at a node are exactly
   `[attest (hashList xs)]` (`calls_node`). Over P1's `W1` it is `KSA` at error `0` with **one call
   per verification at every level of the tree** (`att_W1`). The root of a depth-2 tree on a
   concrete well-formed log makes one call (`root_calls`) and the whole tree is extracted or ends
   in a returned collision (`root_extracts`). The work moves into the prover's `certify` calls,
   which the service checks and which `qV` does not count. This does not contradict
   Barbara–Chiesa–Guan: `attest` is a stateful service, not a random oracle, so the model is outside
   the pure ROM (an SROM-like model, BRIEF §3) (**paper**).
2. **Composition from one log holds with the collision disjunct.** Below potential `1` on a
   well-formed log, the extractor's walk from an accepted root either extracts the tree to every
   depth or returns a named pair `(x, y)` with `IsColl x y`, a BLAKE2s collision (`compose`,
   `compose_all`, `compose_blake2s`). In probability, certifications are free. The failure
   probability of a game with `nq` queries and `nc` certifications, `nq + nc ≤ logCap`, is at most
   `nq · ε`, for one level (`Paper.paper`) and for the whole tree (`Paper.paper_tree`). This checks
   W2 §A.6's "one-line extension". It took a new game type and about 140 lines, but the argument is
   the library's, plus the `cert` law and a `WF` invariant.
3. **The collision disjunct is only as strong as `Computes`.** As the task predicted, the
   proposition form is vacuous (`final_prop_vacuous`, from the pigeonhole `exists_isColl`). The
   output form is not enough by itself either. The accept-all verifier, with the extractor that
   returns the `Classical.choose` of a pigeonhole collision, is `KSA` at error `0` with no call
   (`acceptAll_choice`). In v3 the accept-all certificate needed an open fact about BLAKE2s
   (`acceptAll_kstate_iff`: every digest has a witness). Here it is a theorem. So D4's knowledge
   content rests entirely on v3's requirement that a step-bounded program compute the extractor
   (`Computes`, not modelled here). For a constant extractor with a named pair, the certificate
   holds exactly when the pair is a collision (`acceptAll_iff`, `acceptAll_blake2s`).
4. **The collision must be between bounded lists (W2 M1, now kernel).** `enc64` wraps at `2^64`,
   so `encList` is not injective (`encList_not_inj`): an answer to a `2^64`-byte query re-parses as
   an answer to the empty query followed by `39` hash items and `j + 1` empty answers. Two distinct
   lists then share a `hashList` with the **same preimage** (`hashList_not_coll`), which is no
   BLAKE2s collision. `IsColl` therefore requires both lists to be bounded (all queries shorter
   than `2^64` bytes). On bounded lists the item codes are prefix-free and `encList` is injective
   (`Item.enc_append_inj`, `encList_inj`), so `IsColl` is a BLAKE2s collision (`IsColl.blake2s`).
5. **`final`'s `WF` hypothesis costs nothing.** The potential guarded by `WF` (`1` off well-formed
   logs) satisfies `empty`, `step`, `cert`, and its `final` needs no `WF` (`KStateA.gμ_*`). The
   game only reaches well-formed logs (`WF.snoc_ans`, `WF.snoc_cert`, used in
   `Paper.prob_le_pot`).

## Theorems

| Lean name | File | What it says |
|---|---|---|
| `Item`, `Ev`, `ALog`, `tagList`, `Item.enc`, `encList`, `hashList` | Model | W2 §A.1's items, events and byte layout: `ans q a ↦ 0x00 ‖ enc64 \|q\| ‖ q ‖ a`, `att h ↦ 0x01 ‖ h`, `hashList xs = BLAKE2s(0x41 ‖ encList xs)`. |
| `enc64_inj`, `Item.enc_append_inj`, **`encList_inj`** | Model | `enc64` is injective below `2^64`. Small items are prefix-free. `encList` is injective on bounded lists. |
| `hashList_coll` | Model | Two distinct bounded lists with one `hashList` give distinct BLAKE2s preimages with one digest. |
| `firstAns`, `certOf`, `attested`, `attested_iff`, `certOf_spec` | Model | `L`'s answer to `q` is its first `ans q _` event. `attested L h` holds iff some `cert xs ∈ L` has `hashList xs = h`. |
| `Valid`, `Item.OK`, `WF`, `WF.valid_of_mem`, `WF.snoc_ans`, `WF.snoc_cert`, `WF.ans_of_cert` | Model | A list is valid on `L` when each answer is bounded and is `L`'s first answer, and each hash is attested. A log is well formed when each `cert` is valid on its prefix. Well-formedness is kept by answers and valid certifications. A well-formed log's certified lists are valid on the whole log. |
| `AProg`, `AProg.runLog`, `AProg.runItems`, `AProg.calls`, `Call` | Model | Programs with `query` and `attest`. Read from a log; read from a list of items (the in-circuit run of a child); the list of calls under an oracle and an attest predicate. |
| **`runItems_valid`** | Model | **Lifting**: a verdict read from a list valid on `L` is the verdict read from `L`. |
| `OProg.toA`, `ansLog`, `firstAns_eq`, `toA_runLog`, `toA_calls` | Model | Embedding of the contract model: a lifted program reads from `L` what the original reads from `L`'s answers, and makes the same queries. |
| `RelA`, `relA_leaf`, `relA_node` | KState | The relativized relation on an attested log: v3's leaf clause; node: `c = nodeStmt c₁ c₂` and both children accepted on `L`. |
| `Out`, `IsColl`, `IsColl.blake2s`, `Sound` | KState | Extractor output `wit w \| coll x y`. `Sound` for `coll x y`: distinct bounded lists with one `hashList`, hence a BLAKE2s collision. |
| `exists_isColl` | KState | Pigeonhole (`Finite.exists_ne_map_eq_of_infinite`): a list-hash collision exists. |
| **`KStateA`**, `KSA` | KState | `μ`, `empty`, `step` (fresh `q`: average rise ≤ `ε` over `2^256` answers, `L.length < logCap`, `μ L < 1`), `cert` (`L.length < logCap → Valid L xs → μ (L ++ [cert xs]) ≤ μ L`), `final` (`WF L → L.length ≤ logCap → μ L < 1 →` accepted `→ ∃ o, E c π L = some o ∧ Sound V L c o`). `KSA` also bounds `V`'s calls by `qV`. |
| `KStateA.gμ`, `gμ_empty`, `gμ_step`, `gμ_cert`, `gμ_final` | KState | `WF` in `final` costs nothing (Conclusion 5). |
| `KStateA.zero`, `KStateA.ofRel`, `KSA.ofRel`, `liftV`, `liftE` | KState | Builders. Every P1 `KStateRel` lifts, with potential `μ ∘ ansLog`, which ignores certifications. |
| `TreeOKA`, `collAt`, **`compose`**, **`compose_all`**, `compose_blake2s` | Compose | For every depth `d`, either `collAt … d = none` and the tree is extracted to depth `d`, or `collAt … d = some (x, y)` with `IsColl x y`. In the second case the pair is a BLAKE2s collision. |
| `AFrame`, `attV`, `attE`, `liftOut`, `attV_base`, `attV_node` | Escape | The attesting node verifier and its extractor (see Conclusion 1). |
| **`attState`**, `attState_μ` | Escape | `KStateA Vc Ec ε → KStateA (attV C Vc) (attE C Ec) ε`, same `μ`. On a node: the certified `ys` with the carried hash equals `xs`, giving the node witness by `runItems_valid`, or differs, giving `coll xs ys`. |
| **`calls_node`**, `attV_calls`, `attKSA` | Escape | A node's calls are exactly `[attest (hashList xs)]`. `KSA` passes from `Vc` to `attV` for every `qV ≥ 1`. |
| `attV_empty` | Escape | On the empty log a node frame is rejected (contrast `lazy_accepts`). |
| `W1A`, `w1A`, `w1A_ksa`, **`att_W1`**, `att_W1_unary` | Escape | Over `W1`: `KSA` at error `0`, one call. Holds for every codec, the unary one included. |
| `Clean`, `exists_items`, `clean_attV`, **`attV_complete`**, `runLog_append_of_clean`, `clean_W1A` | Escape | Completeness at a node: from clean accepted children on a well-formed `L`, a valid list `xs` exists, `L ++ [cert xs]` is well formed, and the node proof carrying `xs` is accepted on it. Clean accepted runs stay accepted and clean as the log grows. |
| `Paper.Game`, `Paper.prob`, `Paper.pot`, `Paper.DepthLE` | Paper | Games with query, attest and certify moves; lazy sampling; the stopped capped potential. |
| `Paper.pot_le`, `Paper.prob_le_pot`, `Paper.paper_of`, **`Paper.paper`**, **`Paper.paper_tree`** | Paper | Failure probability ≤ `nq · ε` for `nq` queries and `nc` certifications, `nq + nc ≤ logCap`; per level and for the whole tree. |
| `acceptAll`, **`acceptAll_iff`**, `acceptAll_blake2s` | Controls | (a) Accept-all with the constant `coll x y` extractor has a `KStateA` (any `ε`) iff `IsColl x y`, hence a BLAKE2s collision. |
| `final_prop_vacuous`, `chosen`, **`acceptAll_choice`** | Controls | (a) The proposition form is vacuous. With `Classical.choose`, accept-all is `KSA` at `0`, `0` (Conclusion 3). |
| `wrong_not_wf`, `unasked_not_wf`, `shadowed_not_wf`, `unattested_not_wf`, `wf₁`, `wf₂` | Controls | (b) A certified wrong answer, an unasked answer, a non-first answer, or an unattested hash makes the log ill formed. One answer plus its certification is well formed, and so is a recursive certification on top. |
| `wsA`, `wsA_μ`, `ws_ksa` | Controls | (c) Witness-sending: `KStateA` at `μ = 0`; `KSA` at error `0`, `0` calls. |
| `L₂`, `π₂`, `wf_L₂`, `root_accepts`, `root_calls`, `root_extracts` | Controls | (d) A depth-2 tree of `W1` leaves on a concrete well-formed log: the root is accepted with one call, and `compose_all` applies. |
| **`encList_not_inj`**, `hashList_not_coll` | Controls | (e) The unbounded encoding is not injective (Conclusion 4). |

## `#print axioms`

`lake env lean <scratchpad>/P2Axioms.lean` (59 declarations, `logs/p2-axioms.log`). Every one
depends only on a subset of `propext`, `Classical.choice`, `Quot.sound`. The pure model and
control lemmas (`attested_iff`, `WF.*`, `runItems_valid`, `toA_runLog`, `calls_node`,
`attV_complete`, `runLog_append_of_clean`, the `*_not_wf`, `encList_not_inj`, …) avoid
`Classical.choice`. `toA_calls` uses
`propext` only. Every knowledge state uses `Classical.choice` through `NNReal`. A source scan for
`sorry`, `native_decide`, `implemented_by`, `extern`, `csimp`, `admit`, `axiom` over
`RecursionFast/Explore/Attested/` finds nothing.

```
'encList_inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'runItems_valid' depends on axioms: [propext, Quot.sound]
'compose_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'attState' depends on axioms: [propext, Classical.choice, Quot.sound]
'calls_node' depends on axioms: [propext, Quot.sound]
'att_W1' depends on axioms: [propext, Classical.choice, Quot.sound]
'attV_complete' depends on axioms: [propext, Quot.sound]
'Paper.paper_tree' depends on axioms: [propext, Classical.choice, Quot.sound]
'acceptAll_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'acceptAll_choice' depends on axioms: [propext, Classical.choice, Quot.sound]
'encList_not_inj' depends on axioms: [propext, Quot.sound]
(… the full 59 lines are in logs/p2-axioms.log)
```

## Check times (**measured**)

`timeout 600 lake env lean RecursionFast/Explore/Attested/<File>.lean` with its imports built
(`logs/p2-check-times.log`). Each figure includes about 2.7 s of import:

| File | Wall | Code lines (`scripts/loc.py`) |
|---|---|---|
| Model | 6.3 s | 236 |
| KState | 5.8 s | 98 |
| Compose | 5.3 s | 59 |
| Escape | 6.2 s | 190 |
| Paper | 7.2 s | 144 |
| Controls | 5.7 s | 127 |
| All | 4.9 s | 6 |

`lake build RecursionFast.Explore.Attested.All` took 26 s for all seven modules after an edit to
`Model` (terminal output), and 13.6 s after an edit to `Escape` (`logs/p2-build-all.log`).

One slowdown was found and fixed. `Paper.pot_le` first took 15.5 s, because `pot_le k _ nq nc _ …`
left the program and log as holes, and the elaborator searched `NNReal`/`Real` order instances
while unifying `pot` against the expected type. Explicit arguments bring the file to 7.2 s.

## Deviations from W2 §A and from the brief, and why

1. **`Sound` for `coll` requires bounded lists** (brief: `x ≠ y ∧ hashList x = hashList y`). The
   brief's form is satisfiable without a BLAKE2s collision (`hashList_not_coll`, kernel), so it
   would not mean what it is meant to. Corrected: `IsColl x y := Bounded x ∧ Bounded y ∧ x ≠ y ∧
   hashList x = hashList y`. The extractor's pair is `(carried, certified)`. The certified list is
   bounded because `Valid` includes the bound (W2 m1), and the carried list because `attV` checks
   `Bounded xs`. W2 put byte strings and `blake2s256` in `Out`; `IsColl.blake2s` turns the
   list-level pair into exactly that.
2. **`AProg` has no `certify` constructor.** In W2 a verifier's `certify` reads as `none`, so a
   certifying verifier is never accepted. Leaving it out changes no verdict. Certification is a
   **game** move, in `Paper.Game`.
3. **`runItems`: lookup semantics instead of W2's `runTrace`.** W2 answers the `i`-th call with the
   `i`-th item. Here a query is answered by the first `ans q _` item, and `attest h` succeeds iff
   `att h` is an item (otherwise `none`, never `false`). A `false` read from the list could be
   `true` on the log, so answering `false` would break lifting. With `none`, `runItems_valid` (the
   analogue of W2's `runTrace_valid_runLog`) holds for every program. On a list valid on `L`,
   lookup gives the same verdict as trace semantics whenever trace semantics gives one: both read
   `L`'s first answers and attested hashes (**paper**, not stated in Lean).
4. **`final` takes `WF L`** (the brief's form; W2's `final` has no `WF`). They are equivalent
   (`KStateA.gμ_*`).
5. **`Valid` needs the answers in the log already.** The deployed service evaluates an unqueried
   item on the fly. The model reads that as "query, then certify" (W2 §A.1 says the same), so an
   honest prover's list holds answers it has already asked.
6. **No proof-size cap in `RelA`**, as in P1's `RelL` (W2's `accL` has `π.size ≤ proofCap`). It
   would only add a conjunct to the node clause.
7. **Node frames abstract the byte format and carry children in the clear** (P1's `Codec`;
   `Codec.unary` inhabits it). The brief allowed this. No SNARK hides them, so proofs grow linearly
   and a node's local work equals running its children on `xs`. The probe isolates the oracle-call
   count.
8. **`KSA` counts calls as a list** (`AProg.calls H A : List Call`, W2's `calls : ℕ` is its length),
   so `calls_node` can state exactly which call a node makes, not only how many.
9. **Extras beyond the brief**: `Paper.lean` (probability with certify moves), `attV_complete`
   (node completeness), `KStateA.ofRel` (every P1 state lifts), the `gμ` lemmas, and controls (d)
   and (e).

## What the probes do not show

- **`Computes`.** The extractor's computability is not modelled, and the accept-all certificate
  `acceptAll_choice` shows that D4 needs it more than v3 does (Conclusion 3).
- **Deployment.** PRF security of the keyed oracle, key secrecy, the service's correctness, and
  O-25's closure are W2 §A.7, **paper**.
- **Succinctness or a SNARK node.** Children are in the clear. That a SNARK node proving
  `runItems xs cᵢ πᵢ = some true ∧ hashList xs = hᵢ` in-circuit is sound is W2 §A.4, **paper**
  (issue #7's decoding is unchanged).
- **Cost.** The service's `certify` re-evaluations are prover-side work, not counted by `qV`.
  Their price is C1/W2 M3–M4, **measured/estimate** there.
- **Whole-tree completeness.** Only one node is proved complete (`attV_complete`), plus the
  monotonicity the induction up the tree needs (`runLog_append_of_clean`). The induction over a
  tree of honest proofs is not written; control (d) is a concrete depth-2 instance.
- **The `coll` branch of `attE` firing on a concrete log.** That would need a concrete BLAKE2s
  collision. Only the accept-all controls exercise the disjunct.
- **The passage from lazy sampling to a random function and to randomised adversaries**, as in the
  library (**paper**).
- **A flat witness** (P1's `compose_flat`) is not ported.
