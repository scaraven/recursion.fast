# Lean fidelity review of the recursive-KS probes

This review checks the Lean behind `SYNTHESIS.md` C-1, C-3 and C-4; no Lean file was edited. The
five `Explore/` probes were read against the contract, `Library/{KS,Compose}`,
`Controls/Backdoor` and `harness/rfh`.

## 0. Build and hygiene (measured)

- Every file passes `lake env lean` through the capped runner, exit 0 (logs
  `logs/audit/review-lean-<File>.log`; scratch copies with `#print axioms` added for every cited
  theorem). The CombCompose olean is newer than its source. Every cited theorem, plus `combWalk`
  and `Controls.Backdoor.certified`, uses only `[propext, Classical.choice, Quot.sound]`.
- A grep for `sorry|native_decide|axiom|opaque|implemented_by|extern|unsafe|partial` finds
  nothing. One warning: `FirstEscape.lean:28` uses the deprecated `dite_cond_eq_true`.
- The `#guard` known answers (`CombCompose.lean:281-293`) pass and match `harness/rfh/digest.py`
  (re-derived: step 1 `e8fb8e…`, step 3 `ceb1d5…`).
- My kernel probes (scratch only, `logs/audit/review-lean-probe.log`, clean axioms):
  `collision_exists`, `comb_compose_trivial`, `backdoor_escape`, and an `rfl` check on the
  extractor's statement argument. They back findings 1, 3 and 4.

## 1. Findings

1. **Major: `comb_compose` is vacuous as a proposition** (`CombCompose.lean:233-238`). Its
   disjunct `Nonempty Collision` is a theorem, by pigeonhole (BLAKE2s maps the infinite
   `List UInt8` into the finite `Digest`). My probe `comb_compose_trivial` proves the whole
   conclusion for every `S, vk, L, l₀, ls, p`, without `hacc` or `hn`. The content is in the
   term `combWalk` (`:222`), whose type `COut` carries an explicit `Collision`, `Forgery` or
   `Forall₂` proof of the starts, and in the `.Escaped` events of `comb_prob`/`stream_prob`.
   Fix: cite those, not `comb_compose`. `Compose.compose` is vacuous too, undocumented.
2. **Minor: the kernel walk is not V-free.** `combWalk` calls `Compose.extract`, which decides
   `Rel (S.acc vk)` and so runs `V` on extracted children. Used as a collision or forgery finder,
   it has the same unbounded-`V` problem as C-3(b) has for the PRF distinguisher. C-1 already
   files "the E-only comb walk" under paper. The synthesis should add that the EUF-CMA and
   collision reductions need that paper walk too, not only the PRF hybrid.
3. **Minor: the extractor gets the key as its statement** (`T2Backdoor.lean:69, 95, 101`):
   `S.E vk (magic c) L`. This is true only because `WitnessSending.E` ignores its statement
   (probe: `rfl`). In `comb_collapse`/`tree_collapse` the `vk` is shared with `accT2`, so the
   conjunct is not extraction at the root's statement. `T2-backdoor.md` F2 copies it. Fix:
   `S.E (combRoot d₀ ds) …`.
4. **Minor: "extraction fails" (C-4) holds for the named extractor only.** It is not an
   extractor that never answers: `S.E = decode` opens every honest proof (`decode_encode`). But
   `relT2_node_magic` shows that every node statement has a `RelT2` witness one level down, and
   no false leaf statement is exhibited (`T2-backdoor.md` F2 says so; C-4 should too). The
   failure is recursive: finding leaf starts for arbitrary digests inverts BLAKE2s (paper).
5. **Minor: "at every depth" has no recursive content in `comb_collapse` and `tree_collapse`.**
   Both are `accT2_magic` instantiated at `combRoot`/`treeRoot` (`:96, :102`). The root is
   accepted directly and no child is checked (per-node: `comb_spine_magic`). That makes C-4
   stronger, not weaker. `T2Backdoor.combRoot` (`:77`) duplicates `CombCompose.combRoot`.
6. **Minor: `accT2` is a fair public-hash Fiat–Shamir verdict.** It is `(V c π).run Hpub` with
   `Hpub` unkeyed BLAKE2s (`:31, :34`), which is the replay a T2 node circuit runs
   (`runSeq_ownTrace`). It drops `acc`'s length, `qV` and `queryCap` conjuncts, which the magic
   proof meets anyway. `node_wraps_magic`'s `SigOk` hypotheses are dischargeable by
   `Signer.sigOk_sign`, but no control in the file shows it.
7. **Minor: the stream bound does not depend on the comb.** `stream_prob` (`StreamBound.lean:86`)
   and `stream_bad_prob` (`:182`) go through `escape_any_le`, whose event ignores `A`'s output.
   The comb enters only through the walk's typed outcome. So depth independence is a property
   of `KS` + `Escape.wins`, and the bound is robust to errors in the statement.
8. **Minor: C-3(c) wording.** `tape_out_of_domain` (`SeamsT1.lean:52`) puts a log of at least
   `2^62` entries (distinct queries) outside `Computes`. A `2^64`-query run is outside only if
   its log gets that large, so "not covered" is accurate and "outside" overstates.

## 2. Fidelity checks that pass

- **The comb matches the harness.** `bench.py:372-374` gives `stmts[i-1] = combStmt l₀ (ls.take i)`
  with per-leaf lengths. `stream_prob` checks `xs[i]` against `ls.take (i+1)`, which is step
  `i+1`. Acceptance is `S.acc vk`, the harness's `check`.
- **The hypotheses can be discharged.** `n ≤ chainCap` holds because `draws.length` clamps to
  `n_hi = 2^20 = chainCap`. `Q + qV ≤ logCap` holds because `qV ≤ 2^16` and `Q ≤ 2^64`.
  Functional logs are an invariant discharged inside the proof, not a hypothesis.
- **`KS.exists_wins` uses a legitimate `KS` adversary.** `KS.select` builds it as `withLog A`
  followed by `sel`. The contract's `KS` quantifies over every `OProg`, which is unbounded, so an
  epsilon selector is admissible. `Wins` requires `runLog L = some true`, so `V` asks nothing
  fresh. A PRF distinguisher cannot run this search; `stream_bad_prob` is what covers that.
- **The hypotheses are non-vacuous.** `hks` holds for `WitnessSending.certificate` (`ε = 0`) and
  for `Backdoor.certified` (`ε = 2^-120`). The event can occur: `backdoor_escape` exhibits an
  `Escape` under a real signer key. `combPaths_suffix` discharges `stream_bad_prob`'s
  suffix-closure hypothesis. `StructOk` has positive and negative controls.
- **Arithmetic.** `stream_err_target` gives `≤ 2^-55`; the true value is about `2^-56`.

## 3. Verdicts per cited theorem

| Theorem | Verdict |
|---|---|
| `CombCompose.comb_compose` | **misdescribed** (vacuous Prop; cite `combWalk`, F1) |
| `CombCompose.comb_prob` / `combWalk` | faithful with caveat (kernel walk runs `V`, F2) |
| `FirstEscape.escape_prob_le_first` | faithful (subsumed by `escape_any_le`) |
| `StreamBound.KS.exists_wins` | faithful |
| `StreamBound.escape_any_le`, `stream_escape_le` | faithful |
| `StreamBound.stream_prob` | faithful with caveat (bound is comb-independent, F7) |
| `StreamBound.stream_bad_prob` | faithful (V-free event; the walk to it is paper) |
| `StreamBound.stream_err_target` | faithful |
| `T2Backdoor.accT2_magic` | faithful |
| `T2Backdoor.extract_magic` | faithful with caveat (statement argument is `vk`; named `E` only, F3, F4) |
| `T2Backdoor.comb_collapse`, `tree_collapse` | faithful with caveat (F3, F5; no recursion involved) |
| `Controls.Backdoor.certified` | faithful |
| `SeamsT1.outputs_escape_le`, `tape_out_of_domain` | faithful (C-3(c) wording, F8) |

The conclusion of C-1 is supported in the kernel as stated: the probability that some accepted
output's walk ends in an escape is at most `(Q+qV)·ε`. C-4's kernel part holds for the named
extractor. No cited statement is weaker than claimed in a way that changes a ruling.
