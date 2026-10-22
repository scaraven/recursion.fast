# A3. Attacks on D4+ (the oracle-chain leaf)

Adversarial note, 2026-10-20, on W2 §D ("D4+, for a later decision"). Sources: `docs/explore/BRIEF.md`;
W2 §A–§D; T1 §0–§4 (flat lift, Theorem 2.2, §4.4); W1 §6–§7 (W4, W5); C1 §2–§5; issue #6; P2
(kernel results for D4); `Contract/{Relation,Oracle,Security,Certificate}.lean` at `05fde28`. Tags as in
the brief: **kernel**, **paper**, **measured** (C1's `svc.log`, issue #6's logs, S2b), **estimate**
(arithmetic shown). Shapes: ranked `r = 8`, `n = 2^14`; long `r = 4`, `n = 2^20`. `proofCap = 2^20` B,
the contract's `qV ≤ 2^16`, `chainCap = 2^20`. Findings `M<i>` must be fixed before adoption; `m<i>` are
answered.

## Verdict

1. **D4+ closes issue #6(a), the trivial root, by the theorem, and that is its only gain.** Under an
   oracle chain the root verifier's view is `proofCap` bytes of proof, `qV` answers and `qV` bits, so it
   cannot recompute `2^22` chain steps from 8 KB of starts; the root must be a SNARK-shaped proof and
   `T_V` is a liveness cap (§3). The mechanism is **`proofCap` and `qV` together**, not `qV` (M2).
2. **It does not close #6(b).** T1's flat lift survives with one change: the extractor emits not
   witness-sending children but *the parent's own flat proof relabelled* for each descendant, with the
   starts in the clear for completeness (M1). That verifier is certifiable, complete, within every cap,
   and the benchmark prover flattens to the memory limit (`j ≈ 4`) exactly as in v3, 2.3–7.5× cheaper
   than full recursion (**estimate**). The per-level `T_V` rule cannot see it either: a relabelled flat
   proof verifies as fast as a recursive one. D4+ forces every inner proof to be a *real proof*; it does
   not force recursion below the flattening level, and economically those differ by the same factor as in v3.
3. **At the stated cap `qV ≤ n` witness-sending still exists at level 1** (one chain re-queried, the
   sibling's transcript carried: `n` queries, 512 KB), and at the contract's `2^16` at level 2; list-sending
   at level 1 misses `proofCap` by 64 bytes at `n = 2^14` and fits at `n = 2^13` (M2). The cap must be
   `qV ≤ 2^13` and `proofCap < 64·n_bench` must be a stated invariant; issue #8's proposal to raise
   `proofCap` for node proofs reopens it.
4. **Sound and formalisable.** Attestation removes the Ω(n) obstacle exactly as at nodes; the leaf SNARK
   over an attested list is knowledge-sound with the collision disjunct; completeness holds in the context
   form (§3). The leaf is the same BLAKE2s gadget at 1.16× the bytes, not 1.6× (m1); with a chain-specific
   encoding it is 0.5×. The benchmark still measures BLAKE2s proving.
5. **Engineering:** the chain is `n` dependent service calls per leaf, 17 ms (spin) to 0.6 s (futex) at
   `2^14`, 1.1–39 s at `2^20` (**measured** RTTs, **estimate** products): fatal for a Flock-class prover on a
   futex ring, fixed by a batched `chain(s, n)` service call (M3). Instances now depend on the secret key:
   not reproducible without W4's key release, and the three-repeat rule must change (M4).
6. **Recommendation.** Adopt D4+ only if `T_V`-as-liveness is worth a leaf decoder in `E`, key-dependent
   instances and the `chain` call; adopt it with `qV ≤ 2^13`, W4, and the invariant of item 3. Say in the
   design that #6(b) is a shape and memory question that no relation closes; the long shape (recursion
   1.17× of flat, C1 §2.2) is the incentive fix, not a cap.

## 1. D4+ made precise

Leaf clause: `RelL L c (.leaf s n) := n ≤ chainCap ∧ chainO L s n = some h ∧ c = leafStmt h n`, where
`chainO L s 0 = some s` and `chainO L s (i+1) = (chainO L s i).bind (fun d => L.answer (tagChain ‖ d))`.
It must be `Option`-valued: a leaf whose chain is not in the log is *not* in the relation, so `final`
obliges `V` to reject it, which `V` can only learn through `attest`. The honest leaf prover queries the
chain (`n` fresh queries, the context of W2 §A.5), certifies the `n`-item list, proves in-circuit
"`listHash xs = h ∧ xs` chains from `s` to `h_end` in `n` steps ∧ `c = leafStmt h_end n`"; `V` attests `h`
and checks the SNARK; `E` decodes `xs'` from `L` (issue #7, now at leaves) and returns `.leaf s n` or
`.coll`. The runner computes the instance through the service (it never holds `k`). W2's cap: `qV ≤ n`.

Verifier-side resources under D4+ (the only ones a cap can see): proof bytes `≤ proofCap`, oracle
answers `≤ qV` (32 B each), attest bits `≤ qV`, unbounded local computation. A verifier that learns a
chain digest it did not receive as an answer or in the proof must have hashed it from data it holds, and
chain digests are PRF outputs: the information bound of §3.

## 2. Findings

**M1. The flat lift survives as "proof of parent": #6(b) is not closed, and becomes invisible.**
*Attack (paper).* Let `V` have, beside its leaf and recursive branches, a flat branch (F): a proof
`(starts[2^j], π_flat, path)` where `π_flat` is one SNARK for "the `2^j` attested lists chain from
`starts` and the statements tree to `c₀`", with recursive attestation (one `attest`) and `starts`
hashed as public input (`2^j` local hashes), and `path` names a position in that subtree: `V` reads the
subtree's statements along `path` from the SNARK's public outputs (the circuit exposes the `2^{j+1} − 1`
digests, or `V` recomputes the `≤ j` `nodeStmt` hashes above the position from the exposed children),
checks the position's statement is `c`, and verifies `π_flat`. The same `π_flat`
is then an accepted proof of **every** statement in the subtree, with `≈ 5–10k` queries + 1 attest, and
`≤ proofCap` bytes. *Certifiable:* `final` for `(c, (starts, π_flat, path))` is the flat SNARK's
`final` plus `nodeStmt`/`leafStmt` consistency along `path` (a constructive collision otherwise); `E`
is straight-line: decode the lists once from `L`, emit `(π_flat, path·left)` and `(π_flat, path·right)`
as the children's proofs, which `V` accepts on the same `L` by construction, down to `.leaf sᵢ n` at the
leaves (the lists are `Valid`, so `chainO L sᵢ n = some hᵢ`). *Complete:* the honest node prover, handed
two (F) or (R) children, reads their starts, re-queries the chains (prover-side, uncounted) and
re-flattens, or simply recurses (branch R); `CompleteWithError` needs only one accepting strategy.
*Within the caps:* `qV` = the flat SNARK's own count; `proofCap` bounds `π_flat`, which bounds `j` by
proof size and the prover's memory at `j ≈ 3–4` (C1 §2.2, issue #8, **estimate**), as in v3.
*Why W2's argument misses it.* W2 counts queries of a witness-sending child; the child proof here is a
SNARK with its own `≈ 5k` queries, and T1 §1.5's premise holds unchanged: accepted child proofs are
never too short to carry 32 B per leaf. *Consequence.* The benchmark prover makes `2^{8−j}` flat SNARKs
at level `j` and `2^{8−j} − 1` recursive nodes above, emits relabelled proofs for every inner node
below `j` (the harness's sample checks pass, the liveness check of `E` passes). Work against full
recursion at `j = 4`: `(256 + 255·ν)/(256 + 15·ν)` leaf-units for a node cost `ν` = 1.46 / 3.16 / 11.6
(C1 §2.2): **2.3× / 3.5× / 7.5×** cheaper (**estimate**). This is v3's #6(b) strategy with the same `j`.
What changes: the per-level CPU rule of #6 (which only ever bit from level 5, where memory already bites)
has nothing left to measure, because a relabelled flat proof verifies as fast as a recursive one.
*Smallest fix.* None inside `KS` (A1 m1 stands). Record in the design that recursion below the memory
level is a *shape* question: at the long shape a node costs 0.18 leaf-units and flattening to `j = 2`
saves `< 15%` (C1 §2.2, **estimate**), so the incentive to flatten vanishes without a rule. Do not claim
"#6(b) closes by the theorem".

**M2. `qV ≤ n` alone excludes nothing above the leaf that `proofCap` does not, and at the stated cap
witness-sending reaches level 1 (level 2 at the contract's `2^16`).** *Attack (paper, arithmetic
**estimate**).* Three witness-sending forms exist for a level-`j` statement: (Q) carry the `2^j` starts
and re-query, `2^j·n` queries; (L) carry each chain's transcript in the compact form `s ‖ d₁ ‖ … ‖ d_n`
(`V` rebuilds the items, hashes them locally, one `attest` per list or one for the recursively certified
list of their hashes), `2^j·32(n+1)` bytes, **`qV = 1`**; (H) a hybrid, `a` chains by (Q) and `b` by (L),
`a·n ≤ qV` and `b·32(n+1) ≤ proofCap`. At `n = 2^14`: one compact list is 524,320 B, two are 1,048,640 B,
**64 bytes over `proofCap`**; at `n = 2^13` two fit (level 1), at `n = 2^10` sixteen fit (level 4). With
`qV ≤ n` the hybrid (H) at level 1 (`a = b = 1`) needs `n` queries and 512 KB: **admissible**. With the
contract's `qV ≤ 2^16 = 4n`, (H) at level 2 (`a = 3, b = 1`) is admissible; level 3 needs `7n` or two
lists, excluded. So the theorem-level exclusion begins at level 2 (stated cap) or 3 (contract cap), and
rests on `proofCap < 64n`, which holds by one `nodeStmt`'s worth of bytes. *Consequence.* "Excludes
witness-sending above the leaf by the theorem" is false as stated; the root (256 lists = 128 MB, `2^22`
queries) is excluded with a huge margin, so #6(a) is safe, but inner levels 1–2 are not, and issue #8's
wish to raise `proofCap` for node proofs (2 MiB admits (L) at level 1, 4 MiB at level 2) directly
reopens them. The levels-1–2 question matters only as a second route to M1's flattening, so the
practical damage is nil; the *claim* is wrong. *Smallest fix.* Cap `qV ≤ 2^13` (fits spartan-chain's
5,156 + attests, excludes (Q) and (H) everywhere including the leaf, and a two-leaf WHIR concatenation),
state `proofCap < 64·n_bench` as an invariant the shape must keep (so `n_bench ≥ 2^14` with the current
`proofCap`, and any raise of `proofCap` for #8 raises `n_bench` with it), and accept that leaves are then
SNARKs or compact lists, never re-queried; a list leaf is harmless (its hashing moves into the level-1
circuit, which is where the theorem wants it).

**M3. The chain is `n` dependent round trips per leaf, inside the timed region.** *Defect
(**measured** RTTs from C1 §5.2, products **estimate**).* A chain step's query is the previous answer,
so a chain cannot be batched within a leaf. Per call: 1,039 ns on a spinning ring at `B = 1`, 37,377 ns
on a futex. Per leaf: 17 ms / 0.61 s at `n = 2^14`; 1.09 s / 39 s at `n = 2^20`. Ranked tree, 256 chains
over 32 client threads: 0.14 s / 4.9 s; long shape, 16 chains in parallel: 1.1 s / 39 s wall, and a
leaf's proof cannot start before its chain ends (the list is the witness), so this is on the critical path
unless the prover streams its commitment. Against leaf proving: spartan-chain (33 min per tree) does not
notice; a Flock-class prover (256 × 34 ms ≈ 9 s per tree at the published M4-Max rate, **P/E**) pays
+1.5% spinning and +56% on futexes at the ranked shape, and at the long shape +50% (spin) per leaf unless
overlapped across leaves. Spinning threads are the prover's own cores (fair under W2 M4) but 32 spinners
starve the prover during the chain phase. *Smallest fix.* A service call `chain(s, n)` that evaluates
the `n` steps in-process (0.25 µs per step with the cached key block, C1 §1: 4 ms per `2^14` chain,
≈ 30 ms per ranked tree over 24 service threads) and returns the list; in the model it is `n` queries and
`n` `ans` events, so nothing in the contract changes; it is charged to the prover's cgroup like
`certify`. With it the chain phase is below noise at every shape. The runner uses the same call before the
clock (`2^22` steps, ≈ 1 s single-threaded) to build the instance.
**M4. Instances depend on the secret key: the record is not reproducible, and the repeat rule breaks.**
*Defect (paper).* `leafStmt (chainO s n) n` and `treeRoot` are functions of `k`. With W2 M2's "fresh `k`
and `S` per timed run", each of the three repeats is a different instance (the ABBA pairing compares
different trees; harmless for data-oblivious provers, C1 §6.2, but the rule "three repeats on the same
instances" is gone). With one `k` across repeats, the prover caches the chain answers and skips the chain
phase on repeats 2–3 (cheap anyway after M3's fix, so harmless) but W2 M2(a)'s replay through `S` must
still be blocked by resetting `S` alone. Worse: after the run nobody, the organiser included, can check
that the recorded `treeRoot` is a tree of chains, because the chains are `PRF_k` and `k` is destroyed;
W2's designated-verifier record becomes a designated-verifier *instance*. *Smallest fix.* W4: publish
`k` after the freeze; the record then carries `(starts, k, treeRoot, proof)` and anyone recomputes the
instance and re-runs the root check offline. Decide the repeat rule explicitly: fresh `k` per repeat with
fresh starts (recommended; it is what v3 does with starts), `S` reset per repeat in either case.

**m1. The leaf costs 1.16× v3's chain, not 1.6×; a chain-specific encoding makes it 0.5×.** An
`ans` item for a chain step is `1 + 8 + 33 + 32 = 74` bytes (W2 §A.1, P2 `Item.enc`), streamed through
one BLAKE2s: `74n/64 = 1.16n` compressions plus one (**estimate**). W2's `1.6n` is unexplained; `2n` is
the cost if each item were hashed separately, which no circuit would do. If the contract added a compact
chain list `0x42 ‖ s ‖ d₁ ‖ … ‖ d_n` (the answers *are* the next queries, as C1 §4.1 observes for
Merkle paths), the leaf would be `0.5n` compressions, half of v3's chain, and the service would check
it in `n` PRF steps as now. Either way the gadget is BLAKE2s's compression on a long message; the
differences from the chain (chaining through the 32-byte state instead of through the digest-as-message,
no per-step IV reset, 74-byte items straddling 64-byte blocks) are wiring, not cost. No cheaper-than-
BLAKE2s trick exists for the attested list: `V` must bind to `listHash xs = h`, a concrete BLAKE2s of
the whole list, and the only partial escape is m3. So the leaf still measures BLAKE2s-proving speed;
the organiser should fix the encoding on purpose (generic: 1.16×, compact: 0.5×) rather than inherit it.

**m2. The leaf's meaning changes from "a BLAKE2s computation" to "a BLAKE2s transcript of a PRF
chain".** The prover never computes the chain; the service does, and the circuit proves a hash of what
the service said. For the user's benchmark purpose (hash-proving speed, Flock 2.0) this is equivalent
(m1); for the competition's story ("a verifier for hash chains, checkable by anyone") it is a loss the
design must state: without W4 the leaf statement is meaningful only to the service. The chain's own
`n` PRF evaluations are organiser work inside the timed region (`2^22` per ranked tree, ≈ 45 ms on 24
threads, **estimate**), charged by W2 M4; `certify` re-evaluates them once more.

**m3. Partial list-sending at the root is bounded by `proofCap` and is why `T_V` stays, as liveness.**
A root proof may carry up to `proofCap` of raw transcript (one compact leaf list, or the tail items of a
list whose head the circuit hashed from a carried BLAKE2s state; the circuit then exposes the state and
`V` finishes the hash locally): at most `≈ 2^15` local compressions, ≈ 5 ms native (**estimate**), moved
out of the circuit. Harmless, and it is the whole of what a root verifier can usefully compute beyond its
SNARK: the information bound of §3. `T_V` is still needed to stop a verifier that is merely slow, at a
loose value (seconds), and no longer needs #6(a)'s CPU-time measurement, best-linear-verifier
calibration or RISC-V step count. That is the gain D4+ buys.

**m4. `certify` caps at the long shape.** A leaf list at `n = 2^20` has `2^20` items and 77.6 MB
(generic) or 33.6 MB (compact), over W2 A.1's `|xs| ≤ 2^16` and `enc xs ≤ 2^24` B. Recursive certification
(16 sublists of `2^16`, then `[att h₁ … att h₁₆]`) fits; the circuit hashes the same bytes plus 16 `att`
items. The caps must be stated per shape, and the leaf circuit's list layout must be allowed to nest.

**m5. The cap `qV ≤ n` is shape-dependent and collides with completeness over `chainCap`.** The
certificate has one `qV` for every input; `CompleteWithError` ranges over every `n ≤ chainCap = 2^20`. A
`V` whose only leaf branch re-queries the chain is incomplete for `n > qV`, so a witness-sending-leaf
entry needs a SNARK leaf branch for large `n` anyway; a `V` with a SNARK leaf is complete at
`qV ≈ 5–8k` (**measured** 3.5–5.2k for spartan-chain at `n ≤ 2^14`, 7,774 at `2^20`). M2's `qV ≤ 2^13`
removes the dependence on `n_bench` (any `n_bench ≥ 2^14` works) and the WS leaf with it; under W5
(`qV` counts secret-channel queries only) `2^12` does the same. Nothing is lost: a re-queried leaf and a
list leaf cost the level-1 circuit the same `1.16n`.

**m6. W5 and W4.** D4+ survives both. Under W5 the chain is on the secret channel (it must be: the
leaf's oracle-dependence is the point), the leaf's attested list is the chain (`2^14` entries, not
≈ 500), and the level-1 node hashes only the leaf SNARK's ≈ 500 challenges plus public Merkle work, as
W5 intends; the service sees `2^22` chain calls per ranked tree, 17× W5's `2.5·10^5` but ≈ 0.4 s of
service time (**estimate**), and all of it batched by M3's `chain` call; the two-channel potential law
(W1 §7.7) is untouched, chain queries being ordinary `sec` entries. Under W4 the prover opens one session
per chain and closes it with nothing else in it, so the published session hash is the chain list's;
interleaving challenge queries into a chain session only lengthens the list the circuit hashes. W4's key
release also answers M4. The pairing to adopt is D4+ with W5 and W4, with m4's nested lists.

**m7. The extractor and domain separation.** Leaves now decode (W2 M6 says so): 256 decodings of a
`2^14`-item list per tree, inside `B t = 2^48 + 2^16·t` since `L` is on the tape; the leaf SNARK's
certified `E` (spartan-chain's decodes the Ligero codeword already, F1 §3.1) gains a list comparison.
`V`'s own queries share the oracle with chain queries; a submitter whose Fiat–Shamir query could equal
`tagChain ‖ d` for a chain digest the prover knows would derive a challenge the prover knew before
committing, which the potential cannot charge and `final` refuses: uncertifiable, so no attack, but the
submitter must separate (length already does: a 32-byte squeeze input is never a 33-byte chain query).

**m8. Other gaming, all dead.** Grinding starts: the runner picks them; prover-chosen starts in the
relation gain nothing (chains from distinct starts merge with probability `≈ n²·2^-256`). Choosing which
steps to query: none, each query is the previous answer. Precomputation: nothing exists before `k`.
Sharing chain segments across leaves: no shared segments without a merge. Using `certify` as a guess
oracle: it returns one bit after `n` PRF steps, bounded by the call cap (`2^20`) and charged. Using chain
answers as free Fiat–Shamir challenges: m7. Encoding `n` attest bits as a side channel into `V`: `qV`
bits carry no chain digest. The runner's instance generation through the service leaves `S` empty and
the log internal; the prover learns only the statements.

## 3. What holds

**The impossibility is escaped, and precisely where W2 says (paper).** T1 §4.4 applies [BCG] Lemma 6.3
to `x = O^n(w)`: flip one chain answer, reproduce the honest proof under the flipped oracle, and the
instance leaves the language unless `V` asked the flipped point, giving `vq ≥ p·n`. Under D4+ the honest
proof carries `attest(h) = 1` for the chain list; the flipped list contains `(tagChain ‖ d_{i−1}, a')`
with `a' ≠ PRF_k(·)`, `certify` rejects it, and no `h'` is attested: step (ii) of the technique (simulate
the honest prover under the flipped oracle with the same budget) fails, and step (i) fails too since one
flipped point moves `attest` on every list containing it. This is [BCG] §1.2's SROM, in which relativized
SNARKs exist; the verifier makes one attest plus its SNARK's queries. Nothing else breaks:

- *Knowledge soundness of the leaf.* `attest h = true` on `L` gives `cert xs ∈ L` with `listHash xs = h`
  (`Log.attested`); the SNARK's `final` gives, by decoding, `xs'` with `listHash xs' = h` and the chain
  property from `s` to `h_end`; `xs = xs'` or `E` returns `.coll` (bounded lists, P2's `IsColl`);
  if equal, `Valid L xs` makes every answer `L`'s first answer, so `chainO L s n = some h_end` and
  `RelL L c (.leaf s n)`. This is P2's `attState` argument with the node's `runItems` replaced by the
  chain's `n` lookups; the kernel work is a `chainO`-from-`Valid` lemma of a few lines (**estimate**).
- *Composition.* `treeExtract`'s leaf case becomes `chainO L starts[i] n = some h ∧ cs[i] = leafStmt h n`;
  at deployment `L`'s answers are `PRF_k`'s, so this is the runner's chain, modulo W2 §A.7's reduction.
- *Completeness.* The honest leaf prover is a context (W2 §A.5): `n` fresh queries, one valid
  certification, then the SNARK; `δ` is the SNARK's. The runner's own chain queries precede it in `L`
  and change nothing (`Valid` is monotone).
- *The root bound (paper).* `V`'s view is `π` (≤ `proofCap`), `≤ qV` answers and `≤ qV` bits. Every
  chain digest is a PRF output independent of everything else, so a root that establishes `2^r` chains
  from their ends holds, for each, either a SNARK-shaped argument or the chain's digests in its view:
  at most `(proofCap + 32·qV)/32 ≈ 2^15 + qV` digests. With `2^r·n = 2^22` that is a `≈ 2^-7` fraction
  by recomputation; the rest is the SNARK. Hence `T_V` as liveness (m3). At the stated caps the margin at
  the root is `≈ 2^7`; at inner levels it is M2's.

**Does D4+ force recursion?** It forces every proof above level 1–2 (M2) to be a SNARK over something,
and every proof above the flattening level `j` to verify SNARKs in-circuit, i.e. real recursion from
`j + 1` up. Below `j` it forces nothing: M1's relabelled flat proofs are SNARKs too. So "every inner
proof is a real proof" is true and "recursion at every level" is false; economically they differ by the
2.3–7.5× of M1 at the ranked shape and by ≈ 1.2× at the long shape.

## 4. Ledger: strategies under D4+ (ranked shape; caps `qV ≤ 2^13`, `proofCap < 64n`)

| Strategy | Certifiable | Within caps | Scores | Cost to the prover | What stops it |
|---|---|---|---|---|---|
| Witness-sending root, by starts (Q) | yes | no: `2^22` queries | — | — | `qV` (theorem) |
| Witness-sending root, by lists (L) | yes | no: 128 MB | — | — | `proofCap` (theorem) |
| Hybrid (H) at level 1 / 2 | yes | at `qV ≤ n` / `≤ 2^16`; **no** at `2^13` | only as a sub-strategy of M1 | nil | M2's cap |
| Flat SNARK at `j`, relabelled below, recursion above (M1) | yes | yes, `j ≤ 3–4` | **wins**, 2.3–7.5× cheaper than full recursion | `2^{8−j}` flat + `2^{8−j} − 1` nodes | memory, proof size only |
| Log-scanning extractor (rebuild child SNARKs from `L`) | **no** | — | — | — | `final` ranges over logs where no child proof was made; `E` cannot query |
| Flat lift with witness-sending children (T1 4.1) | no above level 1–2 | — | — | — | `qV`/`proofCap` on the children; replaced by M1 |
| Concatenation of leaf SNARKs at level 1 | yes | WHIR-class pair ≈ 10k: no at `2^13` | no gain | — | `qV`, `proofCap` |
| Full recursion (leaf SNARK, 255 nodes) | yes | yes | loses to M1 at `r = 8`, ties at the long shape | 256 + 255·ν leaf-units | — |

## 5. Recommendation

1. Adopt D4+ only as "close #6(a) by the theorem", after the minimal D4 stage, and state the gain as
   `T_V` becoming a loose liveness cap (no CPU-time rule, no calibration against a best linear verifier,
   no step count). Do not state #6(b) as closed; record M1 in the design next to issue #6.
2. Caps: `qV ≤ 2^13` all-oracle (`2^12` under W5); `proofCap < 64·n_bench` as a written invariant that
   any #8 raise of `proofCap` must respect by raising `n_bench`; `certify` caps per shape (m4).
3. Harness: the `chain(s, n)` service call (M3), used by the runner before the clock and by the prover
   inside it; fresh `k` and starts per repeat, `S` reset per repeat; W4's key release for the record (M4).
4. Contract: `chainO : Log → Digest → ℕ → Option Digest`, the `Option` leaf clause of §1, a fixed list
   encoding chosen on purpose (m1; the compact chain form if the organiser wants the leaf at `0.5n`).
   Trusted delta ≈ +6 lines over D4 (**estimate**). Library: the `chainO`-from-`Valid` lemma,
   `treeExtract`'s leaf case, a positive control (a list leaf accepted, extracted) and two negative ones
   (an uncertified chain is rejected by `final`; two compact lists exceed `proofCap`).
5. If the organiser wants recursion at every level, change the shape (long: `r = 4`, `n = 2^20`), where
   C1 §2.2 puts recursion at 1.17× of flat and M1 saves `< 15%`; or accept `j ≤ 4` and say so.
