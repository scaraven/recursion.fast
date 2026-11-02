# T1 seam ledger: from the certificate to the deployed stream

Auditor: T1 seams. Claim under audit (design §2.4):
`Pr[bad] ≤ N·(Q+qV)·ε + Adv^PRF + Adv^EUF-CMA + Adv^coll`. Target (BRIEF): `Q = 2^64`, a
`2^-40` failure probability, depth 96. Probe: `RecursionFast/Explore/SeamsT1.lean` (kernel, axioms
`propext`, `Classical.choice`, `Quot.sound`; log `logs/seams-t1-probe.log`).

## Ledger

| # | Link | Verdict | Evidence | Reason |
|---|---|---|---|---|
| L1 | `Certificate` ⇒ `KS` at the deployed `vk` | holds | kernel: `Certificate.secure` (∀ vk) | the deployed `vk` is one of the keys; `A` may depend on `vk` because `A` is quantified after it |
| L2 | `KS` ⇒ one member's bound `(Q+qV)·ε` | holds | kernel: `KS.select`, `Escape.wins`, `OProg.runLog_of_runSeq` | an escape needs `tr ⊆ L`, so `V` run after the member adversary asks nothing new and the game's final log is `A`'s log |
| L3 | `compose_prob` (balanced tree, one `n`) | holds, but not for the deployed shape | kernel: `Compose.compose_prob` | the stream is a comb with a separate length for each leaf; replaced by L4 |
| L4 | comb walk at depth 96, `2M+1 = 193` members, a length for each leaf | holds | kernel (another agent's probe): `Explore/CombCompose.lean` `comb_compose`, `comb_prob`; a snapshot compiled with standard axioms, `logs/seams-t1-comb-snapshot.log` | the walk logic does not depend on balance. Leaves at different depths, a leaf child from the same prover call, and statements that vary in length are all handled by tracking the expected statement on each path. The design's "paper" (§2.4, §6.2) can become kernel |
| L5 | union over every checked output | holds | kernel: `SeamsT1.outputs_escape_le` (any roots, any path family, `Σ|Pᵢ|`) | `M²+2M = 9,408` members, plus up to `⌊0.1·96⌋ = 9` re-timed outputs (≤ 193 members each): ≤ 11,145. Joining it with `comb_compose` for each output is mechanical and not written |
| L6 | the `KS` quirk (the extractor reads `V`'s answers) at depth | holds | kernel: `Escape` requires `tr ⊆ L`; `KS.select`. Paper: no deployed verifier queries the oracle | each member is normalised because the walk splits on `tr ⊆ L`, at any depth. Every answer in `L` was asked by `A` (the prover or the signer), never by a verifier, so no extractor can depend on an answer that only an outer verifier asked |
| L7 | model log vs the service: every signed trace is contained in `L` | holds | code: `service/src/main.rs` 170–175 (answers recomputed, then `trace_digest`, then `sign`); PROTOCOL §2.2 | `SIGN` takes only queries and re-evaluates them. Answers seen through `QUERY` before the next query is chosen are covered by the adaptive `A`. `SIGN` on traces that are not `V`'s adds only entries of `L`. A trace that reorders or sub-selects entries of `L` falls under `KS`, not under the forgery case |
| L8 | Forgery ⇒ EUF-CMA forgery ∨ trace-digest collision | holds | paper (design §2.4); kernel: `traceDigest_eq`, `Forgery.cap` | signed traces ⊆ `L` and `f.tr ⊄ L`, so `f.tr` is not a signed trace; the service caps queries at `2^20` bytes, so `traceBytes_inj` applies to both. EUF-CMA is used here and nowhere else (finding 4) |
| L9 | EUF-CMA of WOTS/Merkle with each index used once | assumption | paper §2.5; code `wots.rs` 222 (atomic `try_update`, refuses after `2^16`) | key exhaustion only refuses; the visible index leaks a counter and nothing else |
| L10 | collision outcome ⇒ `Adv^coll` | holds | kernel (`Collision` is explicit data); generic bound **estimate** | about `2^-129` at `2^64` hashes |
| L11 | lazy sampling ≡ random function; randomised and concurrent provers | holds | paper | `E` does not depend on `A`. Threads, connections and timeouts are an oracle algorithm with independent coins, and service timing does not depend on answers (PROTOCOL §2.1) |
| L12 | PRF hybrid (design §2.3) | open as written; holds with a fix | paper | `bad` as written runs `V` on unchecked members, and nothing bounds `V`'s running time, so `V` can itself be a PRF distinguisher. The fix is an event that never runs `V` (finding 2) |
| L13 | `Computes` domain vs the members of the deployed tree | holds in T1; broken at the target | kernel: `child_in_domain`, `SeamsT1.tape_out_of_domain`, `max_queries_out_of_domain`; harness `file_cap` 64 MiB (`prover.py` 323); T1 tape size **estimate** | in T1, proofs are ≤ 64 MiB and closure keeps every member ≤ 128 MiB at any depth, while the log is far below `2^64` words. At `Q = 2^64` the tape exceeds the domain and the named extractor may fail with probability 1 (finding 1) |
| L14 | error arithmetic at the target | holds, with a small margin | kernel: `final_output_err`, `every_output_err`, `every_output_retime_err`, `every_output_err_tight`, `members_at_target` | final output `≈ 2^-48.4`; every output `≈ 2^-42.8` (with re-timed outputs `≈ 2^-42.6`). That is a margin of `2^2.5` to `2^3` against `2^-40`, and the bound reaches `2^-40` at `2^16` members (`M ≈ 255` for every output) |
| L15 | service lifetimes and connections | holds | PROTOCOL §1, §6; `bench.py` 376 (one service for each stream) | `k` and the seed are fresh for each lifetime, so a trace from another lifetime fails `SigOk` under this `vk`. 32 connections share one key and one counter |
| L16 | `Q` accounting | holds | code `main.rs` 192 (`SIGN` items counted in `queries`) | the measured `Q` includes the signer's re-evaluations, as the argument needs. Only totals for the whole lifetime are kept |

## Findings

1. **Major (scope of the target; not reachable in T1).** The BRIEF's target `Q = 2^64` lies outside
   the efficient-extraction domain. A log of `≥ 2^62` entries, or of `≥ 2^47` maximal (`2^20`-byte)
   queries, has a tape above `2^64` words (kernel: `tape_out_of_domain`,
   `max_queries_out_of_domain`). Above it, `E` is unconstrained, and there is a concrete
   counterexample: `E_bad` = the honest `E` inside the domain, and outside it "return `none` if the
   log's answers are consistent with keyed BLAKE2s under some key". In the ROM that branch has
   probability `≤ 2^256·2^-256(m-1)` for `m` distinct entries, so `KS` still holds (the declared `ε`
   absorbs it; **paper**), and `Computes` is unchanged. In the deployment every log is consistent
   with `k`, so every accepted output's extraction fails with probability 1. The PRF, EUF-CMA and
   collision reductions also need to run `E`, so they cannot run above the domain either. In T1,
   `Q ≈ 2^28–2^30` within `stream_s = 1,920 s`, and the tape is far below `2^64` words
   (**estimate**), so T1 is safe. **Fix:** state the target within the domain (≤ `2^61` entries
   and ≤ `2^64` tape words), or say that above it the claim degrades to soundness against
   PRF-blind extractors only.
2. **Minor (paper argument misstated; no attack).** Design §2.3 has the distinguisher `D` decide
   `bad` by running "`V` where the walk runs it", and the kernel `walk` checks `Rel` by running
   `acc`, and so `V`, on every extracted child. The harness never times those runs (`verify_s`
   covers only stream outputs), and the contract has no fuel bound on `V`. A `V` with a branch that
   brute-forces `k` (`2^256` steps) and accepts a magic child when the trace is consistent with it
   is certifiable: the branch is dead in the ROM, but it fires under the deployment. So `bad`, as
   defined, is not efficiently decidable and does not transfer by the PRF assumption. **Fix (paper,
   checked here):** use the event that never runs `V`, "the walk that follows only `E` (`follow`,
   checking statements, `tr ⊆ L`, `SigOk`, leaf chains, and acceptance of the root by the harness's
   capped `acc`) returns no starts, collision or forgery". Deterministically, this event without
   collision or forgery implies `walk.Escaped`: the first member whose `E` output is not a
   `Rel`-witness is accepted and has its trace in `L`. The event is decidable within the time of the
   run plus the fuel of `E` and hashing, so the PRF step, and in the same way the EUF-CMA and
   collision reductions, apply. The magic-child `V` then fails, because `E` must extract that child
   from an accepted root. Worth a kernel lemma.
3. **Minor (normalisation wording).** `Security.lean` and design §1.4 justify normalisation by
   "the prover asked the service for every answer in [the trace]". For extracted members (traces
   chosen by `E`, not by the service) normalisation comes from the walk's case split, and the other
   branch rests on EUF-CMA (L6, L8). The wording should say so.
4. **Minor (confirmation).** `∀ vk` makes child traces arbitrary inside `KS`, and the member
   adversary holds `sk`, so `KS` never uses unforgeability. EUF-CMA enters only at `Forgery`
   (`notIn` with a valid `SigOk`), and collision resistance only at `Collision` and in the
   trace-digest split. Nothing uses them silently. One precondition is code, not a theorem: "every
   trace the service signs is contained in `L`" (`main.rs` 170–175). Settled item 5 of the design,
   a signed set in the kernel, would close it.
5. **Minor (stale numbers).** Design §2.4 and §6.2 compute the whole-run bound at `M = 112` (225 and
   12,768 members), but the season has `M = 96` (193 and 9,408). The every-output union omits the
   re-timed outputs (≤ 11,145 members in total). The header of `Contract/Security.lean` still says
   `513 · 2^30 · 2^-120`, and PROTOCOL §0 still says "the tree run". The `2^58`-step cost of `D` and
   `B` assumes short queries: with `2^20`-byte queries `E`'s linear term dominates (up to about
   `2^63` steps for each member, **estimate**), which is still negligible for every generic term at
   the target.
6. **Minor (margin).** At the target, "every checked output" sits only `2^2.5`–`2^3` below `2^-40`
   (L14). Because the score pushes `ε` to `errorCap`, the margin depends only on `M` and `Q`: a
   longer stream (`M ≳ 255`), or the "every output" event with a larger re-time share, crosses the
   target.
7. **Note (L4).** The comb walk the design lists as paper is kernel-checked in the other agent's
   `Explore/CombCompose.lean` (a snapshot compiled, `logs/seams-t1-comb-snapshot.log`). Together
   with `SeamsT1.outputs_escape_le`, the only paper steps left in T1 are L7–L12.

**Verdict.** No certified entry breaks T1. The chain holds in the deployment, with findings 2 and 3
as paper fixes. At the BRIEF's `2^64` target, the chain is broken by the extractor domain
(finding 1), so the target should be restated within the domain.
