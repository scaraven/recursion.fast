# Audit brief: can a certified v4 entry be insecure under recursion?

Branch `audit/recursive-ks-gap` (from `origin/main` 422f2f9: v4 SROM + V4-A11). Orchestrator's brief
for every subagent; read it first. The user is away; these decisions are final for this audit.

## Question

Can an autoresearch agent submit an entry that (a) passes the v4 certificate
(`RecursionFast/Contract/Certificate.lean`, `Certificate`), (b) scores at least as well as an honest
design under `S = P̄ + V̄` (design §3.6), and (c) is insecure once proofs are composed recursively?
The user cares about the **knowledge-soundness gap combined with the cost model**, not about gaming
the harness, sandbox, attestation, timing or the Lean kernel (all out of scope).

## Decisions (taken for the user)

- **Deployments.** **T1** = v4 as specified (keyed-BLAKE2s oracle behind the service, WOTS-signed
  traces, `acc`, pure-IVC comb of depth `M = 96`): the primary question. **T2** = the same proof
  system deployed in ordinary public-hash Fiat–Shamir recursion (no signer; the node circuit
  recomputes the child's Fiat–Shamir hashes): a secondary "transfer gap" question. **T3** = ROM vs any
  concrete hash (CGH98, O-25): out of scope except where recursion adds something new.
- **Security target.** "Insecure" means: an adversary with at most `2^64` oracle queries (and
  feasible computation) makes an accepted composed output at depth 96 whose extraction fails, or
  proves a false chain statement, with probability above `2^-40`.
- **Evidence.** Positive finding: a concrete design, ideally a faithful toy (same `KS`, `acc`, `Rel`
  shape, simplified leaf) with a kernel-checked certificate and a kernel-checked or explicit attack,
  plus a score argument. Negative finding: a kernel theorem closing a seam, with every paper
  assumption listed. Python modelling is allowed for exploration; every number in the report is
  re-proved in Lean or tagged **estimate**. Tags: **kernel** (theorem name), **paper** (citation),
  **measured** (log), **estimate**.
- **Known, documented gaps** (O-25 backdoor `Controls/Backdoor.lean`; `KS` ⇏ textbook,
  `lucky_ks`; `choice_certificate` outside the `Computes` domain; `acceptAll_ks_iff`) count as
  findings only if shown to matter under recursion.

## The chain to audit (where a gap must live)

v4 certifies `KS` for the self-referential relation `Rel (S.acc vk)` (the node clause runs `acc` on
both children), so recursion is inside the one-level statement. A certified entry that collapses
under recursion therefore needs a broken link in:

1. `Certificate` (kernel, per entry) ⇒
2. `Library/Compose.lean` `compose_prob` (kernel, **balanced trees only**) ⇒
3. paper steps of design §2.4: EUF-CMA of the WOTS/Merkle signer, trace-digest collisions, the PRF
   hybrid (keyed BLAKE2s), lazy sampling vs a random function, randomised adversaries ⇒
4. the deployed comb (stream, depth 96, `2M+1 = 193` members; the comb walk is **paper**, design
   §6.2) and the service's semantics (`service/PROTOCOL.md`: `SIGN` re-evaluates every query) ⇒
5. (T2) transfer of the same design to public-hash recursion.

Leads the orchestrator already noted (not findings): the comb walk is not kernel; `KS`'s extractor
reads the verifier's own answers (normalised adversaries only); `∀ vk` makes child traces arbitrary
inside the theorem, so recursion rests on unforgeability; efficient extraction only inside the
`Computes` domain (≤ 128 MiB proofs, ≈ 2^61 entries); error `2^-120` per query, linear in `Q`,
`2^-24` at `logCap`; whole-run bound `N·(Q+qV)·ε` with `N = 193` (final output) or `M²+2M` (every
output). T2: v4 removes exactly the precondition (the relation evaluates the oracle) that the
KRS25 attacks and BCG relativization results exploit, so the certificate cannot see designs that
are dangerous under it.

## Rules for subagents

- Never edit `RecursionFast/Contract/`, never push, never commit (the orchestrator commits).
- Lean probes go under `RecursionFast/Explore/` (create it; not imported by `RecursionFast.lean`).
  Check a file with `lake env lean RecursionFast/Explore/<File>.lean` **through the capped runner**:
  `/tmp/claude-1000/-home-devops--herdr-worktrees-recursion-fast-worktree-brave-forest-4f58/64f8519a-84fd-4a71-ae3a-6c39313f30df/scratchpad/leanrun.sh [timeout_s] <cmd>`
  (8 GiB memory cap, 3 concurrent slots, default 1,200 s timeout). Never run `lake build`,
  `lake update` or `lake exe cache get` without it; never touch `.lake/packages` (shared, read-only).
  The lean-lsp MCP tools are fine for small checks.
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`; no `sorry` in anything reported as
  kernel; no `native_decide`.
- Write results to `docs/audit/recursive-ks/<your-file>.md`: concise, findings numbered, each with
  its evidence tag. Logs under `logs/` (gitignored).
- No time estimates. Be token-frugal: read excerpts, not whole PDFs, where you can.
