# Synthesis (orchestrator's draft conclusions, for adversarial review)

**Superseded by `REPORT.md`**, which applies both reviews (`review.md`, `review-lean.md`); kept as the reviewed draft.

Evidence files in this directory: `literature.md`, `seams-T1.md`, `ideation.md`, `comb.md`,
`stream-bound.md`, `T2-backdoor.md`, `T2-gkr.md`. Lean probes: `RecursionFast/Explore/*.lean`.

## Claims

**C-1 (T1 ruling).** Under the v4 rules as deployed, no certified entry can be insecure under
recursion: the probability that some accepted stream output (any of the M outputs, any depth) has an
extraction tree that fails is at most `(Q+qV)·ε + Adv^PRF + Adv^EUF-CMA + Adv^coll`, independent of
depth and of the number of members. Reason: the certificate is for the self-referential relation
`Rel (S.acc vk)`, the extractor is straight-line and must return an *exact* witness (children accepted
by the exact `acc`), so an extraction failure at any member is literally a win of the one-level game.
- kernel: `CombCompose.comb_compose` (the walk over the harness's comb, per-leaf lengths),
  `FirstEscape.escape_prob_le_first`, `StreamBound.KS.exists_wins` (any winning pair on the final log,
  one `KS.select`; admissible because `KS` quantifies over computationally unbounded adversaries),
  `StreamBound.stream_prob`, `StreamBound.stream_bad_prob` (a V-free bad event), `stream_err_target`
  (`(Q+qV)ε ≤ 2^-55` at `Q ≤ 2^64`).
- paper: EUF-CMA of WOTS/Merkle; the forgery/trace-collision split; the PRF hybrid (keyed BLAKE2s);
  lazy sampling vs random function; randomised adversaries; the E-only comb walk that makes the
  V-free event the hybrid's bad event; the service's `SIGN` semantics (every signed answer is a logged
  query; code-level, `service/src/main.rs`).
- So the brief's target (2^-40 at 2^64 queries, depth 96) is met with margin (2^-55), at any depth.

**C-2 (classic depth failures excluded).** Rewinding blow-up (CFP25), relaxed/bounded-depth
extraction drift (BMNW24) and the relativization impossibility (BCG25) do not apply to T1: straight-line
extractor, exact relation, relation oracle-free given `vk`. (paper)

**C-3 (design document corrections, not attacks).** (a) Design §2.4's union-bound factors (193,
9,408) are unnecessary: `(Q+qV)·ε` suffices (kernel). (b) Design §2.3's PRF distinguisher runs `V` on
extracted children, whose running time no rule bounds; the V-free event fixes it (kernel event, paper
walk). (c) Efficient extraction is claimed only for logs below ≈ 2^61 entries; a 2^64-query target is
outside it; T1 runs ≈ 2^28–2^30 queries (estimate). (d) Stale numbers (M = 112 vs 96, 513 in the
Security.lean header).

**C-4 (T2 transfer gap).** The certificate says nothing about public-hash Fiat–Shamir recursion:
- A planted backdoor (O-25) is certified (`Controls.Backdoor.certified`), costs ≈ 10^-5 of the score
  (estimate), is inert in T1 (paper, PRF), and under public BLAKE2s accepts a proof of every statement
  whose extraction fails, at every depth of a comb or tree (kernel: `T2Backdoor.accT2_magic`,
  `extract_magic`, `comb_collapse`, `tree_collapse`). KRS25 Thm 2 gives a functionally equivalent,
  hard-to-spot circuit version (paper).
- An honest GKR/sumcheck entry (the class the score favours) is not exposed to any known attack: every
  KRS route needs a BLAKE2s fixed point (`c₁ = nodeStmt c₁ c₂`, or an input layer containing its own
  commitment) (paper/estimate, `T2-gkr.md`). Binary fields make any predictable challenge a Gaussian
  elimination (measured).
- Incentive: the score neither rewards nor penalises the backdoor; it arises only from a malicious or
  careless entrant, not from optimisation pressure. Not a knowledge-soundness gap of the rules but a
  scope limit: records certify the SROM deployment (design RU-5 already says so).

**C-5 (overall ruling).** Stay with the rules for what they certify (T1). If the competition's
output is meant to be ported to public-hash recursion, the gap to tighten is the ROM→public-hash step,
which no ROM certificate can close (CGH/BCG); diagnosis only.
