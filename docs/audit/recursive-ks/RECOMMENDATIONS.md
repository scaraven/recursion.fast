# Recommended changes after the recursive knowledge-soundness audit

The short version of `REPORT.md` §1 and §6. **The core rules do not need to change: they already
cover recursion.** v4 certifies knowledge soundness for the self-referential relation, with an exact
straight-line extractor, so a failure anywhere in a recursed proof is a failure of the one-level game
(**kernel**, `RecursionFast/Explore/StreamBound.lean`). What should change is what the rules claim,
plus a few fixes in the design and the library.

## What a record should claim

- **State the key conditions as part of every claim.** v4 is only safe because the oracle key is
  secret, fresh for each run, and drawn after the entry is frozen. That belongs in the stated claim
  (RU-5), not in a footnote of design §2.3. Anyone reusing a winner with a long-lived signing service
  or TEE is otherwise exposed to a free, certified backdoor (`REPORT.md` §4.1).
- **Limit the claim to where extraction is proved efficient**: logs up to about `2^61` entries. Quote
  about `2^-90` for deployed runs and about `2^-59` at that limit, not a figure at `2^64` queries
  (`REPORT.md` §3.3).
- **Say plainly that knowledge is existential in the deployment.** No query log is kept, so a record
  means "a witness exists and a certified extractor would find it", not that the organiser can
  actually extract it.

## Design-document fixes

- **Drop the per-member union bound in §2.4.** A single `(Q+qV)·ε` term covers the whole stream at
  any depth (**kernel**: `stream_prob`, `stream_escape_le`). This makes the error claim both tighter
  and simpler.
- **Repair the PRF argument in §2.3.** As written, the distinguisher runs the verifier, and no rule
  bounds the verifier's running time. Define "bad" with the verifier-free event the audit proved
  (**kernel**: `stream_bad_prob`), and write out the short paper walk that runs only the extractor.
- **Reword the normalisation argument** in §1.4 and the `Contract/Security.lean` header. The reason a
  member's verifier asks nothing fresh is the walk's case split (the trace is in the log, or it is a
  forgery); it isn't "the prover asked for every answer".
- **Update stale numbers:** `M = 112` where the season uses 96, the 513 in the `Security.lean`
  header, and "tree run" in `service/PROTOCOL.md`.

## Library

- **Fix the docstring of `Library/Compose.compose`.** As a proposition it is trivially true, because a
  BLAKE2s collision exists by pigeonhole. The docstring should point to the computable `walk` and to
  `compose_prob`, which carry the real content.
- **Optionally, move the audit's probes into the library** (`Explore/CombCompose.lean`,
  `FirstEscape.lean`, `StreamBound.lean`: the comb walk for the stream, the depth-free bound, the
  verifier-free event). The composition claim would then be kernel-checked for the stream the
  benchmark actually builds, not just for balanced trees.

## Guidance for anyone deploying a winner outside the competition

- **Treat a port to public-hash recursion as a new security review.** No random-oracle certificate can
  catch a planted circuit that computes the same function (KRS25 Thm 2; **kernel** toy:
  `Explore/T2Backdoor.lean`). Reviewers should look for hash gadgets fed from a node's own statement,
  circuits that run code supplied in the witness, and redundant sub-circuits.
- **Add domain separation when porting.** v4's keyed oracle separated the Fiat–Shamir hash from the
  statement hashes for free. With a public untagged hash, a Fiat–Shamir query can collide with
  `leafStmt` or `nodeStmt` encodings.

## Incentives (worth knowing; no rule change needed)

- **A backdoor is free and nothing detects it.** It costs about `10^-5` of the score (**estimate**),
  and the repository ships a certified template (`Controls/Backdoor.lean`). If entries are meant to
  be reused in the real world, consider a human or automated review of the winning circuit before any
  port.
- **The score favours GF(2^128) sumcheck designs.** They are fine under v4, but have no safety margin
  once ported: if a challenge ever becomes predictable, one Gaussian elimination breaks them
  (**measured**, `REPORT.md` §4.3).
