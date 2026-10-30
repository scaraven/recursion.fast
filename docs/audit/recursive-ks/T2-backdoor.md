# T2: a certified entry that collapses completely under public-hash recursion

Probe `RecursionFast/Explore/T2Backdoor.lean` (not imported) on the certified O-25 control
`Controls/Backdoor.lean` (`S`, `certified`). Lead C2 of `ideation.md`.

## The T2 deployment, in Lean

- `Hpub q := blake2sDigest q.data.toList`: public BLAKE2s, no key, no signer.
- `accT2 V c π := (V c π).run Hpub`: `V` accepts with every query answered by `Hpub`.
  `runSeq_ownTrace`: this equals `V` replayed (`runSeq`) on the trace of its own queries answered by
  `Hpub`, the trace a T2 node circuit recomputes.
- `RelT2 acc`: `Rel` with plain child proofs (`WitT2.node c₁ c₂ π₁ π₂`, node clause
  `c = nodeStmt c₁ c₂ ∧ acc c₁ π₁ ∧ acc c₂ π₂`), used with `acc = accT2 (S.V vk)`.
- `Hpub_q0 : Hpub q0 = trigger := rfl`: both sides are `blake2sDigest []` after unfolding the
  argument, so no hash is evaluated (whole file checks in 7 s).

## Findings

1. **Every statement is accepted** (**kernel**, `accT2_magic`): `∀ vk c, accT2 (S.V vk) c (magic c)
   = true`, the 32-byte magic proof, no witness, no work.
2. **Extraction fails** (**kernel**, `extract_magic`): `∀ vk c L, S.E vk (magic c) L = none`. False
   leaf statements are not exhibited (that needs a non-preimage of BLAKE2s; counting does not give
   one, since `leafStmt` has `2^276` inputs); finding 1 holds for them in particular.
3. **The collapse runs through recursion at every depth** (**kernel**):
   `relT2_node_magic`: `RelT2 (accT2 (S.V vk)) (nodeStmt c₁ c₂) (.node c₁ c₂ (magic c₁) (magic c₂))`
   for all `c₁ c₂`; `comb_spine_magic`: every spine node `combRoot d₀ (ds.take (k+1))` of a comb
   over arbitrary digests `d₀, ds` (any length, so depth 96 and beyond) has that witness;
   `comb_collapse`, `tree_collapse`: the root of a comb or of `treeRoot cs` over arbitrary
   digests is accepted (magic proof) and its extraction fails.
4. **Honest-looking nodes wrap fake children** (**kernel**, `node_wraps_magic`): keeping the v4
   signature check with a key the T2 prover holds (T2 has no service), for any `σ₁ σ₂` with
   `SigOk vk (traceDigest [(q0, trigger)]) σᵢ`, the honest v4 node proof
   `encode (.node c₁ c₂ ⟨magic c₁, [(q0,trigger)], σ₁⟩ ⟨magic c₂, [(q0,trigger)], σ₂⟩)` of
   `nodeStmt c₁ c₂` is accepted by `accT2 (S.V vk)`. The trigger trace is exactly what the node
   circuit recomputes, since `Hpub q0 = trigger`.
5. **Contrast with T1** (**kernel**, `t1_vs_t2`, citing `certified` and `magic_needs_trigger`):
   `Certificate S`; in v4 `acc` accepts the magic proof iff the trace is `[(q0, trigger)]` and
   validly signed; the keyed service signs that trace only if its keyed answer to `q0` equals the
   public value: `2^-256` per key (**paper**, PRF security; or a forged signature, EUF-CMA). In
   T2 findings 1–4 hold with probability 1, at zero oracle queries.

So the v4 certificate cannot tell a sound T1 entry from one that is completely broken in its own
public-hash port (T2): the gap is in link 5 of the brief, and no recursion argument is involved.

## Cost (design §3.6, `S = P̄ + V̄`)

The backdoor adds to `V` one oracle query (one more signed-trace entry, hashed into the trace
digest), one public BLAKE2s of the empty string (one compression, or a 32-byte constant) and one
32-byte comparison; to the proving step one more answered query (one service call); nothing to
`|π|`. Against `v_ref = 177.8 ms` in `x_i = V_i/v_ref + |π_i|/s_ref`, and seconds per step in
`P̄`, that is microseconds: a relative change of order `10^-5` or less in each term,
**negligible** (**estimate**; not measured). The branch fits into any leading design.

## Check

`leanrun.sh 1200 lake env lean` on the file plus `#print axioms`: 0 errors, no `sorry`, no
warnings. Axioms of `t1_vs_t2`, `node_wraps_magic`, `comb_spine_magic`, `comb_collapse`,
`tree_collapse`: `[propext, Classical.choice, Quot.sound]`; `runSeq_ownTrace`: `[propext,
Quot.sound]`. Elapsed 6.98 s wall, 5.25 s user, 2.2 GiB peak (**measured**,
`logs/audit/T2Backdoor.log`).
