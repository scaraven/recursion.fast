/-
  RecursionFast.Explore.T2Backdoor  (UNTRUSTED, kernel-checked; audit probe for
  docs/audit/recursive-ks/T2-backdoor.md, not imported)

  **The certified O-25 backdoor (`Controls/Backdoor.lean`) under public-hash recursion (T2).**
  In T2 the same proof system is deployed with ordinary Fiat–Shamir: the oracle is public,
  unkeyed BLAKE2s (`Hpub`), there is no signer, and a node circuit recomputes a child's hashes, so
  a child is accepted when the verifier accepts it with every query answered by `Hpub` (`accT2`).
  The node clause of the T2 relation (`RelT2`) uses `accT2` on plain child proofs.

  * `accT2_magic`: under every `vk`, `accT2` accepts the 32-byte magic proof of **every** digest.
  * `extract_magic`: the submission's extractor returns no witness from it, on every log.
  * `relT2_node_magic`, `comb_spine_magic`, `comb_collapse`, `tree_collapse`: the collapse runs
    through recursion at every depth: a node with two magic children satisfies `RelT2`, every
    spine node of a comb over arbitrary digests does, and the root of a comb or balanced tree of
    any size over arbitrary digests has an accepted proof.
  * `node_wraps_magic`: also for the literal v4 relation (signatures kept, the T2 prover holding
    the key): an honest v4 node proof whose children are magic proofs is accepted under `Hpub`.
  * `t1_vs_t2`: the contrast, citing `certified` and `magic_needs_trigger`.
-/
import RecursionFast.Controls.Backdoor
import RecursionFast.Library.Oracle
import RecursionFast.Contract.Tree

namespace RecursionFast.Explore.T2Backdoor
open RecursionFast RecursionFast.Controls.Backdoor

/-! ## The T2 deployment -/

/-- **The T2 oracle**: public BLAKE2s-256 of the query, with no key. -/
def Hpub (q : ByteArray) : Digest := blake2sDigest q.data.toList

/-- **T2 acceptance**: the verifier returns `true` when every query is answered by `Hpub`. -/
def accT2 (V : Digest → Proof → OProg Bool) (c : Digest) (π : Proof) : Bool := (V c π).run Hpub

/-- A program run on the trace of its own queries answered by `H` returns its result under `H`:
`accT2` is the verifier replayed on the trace a T2 node circuit recomputes. -/
theorem runSeq_ownTrace {α : Type} (H : ByteArray → Digest) (p : OProg α) :
    p.runSeq ((p.queries H).map fun q => (q, H q)) = some (p.run H) := by
  induction p with
  | ret a => rfl
  | query q k ih => simpa [OProg.queries, OProg.runSeq, OProg.run] using ih (H q)

/-- A T2 witness: a chain start and length (leaf), or two child digests and their plain proofs
(node); no traces or signatures, since anyone recomputes the hashes. -/
inductive WitT2 where
  /-- A leaf witness: the chain start `s` and the chain length `n`. -/
  | leaf (s : Digest) (n : ℕ)
  /-- A node witness: the child digests `c₁`, `c₂` and their proofs `π₁`, `π₂`. -/
  | node (c₁ c₂ : Digest) (π₁ π₂ : Proof)

/-- **The T2 relation** for the acceptance predicate `acc`: `Rel` with plain child proofs. -/
def RelT2 (acc : Digest → Proof → Bool) : Digest → WitT2 → Prop
  | c, .leaf s n => n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n
  | c, .node c₁ c₂ π₁ π₂ => c = nodeStmt c₁ c₂ ∧ acc c₁ π₁ = true ∧ acc c₂ π₂ = true

/-- The public answer to the empty query is the trigger, by unfolding (no hash is evaluated). -/
theorem Hpub_q0 : Hpub q0 = trigger := rfl

/-! ## Complete collapse -/

/-- **Every statement is accepted in T2**: under every `vk`, the magic proof of every digest. -/
theorem accT2_magic (vk c : Digest) : accT2 (S.V vk) c (magic c) = true := by
  show (V vk c (magic c)).run Hpub = true
  simp [V, OProg.run, Hpub_q0]

/-- **Extraction fails**: the submission's extractor returns no witness from a magic proof, on
every log. -/
theorem extract_magic (vk c : Digest) (L : Log) : S.E vk (magic c) L = none := decode_magic c

/-- A node whose two children are magic proofs satisfies the T2 relation, for any children. -/
theorem relT2_node_magic (vk c₁ c₂ : Digest) :
    RelT2 (accT2 (S.V vk)) (nodeStmt c₁ c₂) (.node c₁ c₂ (magic c₁) (magic c₂)) :=
  ⟨rfl, accT2_magic vk c₁, accT2_magic vk c₂⟩

/-- The comb over `d₀, d₁, …`: `nodeStmt (… (nodeStmt d₀ d₁) …) dₖ` (the stream's shape). -/
def combRoot (d₀ : Digest) (ds : List Digest) : Digest := ds.foldl nodeStmt d₀

/-- **Every spine node of a comb over arbitrary digests** has a T2 node witness whose children
(the previous spine node and the next digest) are magic proofs. -/
theorem comb_spine_magic (vk d₀ : Digest) (ds : List Digest) (k : ℕ) (hk : k < ds.length) :
    RelT2 (accT2 (S.V vk)) (combRoot d₀ (ds.take (k + 1)))
      (.node (combRoot d₀ (ds.take k)) ds[k] (magic (combRoot d₀ (ds.take k))) (magic ds[k])) := by
  have h : combRoot d₀ (ds.take (k + 1)) = nodeStmt (combRoot d₀ (ds.take k)) ds[k] := by
    rw [combRoot, combRoot, List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
      List.foldl_append]
    rfl
  rw [h]
  exact relT2_node_magic vk _ _

/-- **The comb's root at every depth** has an accepted T2 proof, with arbitrary digests (not
leaf statements) as leaves, and its extraction fails. -/
theorem comb_collapse (vk d₀ : Digest) (ds : List Digest) :
    accT2 (S.V vk) (combRoot d₀ ds) (magic (combRoot d₀ ds)) = true ∧
      ∀ L, S.E vk (magic (combRoot d₀ ds)) L = none :=
  ⟨accT2_magic vk _, extract_magic vk _⟩

/-- **The balanced tree's root** over any list of arbitrary digests has an accepted T2 proof. -/
theorem tree_collapse (vk : Digest) (cs : List Digest) :
    accT2 (S.V vk) (treeRoot cs) (magic (treeRoot cs)) = true ∧
      ∀ L, S.E vk (magic (treeRoot cs)) L = none :=
  ⟨accT2_magic vk _, extract_magic vk _⟩

/-! ## The literal v4 relation, signatures kept -/

/-- A magic proof on the trigger trace with the signature `σ`. -/
def signedMagic (c : Digest) (σ : Sig) : Signed := ⟨magic c, [(q0, trigger)], σ⟩

/-- **An honest-looking node wraps fake children**: if the T2 prover can sign the trigger trace
under `vk` (its own key; T2 has no service), the honest v4 node proof of `nodeStmt c₁ c₂` with
two magic children is accepted under `Hpub`, for any `c₁`, `c₂`. -/
theorem node_wraps_magic (vk c₁ c₂ : Digest) (σ₁ σ₂ : Sig)
    (h₁ : SigOk vk (traceDigest [(q0, trigger)]) σ₁ = true)
    (h₂ : SigOk vk (traceDigest [(q0, trigger)]) σ₂ = true) :
    accT2 (S.V vk) (nodeStmt c₁ c₂)
      (WitnessSending.encode (.node c₁ c₂ (signedMagic c₁ σ₁) (signedMagic c₂ σ₂))) = true := by
  have hR : Rel (S.acc vk) (nodeStmt c₁ c₂) (.node c₁ c₂ (signedMagic c₁ σ₁) (signedMagic c₂ σ₂)) :=
    ⟨rfl, (magic_needs_trigger vk c₁ _ σ₁).mpr ⟨rfl, h₁⟩,
      (magic_needs_trigger vk c₂ _ σ₂).mpr ⟨rfl, h₂⟩⟩
  show (V vk _ _).run Hpub = true
  simp [V, OProg.run, check_encode hR]

/-! ## The contrast with T1 -/

/-- **T1 vs T2**: the submission is certified; in v4 (T1) `acc` accepts the magic proof only on
the signed trace answering the empty query with the public value (`magic_needs_trigger`), which
the keyed service signs with probability `2^-256` per key; in T2 the magic proof of every digest
is accepted and extraction from it fails. -/
theorem t1_vs_t2 :
    Certificate S ∧
    (∀ vk c tr σ, S.acc vk c ⟨magic c, tr, σ⟩ = true ↔
      tr = [(q0, trigger)] ∧ SigOk vk (traceDigest tr) σ = true) ∧
    (∀ vk c, accT2 (S.V vk) c (magic c) = true ∧ ∀ L, S.E vk (magic c) L = none) :=
  ⟨certified, magic_needs_trigger, fun vk c => ⟨accT2_magic vk c, extract_magic vk c⟩⟩

end RecursionFast.Explore.T2Backdoor
