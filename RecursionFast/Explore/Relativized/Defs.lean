/-
# Exploration: the relativized relation and its knowledge state                   (UNTRUSTED)

Branch `explore/relativized-nark`, probe P1 (`docs/explore/BRIEF.md` §3). v3's relation `Rel Vb`
judges a node's children with the verifier instantiated at **concrete** BLAKE2s. The relativized
relation `RelL V L` judges them with the verifier reading the **same query log** `L` as the
knowledge game, so the oracle in the node clause is the random oracle itself. This file states it
and its knowledge state; the other probes use them.

* `RelWith P`: the relation's two clauses, with the node clause's child condition `P` left open.
  `rel_eq`: v3's `Rel Vb` is `RelWith (Vb · · = true)`. `RelL V L` is `RelWith` with the children
  accepted on `L` (`relL_leaf`, `relL_node` state the clauses literally); `RelH V H` with the
  children accepted under the oracle function `H`.
* `KStateRel V E ε`: `KState`'s laws `empty` and `step` unchanged; `final` concludes `RelL V L`
  for the log `L` it is applied to. `KSRel` is `KS` with it.
* Logs and oracles: `runLog_run` (a log that agrees with `H` on all its entries gives the verdict
  of `run H`), so `RelL.toH` (a witness of `RelL V L` is one of `RelH V H` for every such `H`).
  `runLog_of_agrees` (monotonicity: if every entry of `Q` is the first answer `L` gives to its
  query, a verdict read from `Q` is the verdict read from `L`).
* Builders: `KStateRel.ofKState` (reuse the potential of any `KState`), `KStateRel.zero`,
  `KStateRel.ofBool` (a good/bad predicate pair with at most `ε · 2^256` bad answers per query).
* **The paper theorem carries over** (`KStateRel.paper_of`, `KStateRel.paper`): the potential of a
  relativized state is a contract potential (`KStateRel.toKState`), so `Library/PaperTheorem.lean`
  applies verbatim: for a game of at most `n ≤ logCap` lazily sampled queries, any event that
  forces the potential to `1` within `logCap` has probability at most `n · ε`; in particular
  acceptance without a `RelL` witness on the final log.
* `OProg.bind` (copied from the rules worktree's contract, V3-S2R-A2; delete when the contract has
  it) and `OProg.band` (the conjunction of two verdicts, the second asked only if the first holds).
* `Codec F sub`: an abstract proof codec for a frame type `F` whose sub-proofs `sub f` are strictly
  shorter than the proof. The concatenation and deferral probes abstract their byte formats behind
  it, to keep byte parsing out of the probes. `Codec.unary` shows every `Encodable` frame type has
  one (a unary length code, absurdly long but enough for non-vacuity), and `CFrame`, `DFrame` (the
  two frame types the probes use) are `Encodable`.
-/
import RecursionFast.Library.Security
import RecursionFast.Library.PaperTheorem
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Nat.Pairing

open scoped NNReal

namespace RecursionFast

namespace OProg
variable {α β : Type}

/-- The program that runs `p` and then `f` on its result, against the same oracle. -/
def bind : OProg α → (α → OProg β) → OProg β
  | ret a, f => f a
  | query q k, f => query q fun d => (k d).bind f

theorem runLog_bind (L : Log) (p : OProg α) (f : α → OProg β) :
    (p.bind f).runLog L = (p.runLog L).bind fun a => (f a).runLog L := by
  induction p with
  | ret a => rfl
  | query q k ih => simp only [bind, runLog, ih, Option.bind_assoc]

theorem run_bind (H : ByteArray → Digest) (p : OProg α) (f : α → OProg β) :
    (p.bind f).run H = (f (p.run H)).run H := by
  induction p with
  | ret a => rfl
  | query q k ih => exact ih (H q)

/-- Both verdicts: `p`, then `r` if `p` accepts. -/
def band (p r : OProg Bool) : OProg Bool := p.bind fun b => if b then r else ret false

theorem runLog_band (L : Log) (p r : OProg Bool) :
    (band p r).runLog L = some true ↔ p.runLog L = some true ∧ r.runLog L = some true := by
  rw [band, runLog_bind]
  cases p.runLog L with
  | none => simp
  | some b => cases b <;> simp [runLog]

theorem run_band (H : ByteArray → Digest) (p r : OProg Bool) :
    (band p r).run H = (p.run H && r.run H) := by
  rw [band, run_bind]; cases p.run H <;> rfl

end OProg

namespace Explore.Relativized

/-! ## The relation -/

/-- The relation's two clauses, with the node clause's condition on the children left as `P`: a
leaf digest is the statement of a chain of at most `chainCap` steps from the witness's start; a
node digest is the statement of two children whose digests and proofs satisfy `P`. -/
def RelWith (P : Digest → Proof → Prop) : Digest → Wit → Prop
  | c, .leaf s n => n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n
  | c, .node c₁ c₂ π₁ π₂ => c = nodeStmt c₁ c₂ ∧ P c₁ π₁ ∧ P c₂ π₂

/-- A weaker child condition gives a weaker relation. -/
theorem RelWith.mono {P Q : Digest → Proof → Prop} (h : ∀ {c π}, P c π → Q c π) :
    ∀ {c w}, RelWith P c w → RelWith Q c w
  | _, .leaf _ _, hw => hw
  | _, .node _ _ _ _, ⟨hc, h₁, h₂⟩ => ⟨hc, h h₁, h h₂⟩

/-- v3's relation is `RelWith` with the children accepted by the instantiated verifier `Vb`. -/
theorem rel_eq (Vb : Digest → Proof → Bool) : Rel Vb = RelWith fun c π => Vb c π = true := by
  funext c w; cases w <;> rfl

/-- **The relativized relation** on the query log `L`: the leaf clause of `Rel`; a node digest is
the statement of two children whose proofs `V` accepts reading its answers from `L`. -/
def RelL (V : Digest → Proof → OProg Bool) (L : Log) : Digest → Wit → Prop :=
  RelWith fun c π => (V c π).runLog L = some true

/-- The relativized relation under the oracle function `H`: the children are accepted by `V` run
with `H`. (`RelH V blake2sOracle` is v3's `Rel` without the proof-size cap.) -/
def RelH (V : Digest → Proof → OProg Bool) (H : ByteArray → Digest) : Digest → Wit → Prop :=
  RelWith fun c π => (V c π).run H = true

variable {V : Digest → Proof → OProg Bool} {E : Digest → Proof → Log → Option Wit} {ε : ℝ≥0}

@[simp] theorem relL_leaf (L : Log) (c s : Digest) (n : ℕ) :
    RelL V L c (.leaf s n) ↔ n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n := Iff.rfl

@[simp] theorem relL_node (L : Log) (c c₁ c₂ : Digest) (π₁ π₂ : Proof) :
    RelL V L c (.node c₁ c₂ π₁ π₂) ↔ c = nodeStmt c₁ c₂ ∧ (V c₁ π₁).runLog L = some true ∧
      (V c₂ π₂).runLog L = some true := Iff.rfl

/-! ## Logs, oracles and agreement -/

/-- The answer a log gives to the query `q`: its first entry for `q`, as `runLog` reads it. -/
def firstAns (L : Log) (q : ByteArray) : Option Digest :=
  (L.find? fun e => e.1 = q).map Prod.snd

/-- **A log consistent with an oracle function** gives a verdict only if it is the verdict under
that function. (Every entry agreeing with `H` is the condition; it holds for the log of any run
against `H`.) -/
theorem runLog_run {α : Type} {H : ByteArray → Digest} {L : Log} (hL : ∀ e ∈ L, H e.1 = e.2)
    {p : OProg α} {b : α} (h : p.runLog L = some b) : p.run H = b := by
  induction p with
  | ret a => exact Option.some.inj h
  | query q k ih =>
    obtain ⟨e, he, hk⟩ := Option.bind_eq_some_iff.mp h
    have hq : e.1 = q := by simpa using List.find?_some he
    rw [OProg.run, ← hq, hL e (List.mem_of_find?_eq_some he)]
    exact ih e.2 hk

/-- A witness of the relativized relation on a log is one under every oracle function the log is
consistent with. -/
theorem RelL.toH {H : ByteArray → Digest} {L : Log} (hL : ∀ e ∈ L, H e.1 = e.2) {c : Digest}
    {w : Wit} (h : RelL V L c w) : RelH V H c w :=
  h.mono fun h => runLog_run hL h

/-- `Q` **agrees with** `L`: every entry of `Q` is the answer `L` gives to its query. -/
def Agrees (Q L : Log) : Prop := ∀ e ∈ Q, firstAns L e.1 = some e.2

/-- **Monotonicity**: a verdict read from `Q` is the verdict read from any `L` that `Q` agrees
with. -/
theorem runLog_of_agrees {α : Type} {Q L : Log} (hQ : Agrees Q L) {p : OProg α} {b : α}
    (h : p.runLog Q = some b) : p.runLog L = some b := by
  induction p with
  | ret a => exact h
  | query q k ih =>
    obtain ⟨e, he, hk⟩ := Option.bind_eq_some_iff.mp h
    have hq : e.1 = q := by simpa using List.find?_some he
    obtain ⟨f, hf, hfe⟩ := Option.map_eq_some_iff.mp (hQ e (List.mem_of_find?_eq_some he))
    rw [hq] at hf
    simp only [OProg.runLog, hf, Option.bind_some, hfe]
    exact ih e.2 hk

/-! ## The relativized knowledge state -/

/-- **A relativized knowledge state** with per-query error `ε` for the verifier `V` and the
extractor `E`: `KState`'s potential, `empty` and `step`; `final` extracts a witness of the
relativized relation **on the same log** from every proof `V` accepts on it. -/
structure KStateRel (V : Digest → Proof → OProg Bool) (E : Digest → Proof → Log → Option Wit)
    (ε : ℝ≥0) where
  /-- The potential of a log; below `1`, no accepted proof escapes the extractor. -/
  μ : Log → ℝ≥0
  /-- The empty log has potential `0`. -/
  empty : μ [] = 0
  /-- Within `logCap` and below `1`, a fresh query raises the potential by at most `ε` on average
  over its `2^256` answers. -/
  step : ∀ L q, L.length < logCap → μ L < 1 → q ∉ L.map Prod.fst →
    ∑ a : Digest, μ (L ++ [(q, a)]) ≤ (μ L + ε) * 2 ^ 256
  /-- Within `logCap` and below `1`, every proof the verifier accepts on the log's answers is
  extracted to a witness of the relativized relation on that log. -/
  final : ∀ L c π, L.length ≤ logCap → μ L < 1 → (V c π).runLog L = some true →
    ∃ w, E c π L = some w ∧ RelL V L c w

/-- **Relativized knowledge soundness**: a relativized knowledge state with error `ε` exists, and
`V` asks at most `qV` queries on every input and oracle. -/
def KSRel (V : Digest → Proof → OProg Bool) (E : Digest → Proof → Log → Option Wit) (ε : ℝ≥0)
    (qV : ℕ) : Prop :=
  Nonempty (KStateRel V E ε) ∧ ∀ H c π, ((V c π).queries H).length ≤ qV

/-- The potential of any knowledge state (for any relation, verifier and extractor), with a
relativized `final` proved for it. -/
def KStateRel.ofKState {R : Digest → Wit → Prop} {V' : Digest → Proof → OProg Bool}
    {E' : Digest → Proof → Log → Option Wit} (k : KState R V' E' ε)
    (h : ∀ L c π, L.length ≤ logCap → k.μ L < 1 → (V c π).runLog L = some true →
      ∃ w, E c π L = some w ∧ RelL V L c w) : KStateRel V E ε :=
  ⟨k.μ, k.empty, k.step, h⟩

/-- The potential `0`, when every accepted proof is extracted on every log. -/
def KStateRel.zero (ε : ℝ≥0)
    (h : ∀ L c π, (V c π).runLog L = some true → ∃ w, E c π L = some w ∧ RelL V L c w) :
    KStateRel V E ε :=
  ⟨fun _ => 0, rfl, fun _ _ _ _ _ => by simp, fun L c π _ _ => h L c π⟩

/-- **A boolean relativized knowledge state**: good logs stay good after a fresh query unless its
answer is bad, at most an `ε` fraction of answers is bad on logs shorter than `logCap`, and on
good logs every accepted proof is extracted. The potential is `0` on good logs, `1` elsewhere. -/
noncomputable def KStateRel.ofBool (good : Log → Prop) (bad : Log → ByteArray → Digest → Prop)
    (empty : good [])
    (step : ∀ L q a, good L → q ∉ L.map Prod.fst → ¬ bad L q a → good (L ++ [(q, a)]))
    (bound : ∀ L q, L.length < logCap → (Nat.card {a // bad L q a} : ℝ≥0) ≤ ε * Nat.card Digest)
    (final : ∀ L c π, good L → (V c π).runLog L = some true →
      ∃ w, E c π L = some w ∧ RelL V L c w) : KStateRel V E ε :=
  let k : BoolKState (fun _ _ => True) V (fun _ _ _ => some (.leaf (Vector.replicate 32 0) 0)) :=
    ⟨good, bad, empty, step, fun _ _ _ _ _ => ⟨_, rfl, trivial⟩⟩
  .ofKState (KState.ofBool k bound) fun L c π _ hμ h => final L c π (by
    by_contra hg; simp [KState.ofBool, k, hg] at hμ) h

/-- The potential of a relativized knowledge state, as a contract knowledge state (for the
trivial relation and a constant extractor, so only `μ`, `empty` and `step` carry content). -/
def KStateRel.toKState (k : KStateRel V E ε) :
    KState (fun _ _ => True) V (fun _ _ _ => some (.leaf (Vector.replicate 32 0) 0)) ε :=
  ⟨k.μ, k.empty, k.step, fun _ _ _ _ _ _ => ⟨_, rfl, trivial⟩⟩

open PaperTheorem in
/-- **The paper theorem for any event below potential `1`**: if an event `B` at the end of a game
never holds on a log within `logCap` of potential below `1`, a game asking at most `n ≤ logCap`
lazily sampled queries ends in it with probability at most `n · ε`. -/
theorem KStateRel.paper_of (k : KStateRel V E ε) (B : Digest × Proof → Log → Prop)
    (hB : ∀ x L, B x L → L.length ≤ logCap → k.μ L < 1 → False) (G : OProg (Digest × Proof))
    (n : ℕ) (hG : DepthLE G n) (hn : n ≤ logCap) : prob B G [] ≤ n * ε :=
  calc prob B G [] ≤ pot k.toKState G [] :=
        prob_le_pot _ B (fun x L h hl => not_lt.mp (hB x L h hl)) G n [] hG (by simpa using hn)
    _ ≤ min 1 (k.μ []) + n * ε := pot_le k.toKState G n [] hG (by simpa using hn)
    _ = n * ε := by simp [k.empty]

open PaperTheorem in
/-- **The relativized paper theorem**: the probability that the verifier accepts on the final log
and the extractor returns no witness of the relativized relation on that log is at most
`n · ε`. -/
theorem KStateRel.paper (k : KStateRel V E ε) (G : OProg (Digest × Proof)) (n : ℕ)
    (hG : DepthLE G n) (hn : n ≤ logCap) :
    prob (fun x L => (V x.1 x.2).runLog L = some true ∧
      ¬ ∃ w, E x.1 x.2 L = some w ∧ RelL V L x.1 w) G [] ≤ n * ε :=
  k.paper_of _ (fun x L h hl hμ => h.2 (k.final L x.1 x.2 hl hμ h.1)) G n hG hn

/-! ## Abstract proof codecs -/

/-- **A proof codec** for frames `F` whose sub-proofs are `sub f`: an encoder, a decoder that
inverts it, and every sub-proof of a decoded frame strictly shorter than the proof (so a verifier
that recurses into sub-proofs terminates). -/
structure Codec (F : Type) (sub : F → List Proof) where
  /-- The proof of a frame. -/
  enc : F → Proof
  /-- The frame a proof denotes, if any. -/
  dec : Proof → Option F
  /-- Decoding inverts encoding. -/
  dec_enc : ∀ f, dec (enc f) = some f
  /-- The sub-proofs of a decoded frame are shorter than the proof. -/
  lt : ∀ {π f}, dec π = some f → ∀ π' ∈ sub f, π'.size < π.size

/-- A concatenation frame: a leaf verifier's proof, or a node's two child digests and child proofs
in the clear. -/
inductive CFrame where
  /-- A proof for the leaf verifier. -/
  | leaf (π : Proof)
  /-- A node: the two child digests and the two child proofs. -/
  | node (c₁ c₂ : Digest) (π₁ π₂ : Proof)

/-- The sub-proofs of a concatenation frame: a node's two child proofs. -/
def CFrame.sub : CFrame → List Proof
  | .leaf _ => []
  | .node _ _ π₁ π₂ => [π₁, π₂]

/-- A deferral frame: a base verifier's proof, or a node's two child digests, child proofs and the
oracle answers `Q` the children are judged against. -/
inductive DFrame where
  /-- A proof for the base verifier. -/
  | base (π : Proof)
  /-- A node: the child digests, the child proofs, and a list of oracle answers. -/
  | defer (c₁ c₂ : Digest) (π₁ π₂ : Proof) (Q : Log)

/-- The sub-proofs of a deferral frame: a node's two child proofs. -/
def DFrame.sub : DFrame → List Proof
  | .base _ => []
  | .defer _ _ π₁ π₂ _ => [π₁, π₂]

/-- **The unary codec** of an encodable frame type: the proof of `f` is a run of zero bytes whose
length pairs `f`'s code with one more than the total size of its sub-proofs. -/
def Codec.unary {F : Type} [Encodable F] (sub : F → List Proof) : Codec F sub where
  enc f :=
    ⟨Array.replicate (Nat.pair (Encodable.encode f) (((sub f).map ByteArray.size).sum + 1)) 0⟩
  dec π := (Encodable.decode (α := F) (Nat.unpair π.size).1).bind fun f =>
    if ((sub f).map ByteArray.size).sum + 1 = (Nat.unpair π.size).2 then some f else none
  dec_enc f := by simp [ByteArray.size, Nat.unpair_pair, Encodable.encodek]
  lt {π f} h π' hπ' := by
    obtain ⟨g, -, hg⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at hg with hs
    cases hg
    have h1 : π'.size ≤ ((sub f).map ByteArray.size).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem hπ')
    have h2 := Nat.unpair_right_le π.size
    omega

instance : Encodable UInt8 := Encodable.ofEquiv (Fin 256) ⟨UInt8.toFin, UInt8.ofFin, fun _ => rfl,
  fun _ => rfl⟩

instance : Encodable ByteArray := Encodable.ofEquiv (List UInt8)
  ⟨fun b => b.data.toList, fun l => ⟨l.toArray⟩, fun _ => rfl, fun _ => by simp⟩

instance : Encodable Digest :=
  Encodable.ofLeftInjection Vector.toList
    (fun l => if h : l.length = 32 then some ⟨l.toArray, by simp [h]⟩ else none)
    fun v => by simp [Vector.toList]

instance : Encodable CFrame := Encodable.ofEquiv (Proof ⊕ (Digest × Digest × Proof × Proof))
  { toFun := fun | .leaf π => .inl π | .node c₁ c₂ π₁ π₂ => .inr (c₁, c₂, π₁, π₂)
    invFun := fun | .inl π => .leaf π | .inr (c₁, c₂, π₁, π₂) => .node c₁ c₂ π₁ π₂
    left_inv := fun f => by cases f <;> rfl
    right_inv := fun f => by rcases f with _ | ⟨_, _, _, _⟩ <;> rfl }

instance : Encodable DFrame := Encodable.ofEquiv (Proof ⊕ (Digest × Digest × Proof × Proof × Log))
  { toFun := fun | .base π => .inl π | .defer c₁ c₂ π₁ π₂ Q => .inr (c₁, c₂, π₁, π₂, Q)
    invFun := fun | .inl π => .base π | .inr (c₁, c₂, π₁, π₂, Q) => .defer c₁ c₂ π₁ π₂ Q
    left_inv := fun f => by cases f <;> rfl
    right_inv := fun f => by rcases f with _ | ⟨_, _, _, _, _⟩ <;> rfl }

end Explore.Relativized

end RecursionFast
