/-
# Exploration: the attested knowledge state                                        (UNTRUSTED)

Probe P2, item 2 (`docs/explore/notes/W2-attested-oracle.md` §A.3–A.4). The knowledge state of
the attested model: v3's potential with its `empty` and `step` laws, a new **deterministic** law
`cert` for certifications, and a `final` law whose extractor returns either a witness of the
relativized relation on the log or a collision of the list hash.

* `RelA V L`: the relativized relation on an attested log (P1's `RelWith` with the children
  accepted by `V` reading `L`). Leaf clause as in v3; node clause `c = nodeStmt c₁ c₂` and both
  children accepted on `L`.
* `Out`: the extractor's output, `wit w` or `coll x y`; `Sound V L c o`: `wit w` is a witness of
  `RelA V L c`, `coll x y` is a collision of `hashList` between distinct **bounded** lists
  (`IsColl`), hence a BLAKE2s collision between distinct byte strings (`IsColl.blake2s`).
* `KStateA V E ε`: `μ`, `empty`, `step` (a fresh query, `firstAns L q = none`, raises the
  potential by at most `ε` on average over its `2^256` answers, within `logCap`), `cert` (a valid
  certification does not raise it), `final` (on a well-formed log within `logCap` below potential
  `1`, every accepted proof is extracted to a sound output). `KSA` adds the bound `qV` on the
  number of calls (queries and attestation requests) of `V`.
* `WF` in `final` costs nothing: the potential guarded by `WF` (`KStateA.gμ`, `1` off well-formed
  logs) satisfies `empty`, `step` and `cert`, and its `final` needs no `WF` (`gμ_empty`, `gμ_step`,
  `gμ_cert`, `gμ_final`). The game only produces well-formed logs (`WF.snoc_ans`, `WF.snoc_cert`).
* `KStateA.ofRel`: P1's relativized knowledge state of a contract verifier (`KStateRel`) lifts to
  the attested model, with the potential read from the log's answers (`μ ∘ ansLog`, which ignores
  certifications, so `cert` holds with equality). `KStateA.zero` for extractors that never fail.

**Why the collision is the extractor's output and not a proposition.** A collision of BLAKE2s
exists: there are infinitely many bounded lists and `2^256` digests, so by pigeonhole
(`Finite.exists_ne_map_eq_of_infinite`) two of them share a `hashList` (`exists_isColl`, kernel).
A `final` concluding `(∃ w, E c π L = some w ∧ RelA V L c w) ∨ ∃ x y, IsColl x y` would therefore
hold for **every** verifier, the accept-all one included. With the collision as the value of
`E c π L`, a proof of `final` through the `coll` branch must name the pair the extractor returns
(`Controls.lean`, `acceptAll_iff`: the accept-all verifier with a constant `coll x y` extractor
has a state exactly when `IsColl x y`). Naming it in the **type** is not enough on its own: an
extractor defined by `Classical.choose` of `exists_isColl` certifies the accept-all verifier
(`Controls.lean`, `acceptAll_choice`), so the knowledge content needs the extractor to be computed
by a program (v3's `Computes`, the rules worktree's `Extractor.lean`), exactly as for v3's
`acceptAll_kstate_iff`. The difference with v3 is that there the accept-all certificate needed an
open fact about BLAKE2s (every digest has a witness), and here it is a theorem.
-/
import RecursionFast.Explore.Attested.Model
import Mathlib.Data.Fintype.Pigeonhole

open scoped NNReal

namespace RecursionFast.Explore.Attested

open Relativized

/-! ## The relation and the extractor's output -/

/-- **The relativized relation on an attested log**: v3's leaf clause; a node digest is the
statement of two children whose proofs `V` accepts reading `L`. -/
def RelA (V : Digest → Proof → AProg Bool) (L : ALog) : Digest → Wit → Prop :=
  RelWith fun c π => (V c π).runLog L = some true

@[simp] theorem relA_leaf {V : Digest → Proof → AProg Bool} (L : ALog) (c s : Digest) (n : ℕ) :
    RelA V L c (.leaf s n) ↔ n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n := Iff.rfl

@[simp] theorem relA_node {V : Digest → Proof → AProg Bool} (L : ALog) (c c₁ c₂ : Digest)
    (π₁ π₂ : Proof) : RelA V L c (.node c₁ c₂ π₁ π₂) ↔ c = nodeStmt c₁ c₂ ∧
      (V c₁ π₁).runLog L = some true ∧ (V c₂ π₂).runLog L = some true := Iff.rfl

/-- What the extractor returns: a witness, or two lists of items. -/
inductive Out where
  /-- A witness. -/
  | wit (w : Wit)
  /-- Two lists of items (claimed to collide under `hashList`). -/
  | coll (x y : List Item)

/-- `x` and `y` are a **collision of the list hash**: distinct bounded lists with one `hashList`. -/
def IsColl (x y : List Item) : Prop := Bounded x ∧ Bounded y ∧ x ≠ y ∧ hashList x = hashList y

/-- A collision of the list hash is a BLAKE2s-256 collision between distinct byte strings. -/
theorem IsColl.blake2s {x y : List Item} (h : IsColl x y) :
    tagList :: encList x ≠ tagList :: encList y ∧
      blake2s256 (tagList :: encList x) = blake2s256 (tagList :: encList y) :=
  hashList_coll h.1 h.2.1 h.2.2.1 h.2.2.2

/-- **A sound output** for the statement `c` on the log `L`: a witness of `RelA V L c`, or a
collision of the list hash. -/
def Sound (V : Digest → Proof → AProg Bool) (L : ALog) (c : Digest) : Out → Prop
  | .wit w => RelA V L c w
  | .coll x y => IsColl x y

/-- **A collision of the list hash exists** (pigeonhole: the lists `[att 0, …, att 0]` are
infinitely many and bounded, the digests finite). So "a collision exists" is no knowledge. -/
theorem exists_isColl : ∃ x y, IsColl x y := by
  obtain ⟨n, m, hnm, h⟩ := Finite.exists_ne_map_eq_of_infinite fun n : ℕ =>
    hashList (List.replicate n (Item.att (Vector.replicate 32 0)))
  have hb : ∀ k, Bounded (List.replicate k (Item.att (Vector.replicate 32 0))) := fun k x hx => by
    rw [List.eq_of_mem_replicate hx]; rfl
  exact ⟨_, _, hb n, hb m, fun h' => hnm (by simpa using congrArg List.length h'), h⟩

/-! ## The knowledge state -/

variable {V : Digest → Proof → AProg Bool} {E : Digest → Proof → ALog → Option Out} {ε : ℝ≥0}

/-- **An attested knowledge state** with per-query error `ε` for the verifier `V` and the
extractor `E`: a potential on attested logs with v3's laws `empty` and `step`, the deterministic
law `cert`, and `final` extracting a witness of the relativized relation or a list-hash
collision. -/
structure KStateA (V : Digest → Proof → AProg Bool) (E : Digest → Proof → ALog → Option Out)
    (ε : ℝ≥0) where
  /-- The potential of a log; below `1`, no accepted proof escapes the extractor. -/
  μ : ALog → ℝ≥0
  /-- The empty log has potential `0`. -/
  empty : μ [] = 0
  /-- Within `logCap` and below `1`, a fresh query raises the potential by at most `ε` on average
  over its `2^256` answers. -/
  step : ∀ L q, L.length < logCap → μ L < 1 → firstAns L q = none →
    ∑ a : Digest, μ (L ++ [.ans q a]) ≤ (μ L + ε) * 2 ^ 256
  /-- Within `logCap`, a valid certification does not raise the potential (it adds no
  randomness). -/
  cert : ∀ L xs, L.length < logCap → Valid L xs → μ (L ++ [.cert xs]) ≤ μ L
  /-- On a well-formed log within `logCap` below potential `1`, every proof the verifier accepts
  is extracted to a witness of the relativized relation on that log or to a list-hash collision. -/
  final : ∀ L c π, WF L → L.length ≤ logCap → μ L < 1 → (V c π).runLog L = some true →
    ∃ o, E c π L = some o ∧ Sound V L c o

/-- **Attested knowledge soundness**: an attested knowledge state with error `ε` exists, and `V`
makes at most `qV` calls (queries and attestation requests) on every input, oracle and attest
predicate. -/
def KSA (V : Digest → Proof → AProg Bool) (E : Digest → Proof → ALog → Option Out) (ε : ℝ≥0)
    (qV : ℕ) : Prop :=
  Nonempty (KStateA V E ε) ∧ ∀ H A c π, ((V c π).calls H A).length ≤ qV

/-- The potential `0`, when every accepted proof is extracted on every well-formed log. -/
def KStateA.zero (ε : ℝ≥0)
    (h : ∀ L c π, WF L → (V c π).runLog L = some true → ∃ o, E c π L = some o ∧ Sound V L c o) :
    KStateA V E ε :=
  ⟨fun _ => 0, rfl, fun _ _ _ _ _ => by simp, fun _ _ _ _ => le_rfl,
    fun L c π hW _ _ => h L c π hW⟩

/-! ## `WF` in `final` costs nothing -/

open Classical in
/-- The potential guarded by well-formedness: `μ` on well-formed logs, `1` elsewhere. -/
noncomputable def KStateA.gμ (k : KStateA V E ε) (L : ALog) : ℝ≥0 := if WF L then k.μ L else 1

theorem WF.of_append {L : ALog} {e : Ev} (h : WF (L ++ [e])) : WF L := fun P xs S hL =>
  h P xs (S ++ [e]) (by simp [hL])

theorem KStateA.gμ_empty (k : KStateA V E ε) : k.gμ [] = 0 := by simp [gμ, WF.nil, k.empty]

theorem KStateA.gμ_step (k : KStateA V E ε) (L : ALog) (q : ByteArray) (hL : L.length < logCap)
    (hμ : k.gμ L < 1) (hq : firstAns L q = none) :
    ∑ a : Digest, k.gμ (L ++ [.ans q a]) ≤ (k.gμ L + ε) * 2 ^ 256 := by
  have hW : WF L := by by_contra hW; simp [gμ, hW] at hμ
  simp only [gμ, hW, WF.snoc_ans hW, ite_true] at hμ ⊢
  exact k.step L q hL hμ hq

theorem KStateA.gμ_cert (k : KStateA V E ε) (L : ALog) (xs : List Item) (hL : L.length < logCap)
    (hv : Valid L xs) : k.gμ (L ++ [.cert xs]) ≤ k.gμ L := by
  by_cases hW : WF L
  · simp only [gμ, hW, WF.snoc_cert hW hv, ite_true]; exact k.cert L xs hL hv
  · have : ¬ WF (L ++ [.cert xs]) := fun h => hW h.of_append
    simp [gμ, hW, this]

/-- `final` for the guarded potential, without the well-formedness hypothesis. -/
theorem KStateA.gμ_final (k : KStateA V E ε) (L : ALog) (c : Digest) (π : Proof)
    (hL : L.length ≤ logCap) (hμ : k.gμ L < 1) (h : (V c π).runLog L = some true) :
    ∃ o, E c π L = some o ∧ Sound V L c o := by
  have hW : WF L := by by_contra hW; simp [gμ, hW] at hμ
  simp only [gμ, hW, ite_true] at hμ
  exact k.final L c π hW hL hμ h

/-! ## Lifting P1's relativized knowledge states -/

/-- A contract verifier as an attested one. -/
def liftV (V : Digest → Proof → OProg Bool) (c : Digest) (π : Proof) : AProg Bool := (V c π).toA

/-- A contract extractor as an attested one: read the log's answers, return a witness. -/
def liftE (E : Digest → Proof → Log → Option Wit) (c : Digest) (π : Proof) (L : ALog) :
    Option Out := (E c π (ansLog L)).map Out.wit

theorem firstAns_none {L : ALog} {q : ByteArray} (h : firstAns L q = none) :
    q ∉ (ansLog L).map Prod.fst := by
  rw [firstAns_eq, Relativized.firstAns, Option.map_eq_none_iff, List.find?_eq_none] at h
  simpa using fun a ha => h (q, a) ha (by simp)

/-- **P1's relativized knowledge states lift to the attested model**: a `KStateRel V E ε` gives a
`KStateA (liftV V) (liftE E) ε` whose potential reads the log's answers only. -/
def KStateA.ofRel {V : Digest → Proof → OProg Bool} {E : Digest → Proof → Log → Option Wit}
    (k : KStateRel V E ε) : KStateA (liftV V) (liftE E) ε where
  μ L := k.μ (ansLog L)
  empty := k.empty
  step L q hL hμ hq := by
    simpa using k.step (ansLog L) q ((ansLog_length L).trans_lt hL) hμ (firstAns_none hq)
  cert L xs _ _ := by simp
  final L c π _ hL hμ h := by
    rw [liftV, toA_runLog] at h
    obtain ⟨w, hE, hw⟩ := k.final _ c π ((ansLog_length L).trans hL) hμ h
    exact ⟨.wit w, by simp [liftE, hE], hw.mono fun h => by rwa [liftV, toA_runLog]⟩

theorem KStateA.ofRel_μ {V : Digest → Proof → OProg Bool} {E : Digest → Proof → Log → Option Wit}
    (k : KStateRel V E ε) : (KStateA.ofRel k).μ = fun L => k.μ (ansLog L) := rfl

/-- A lifted verifier makes the original's calls: at most `qV` if the original asks at most `qV`
queries. -/
theorem liftV_calls {V : Digest → Proof → OProg Bool} {qV : ℕ}
    (h : ∀ H c π, ((V c π).queries H).length ≤ qV) (H : ByteArray → Digest) (A : Digest → Bool)
    (c : Digest) (π : Proof) : ((liftV V c π).calls H A).length ≤ qV := by
  simpa [liftV, toA_calls] using h H c π

/-- **`KSRel` lifts to `KSA`** with the same error and call bound. -/
theorem KSA.ofRel {V : Digest → Proof → OProg Bool} {E : Digest → Proof → Log → Option Wit}
    {qV : ℕ} (h : KSRel V E ε qV) : KSA (liftV V) (liftE E) ε qV :=
  ⟨⟨.ofRel h.1.some⟩, liftV_calls h.2⟩

end RecursionFast.Explore.Attested
