/-
# Exploration: the relativized requirement is met without recursion             (UNTRUSTED)

Probe P1, item 3. **Relativized knowledge soundness does not force a verifier to compress.** The
relativized node clause asks only that the children be accepted by the same verifier on the same
log. A verifier that takes a node proof to be the two child proofs in the clear and runs **itself**
on each (concatenation) meets that clause by its own definition: the extractor returns the node
proof's fields, and `final` holds at once. So a leaf verifier with a knowledge state for the leaf
clause alone gives a concatenating verifier with a relativized knowledge state with **the same
potential and the same error** (`concatState`), with no argument about recursion at all. The root
verifier of a tree of `m` leaves then does `m` leaf verifications: nothing compresses, and nothing
in `KSRel` objects.

* `concatV C Vl`: decode the proof with the codec `C`; a leaf frame goes to the leaf verifier
  `Vl`; a node frame `(c₁, c₂, π₁, π₂)` is accepted when `c = nodeStmt c₁ c₂` and `concatV`
  accepts both children (`concatV_leaf`, `concatV_node`). `concatE C El`: the leaf extractor on a
  leaf frame, the frame's fields on a node frame.
* `concatState`: from `k : KState LeafRel Vl El ε` (the leaf clause only; `LeafRel` has no node
  witness) a `KStateRel (concatV C Vl) (concatE C El) ε` whose potential is `k.μ`
  (`concatState_μ`).
* The honest node prover is the identity: a node witness of `RelH` under an oracle `H` is accepted
  as its own encoding (`concatV_node_run`), so completeness for nodes is free.
* `wsState`: the minimum the brief asks for, on the real byte format. The witness-sending verifier
  (`Library/WitnessSending.lean`, no oracle query; its node proofs are a node witness's bytes, so
  it is the concatenating verifier of the leaf check) has a relativized knowledge state with
  potential `0` and error `0` (`ws_ksRel`: `KSRel` with `qV = 0`).

**Abstraction.** The generic construction takes the byte format as a `Codec CFrame CFrame.sub`
(`Defs.lean`): an encoder, a decoder inverting it, and node sub-proofs strictly shorter than the
proof. `Codec.unary` shows one exists. `wsState` uses no abstraction.
-/
import RecursionFast.Explore.Relativized.Defs
import RecursionFast.Library.WitnessSending

open scoped NNReal

namespace RecursionFast.Explore.Relativized

/-- The leaf clause alone: a leaf witness of `Rel`'s leaf clause; no node witness. -/
def LeafRel : Digest → Wit → Prop := RelWith fun _ _ => False

variable (C : Codec CFrame CFrame.sub) (Vl : Digest → Proof → OProg Bool)
  (El : Digest → Proof → Log → Option Wit) {ε : ℝ≥0}

/-- **The concatenating verifier** over the leaf verifier `Vl`: a leaf frame is judged by `Vl`; a
node frame `(c₁, c₂, π₁, π₂)` is accepted when `c` is their node statement and this verifier
accepts both children. -/
def concatV (c : Digest) (π : Proof) : OProg Bool :=
  match _h : C.dec π with
  | some (.leaf π') => Vl c π'
  | some (.node c₁ c₂ π₁ π₂) =>
    if c = nodeStmt c₁ c₂ then .band (concatV c₁ π₁) (concatV c₂ π₂) else .ret false
  | none => .ret false
termination_by π.size
decreasing_by all_goals exact C.lt _h _ (by simp [CFrame.sub])

/-- The concatenating extractor: the leaf extractor on a leaf frame, the frame's fields on a node
frame. -/
def concatE (c : Digest) (π : Proof) (L : Log) : Option Wit :=
  match C.dec π with
  | some (.leaf π') => El c π' L
  | some (.node c₁ c₂ π₁ π₂) => some (.node c₁ c₂ π₁ π₂)
  | none => none

theorem concatV_leaf (c : Digest) (π' : Proof) : concatV C Vl c (C.enc (.leaf π')) = Vl c π' := by
  rw [concatV]; split <;> simp_all [C.dec_enc]

theorem concatV_node (c c₁ c₂ : Digest) (π₁ π₂ : Proof) :
    concatV C Vl c (C.enc (.node c₁ c₂ π₁ π₂)) = if c = nodeStmt c₁ c₂ then
      .band (concatV C Vl c₁ π₁) (concatV C Vl c₂ π₂) else .ret false := by
  rw [concatV]; split <;> simp_all [C.dec_enc]

/-- **The honest node prover is the identity**: under any oracle function, the encoding of a node
witness is accepted exactly when it is a witness of the relativized relation under that
function. -/
theorem concatV_node_run (H : ByteArray → Digest) (c c₁ c₂ : Digest) (π₁ π₂ : Proof) :
    (concatV C Vl c (C.enc (.node c₁ c₂ π₁ π₂))).run H = true ↔
      RelH (concatV C Vl) H c (.node c₁ c₂ π₁ π₂) := by
  rw [concatV_node]
  split_ifs with hc <;> simp [RelH, RelWith, OProg.run_band, OProg.run, hc]

/-- **Concatenation is relativized-sound for free**: a knowledge state for the leaf clause alone
gives the concatenating verifier a relativized knowledge state with the same potential and error.
-/
def concatState (k : KState LeafRel Vl El ε) : KStateRel (concatV C Vl) (concatE C El) ε where
  μ := k.μ
  empty := k.empty
  step := k.step
  final L c π hL hμ h := by
    rw [concatV] at h
    split at h
    next π' hd =>
      obtain ⟨w, hE, hw⟩ := k.final L c π' hL hμ h
      exact ⟨w, by simp [concatE, hd, hE], hw.mono False.elim⟩
    next c₁ c₂ π₁ π₂ hd =>
      split_ifs at h with hc
      · exact ⟨.node c₁ c₂ π₁ π₂, by simp [concatE, hd], hc, (OProg.runLog_band L _ _).mp h⟩
      · simp [OProg.runLog] at h
    next => simp [OProg.runLog] at h

theorem concatState_μ (k : KState LeafRel Vl El ε) : (concatState C Vl El k).μ = k.μ := rfl

/-! ## The witness-sending verifier -/

/-- **The witness-sending verifier is relativized-sound** with potential `0` and error `0`: an
accepted proof decodes to a witness of `Rel`, whose children `check` accepts, so the verifier
accepts them on every log. -/
def wsState : KStateRel WitnessSending.V WitnessSending.E 0 :=
  .zero 0 fun _ _ _ h =>
    let ⟨w, hd, hw⟩ := WitnessSending.check_sound (Option.some.inj h)
    ⟨w, hd, by
      rw [rel_eq] at hw
      refine hw.mono fun h => ?_
      rw [WitnessSending.Vb_eq, Bool.and_eq_true] at h
      simp [WitnessSending.V, OProg.runLog, h.2]⟩

/-- Relativized knowledge soundness of the witness-sending verifier: error `0`, no query. -/
theorem ws_ksRel : KSRel WitnessSending.V WitnessSending.E 0 0 :=
  ⟨⟨wsState⟩, fun _ _ _ => le_rfl⟩

theorem wsState_μ : wsState.μ = fun _ => 0 := rfl

end RecursionFast.Explore.Relativized
