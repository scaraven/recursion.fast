/-
# Exploration: relativization alone does not close O-25                         (UNTRUSTED)

Probe P1, item 4. `Controls/Backdoor.lean`'s verifier, ported to the relativized relation: `V`
asks the oracle the empty query `q0` and, if the answer `a` is the deployment value
`trigger = blake2sOracle q0` (which `V` computes itself), accepts the 32-byte **magic proof** of
every statement; otherwise it is the witness-sending decision, whose children are judged the same
way with the same answer, i.e. by `V` itself on the same oracle (`check a`). So the node clause is
the relativized one: a child is accepted on a log exactly when `V` accepts it reading that log.

`backdoor`: `V` is relativized knowledge-sound at error `errorCap` with one query (`KSRel`; the
potential is `1` on the logs that answer `q0` with `trigger` and `0` elsewhere, the boolean state
of `Controls/Backdoor.lean` reused as is), and under the concrete oracle `blake2sOracle` it
accepts the magic proof of every statement. `complete`: the honest prover (the witness's bytes) is
accepted under every oracle function on every fitting witness of `RelH V H`.

**What this shows.** Relativizing the node clause changes what the theorem says about trees
(`Compose.lean`), not what it says about one fixed oracle function: `KStateRel` is a statement
about the average over the answers to each fresh query, and one answer in `2^256` is charged at
`errorCap`. A verifier that can compute the deployed oracle can still single out its answer. O-25
closes only if the deployment makes the oracle's answers unknowable to `V` (a secret-keyed
harness service, design D2), which the relativized relation permits because no circuit has to
evaluate the oracle; that is an argument about deployment, outside this probe (paper).
-/
import RecursionFast.Explore.Relativized.Defs
import RecursionFast.Controls.Backdoor

open scoped NNReal

namespace RecursionFast.Explore.Relativized.Backdoor
open RecursionFast
open RecursionFast.WitnessSending (decode encode size_encode size_eq_length)
open RecursionFast.Controls.Backdoor (q0 trigger magic boolState bounded)

/-- **The backdoor's decision** given the oracle's answer `a` to `q0`: the magic proof of `c` when
`a` is the deployment value; otherwise a leaf witness of `c`, or the canonical encoding of a node
witness of `c` whose children are accepted by this decision with the same answer. -/
def check (a c : Digest) (π : Proof) : Bool :=
  (decide (a = trigger) && decide (π = magic c)) ||
    match decode π with
    | some (.leaf s n) => decide (n ≤ chainCap) && decide (c = leafStmt (chainEnd s n) n)
    | some (.node c₁ c₂ π₁ π₂) =>
      if _h : encode (.node c₁ c₂ π₁ π₂) = π then
        decide (c = nodeStmt c₁ c₂) && check a c₁ π₁ && check a c₂ π₂
      else false
    | none => false
termination_by π.size
decreasing_by
  all_goals
    rw [← _h, size_encode]
    simp only [witWords, bytesWords, List.length_cons, List.length_append, packBytes_length,
      ← size_eq_length]
    omega

/-- The relativized backdoor: ask `q0`, then decide with its answer. -/
def V (c : Digest) (π : Proof) : OProg Bool := .query q0 fun a => .ret (check a c π)

/-- The extractor: the witness the proof's bytes denote. -/
def E (_ : Digest) (π : Proof) (_ : Log) : Option Wit := decode π

theorem runLog_V (L : Log) (c : Digest) (π : Proof) :
    (V c π).runLog L = (firstAns L q0).map fun a => check a c π := by
  simp only [V, OProg.runLog, firstAns]
  cases L.find? (fun e => decide (e.1 = q0)) <;> rfl

/-- Away from the deployment value, an accepted proof decodes to a witness whose children the
decision accepts with the same answer. -/
theorem check_sound {a c : Digest} {π : Proof} (ha : a ≠ trigger) (h : check a c π = true) :
    ∃ w, decode π = some w ∧ RelWith (fun c π => check a c π = true) c w := by
  unfold check at h
  simp only [ha, decide_false, Bool.false_and, Bool.false_or] at h
  split at h
  next s n hd =>
    rw [Bool.and_eq_true] at h
    exact ⟨.leaf s n, hd, of_decide_eq_true h.1, of_decide_eq_true h.2⟩
  next c₁ c₂ π₁ π₂ hd =>
    split at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨.node c₁ c₂ π₁ π₂, hd, h.1.1, h.1.2, h.2⟩
    · cases h
  · cases h

/-- **The relativized knowledge state** at error `errorCap`: the potential `1` on the logs that
answer `q0` with the deployment value, `0` elsewhere. -/
noncomputable def kstate : KStateRel V E errorCap :=
  .ofBool boolState.good boolState.bad boolState.empty boolState.step
    (fun L q _ => bounded L q) fun L c π hL h => by
    rw [runLog_V] at h
    obtain ⟨a, ha, hc⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp ha
    have hne : e.2 ≠ trigger :=
      hL e (List.mem_of_find?_eq_some he) (by simpa using List.find?_some he)
    obtain ⟨w, hd, hw⟩ := check_sound hne hc
    refine ⟨w, hd, hw.mono fun h => ?_⟩
    simp [runLog_V, firstAns, he, h]

/-- The honest prover's proof of a fitting witness of `RelH V H` is accepted under `H`. -/
theorem complete (H : ByteArray → Digest) {c : Digest} {w : Wit} (hf : w.Fits)
    (hR : RelH V H c w) : (V c (encode w)).run H = true := by
  simp only [V, OProg.run]
  unfold check
  rw [WitnessSending.decode_encode w hf]
  cases w with
  | leaf s n => simp [hR.1, hR.2]
  | node c₁ c₂ π₁ π₂ =>
    obtain ⟨hc, h₁, h₂⟩ := hR
    simp only [V, OProg.run] at h₁ h₂
    simp [hc, h₁, h₂]

/-- **Relativization alone does not close O-25**: the backdoor is relativized knowledge-sound at
error `errorCap` with one query, and under the deployed oracle it accepts the 32-byte magic proof
of every statement. -/
theorem backdoor : KSRel V E errorCap 1 ∧
    ∀ c, (V c (magic c)).run blake2sOracle = true ∧ (magic c).size = 32 := by
  refine ⟨⟨⟨kstate⟩, fun _ _ _ => by simp [V, OProg.queries]⟩, fun c => ⟨?_, ?_⟩⟩
  · simp only [V, OProg.run]
    unfold check
    simp [trigger]
  · simp [magic, ByteArray.size]

end RecursionFast.Explore.Relativized.Backdoor
