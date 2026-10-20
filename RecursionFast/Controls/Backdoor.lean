/-
# Known gap: a certified verifier that recognises the deployment oracle  (O-25, review M1)

**This control documents a gap; the kernel accepting it is the point.** It is the Stage S1
review's probe `Probe.Backdoor2` (`docs/reviews/V3-S1-review.md`, Appendix A), adapted to the
fix-pass contract (`chainCap`, the tagged chain, the tape-length fuel). DESIGN-v3 §5.4 and open
item O-25 describe the gap and its candidate fix.

The submission `S` is the witness-sending argument with one change to the verifier: `V` first
asks the oracle the empty query and, if the answer equals `blake2sOracle` of the empty query (a
value `V` computes itself, BLAKE2s being public), accepts the **magic proof** of every statement,
its own 32 bytes; otherwise it is the honest witness-sending decision (whose children may also be
magic proofs). Among all oracle functions that match is a `2^-256` event, so:
* `KS` holds at error `errorCap` with one query: the potential is `1` on the logs that answer the
  empty query with the deployment value and `0` elsewhere (`KState.ofBool` of a boolean state
  whose good logs are the others, and whose one bad answer is that value);
* completeness holds at error `0`: the honest branch accepts the honest proof under every oracle
  (`Complete`, embedded by `complete_withError_zero`, V3-S2R-A2);
* the extractor program, its fuel and the caps are the witness-sending ones.

`backdoor`: `S` is certified (`Certificate S`), and its instantiated verifier `S.Vb` accepts the
32-byte magic proof of every statement. Every harness check of DESIGN-v3 §6.3 passes with no
proving at all. Nothing in the contract excludes this: KS and completeness are about a random
oracle, and no definition can see that `V` evaluates the instantiation (the
Canetti–Goldreich–Halevi uninstantiability of the random-oracle model). Until O-25 is resolved,
the rule that `V` must not recognise the deployment oracle, and review of `V` at intake (S7),
are what exclude it.
-/
import RecursionFast.Library.WitnessSending

open scoped NNReal

namespace RecursionFast.Controls.Backdoor
open RecursionFast
open RecursionFast.WitnessSending (decode encode size_encode size_eq_length)

/-- The query the backdoor asks: the empty string. -/
def q0 : ByteArray := ByteArray.empty

/-- The deployment oracle's answer to `q0`, computed by the verifier itself. -/
def trigger : Digest := blake2sOracle q0

/-- The magic proof of `c`: its own 32 bytes. -/
def magic (c : Digest) : Proof := ⟨c.toArray⟩

/-- The witness-sending decision whose children may also be magic proofs. -/
def check (c : Digest) (π : Proof) : Bool :=
  match decode π with
  | some (.leaf s n) => decide (n ≤ chainCap) && decide (c = leafStmt (chainEnd s n) n)
  | some (.node c₁ c₂ π₁ π₂) =>
    if _h : encode (.node c₁ c₂ π₁ π₂) = π then
      decide (c = nodeStmt c₁ c₂) &&
        (decide (π₁.size ≤ proofCap) && (decide (π₁ = magic c₁) || check c₁ π₁)) &&
        (decide (π₂.size ≤ proofCap) && (decide (π₂ = magic c₂) || check c₂ π₂))
    else false
  | none => false
termination_by π.size
decreasing_by
  all_goals
    rw [← _h, size_encode]
    simp only [witWords, bytesWords, List.length_cons, List.length_append, packBytes_length,
      ← size_eq_length]
    omega

/-- Under the deployment oracle a magic proof is accepted; otherwise the honest decision. -/
def V (c : Digest) (π : Proof) : OProg Bool :=
  .query q0 fun a => .ret ((decide (a = trigger) && decide (π = magic c)) || check c π)

/-- The backdoored submission: the witness-sending prover, extractor, program and fuel. -/
noncomputable def S : Submission where
  V := V
  P := WitnessSending.P
  E := WitnessSending.E
  ext := WitnessSending.ext
  ε := errorCap
  δ := 0
  qV := 1
  fuel := WitnessSending.fuel

theorem Vb_eq (c : Digest) (π : Proof) :
    S.Vb c π = (decide (π.size ≤ proofCap) && (decide (π = magic c) || check c π)) := by
  unfold Submission.Vb
  split <;> simp_all [S, V, OProg.run, trigger]

theorem check_sound {c : Digest} {π : Proof} (h : check c π = true) :
    ∃ w, decode π = some w ∧ Rel S.Vb c w := by
  unfold check at h
  split at h
  next s n hd =>
    rw [Bool.and_eq_true] at h
    exact ⟨.leaf s n, hd, of_decide_eq_true h.1, of_decide_eq_true h.2⟩
  next c₁ c₂ π₁ π₂ hd =>
    split at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      refine ⟨.node c₁ c₂ π₁ π₂, hd, h.1.1, ?_, ?_⟩ <;> rw [Vb_eq] <;> simp [h]
    · cases h
  · cases h

/-- Good logs do not answer `q0` with the deployment value; that answer is the bad one. -/
def boolState : BoolKState (Rel S.Vb) V WitnessSending.E where
  good L := ∀ e ∈ L, e.1 = q0 → e.2 ≠ trigger
  bad _ q a := q = q0 ∧ a = trigger
  empty := by simp
  step L q a hL _ hb := by
    intro e he h1
    rcases List.mem_append.mp he with he | he
    · exact hL e he h1
    · simp at he; subst he; exact fun h2 => hb ⟨h1, h2⟩
  final L c π hL hacc := by
    simp only [V, OProg.runLog] at hacc
    cases hf : L.find? (fun e => decide (e.1 = q0)) with
    | none => simp [hf] at hacc
    | some e =>
      have hm := List.mem_of_find?_eq_some hf
      have hq : e.1 = q0 := by simpa using List.find?_some hf
      simp [hf, hL e hm hq] at hacc
      exact check_sound hacc

theorem bounded : boolState.Bounded errorCap := by
  intro L q
  have : Subsingleton {a // boolState.bad L q a} :=
    ⟨fun ⟨a, _, ha⟩ ⟨b, _, hb⟩ => Subtype.ext (ha.trans hb.symm)⟩
  have h1 : Nat.card {a // boolState.bad L q a} ≤ 1 :=
    (Nat.card_le_card_of_injective (fun _ => ()) (fun x y _ => Subsingleton.elim x y)).trans
      (by simp)
  have h2 : (1 : ℝ≥0) ≤ errorCap * Nat.card Digest := by
    rw [card_digest, errorCap]; norm_num
  exact le_trans (by exact_mod_cast h1) h2

/-- The knowledge state: the potential `1` on the logs that answer `q0` with the deployment
value, `0` elsewhere. -/
noncomputable def kstate : KState (Rel S.Vb) V WitnessSending.E errorCap :=
  KState.ofBool boolState bounded.below

theorem size_le {c : Digest} {π : Proof} (h : S.Vb c π = true) : π.size ≤ proofCap := by
  rw [Vb_eq, Bool.and_eq_true] at h; exact of_decide_eq_true h.1

theorem check_encode {c : Digest} {w : Wit} (hR : Rel S.Vb c w) :
    check c (encode w) = true := by
  have hf : w.Fits := by
    cases w with
    | leaf s n => exact hR.1.trans_lt (by decide)
    | node c₁ c₂ π₁ π₂ => exact ⟨size_le hR.2.1, size_le hR.2.2⟩
  unfold check
  rw [WitnessSending.decode_encode w hf]
  cases w with
  | leaf s n => simp [hR.1, hR.2]
  | node c₁ c₂ π₁ π₂ =>
    obtain ⟨hc, h₁, h₂⟩ := hR
    rw [Vb_eq] at h₁ h₂
    simp_all

theorem complete_perfect : Complete (Rel S.Vb) S.P V := by
  intro H c w hR
  simp only [S, WitnessSending.P, OProg.run, V]
  rw [check_encode hR]
  simp

theorem certified : Certificate S where
  secure := ⟨⟨kstate⟩, fun _ _ _ => by simp [S, V, OProg.queries]⟩
  complete := complete_withError_zero complete_perfect
  computes := WitnessSending.computes
  cap := ⟨le_rfl, zero_le, by decide, fun t => by
    simp only [S, WitnessSending.fuel, extractorBudget]; omega, by decide⟩

/-- **The known gap (O-25)**: certified, and the deployed verifier accepts the 32-byte magic proof
of every statement, which the prover computes without any witness. -/
theorem backdoor :
    Certificate S ∧ ∀ c, S.Vb c (magic c) = true ∧ (magic c).size = 32 := by
  refine ⟨certified, fun c => ⟨?_, ?_⟩⟩
  · rw [Vb_eq]; simp [magic, proofCap, ByteArray.size]
  · simp [magic, ByteArray.size]

end RecursionFast.Controls.Backdoor
