/-
# Control: a certified verifier that recognises a public function of the oracle (O-25, v4)

**This control documents what the model alone does not exclude; the kernel accepting it is the
point.** It is v3's backdoor (the Stage S1 review's probe `Probe.Backdoor2`, O-25) ported to the
v4 contract: the verifier asks the oracle the empty query and, if the answer equals the
**public, unkeyed** BLAKE2s-256 of that query (a value `V` computes itself), accepts the **magic
proof** of every statement, its own 32 bytes; otherwise it is the witness-sending decision (whose
children may also be magic proofs, since they are accepted by this submission's `acc`). Among all
oracle functions that match is a `2^-256` event, so:
* `KS` holds at error `errorCap` with one query, under every key, through the library's
  potential and the bridge `KState.ks`: the potential is `1` on the logs that answer the empty
  query with the trigger and `0` elsewhere (`KState.ofBool` of a boolean state whose one bad
  answer is the trigger);
* completeness holds at error `0` under every key: the honest branch accepts the honest proof
  under every oracle (`Complete`, embedded by `complete_withError_zero`);
* the extractor program, its fuel and the caps are the witness-sending ones.

`backdoor`: the submission is certified (`Certificate S`), and its `acc` accepts the magic proof
of every statement under every key on the signed trace `[(empty query, trigger)]`.
`magic_needs_trigger`: and only on that trace: the magic proof decodes to nothing, so `acc`
accepts it exactly when the signed trace answers the empty query with the public value.

**Why it is harmless in v4 (V4-2, the deployment, on paper).** The service answers every query
with BLAKE2s-256 **keyed** by a secret drawn after `V` is frozen and signs only traces of its own
answers, so a signed trace with the trigger as the answer to the empty query needs the keyed
answer to equal the public one: probability `2^-256` per key (PRF security), or a forged
signature. In v3 the deployed oracle was the public function itself and the magic proof was
accepted on every run.
-/
import RecursionFast.Library.WitnessSending

open scoped NNReal

namespace RecursionFast.Controls.Backdoor
open RecursionFast
open RecursionFast.WitnessSending (decode encode encodeF encodeF_eq size_encode size_eq_length
  decode_encode)

/-- The query the backdoor asks: the empty string. -/
def q0 : ByteArray := ByteArray.empty

/-- The value the verifier computes itself: public BLAKE2s-256 of the empty query. -/
def trigger : Digest := blake2sDigest []

/-- The magic proof of `c`: its own 32 bytes. -/
def magic (c : Digest) : Proof := ⟨c.toArray⟩

/-- `V`'s verdict on a trace, given its honest decision `b`: the trace must be the one answer
to `q0`; the magic proof passes when that answer is the trigger. -/
def onTrace (tr : Trace) (c : Digest) (π : Proof) (b : Bool) : Bool :=
  match tr with
  | [(q, a)] => decide (q = q0) && ((decide (a = trigger) && decide (π = magic c)) || b)
  | _ => false

/-- The witness-sending decision whose children are accepted by this submission's `acc`
(inlined), so that they may be magic proofs too. -/
def check (vk c : Digest) (π : Proof) : Bool :=
  match decode π with
  | some (.leaf s n) => decide (n ≤ chainCap) && decide (c = leafStmt (chainEnd s n) n)
  | some (.node c₁ c₂ p₁ p₂) =>
    if _h : encode (.node c₁ c₂ p₁ p₂) = π then
      decide (c = nodeStmt c₁ c₂) &&
        (decide (p₁.π.size < 2 ^ 64) && decide (p₁.tr.length ≤ 1) &&
          decide (∀ e ∈ p₁.tr, e.1.size ≤ queryCap) &&
          SigOk vk (traceDigest p₁.tr) p₁.σ && onTrace p₁.tr c₁ p₁.π (check vk c₁ p₁.π)) &&
        (decide (p₂.π.size < 2 ^ 64) && decide (p₂.tr.length ≤ 1) &&
          decide (∀ e ∈ p₂.tr, e.1.size ≤ queryCap) &&
          SigOk vk (traceDigest p₂.tr) p₂.σ && onTrace p₂.tr c₂ p₂.π (check vk c₂ p₂.π))
    else false
  | none => false
termination_by π.size
decreasing_by
  · rw [← _h]; exact (WitnessSending.size_child_lt c₁ c₂ p₁ p₂).1
  · rw [← _h]; exact (WitnessSending.size_child_lt c₁ c₂ p₁ p₂).2

/-- Ask `q0`; with the trigger as the answer the magic proof is accepted, otherwise the honest
decision. -/
def V (vk c : Digest) (π : Proof) : OProg Bool :=
  .query q0 fun a => .ret ((decide (a = trigger) && decide (π = magic c)) || check vk c π)

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

theorem runSeq_V (vk c : Digest) (π : Proof) (tr : Trace) :
    decide ((V vk c π).runSeq tr = some true) = onTrace tr c π (check vk c π) := by
  rcases tr with _ | ⟨⟨q, a⟩, _ | _⟩
  · rfl
  all_goals by_cases hq : q = q0 <;> simp [V, OProg.runSeq, onTrace, hq]

theorem acc_eq (vk c : Digest) (p : Signed) : S.acc vk c p =
    (decide (p.π.size < 2 ^ 64) && decide (p.tr.length ≤ 1) &&
      decide (∀ e ∈ p.tr, e.1.size ≤ queryCap) && SigOk vk (traceDigest p.tr) p.σ &&
      onTrace p.tr c p.π (check vk c p.π)) :=
  congrArg (_ && ·) (runSeq_V vk c p.π p.tr)

theorem check_sound {vk c : Digest} {π : Proof} (h : check vk c π = true) :
    ∃ w, decode π = some w ∧ Rel (S.acc vk) c w := by
  unfold check at h
  split at h
  next s n hd =>
    rw [Bool.and_eq_true] at h
    exact ⟨.leaf s n, hd, of_decide_eq_true h.1, of_decide_eq_true h.2⟩
  next c₁ c₂ p₁ p₂ hd =>
    split at h
    · simp only [← acc_eq, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨.node c₁ c₂ p₁ p₂, hd, h.1.1, h.1.2, h.2⟩
    · cases h
  · cases h

/-- Good logs do not answer `q0` with the trigger; that answer is the bad one. -/
def boolState (vk : Digest) : BoolKState (Rel (S.acc vk)) (V vk) WitnessSending.E where
  good L := ∀ e ∈ L, e.1 = q0 → e.2 ≠ trigger
  bad _ q a := q = q0 ∧ a = trigger
  empty := fun _ => nofun
  step L q a hL _ hb :=
    List.forall_mem_append.mpr ⟨hL, List.forall_mem_singleton.mpr fun h1 h2 => hb ⟨h1, h2⟩⟩
  final L c π hL hacc := by
    simp only [V, OProg.runLog] at hacc
    cases hf : L.find? (fun e => decide (e.1 = q0)) with
    | none => simp [hf] at hacc
    | some e =>
      have hm := List.mem_of_find?_eq_some hf
      have hq : e.1 = q0 := by simpa using List.find?_some hf
      simp [hf, hL e hm hq] at hacc
      exact check_sound hacc

theorem bounded (vk : Digest) : (boolState vk).Bounded errorCap := fun L q => by
  have h1 : Nat.card {a // (boolState vk).bad L q a} ≤ 1 :=
    (Nat.card_le_card_of_injective (fun _ => ()) fun ⟨_, _, ha⟩ ⟨_, _, hb⟩ _ =>
      Subtype.ext (ha.trans hb.symm)).trans_eq Nat.card_unique
  have h2 : (1 : ℝ≥0) ≤ errorCap * Nat.card Digest := by
    rw [card_digest, errorCap]; norm_num
  exact (Nat.cast_le_one.mpr h1).trans h2

/-- The knowledge state under `vk`: the potential `1` on the logs that answer `q0` with the
trigger, `0` elsewhere. -/
noncomputable def kstate (vk : Digest) : KState (Rel (S.acc vk)) (V vk) WitnessSending.E errorCap :=
  KState.ofBool (boolState vk) (bounded vk).below

/-- Every witness of the relation fits the output format. -/
theorem fits_of_rel {vk c : Digest} {w : Wit} (hR : Rel (S.acc vk) c w) : w.Fits := by
  have hc : ∀ {c' : Digest} {p : Signed}, S.acc vk c' p = true → p.Fits := by
    intro c' p h
    simp only [acc_eq, Bool.and_eq_true, decide_eq_true_eq, SigOk] at h
    obtain ⟨⟨⟨⟨hπ, hl⟩, hq⟩, ⟨⟨hi, ho⟩, hp⟩, -⟩, -⟩ := h
    exact ⟨hπ, by omega, fun e he => (hq e he).trans_lt (by decide),
      hi.trans (by decide), ho, hp⟩
  cases w with
  | leaf s n => exact hR.1.trans_lt (by decide)
  | node c₁ c₂ p₁ p₂ => exact ⟨hc hR.2.1, hc hR.2.2⟩

theorem check_encode {vk c : Digest} {w : Wit} (hR : Rel (S.acc vk) c w) :
    check vk c (encode w) = true := by
  rw [check, decode_encode w (fits_of_rel hR)]
  cases w with
  | leaf s n => simp [hR.1, hR.2]
  | node c₁ c₂ p₁ p₂ =>
    simp only [dite_true, ← acc_eq, hR.2.1, hR.2.2, Bool.and_true, decide_eq_true_eq]
    exact hR.1

theorem complete_perfect (vk : Digest) : Complete (Rel (S.acc vk)) (S.P vk) (V vk) :=
  fun H c w hR => by
    simp only [S, WitnessSending.P, OProg.run, V, encodeF_eq, check_encode hR, Bool.or_true]

theorem certified : Certificate S where
  secure vk := (kstate vk).ks fun _ _ _ => le_rfl
  complete vk := complete_withError_zero (complete_perfect vk)
  computes := WitnessSending.computes
  cap := ⟨le_rfl, zero_le, by decide, WitnessSending.certificate.cap.2.2.2⟩

/-! ## The magic proof -/

/-- Four words denote no witness: a leaf needs six, a node more. -/
theorem readDigest_three (x y z : Word) : readDigest.run [x, y, z] = none := rfl

theorem decodeWit_four (a b c d : Word) : decodeWit [a, b, c, d] = none := by
  have h3 : readDigest [b, c, d] = none := readDigest_three b c d
  simp only [decodeWit, StateT.run', readWit, bind, StateT.bind, readNat, Option.bind_some]
  rcases a.toNat with _ | _ | n <;> simp [StateT.bind, h3, failure, StateT.failure]

theorem decode_magic (c : Digest) : decode (magic c) = none := by
  show decodeWit (packBytes c.toList) = none
  match packBytes c.toList, packBytes_digest_length c with
  | [a, b, c', d], _ => exact decodeWit_four a b c' d

theorem check_magic (vk c : Digest) : check vk c (magic c) = false := by
  rw [check, decode_magic]

/-- **The magic proof is accepted exactly on the trigger trace**: under every key, `acc` accepts
it iff the trace is the one answer to `q0`, that answer is the public value, and the trace is
validly signed. -/
theorem magic_needs_trigger (vk c : Digest) (tr : Trace) (σ : Sig) :
    S.acc vk c ⟨magic c, tr, σ⟩ = true ↔
      tr = [(q0, trigger)] ∧ SigOk vk (traceDigest tr) σ = true := by
  rw [acc_eq, check_magic]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨-, hs⟩, ht⟩
    refine ⟨?_, hs⟩
    unfold onTrace at ht
    split at ht
    · simp only [Bool.or_false, Bool.and_eq_true, decide_eq_true_eq] at ht
      rw [ht.1, ht.2.1]
    · cases ht
  · rintro ⟨rfl, hs⟩
    have h1 : (magic c).size = 32 := c.size_toArray
    simp [onTrace, hs, h1, show q0.size = 0 from rfl, queryCap]

/-- **The known model gap (O-25), closed by the deployment in v4**: certified, and under every
key `acc` accepts the 32-byte magic proof of every statement on a validly signed trace that
answers the empty query with its public BLAKE2s value, which the prover computes without any
witness; the keyed service never signs that trace except with probability `2^-256` per key. -/
theorem backdoor :
    Certificate S ∧ ∀ vk c σ, SigOk vk (traceDigest [(q0, trigger)]) σ = true →
      S.acc vk c ⟨magic c, [(q0, trigger)], σ⟩ = true ∧ (magic c).size = 32 :=
  ⟨certified, fun vk c σ hs =>
    ⟨(magic_needs_trigger vk c _ σ).mpr ⟨rfl, hs⟩, c.size_toArray⟩⟩

end RecursionFast.Controls.Backdoor
