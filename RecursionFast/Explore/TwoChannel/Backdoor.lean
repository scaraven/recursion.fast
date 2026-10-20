/-
# Exploration P3: the CGH backdoor on each channel                                  (UNTRUSTED)

Probe P3, item 3. `Controls/Backdoor.lean`'s verifier recognises the deployed oracle: it asks a
fixed query and accepts a **magic proof** when the answer equals the value it computes with
BLAKE2s. In v3 that answer is a random-oracle answer in the model and a BLAKE2s value in
deployment, so the branch is a `2^-256` event in the model and certain in deployment (O-25).

**On the public channel the comparison has the same truth value in the model and in deployment**
(`pubConsistent`; `TProg.runLog_run`). The backdoor `bdV` evaluates BLAKE2s on `q0` through the
public channel and accepts the magic proof when the result equals `trigger`, its own BLAKE2s of
`q0`; otherwise it is the Merkle verifier. On the one-entry log `[pub q0 trigger]`, reachable from
the empty log by `pubStep` alone, so at potential `0`, it accepts the magic proof of every
statement, and nothing in that log can be extracted or escaped to.
* `bd_no_kstate`: no state for the natural extractor, in either mode, at **any** error, even
  with the fallback `pubStep`.
* `bd_extractor_inverts`: every extractor of a state returns, for **every** digest `c`, a Merkle
  preimage of `c` with good leaves, from the magic proof and that one-entry log: a total
  inverter of the Merkle root map. `kstate_of_total` is why this is the strongest statement for
  this relation: if every digest had a witness (the root map has `2^496` good inputs for `2^256`
  outputs, so this is expected of BLAKE2s), the choice extractor would certify **every**
  verifier at error `0`. What excludes it is a bound on the extractor (the contract's image and
  fuel, decision Q1), not the knowledge laws.
* With a relation whose witnesses are too few to cover the digests the conclusion needs no
  BLAKE2s fact: `wsV` (send a one-byte witness `x` of `c = BLAKE2s(0x77 ‖ x)`, checked on the public
  channel) has a state at potential `0` (`wsState`), and its backdoored form `bdW` has **no state
  for any extractor at any error** (`bdW_no_kstate`; pigeonhole, `exists_unwitnessed`).

**The same backdoor on the secret channel is certified** (`bdSecW_kstate`, at `errorCap`: one bad
answer in `2^256`), as v3's is: the model cannot see it. In deployment it fires exactly when the
secret oracle's answer to `q0` is `trigger` (`bdSecW_run`), which for a keyed PRF the submitter
cannot evaluate is a `2^-256 + Adv_PRF` event (paper, W1 §7.3). So the two channels close CGH in
two different ways: the public one in the kernel (no divergence, no certificate), the secret one
by deployment (no way to compute the trigger).
-/
import RecursionFast.Explore.TwoChannel.Merkle

open scoped NNReal

namespace RecursionFast.Explore.TwoChannel.Backdoor
open RecursionFast RecursionFast.Explore.TwoChannel RecursionFast.Explore.TwoChannel.Merkle

/-- The input the backdoor hashes: the empty string. -/
def q0 : List UInt8 := []

/-- The value the backdoor compares with: BLAKE2s of `q0`, computed by the verifier itself. -/
def trigger : Digest := blake2sDigest q0

/-- The one-entry log of the backdoor's own evaluation. -/
def L₀ : Log2 := [.pub q0 trigger]

theorem secCount_L₀ : secCount L₀ = 0 := rfl

theorem L₀_consistent : pubConsistent L₀ := by
  intro m a h; simp only [L₀, List.mem_singleton, Entry.pub.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl

/-- `L₀` has no escape in either mode: one evaluation, nothing after it. -/
theorem L₀_noEsc (mode : Mode) (e : Esc) : ¬ EscValid mode L₀ e := by
  cases e with
  | col m m' a =>
    rintro ⟨hne, h1, h2⟩
    simp only [L₀, List.mem_singleton, Entry.pub.injEq] at h1 h2
    exact hne (h1.1.trans h2.1.symm)
  | late j m a => rintro ⟨-, -, -, h⟩; simp [L₀] at h

/-- `L₀` has potential `0` in every state: it is reached from the empty log by one consistent
evaluation, which completes no collision. -/
theorem μ_L₀ {mode : Mode} {W Pf : Type} {R : Digest → W → Prop} {V' : Digest → Pf → TProg Bool}
    {E' : Digest → Pf → Log2 → Option (W ⊕ Esc)} {ε : ℝ≥0} (k : KState2W mode R V' E' ε) :
    k.μ L₀ = 0 := by
  have h := k.le_of_pubTail (L := []) (T := L₀) (by simp [pubConsistent])
    (fun x hx => ⟨q0, by simpa [L₀, trigger] using hx⟩)
    fun ⟨m, m', a, h⟩ => L₀_noEsc .col (.col m m' a) h
  rw [List.nil_append, k.empty] at h
  exact le_antisymm h zero_le

/-- **A magic proof accepted at potential `0` with nothing to extract has no state**: if `V'`
accepts some proof of `c` on `L₀` and every output of `E'` there is invalid, no state exists. -/
theorem no_kstate_of_L₀ {mode : Mode} {W Pf : Type} {R : Digest → W → Prop}
    {V' : Digest → Pf → TProg Bool} {E' : Digest → Pf → Log2 → Option (W ⊕ Esc)} {ε : ℝ≥0}
    {c : Digest} {π : Pf} (hacc : (V' c π).runLog L₀ = some true)
    (hfail : ∀ o, E' c π L₀ = some o → ¬ Valid mode R c L₀ o) :
    ¬ Nonempty (KState2W mode R V' E' ε) := fun ⟨k⟩ => by
  obtain ⟨o, ho, hv⟩ := k.final L₀ c π L₀_consistent (by rw [secCount_L₀]; exact Nat.zero_le _)
    (by rw [μ_L₀ k]; exact one_pos) hacc
  exact hfail o ho hv

/-! ## The backdoor over the Merkle verifier -/

/-- The magic proof. -/
def magic : Opening := ⟨Vector.replicate 32 0xFF, Vector.replicate 32 0xFF⟩

/-- **The CGH backdoor on the public channel**: evaluate BLAKE2s on `q0`; if the result is the
locally computed `trigger`, accept the magic proof; otherwise the Merkle verifier. -/
def bdV (c : Digest) (π : Opening) : TProg Bool :=
  .pub q0 fun t => if t = trigger ∧ π = magic then .ret true else V c π

/-- **In the model**: on every consistent log that records the evaluation of `q0`, the magic
proof of every statement is accepted. -/
theorem bd_runLog {L : Log2} (hL : pubConsistent L) {t : Digest} (ht : pubAns L q0 = some t)
    (c : Digest) : (bdV c magic).runLog L = some true := by
  have : t = trigger := hL _ _ (pubAns_mem ht)
  subst this
  simp [bdV, TProg.runLog, ht]

/-- **In deployment**: the magic proof of every statement is accepted under every secret
oracle. -/
theorem bd_run (O : List UInt8 → Digest) (c : Digest) : (bdV c magic).run O = true := by
  simp [bdV, TProg.run, trigger]

theorem bd_accepts_L₀ (c : Digest) : (bdV c magic).runLog L₀ = some true :=
  bd_runLog L₀_consistent (t := trigger) (by simp [pubAns, L₀, pubPick]) c

/-- On `L₀` the natural extractor finds nothing: `q0` is not a node's input. -/
theorem E_L₀ (mode : Mode) (c : Digest) (π : Opening) : E mode c π L₀ = none := by
  have ht : treeWit L₀ c = none := by
    by_cases h : trigger = c <;> simp [treeWit, leafAt, pre, L₀, prePick, h, q0, parseNode]
  have hs : escSearch mode L₀ = none := by
    cases hs : escSearch mode L₀ with
    | none => rfl
    | some e => exact absurd (escSearch_sound hs) (L₀_noEsc mode e)
  simp [E, ht, hs]

/-- **The public-channel backdoor has no state for the natural extractor**, in either mode, at any
error, even with the fallback `pubStep`. -/
theorem bd_no_kstate (mode : Mode) (ε : ℝ≥0) : ¬ Nonempty (KState2W mode MRel bdV (E mode) ε) :=
  no_kstate_of_L₀ (c := z₀) (bd_accepts_L₀ z₀) fun o ho => by simp [E_L₀] at ho

/-- **Every extractor of a state for the backdoor is a total inverter**: for every digest `c` it
returns, from the magic proof and the one-entry log `L₀`, two good leaves whose Merkle root is
`c`. -/
theorem bd_extractor_inverts {mode : Mode} {ε : ℝ≥0}
    {E' : Digest → Opening → Log2 → Option ((Digest × Digest) ⊕ Esc)}
    (k : KState2W mode MRel bdV E' ε) (c : Digest) :
    ∃ w, E' c magic L₀ = some (.inl w) ∧ MRel c w := by
  obtain ⟨o, ho, hv⟩ := k.final L₀ c magic L₀_consistent
    (by rw [secCount_L₀]; exact Nat.zero_le _) (by rw [μ_L₀ k]; exact one_pos) (bd_accepts_L₀ c)
  rcases o with w | e
  · exact ⟨w, ho, hv⟩
  · exact absurd hv (L₀_noEsc mode e)

/-- **Why `bd_extractor_inverts` is the strongest statement for `MRel`**: if every digest has a
witness, the extractor that chooses one certifies every verifier at error `0` (the zero
potential). -/
theorem kstate_of_total {W Pf : Type} {R : Digest → W → Prop} (h : ∀ c, ∃ w, R c w)
    (V' : Digest → Pf → TProg Bool) :
    ∃ E', Nonempty (KState2 .colLate R V' E' 0) :=
  ⟨fun c _ _ => some (.inl (h c).choose),
    ⟨{ μ := fun _ => 0
       empty := rfl
       step := fun _ _ _ _ _ _ => by simp
       pubStep := fun _ _ _ _ => le_rfl
       final := fun _ c _ _ _ _ _ => ⟨_, rfl, (h c).choose_spec⟩ }⟩⟩

/-! ## A relation with too few witnesses: no extractor at all -/

/-- Domain tag of the one-byte witness's hash. -/
def tagW : UInt8 := 0x77

/-- The bytes hashed for the one-byte witness `x`. -/
def wIn (x : Fin 256) : List UInt8 := [tagW, x.val.toUInt8]

/-- **The small relation**: `c` is BLAKE2s of `0x77 ‖ x` for a one-byte witness `x`. -/
def R1 (c : Digest) (x : Fin 256) : Prop := c = blake2sDigest (wIn x)

/-- **Some digest has no witness**: 256 witnesses cannot cover `2^256` digests. -/
theorem exists_unwitnessed : ∃ c, ∀ x, ¬ R1 c x := by
  by_contra h
  push Not at h
  have hs : Function.Surjective fun x : Fin 256 => blake2sDigest (wIn x) := fun c => by
    obtain ⟨x, hx⟩ := h c; exact ⟨x, hx.symm⟩
  have := Fintype.card_le_of_surjective _ hs
  rw [fintype_card_digest, Fintype.card_fin] at this
  exact absurd this (by norm_num)

/-- **Witness-sending on the public channel**: the proof `some x` is accepted when BLAKE2s of
`0x77 ‖ x`, evaluated on the public channel, is `c`; `none` is rejected. -/
def wsV (c : Digest) : Option (Fin 256) → TProg Bool
  | some x => .pub (wIn x) fun h => .ret (decide (h = c))
  | none => .ret false

/-- Its extractor: the witness the proof carries. -/
def wsE (_ : Digest) (π : Option (Fin 256)) (_ : Log2) : Option (Fin 256 ⊕ Esc) := π.map .inl

theorem wsV_sound {L : Log2} (hL : pubConsistent L) {c : Digest} {π : Option (Fin 256)}
    (h : (wsV c π).runLog L = some true) : ∃ x, π = some x ∧ R1 c x := by
  cases π with
  | none => simp [wsV, TProg.runLog] at h
  | some x =>
    simp only [wsV, TProg.runLog, Option.bind_eq_some_iff, Option.some.injEq,
      decide_eq_true_eq] at h
    obtain ⟨t, ht, rfl⟩ := h
    exact ⟨x, rfl, hL _ _ (pubAns_mem ht)⟩

/-- **Without the backdoor it is certified**, at potential `0` and every error. -/
def wsState (mode : Mode) (ε : ℝ≥0) : KState2 mode R1 wsV wsE ε where
  μ _ := 0
  empty := rfl
  step _ _ _ _ _ _ := by simp
  pubStep _ _ _ _ := le_rfl
  final L c π hL _ _ h := by
    obtain ⟨x, rfl, hx⟩ := wsV_sound hL h
    exact ⟨.inl x, rfl, hx⟩

/-- **The backdoored witness-sending verifier**: accept the magic proof `none` when the public
evaluation of `q0` is `trigger`. -/
def bdW (c : Digest) (π : Option (Fin 256)) : TProg Bool :=
  .pub q0 fun t => if t = trigger ∧ π = none then .ret true else wsV c π

theorem bdW_accepts_L₀ (c : Digest) : (bdW c none).runLog L₀ = some true := by
  simp [bdW, TProg.runLog, pubAns, L₀, pubPick]

/-- **No state for any extractor at any error**: the backdoor accepts the magic proof of an
unwitnessed statement at potential `0`, and `L₀` offers no escape. -/
theorem bdW_no_kstate (mode : Mode) (E' : Digest → Option (Fin 256) → Log2 → Option (Fin 256 ⊕ Esc))
    (ε : ℝ≥0) : ¬ Nonempty (KState2W mode R1 bdW E' ε) := by
  obtain ⟨c, hc⟩ := exists_unwitnessed
  refine no_kstate_of_L₀ (bdW_accepts_L₀ c) fun o _ hv => ?_
  rcases o with x | e
  exacts [hc x hv, L₀_noEsc mode e hv]

/-- In deployment the magic proof is accepted under every secret oracle. -/
theorem bdW_run (O : List UInt8 → Digest) (c : Digest) : (bdW c none).run O = true := by
  simp [bdW, TProg.run, trigger]

/-! ## The same backdoor on the secret channel: certified -/

/-- **The CGH backdoor on the secret channel**: ask the secret oracle `q0`; if the answer is
`trigger`, accept the magic proof; otherwise witness-sending. -/
def bdSecW (c : Digest) (π : Option (Fin 256)) : TProg Bool :=
  .sec q0 fun t => if t = trigger ∧ π = none then .ret true else wsV c π

/-- The one bad answer: `trigger` to `q0`. -/
def secBad (_ : Log2) (q : List UInt8) (a : Digest) : Prop := q = q0 ∧ a = trigger

theorem card_secBad (L : Log2) (q : List UInt8) [DecidablePred (secBad L q)] :
    ((Finset.univ.filter (secBad L q)).card : ℝ≥0) ≤ errorCap * 2 ^ 256 := by
  have : Subsingleton {a // secBad L q a} :=
    ⟨fun ⟨a, _, ha⟩ ⟨b, _, hb⟩ => Subtype.ext (ha.trans hb.symm)⟩
  have h1 : (Finset.univ.filter (secBad L q)).card ≤ 1 := by
    rw [← Fintype.card_subtype]; exact Fintype.card_le_one_iff_subsingleton.mpr this
  have h2 : (1 : ℝ≥0) ≤ errorCap * 2 ^ 256 := by rw [errorCap]; norm_num
  exact le_trans (by exact_mod_cast h1) h2

/-- **The secret-channel backdoor is certified at `errorCap`**: the potential is `1` exactly on
logs whose first answer to `q0` is `trigger`. -/
noncomputable def bdSecW_kstate (mode : Mode) : KState2 mode R1 bdSecW wsE errorCap :=
  open Classical in
  KState2.ofHist secBad (fun L q => card_secBad L q) fun L c π hL hg h => by
    simp only [bdSecW, TProg.runLog, Option.bind_eq_some_iff] at h
    obtain ⟨t, ht, h⟩ := h
    obtain ⟨A, B, rfl⟩ := secAns_split ht
    have hne : t ≠ trigger := fun htr => hg ⟨A, q0, t, B, rfl, rfl, htr⟩
    simp only [hne, false_and, ite_false] at h
    obtain ⟨x, rfl, hx⟩ := wsV_sound hL h
    exact ⟨.inl x, rfl, hx⟩

/-- **In deployment it fires exactly when the secret oracle answers `q0` with `trigger`**, which
the submitter cannot arrange when the oracle is a keyed PRF. -/
theorem bdSecW_run (O : List UInt8 → Digest) (c : Digest) :
    (bdSecW c none).run O = true ↔ O q0 = trigger := by
  by_cases h : O q0 = trigger <;> simp [bdSecW, TProg.run, wsV, h]

end RecursionFast.Explore.TwoChannel.Backdoor
