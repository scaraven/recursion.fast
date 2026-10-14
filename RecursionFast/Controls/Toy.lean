/-
# Control (positive): the toy "send the tables" protocol satisfies `Protocol.Secure`

At every class `20 ≤ k ≤ 28`, within the shape caps (S1-A9). The indexer: `VK L` is one
element, `1` iff `L` is admissible at class `k`; the index oracle `IDX L` is the serialisation of
`L` (`Library/Codec.lean`, at most `2^(k+8)` elements), one leaf. One prover round sends the
serialised tables (at most `2^(k+10)` elements), one leaf. The verifier is a query program
(S1-A8): it queries every leaf, i.e. the index oracle's and the message's only leaf, parses the
layout and the tables, and decides `rel` on them (`relBelow 2^8`, the decidable form). No
challenges, so `RbrKS` is vacuous and `ε = 0`. The extractor image is `firstMsgImage`
(`Library/Extractor.lean`, 8 instructions): it outputs the message in place, which the contract
decodes before round 0 as exactly the tables the verifier checks (`toy_extractMid`). This is the
inhabitation witness of `Protocol.Secure` and the skeleton of the stage-8 baseline `P_triv`
(DESIGN §7.3).

Negative control (S4-m3): with an image whose round-0 output on an honest transcript is not a
witness, the same prover and verifier are not secure (`toy_not_secure_of`); the looping image is
one (`toy_spin_not_secure`, every class in range). So `Secure` depends on the image.
-/
import RecursionFast.Contract.Protocol
import RecursionFast.Library.Codec
import RecursionFast.Library.Extractor
import RecursionFast.Library.RbrSound
import RecursionFast.Controls.Extractor

namespace RecursionFast.Controls
open RecursionFast Codec
open scoped NNReal

section Toy
variable (k : ℕ) (hk : 20 ≤ k ∧ k ≤ 28)

/-- The single round: one oracle of `2^(k+10)` elements, one leaf. -/
def toyShape : Fin 1 → Round := fun _ => .msg ⟨k + 10, k + 10⟩

/-- The verification key: `1` iff the layout is admissible at class `k`. -/
def toyVK (L : Layout K) : Fin 1 → K := fun _ => if L.Admissible k then 1 else 0

/-- The decision on the queried leaves: the key says admissible, and the tables parsed from the
message satisfy the layout parsed from the index. -/
def toyDecide (vk : Fin 1 → K) (x : Stmt) (idx msg : List K) : Bool :=
  vk 0 == 1 && decide ((pLayout idx).1.relBelow (2 ^ 8) k x
    (pWit ((pLayout idx).1.chips.map Chip.cols) msg).1)

/-- The verifier: query leaf 0 of the index oracle and of the message, then decide. -/
def toyVerify (vk : Fin 1 → K) (x : Stmt) (_ : Challenges (toyShape k)) : QProg Bool :=
  .query 0 0 fun idx => .query 1 0 fun msg => .done (toyDecide k vk x idx msg)

/-- The tables the extractor parses from a transcript of statement `(L, _)`. -/
def toyWit (L : Layout K) (msg : OVal ⟨k + 10, k + 10⟩) : List (Table K) :=
  (pWit (L.chips.map Chip.cols) (List.ofFn msg)).1

/-- The toy protocol at class `k`. -/
abbrev toy : Protocol k where
  k_range := hk
  n := 1
  n_le := by decide
  shape := toyShape k
  vkLen := 1
  vkLen_le := by decide
  VK := toyVK k
  idxShape := ⟨k + 8, k + 8⟩
  IDX L := toOracle (k + 8) (eLayout L)
  shape_ok := ⟨fun _ => ⟨le_refl _, le_refl _⟩, le_refl _, le_refl _⟩
  prover := { next := fun s w _ _ => toOracle (k + 10) (eWit s.1 w),
              output := fun _ _ _ => ((), ()) }
  verify := toyVerify k
  extractor := firstMsgImage k 1
  ε := fun _ => 0

include hk in
/-- **What the toy verifier decides**: the layout is admissible and the tables parsed from the
message satisfy it. -/
theorem toyDecide_iff (L : Layout K) (x : Stmt) (msg : OVal ⟨k + 10, k + 10⟩) :
    toyDecide k (toyVK k L) x (List.ofFn (toOracle (k + 8) (eLayout L))) (List.ofFn msg) = true ↔
      L.Admissible k ∧ L.rel k x (toyWit k L msg) := by
  by_cases hL : L.Admissible k
  · have hN : ∀ C ∈ (L.normal (2 ^ 8)).chips, ∀ p ∈ C.ports, p.bus < 2 ^ 8 :=
      List.forall_mem_map.mpr hL.bus_lt
    rw [ofFn_toOracle (eLayout_length hk.1 hL)]
    simp only [toyDecide, toyVK, hL, ite_true, beq_self_eq_true, Bool.true_and, decide_eq_true_eq,
      true_and, pLayout_eLayout hk.2 hL, relBelow_iff hN, rel_normal_iff hL.bus_lt, toyWit]
    simp [Layout.normal, Function.comp_def]
  · simp [toyDecide, toyVK, hL]

theorem toy_accepts_iff (s : Layout K × Stmt) (tr : FullTranscript (toyShape k)) :
    (toy k hk).specVerifier s tr = some () ↔ (s, toyWit k s.1 (tr 0)) ∈ relK k := by
  obtain ⟨L, x⟩ := s
  refine Iff.trans ?_ (toyDecide_iff k hk L x (tr 0))
  simp [Protocol.specVerifier, toyVerify, QProg.eval, FullTranscript.oracles, toyShape,
    Round.oracles, OShape.leaves, leaf_zero]
  exact congrArg _ (leaf_zero (k + 10) (tr 0))

/-- No challenge rounds. -/
theorem toy_noChal (c : ChallengeIdx (toyShape k)) : False := by
  have := c.2; simp [toyShape, Round.isMsg] at this

include hk in
/-- **The first-message image is the toy's extractor**: before round 0, for an admissible layout
of a class in range, it returns exactly the tables the toy's verifier checks (`toyWit`), for
every message and every witness after round 0. -/
theorem toy_extractMid {L : Layout K} (hL : L.Admissible k) (x : Stmt)
    (tr : Transcript (toyShape k) (Fin.castSucc 0)) (msg : OVal ⟨k + 10, k + 10⟩)
    (w : Mid 1 (Fin.succ 0)) :
    (((firstMsgImage k 1).toExtractor (toyShape k)).extractMid 0 (L, x) (tr.concat msg) w :
      List (Table K)) = toyWit k L msg := by
  have hL' := Layout.words_length hk.1 hL
  have h36 : 2 ^ (k + 8) ≤ 2 ^ 36 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h38 : 2 ^ (k + 10) ≤ 2 ^ 38 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h12 : 2 ^ (k + 10) ≤ 2 ^ (k + 12) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hf : 8 ≤ (firstMsgImage k 1).fuel (Fin.castSucc 0) := by
    show 8 ≤ 2 ^ (2 * k + 16)
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ 2 * k + 16))
  rw [firstMsg_extractMid k (toyShape k) 0 (L, x) (tr.concat msg) w
    (by simp [Round.words, toyShape]; omega) (by simp [Round.words, toyShape, witCap]; omega)
    (firstMsgImage k 1) rfl hf]
  have e : (tr.concat msg) (Fin.last 0) = msg := Transcript.concat_last tr msg
  show decTables (L.chips.map Chip.cols)
    (List.ofFn fun i => ((tr.concat msg) (Fin.last 0) i).bits) = _
  rw [e, show (List.ofFn fun i => (msg i).bits) = (List.ofFn msg).map K.bits from
    List.map_ofFn.symm, decTables_map_bits]
  rfl

/-- The toy's knowledge state function: before the message, "`w` satisfies the statement";
after it, "the tables parsed from the message satisfy the statement". Written with `Fin.cases`
because the witness before round 0 has type `Mid 1 0 = List (Table K)`. -/
def toyKSF : KSF (relK k) Set.univ (toy k hk).specVerifier
    ((toy k hk).extractor.toExtractor (toy k hk).shape) where
  toFun := fun m => Fin.cases
    (motive := fun m => Layout K × Stmt → Transcript (toyShape k) m → Mid 1 m → Prop)
    (fun s _ w => (s, w) ∈ relK k)
    (fun _ s tr _ => (s, toyWit k s.1 (tr ⟨0, Nat.succ_pos _⟩)) ∈ relK k) m
  empty := fun _ _ => Iff.rfl
  next := fun m s tr msg w h => by
    obtain ⟨m, hm⟩ := m
    obtain rfl : m = 0 := Subsingleton.elim _ _
    obtain ⟨L, x⟩ := s
    have e : (tr.concat msg) (Fin.last 0) = msg := Transcript.concat_last tr msg
    have h' : ((L, x), toyWit k L msg) ∈ relK k := by
      have h0 : ((L, x), toyWit k L ((tr.concat msg) (Fin.last 0))) ∈ relK k := h
      rwa [e] at h0
    show ((L, x), (((firstMsgImage k 1).toExtractor (toyShape k)).extractMid 0 (L, x)
      (tr.concat msg) w : List (Table K))) ∈ relK k
    rw [toy_extractMid k hk h'.1 x tr msg w]
    exact h'
  full := fun s tr _ _ hV _ => (toy_accepts_iff k hk s tr).mp hV

/-- **Positive control**: the toy protocol is secure, at every class in the range. -/
theorem toy_secure : (toy k hk).Secure where
  complete := by
    rintro ⟨L, x⟩ w ⟨hL, hrel⟩ ρ
    refine ⟨(toy_accepts_iff k hk _ _).mpr ⟨hL, ?_⟩, Set.mem_univ _⟩
    show L.rel k x (toyWit k L (toOracle (k + 10) (eWit L w)))
    have h28 : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [toyWit, ofFn_toOracle (eWit_length hL hrel), pWit_eWit L w hrel.1
      (fun T hT => lt_of_le_of_lt (rows_le_of_rel hL hrel T hT) h28)]
    exact (rel_trim_iff hL.readsOwn hrel.1).mpr hrel
  sound := ⟨toyKSF k hk, fun _ c _ => (toy_noChal k c).elim⟩
  cap := fun c => (toy_noChal k c).elim

/-- The honest one-round transcript of the toy for statement `s` and witness `w`. -/
def toyTr (s : Layout K × Stmt) (w : List (Table K)) : Transcript (toyShape k) (Fin.succ 0) :=
  (Transcript.empty (toyShape k)).concat (m := 0) (toOracle (k + 10) (eWit s.1 w))

/-- **Negative control (the image is load-bearing)**: an image whose round-0 output on the honest
transcript of `(triv, 0)` is never a witness makes the toy's prover and verifier insecure, at
any errors. -/
theorem toy_not_secure_of (E : ExtractorImage k 1)
    (hE : ∀ w, ((triv, fun _ => 0), ((E.toExtractor (toyShape k)).extractMid 0
      (triv, fun _ => 0) (toyTr k (triv, fun _ => 0) [⟨1, fun _ _ => 0⟩]) w : List (Table K))) ∉
      relK k)
    (ε : ChallengeIdx (toyShape k) → ℝ≥0) :
    ¬ SecureWith (relK k) Set.univ (toy k hk).prover (toy k hk).specVerifier
        (E.toExtractor (toyShape k)) ε := by
  rintro ⟨hc, ⟨kSF, -⟩, -⟩
  let s0 : Layout K × Stmt := (triv, fun _ => 0)
  have hacc : (toy k hk).specVerifier s0 (toyTr k s0 [⟨1, fun _ _ => 0⟩]) = some () :=
    (hc s0 _ (triv_relK k (by omega)) (fun c => (toy_noChal k c).elim)).1
  have hfull := kSF.full s0 (toyTr k s0 [⟨1, fun _ _ => 0⟩]) () () hacc (Set.mem_univ _)
  exact hE _ ((kSF.empty s0 _).mpr (kSF.next ⟨0, rfl⟩ s0 (Transcript.empty _) _ _ hfull))

/-- **The looping image makes the toy insecure**, at every class in range and all errors. -/
theorem toy_spin_not_secure (ε : ChallengeIdx (toyShape k) → ℝ≥0) :
    ¬ SecureWith (relK k) Set.univ (toy k hk).prover (toy k hk).specVerifier
        ((spinImage k 1).toExtractor (toyShape k)) ε :=
  toy_not_secure_of k hk (spinImage k 1)
    (fun w => by rw [spin_extractMid _ rfl]; exact nil_not_relK k _) ε

end Toy

/-- The toy at class 20 (the smallest class in the range). -/
abbrev toy20 : Protocol 20 := toy 20 (by norm_num)

theorem toy20_secure : toy20.Secure := toy_secure 20 _

end RecursionFast.Controls
