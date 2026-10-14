/-
# Control (positive): the toy "send the tables" protocol satisfies `Protocol.Secure`

At every class `20 ≤ k ≤ 28`, within the shape caps (S1-A9). The indexer: `VK L` is one
element, `1` iff `L` is admissible at class `k`; the index oracle `IDX L` is the serialisation of
`L` (`Library/Codec.lean`, at most `2^(k+8)` elements), one leaf. One prover round sends the
serialised tables (at most `2^(k+10)` elements), one leaf. The verifier is a query program
(S1-A8): it queries every leaf, i.e. the index oracle's and the message's only leaf, parses the
layout and the tables, and decides `rel` on them (`relBelow 2^8`, the decidable form). No
challenges, so `RbrKS` is vacuous and `ε = 0`; the extractor parses the tables from the
transcript. This is the inhabitation witness of `Protocol.Secure` and the skeleton of the
stage-8 baseline `P_triv` (DESIGN §7.3).
-/
import RecursionFast.Contract.Protocol
import RecursionFast.Library.Codec

namespace RecursionFast.Controls
open RecursionFast Codec

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
  WitMid := fun _ => List (Table K)
  extractor := { eqIn := rfl
                 extractMid := fun _ s tr _ => toyWit k s.1 (tr ⟨0, Nat.succ_pos _⟩)
                 extractOut := fun s tr _ => toyWit k s.1 (tr 0) }
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
  · simp [toyDecide, toyVK, hL, K_zero_ne_one]

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

/-- The toy's knowledge state function: before the message, "`w` satisfies the statement";
after it, "the tables parsed from the message satisfy the statement". -/
def toyKSF : KSF (relK k) Set.univ (toy k hk).specVerifier (toy k hk).extractor where
  toFun := fun m s tr w =>
    if h : m = 0 then (s, w) ∈ relK k
    else (s, toyWit k s.1 (tr ⟨0, Nat.pos_of_ne_zero fun h' => h (Fin.ext h')⟩)) ∈ relK k
  empty := fun _ _ => Iff.rfl
  next := fun m s tr msg w h => by
    obtain ⟨m, hm⟩ := m
    obtain rfl : m = 0 := Subsingleton.elim _ _
    simpa using h
  full := fun s tr sOut wOut hV _ => by
    simpa using (toy_accepts_iff k hk s tr).mp hV

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

end Toy

/-- The toy at class 20 (the smallest class in the range). -/
abbrev toy20 : Protocol 20 := toy 20 (by norm_num)

theorem toy20_secure : toy20.Secure := toy_secure 20 _

end RecursionFast.Controls
