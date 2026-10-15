/-
S7 review probe (item 2a): a leaf-board submission whose declared errors are `errorCap`
(noncomputable reals), so `submission` itself has no compiled code. The v2 gate must check the
badge-path fields one by one and pass (v0.3's A7-M2, in the v2 structures).
-/
import RecursionFast.Contract
import RecursionFast.Controls.Toy

open RecursionFast RecursionFast.Controls

namespace S7Eps

theorem h24 : 20 ≤ 24 ∧ 24 ≤ 28 := by decide

noncomputable def P : Protocol 24 := { toy 24 h24 with ε := fun _ => errorCap }

theorem P_secure : P.Secure where
  complete := (toy_secure 24 h24).complete
  sound := ⟨toyKSF 24 h24, fun _ c _ => (toy_noChal 24 c).elim⟩
  cap := fun c => (toy_noChal 24 c).elim

noncomputable def submission : Submission 24 := ⟨P, ⟨.blake2s, 2, by decide⟩, P_secure⟩

theorem certified : Certificate ⟨24, .blake2s, 2⟩ submission ∧
    submission.P.extractor.img = firstMsgImg := ⟨⟨rfl, rfl⟩, rfl⟩

end S7Eps
