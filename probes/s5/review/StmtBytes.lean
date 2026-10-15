/-
S5 review probe (item 1c): the preimage of `d2` determines the pair of children. `stmtBytes` is
256 bytes and injective, so `stmtBytes x₁ ++ stmtBytes x₂` (512 bytes, fixed split) determines
`(x₁, x₂)`: binding of `d2` is collision resistance of `cfg.hash.run` on 512-byte inputs.
-/
import RecursionFast.Library.Compile

namespace RecursionFast.Probes.S5Review
open RecursionFast

theorem stmtBytes_length (x : Stmt) : (stmtBytes x).length = 256 := by
  simp [stmtBytes, List.length_flatMap, K.bytes_length]

theorem stmtBytes_inj {x y : Stmt} (h : stmtBytes x = stmtBytes y) : x = y := by
  have := congrArg kList h
  simp only [stmtBytes, kList_flatMap] at this
  exact List.ofFn_injective this

theorem pair_inj {x₁ x₂ y₁ y₂ : Stmt} (h : stmtBytes x₁ ++ stmtBytes x₂ = stmtBytes y₁ ++ stmtBytes y₂) :
    x₁ = y₁ ∧ x₂ = y₂ := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [stmtBytes_length])
  exact ⟨stmtBytes_inj h1, stmtBytes_inj h2⟩

end RecursionFast.Probes.S5Review

#print axioms RecursionFast.Probes.S5Review.pair_inj
