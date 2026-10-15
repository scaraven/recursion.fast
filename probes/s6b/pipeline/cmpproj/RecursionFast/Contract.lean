/-! Stand-in for the trusted contract: `Good` is unsatisfiable. -/
namespace RecursionFast
structure Sub where
  vk : Nat
def Good (s : Sub) : Prop := s.vk = 42 ∧ s.vk = 43
end RecursionFast
