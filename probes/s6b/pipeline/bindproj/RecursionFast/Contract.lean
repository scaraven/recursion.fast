/-! Stand-in for the trusted contract (A7-M3 probe): the certified property is `vk = 0`. -/
namespace RecursionFast
structure Sub where
  vk : Nat
def Good (s : Sub) : Prop := s.vk = 0
end RecursionFast
