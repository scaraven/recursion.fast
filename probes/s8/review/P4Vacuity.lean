/-
  S8 review probe P4: the exact shape of Clean's balance over `K` (sharper than
  `clean_balance_vacuous`): a balanced interaction list is empty or ONE interaction of
  multiplicity `0`. So Clean's `Statement` over `K` says that no listed channel carries any
  message at all (beyond one silent interaction in the whole witness).
  Also: under a `ChannelMap` that mixes `none` and `some`, a `none` channel's default bus (its
  name's index) can coincide with a `some` bus, silently merging two channels.
-/
import RecursionFast.Clean
open RecursionFast RecursionFast.Clean Air.Flat

namespace S8Review.P4

theorem clean_balance_K (l : List (Interaction K)) (h : BalancedInteractions l) :
    l = [] ∨ ∃ i, l = [i] ∧ i.mult = 0 := by
  obtain ⟨hlen, hb⟩ := h
  rw [ringChar.eq K 2] at hlen
  match l, hlen with
  | [], _ => exact Or.inl rfl
  | [i], _ =>
    refine Or.inr ⟨i, rfl, ?_⟩
    have := hb i.msg
    simpa [balanceOf] using this
  | _ :: _ :: _, hlen => simp at hlen

/-- A map that fixes channel "b" to bus `0` while "a" keeps its default bus `0` (its index). -/
def mixed : ChannelMap := fun nm => if nm = "b" then some (0, true) else none
example : mixed.bus ["a", "b"] "a" = mixed.bus ["a", "b"] "b" := by decide

end S8Review.P4

#print axioms S8Review.P4.clean_balance_K
