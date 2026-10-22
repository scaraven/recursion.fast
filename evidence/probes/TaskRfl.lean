-- ADV1: `Task.spawn`/`Task.get` are kernel-transparent, so a parallel `V` is provably equal to the
-- sequential one by `rfl`.
theorem spawn_get {α : Type} (f : Unit → α) : (Task.spawn f).get = f () := rfl
theorem all_par (cs : List Nat) (p : Nat → Bool) :
    ((cs.map fun c => Task.spawn fun _ => p c).all fun t => t.get) = cs.all p := by
  induction cs <;> simp_all [Task.spawn]
#print axioms all_par
