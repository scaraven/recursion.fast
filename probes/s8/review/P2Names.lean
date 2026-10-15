/-
  S8 review probe P2: a channel is its *name* in `toLayout`/`StatementPerm`, but a `RawChannel`
  in Clean. An interaction on an UNLISTED channel whose name equals a listed channel's name is
  put on the listed channel's bus (`Part.ints`, `OnBus` test `i.channel.name ∈ names`), whereas
  Clean's `interactionsWith ch` filters by `RawChannel` equality and ignores it.

  Ensemble (over `K`, one interaction per channel, so Clean's length side condition `1 < 2` is
  met and Clean's own `Statement` is meaningful here): the verifier pushes its input on the
  listed `chA` ("c") and pulls it on the unlisted `chB` (also "c", different guarantee).
  * `StatementPerm byName ens x` holds (through the bridge, `rel` decided by the kernel).
  * `chA.toRaw ≠ chB.toRaw`, so in Clean `chA` carries one push and nothing else: unbalanced.
-/
import RecursionFast.Clean
open RecursionFast RecursionFast.Clean Air.Flat

namespace S8Review.P2

/-- The listed channel: name "c"; its guarantee is never established (pushed only). -/
def chA : Channel K field where
  name := "c"
  Guarantees _ _ := False

/-- An unlisted channel with the same name and a different guarantee. -/
def chB : Channel K field where
  name := "c"
  Guarantees _ _ := True

/-- The verifier: push the input on `chA`, pull it on `chB`. -/
def verifier : GeneralFormalCircuit K field unit where
  main := fun x => do
    chA.push x
    chB.pull x
  channelsWithRequirements := [chA.toRaw, chB.toRaw]
  Spec _ _ _ := True
  soundness := by
    circuit_proof_start [chA, chB]
    exact fun h _ => h rfl
  completeness := by circuit_proof_start [chA, chB]

/-- Only `chA` is listed. -/
def ens : Ensemble K field where
  tables := []
  channels := [chA.toRaw]
  verifier := verifier
  verifier_length_zero := by simp [circuit_norm, verifier]

/-- The two raw channels differ (their guarantees differ at multiplicity `-1`). -/
theorem chA_ne_chB : chA.toRaw ≠ chB.toRaw := by
  intro h
  simp only [Channel.toRaw, RawChannel.mk.injEq] at h
  have hG := eq_of_heq h.2.2.1
  have := congrFun (congrFun (congrFun hG (-1)) #v[0]) (fun _ _ => #[])
  simp [chA, chB] at this

/-- Both interactions have the name "c", so both become ports of bus `0`, one sending, one
receiving. -/
theorem pub_ports : ((toLayout [] ens).chips.head?.map fun C => C.ports.map fun p => (p.bus, p.send))
    = some [(0, true), (0, false)] := by decide +kernel

theorem buses : ∀ C ∈ (toLayout [] ens).chips, ∀ p ∈ C.ports, p.bus < 1 := by decide +kernel

/-- A Clean witness: no tables, public input `1`. -/
def wit : EnsembleWitness ens where
  tables := []
  data := data0
  publicInput := (1 : K)
  same_length := rfl
  same_circuits := by intro i hi; simp [ens] at hi
  same_data := by simp

/-- The translated layout accepts it ... -/
theorem rel_ok : (toLayout [] ens).rel 6 (pubVec (F := K) (PublicIO := field) 1) (toLayoutWit [] wit) :=
  (relBelow_iff buses _ _ _).mp (by decide +kernel)

theorem supported : Supported ens := by decide +kernel

theorem faithful : LookupsFaithful [] ens := by
  intro c hc l hl
  simp only [Ensemble.allTables, ens, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  simp [Ensemble.verifierTable, Component.rowOperations, verifier, circuit_norm,
    Operations.lookups] at hl

/-- ... so `StatementPerm` (by name) holds for the public input `1`. -/
theorem statementPerm_one : StatementPerm ChannelMap.byName ens (1 : K) :=
  (statementPerm_iff (by decide) supported faithful (1 : K)).mpr ⟨6, _, rel_ok⟩

/-- The verifier's interactions, by channel: `chA` (push, multiplicity `1`), `chB` (pull). -/
theorem verifier_channels :
    (ens.verifierTable.rowOperations.interactions.map (·.channel)) = [chA.toRaw, chB.toRaw] := by
  simp [Ensemble.verifierTable, Component.rowOperations, ens, verifier, circuit_norm,
    Operations.interactions]

/-- **Clean's own statement fails** for every public input: on the listed channel `chA` there is
exactly one interaction (the push, multiplicity `1`), so `balanceOf` at its message is `1 ≠ 0`. -/
theorem not_statement (x : field K) : ¬ ens.Statement x := by
  classical
  rintro ⟨w, -, -, hbal⟩
  obtain ⟨-, hb⟩ := hbal chA.toRaw (by simp [ens])
  have hw : w.tables = [] := by
    have := w.same_length; simp [ens] at this; exact List.eq_nil_of_length_eq_zero this.symm
  have hall : w.allTablesWitness.interactionsWith chA.toRaw =
      w.verifierTable.interactions.filter (·.channel = chA.toRaw) := by
    simp only [Tables.interactionsWith, EnsembleWitness.allTables, hw,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [Air.Flat.Table.interactionsWith_eq_filter]
  have key := hb #[w.publicInput]
  rw [hall] at key
  revert key
  simp only [Air.Flat.Table.interactions, Operations.interactionValues, Component.interactions_eq,
    Component.rowOperations, EnsembleWitness.verifierTable]
  simp [ens, verifier, circuit_norm, Operations.interactions, AbstractInteraction.eval, balanceOf,
    chA_ne_chB.symm, Air.Flat.Table.environment, Expression.eval, toElements]

/-- **The divergence**: `StatementPerm` (by name) accepts `1`; Clean's own `Statement` rejects
every public input, `1` included, on a channel with a single interaction (so not because of the
characteristic-2 length condition). -/
theorem divergence : StatementPerm ChannelMap.byName ens (1 : K) ∧ ¬ ens.Statement (1 : K) :=
  ⟨statementPerm_one, not_statement 1⟩

/-! The other direction: an unmatched interaction on the unlisted `chB` makes `StatementPerm`
reject a statement that Clean's `Statement` accepts. -/

/-- The verifier pushes its input on the unlisted `chB` only. -/
def verifier2 : GeneralFormalCircuit K field unit where
  main := fun x => chB.push x
  channelsWithRequirements := [chB.toRaw]
  Spec _ _ _ := True
  soundness := by
    circuit_proof_start [chB]
  completeness := by circuit_proof_start [chB]

def ens2 : Ensemble K field where
  tables := []
  channels := [chA.toRaw]
  verifier := verifier2
  verifier_length_zero := by simp [circuit_norm, verifier2]

/-- Clean's `Statement` holds for every public input: `chA` carries no interaction. -/
theorem statement2 (x : field K) : ens2.Statement x := by
  classical
  refine ⟨⟨[], fun _ _ => #[], x, rfl, by simp [ens2], by simp⟩, rfl, ?_, ?_⟩
  · intro t ht
    simp only [EnsembleWitness.allTables, List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    intro row _
    rw [Air.Flat.Component.constraintsHold_iff]
    simp [Operations.ConstraintsHold, EnsembleWitness.verifierTable, ens2, verifier2, circuit_norm,
      Component.rowOperations, Operations.constraints, Operations.lookups]
  · intro ch hch
    simp only [ens2, List.mem_singleton] at hch
    subst hch
    refine ⟨Or.inl ?_, fun msg => ?_⟩ <;>
    · simp only [EnsembleWitness.allTablesWitness, Tables.interactionsWith, EnsembleWitness.allTables,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [Air.Flat.Table.interactionsWith_eq_filter]
      simp [Air.Flat.Table.interactions, Operations.interactionValues, Component.interactions_eq,
        Component.rowOperations, EnsembleWitness.verifierTable, ens2, verifier2, circuit_norm,
        Operations.interactions, AbstractInteraction.eval, balanceOf, chA_ne_chB.symm, ringChar.eq K 2]

/-- `StatementPerm` (by name) rejects every public input: bus `0` (name "c") carries the push
and nothing to receive it. -/
theorem not_statementPerm2 (x : field K) : ¬ StatementPerm ChannelMap.byName ens2 x := by
  rintro ⟨w, -, -, hbal⟩
  have hw : w.tables = [] := by
    have := w.same_length; simp [ens2] at this; exact List.eq_nil_of_length_eq_zero this.symm
  have h0 := hbal 0 (by decide)
  have hmem : [w.publicInput] ∈ (w.allTables.map fun t => tableMsgs ChannelMap.byName (chNames ens2) t 0 true).sum := by
    simp [EnsembleWitness.allTables, hw, tableMsgs, EnsembleWitness.verifierTable, ens2, verifier2,
      circuit_norm, Component.interactions_eq, Component.rowOperations, Operations.interactions, OnBus,
      chNames, ChannelMap.bus, ChannelMap.dir, ChannelMap.byName, readMult, chB, chA,
      Air.Flat.Table.environment, toElements]
  rw [h0] at hmem
  simp [EnsembleWitness.allTables, hw, tableMsgs, EnsembleWitness.verifierTable, ens2, verifier2,
    circuit_norm, Component.interactions_eq, Component.rowOperations, Operations.interactions, OnBus,
    chNames, ChannelMap.bus, ChannelMap.dir, ChannelMap.byName, readMult, chB, chA] at hmem

theorem divergence2 : ens2.Statement (1 : K) ∧ ¬ StatementPerm ChannelMap.byName ens2 (1 : K) :=
  ⟨statement2 1, not_statementPerm2 1⟩

end S8Review.P2

#print axioms S8Review.P2.divergence
#print axioms S8Review.P2.chA_ne_chB
#print axioms S8Review.P2.pub_ports
#print axioms S8Review.P2.divergence2
