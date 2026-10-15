/-
  S8 review probe P5 (run from probes/s8/blake2s: `lake env lean ../review/P5Blake2sSupported.lean`):
  the bridge's hypotheses on leanerVM's BLAKE2s table, which S8-RESULT reports as "admissible,
  what remains is only the BF64 → K transport and the compression". `OpsWithin` is copied
  verbatim from `RecursionFast/Clean/Semantics.lean` (that module is not in the probe package).
-/
import LeanerVM.Arithmetization.Tables.Blake2s
import RecursionFast.Clean.ToLayout

open LeanerVM.Arithmetization RecursionFast RecursionFast.Clean Air.Flat

def ens : Ensemble LeanerVM.Parameters.K unit where
  tables := [⟨blake2sTable⟩]
  channels := [StatePull.toRaw, StatePush.toRaw, MemPull.toRaw, MemPush.toRaw,
    BytecodePull.toRaw, BytecodePush.toRaw]

/-- Verbatim from `Semantics.lean`. -/
def OpsWithin {F : Type} [FiniteField F] [DecidableEq F] (w : ℕ) (ops : Operations F) : Prop :=
  (∀ e ∈ ops.constraints, within w e = true) ∧
  (∀ l ∈ ops.lookups, ∀ e ∈ l.entry.toList, within w e = true) ∧
  (∀ i ∈ ops.interactions, within w (readMult i.mult).2 = true ∧ ∀ e ∈ i.msg.toList, within w e = true)

instance {F : Type} [FiniteField F] [DecidableEq F] (w : ℕ) (ops : Operations F) :
    Decidable (OpsWithin w ops) := by unfold OpsWithin; infer_instance

-- `Supported ens` (one component)
#eval decide (OpsWithin (⟨blake2sTable⟩ : Component LeanerVM.Parameters.K).width
  (⟨blake2sTable⟩ : Component LeanerVM.Parameters.K).rowOperations)
-- lookups (for `LookupsFaithful []`): their number
#eval (⟨blake2sTable⟩ : Component LeanerVM.Parameters.K).rowOperations.lookups.length
-- channel names of the interactions vs the listed names
#eval ((⟨blake2sTable⟩ : Component LeanerVM.Parameters.K).rowOperations.interactions.map
  (·.channel.name)).eraseDups
#eval chNames ens
