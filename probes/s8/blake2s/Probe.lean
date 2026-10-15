import LeanerVM.Arithmetization.Tables.Blake2s
import RecursionFast.Clean.ToLayout

open LeanerVM.Arithmetization RecursionFast RecursionFast.Clean Air.Flat

-- leanerVM's `BLAKE2S` table alone, with its six channels and the empty verifier.
def ens : Ensemble LeanerVM.Parameters.K unit where
  tables := [⟨blake2sTable⟩]
  channels := [StatePull.toRaw, StatePush.toRaw, MemPull.toRaw, MemPush.toRaw,
    BytecodePull.toRaw, BytecodePush.toRaw]

-- leanerVM's pull/push pairs on one bus each (S8-A11)
def pairs : ChannelMap := fun nm =>
  if nm = "st.pull" then some (0, false) else if nm = "st.push" then some (0, true)
  else if nm = "mem.pull" then some (1, false) else if nm = "mem.push" then some (1, true)
  else if nm = "bc.pull" then some (2, false) else if nm = "bc.push" then some (2, true) else none

#eval (((toLayout [] ens pairs).chips.getD 1 ⟨0, gadgetOf [] [], [], none⟩).ports.map fun p =>
  (p.bus, p.send, p.msg.length))
#eval decide ((toLayout [] ens pairs).Admissible 24)
#eval decide ((toLayout [] ens pairs).Admissible 20)

-- (cols, cons, t, q, ports, degree, entries, max message length) per chip.
#eval ((toLayout [] ens).chips.map fun C =>
  (C.cols, C.gadget.cons, C.gadget.t, C.gadget.q, C.ports.length,
    (List.ofFn fun i => (C.gadget.S i).length).foldr max 0, Chip.entries C,
    (C.ports.map fun p => p.msg.length).foldr max 0))
-- component width (row cells) and auxiliary columns
#eval ((⟨blake2sTable⟩ : Component LeanerVM.Parameters.K).width,
  (RecursionFast.Clean.Part.auxs (chNames ens) (compPart ⟨blake2sTable⟩)).length)
-- ports per bus and direction of the BLAKE2s chip
#eval (((toLayout [] ens).chips.getD 1 ⟨0, gadgetOf [] [], [], none⟩).ports.map fun p =>
  (p.bus, p.send, p.msg.length))
-- the admission check, evaluated (compiled `Decidable` instance)
#eval decide ((toLayout [] ens).Admissible 24)
#eval (toLayout [] ens).chips.map fun C => decide (C.Admissible)
#eval (toLayout [] ens).chips.map fun C => decide (C.ports.length ≤ 2 ^ 4)

-- two parts of the bridge's `Supported pairs` (OpsWithin: the review's P5): ShapeOK, Separate
#eval (ens.allTables.all fun c => c.rowOperations.interactions.all ShapeOK,
  decide (pairs.Separate (chNames ens)))
