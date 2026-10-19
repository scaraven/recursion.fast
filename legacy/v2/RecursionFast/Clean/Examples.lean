/-
  RecursionFast.Clean.Examples  (UNTRUSTED, kernel-checked; Stage 8, DESIGN §9.3)

  **XOR-Fibonacci with channels over `K`**, the structure of Clean's
  `Clean/Examples/FibonacciWithChannels.lean` moved to characteristic 2 (Clean's own example is
  over `F p` with `p > 512`: its byte range checks read `.val < 256` and its addition is mod 256,
  neither meaningful in `K`). A state channel `fib` carries `(n, x, y)`; the step component pulls
  `(n, x, y)`, looks `x` up in the static table `bits = {0, 1}`, and pushes `(n · X, y, x + y)`
  (`X` the field element `x`, so the counter is `X^k`); the verifier pulls the final state (the
  public input) and pushes the initial state `(1, 0, 1)`.

  `toLayout tabs ens` has three chips: the public chip (34 columns: the 3 public cells, 29 zero
  columns, 2 auxiliary columns for the constants `1` and `0` of the pushed initial state), the
  step chip (6 columns: `n, x, y` and auxiliary columns for the constant-`1` selector, `n · X`
  and `x + y`), and the fixed chip of `bits` (2 columns). The honest witness of three steps has
  `1 · 34 + 3 · 6 + 2 · 2 = 56` cells.

  Positive controls (`decide +kernel` on the translated layout): `fibK_admissible`,
  `fibK_cols`, `fibK_supported`, `fibK_rel`, `fibK_relK` (the instance is in the contract's
  `relK 20`); through the bridge, `fibK_statement` (`StatementPerm`), `fibK_channelsByName` and
  `fibK_statementRaw` (Clean's own statement, ℕ-balanced per `RawChannel`), and
  `fibK_relK_roundtrip` (soundness, then `relK_toLayoutWit` into `relK 20`).
  `holdsPerm_of_relK` / `relK_toLayoutWit`: for any ensemble over `K`, the bridge at the
  contract's `relK k`, both ways (admissibility a hypothesis of the second).

  Channel pairs (S8-A11): `ensP` is the same machine written leanerVM's way, pulling on
  `fib.pull` and pushing on `fib.push`. With the map `pairs` (both on bus `0`, directions fixed)
  the honest witness is accepted (`pair_rel`, `pair_statement`); by name each side is its own
  one-direction bus and the same witness is rejected (`pair_byName_neg`).

  Negative controls: `fibK_wrong_final` (the verifier pulls a state no step pushed),
  `fibK_mutated` (one cell changed), `fibK_lookup_neg` (`bits` registered as `{0}`),
  `fibK_junk_neg` (two copies of an unchained row: their messages cancel in a field-sum balance
  in characteristic 2, never in ℕ). The hypotheses can fail: `fibK_not_faithful_unregistered`,
  `wide_not_supported` (a component reading beyond its width) with `wide_holdsPerm` and
  `wide_rejected` (so `Supported` is needed for completeness), `mixedMap_not_separate` (a silent
  bus merge). Channels are names (S8-M1): `Names.name_merge_weakens` and
  `Names.name_merge_strengthens` (`StatementPerm` and Clean's `Statement` differ both ways when
  an unlisted channel shares a listed name; `Names.not_channelsByName`). Clean over `K`:
  `clean_balance_vacuous`, `clean_balance_K` (a balanced list is empty or one silent
  interaction), `clean_push_requirement_vacuous`. Direction from constructors: `readMult_pull`,
  `readMult_push`, `readMult_pullIf`, `readMult_pushIf_one` (a push written `(1 : K) · en` stays
  a send), `shape_neg`, with `neg_one_eq_one`.
-/
import RecursionFast.Clean.Semantics
import RecursionFast.Library.Layout
import RecursionFast.Contract.Protocol

namespace RecursionFast.Clean

/-- **Over `K`, in the competition relation**: a witness of the translated layout in the
contract's `relK k` (the contract's own `K` arithmetic and `DecidableEq`) gives, by
`toCleanWit`, a Clean witness of the statement that satisfies `HoldsPerm`. The generic bridge
applies to `relK` as stated: its instances at `F := K` are the contract's, definitionally. -/
theorem holdsPerm_of_relK {PublicIO : TypeMap} [ProvableType PublicIO] {cm : ChannelMap}
    {tabs : List (FixedTable K)} {ens : Air.Flat.Ensemble K PublicIO}
    (hL : LookupsFaithful tabs ens)
    {k : ℕ} {x : Stmt} {w : List (Table K)} (h : ((toLayout tabs ens cm, x), w) ∈ relK k) :
    x = pubVec (toCleanWit ens w).publicInput ∧ HoldsPerm cm (toCleanWit ens w) :=
  ⟨(holdsPerm_toCleanWit hL h.2).1, (holdsPerm_toCleanWit hL h.2).2.1⟩

/-- **Over `K`, into the competition relation** (the converse of `holdsPerm_of_relK`): a Clean
witness satisfying `HoldsPerm`, whose translation has at most `2^k` cells, gives by `toLayoutWit`
a witness in the contract's `relK k`, **provided the translated layout is admissible** at `k`.
Admissibility is a hypothesis: no theorem bounds the caps by Clean quantities; it is decided per
instance (`fibK_admissible`). -/
theorem relK_toLayoutWit {PublicIO : TypeMap} [ProvableType PublicIO] {cm : ChannelMap}
    {tabs : List (FixedTable K)} {ens : Air.Flat.Ensemble K PublicIO} {k : ℕ}
    (hadm : (toLayout tabs ens cm).Admissible k) (hS : Supported cm ens)
    (hL : LookupsFaithful tabs ens) {cw : Air.Flat.EnsembleWitness ens} (h : HoldsPerm cm cw)
    (hk : layoutCells (toLayout tabs ens cm) (toLayoutWit tabs cw) ≤ 2 ^ k) :
    ((toLayout tabs ens cm, pubVec cw.publicInput), toLayoutWit tabs cw) ∈ relK k :=
  ⟨hadm, rel_toLayoutWit hS hL h hk⟩

end RecursionFast.Clean

namespace RecursionFast.Clean.FibK

open RecursionFast Air.Flat

/-- The element `X` of `K` (bit 1): the step counter is `X^k`. -/
def gX : K := ⟨2⟩

/-- The state channel: `(counter, x, y)`, no guarantee. -/
def FibChannel : Channel K fieldTriple where
  name := "fib"
  Guarantees _ _ := True

/-- The rows of `bits`. -/
def bitRow : Fin 2 → K := fun i => if i.val = 0 then 0 else 1

/-- The static table `bits = {0, 1}`. -/
def Bits : StaticTable K field where
  name := "bits"
  length := 2
  row := bitRow
  index x := if x = 0 then 0 else 1
  Spec x := x = 0 ∨ x = 1
  contains_iff := by
    intro t
    constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp [bitRow]
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩

/-- One step: pull `(n, x, y)`, look `x` up in `bits`, push `(n · X, y, x + y)`. -/
def step : GeneralFormalCircuit K fieldTriple unit where
  main := fun (n, x, y) => do
    FibChannel.pull (n, x, y)
    lookup (Table.fromStatic Bits) x
    FibChannel.push (n * Expression.const gX, y, x + y)
  ProverAssumptions := fun (_, x, _) _ _ => x = 0 ∨ x = 1
  Spec _ _ _ := True
  soundness := by circuit_proof_start [FibChannel]
  completeness := by
    circuit_proof_start [FibChannel, Bits]
    obtain ⟨n, x, y⟩ := input
    simp only [Prod.mk.injEq] at h_input
    rw [h_input.2.1]
    exact h_assumptions

/-- The verifier: pull the final state (the public input), push the initial state `(1, 0, 1)`. -/
def verifier : GeneralFormalCircuit K fieldTriple unit where
  main := fun final => do
    FibChannel.pull final
    FibChannel.push (1, 0, 1)
  Spec _ _ _ := True
  soundness := by circuit_proof_start [FibChannel]
  completeness := by circuit_proof_start [FibChannel]

/-- The ensemble: one step component, the state channel, the verifier. -/
def ens : Ensemble K fieldTriple where
  tables := [⟨step⟩]
  channels := [FibChannel.toRaw]
  verifier := verifier
  verifier_length_zero := by simp [circuit_norm, verifier]

/-- The registered lookup table `bits`. -/
def tabs : List (FixedTable K) := [⟨"bits", 1, [#v[0], #v[1]]⟩]

/-! ## Positive controls -/

/-- The translated layout is admissible at the smallest class. -/
theorem fibK_admissible : (toLayout tabs ens).Admissible 20 := by decide +kernel

/-- The chips' widths: public 34, step 6, `bits` 2. -/
theorem fibK_cols : (toLayout tabs ens).chips.map Chip.cols = [34, 6, 2] := by decide +kernel

/-- The ensemble satisfies the syntactic side condition. -/
theorem fibK_supported : Supported ChannelMap.byName ens := by decide +kernel

/-- The one lookup reads `bits` exactly: Clean's `Contains` is membership in its rows. -/
theorem fibK_faithful : LookupsFaithful tabs ens := by
  intro c hc l hl
  simp only [Ensemble.allTables, ens, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · simp [Ensemble.verifierTable, Component.rowOperations, verifier, circuit_norm,
      Operations.lookups] at hl
  · simp only [Component.rowOperations, step, circuit_norm, Operations.lookups,
      List.mem_singleton] at hl
    subst hl
    refine ⟨_, rfl, fun data v => ?_⟩
    obtain ⟨⟨xs⟩, hxs⟩ := v
    match xs, hxs with
    | [a], _ =>
      simp only [Table.toRaw, Bits, bitRow]
      constructor
      · rintro ⟨i, hi⟩
        fin_cases i <;> simp_all [ProvableType.fromElements]
      · intro h
        obtain rfl | rfl : a = 0 ∨ a = 1 := by simpa [Vector.toList] using h
        exacts [⟨0, rfl⟩, ⟨1, rfl⟩]

/-- The honest step rows: three steps of XOR-Fibonacci from `(1, 0, 1)`. -/
def rows : List (Vector K 3) := [#v[1, 0, 1], #v[gX, 1, 1], #v[gX * gX, 1, 0]]

/-- The final state `(X^3, 0, 1)`. -/
def final : fieldTriple K := (gX * gX * gX, 0, 1)

/-- A Clean witness: step rows `rs`, no prover data, public input `pub`. -/
def wit (rs : List (Vector K 3)) (pub : fieldTriple K) : EnsembleWitness ens where
  tables := [⟨⟨step⟩, 3, rs.map Vector.toArray, data0, by simp⟩]
  data := data0
  publicInput := pub
  same_length := rfl
  same_circuits := by intro i hi; simp [ens] at hi; subst hi; rfl
  same_data := by simp

/-- Every port of the translated layout is on bus `0` (`fib`) or `1` (`bits`). -/
theorem fibK_buses : ∀ C ∈ (toLayout tabs ens).chips, ∀ p ∈ C.ports, p.bus < 2 := by
  decide +kernel

/-- **Positive control**: the honest witness, translated by `toLayoutWit`, satisfies the
translated layout with the statement `pubVec final`, at class `6` (56 cells). -/
theorem fibK_rel : (toLayout tabs ens).rel 6 (pubVec final) (toLayoutWit tabs (wit rows final)) :=
  (relBelow_iff fibK_buses _ _ _).mp (by decide +kernel)

/-- **In the competition relation**: at the smallest class the honest instance is in the
contract's `relK 20` (admissible layout, `rel` with the contract's own `K` arithmetic: the
generic `rel` at `F := K` through `FiniteField K` is the contract's, definitionally). -/
theorem fibK_relK :
    ((toLayout tabs ens, pubVec final), toLayoutWit tabs (wit rows final)) ∈ relK 20 :=
  ⟨fibK_admissible, (relBelow_iff fibK_buses _ _ _).mp (by decide +kernel)⟩

/-- **Both directions at the contract's relation**: soundness (`holdsPerm_toCleanWit`) turns the
class-6 witness into a Clean witness, and `relK_toLayoutWit` (admissibility decided by the kernel,
`fibK_admissible`) puts its translation into `relK 20`. -/
theorem fibK_relK_roundtrip :
    ((toLayout tabs ens, pubVec final),
      toLayoutWit tabs (toCleanWit ens (toLayoutWit tabs (wit rows final)))) ∈ relK 20 := by
  obtain ⟨hx, hh, hk⟩ := holdsPerm_toCleanWit fibK_faithful fibK_rel
  rw [hx]
  exact relK_toLayoutWit fibK_admissible fibK_supported fibK_faithful hh
    (hk.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)))

/-- **Through the bridge**: Clean's statement, with the ℕ-balance, holds for `final`. -/
theorem fibK_statement : StatementPerm ChannelMap.byName ens final :=
  (statementPerm_iff (by decide) fibK_supported fibK_faithful final).mpr ⟨6, _, fibK_rel⟩

/-- `ChannelsByName` holds: one channel, and every interaction is on it. -/
theorem fibK_channelsByName : ChannelsByName ens := by
  refine ⟨by decide, fun c hc i hi _ => ?_⟩
  have hmap : c.rowOperations.interactions.map (·.channel) =
      [FibChannel.toRaw, FibChannel.toRaw] := by
    simp only [Ensemble.allTables, ens, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
      simp [Ensemble.verifierTable, Component.rowOperations, verifier, step, circuit_norm,
        Operations.interactions]
  have : i.channel ∈ [FibChannel.toRaw, FibChannel.toRaw] := hmap ▸ List.mem_map_of_mem hi
  simpa [ens] using this

/-- **Clean's own statement, ℕ-balanced per `RawChannel`**, through the bridge
(`statementRaw_iff`, under `ChannelsByName`). -/
theorem fibK_statementRaw : StatementRaw ens final :=
  (statementRaw_iff (by decide) fibK_supported fibK_faithful fibK_channelsByName final).mpr
    ⟨6, _, fibK_rel⟩

/-! ## Negative controls -/

/-- A wrong final state `(X^3, 1, 1)`. -/
def wrongFinal : fieldTriple K := (gX * gX * gX, 1, 1)

/-- A wrong final state: the verifier pulls `(X^3, 1, 1)`, which no step pushed. -/
theorem fibK_wrong_final :
    ¬ (toLayout tabs ens).rel 6 (pubVec wrongFinal) (toLayoutWit tabs (wit rows wrongFinal)) :=
      fun h =>
  absurd ((relBelow_iff fibK_buses _ _ _).mpr h) (by decide +kernel)

/-- One cell changed (`y` of the second step). -/
theorem fibK_mutated :
    ¬ (toLayout tabs ens).rel 6 (pubVec final)
      (toLayoutWit tabs (wit [#v[1, 0, 1], #v[gX, 1, 0], #v[gX * gX, 1, 0]] final)) := fun h =>
  absurd ((relBelow_iff fibK_buses _ _ _).mpr h) (by decide +kernel)

/-- `bits` registered as `{0}`: the honest rows look up `x = 1`. -/
theorem fibK_lookup_neg :
    ¬ (toLayout [⟨"bits", 1, [#v[0]]⟩] ens).rel 6 (pubVec final)
      (toLayoutWit [⟨"bits", 1, [#v[0]]⟩] (wit rows final)) := fun h =>
  absurd ((relBelow_iff (N := 2) (by decide +kernel) _ _ _).mpr h) (by decide +kernel)

/-- **The characteristic-2 catch**: the honest rows plus two copies of an unchained row `r`.
Each of `r`'s messages is pulled (or pushed) twice and never matched; a field-sum balance in
characteristic 2 counts it `1 + 1 = 0` (`two_eq_zero`), the ℕ-balance rejects it. -/
theorem fibK_junk_neg :
    ¬ (toLayout tabs ens).rel 7 (pubVec final)
      (toLayoutWit tabs (wit (rows ++ [#v[gX * gX * gX * gX * gX, 1, 1],
        #v[gX * gX * gX * gX * gX, 1, 1]]) final)) := fun h =>
  absurd ((relBelow_iff fibK_buses _ _ _).mpr h) (by decide +kernel)

/-- Two equal multiplicities cancel in `K`. -/
theorem two_eq_zero : (1 : K) + 1 = 0 := by decide

/-- **Clean's own balance over `K` is vacuous**: `BalancedInteractions` requires fewer
interactions than `ringChar K = 2`, so every list of two or more interactions fails it (see
`clean_balance_K` for the exact shape). -/
theorem clean_balance_vacuous (l : List (Interaction K)) (hl : 2 ≤ l.length) :
    ¬ BalancedInteractions l := by
  rintro ⟨h, -⟩
  rw [ringChar.eq K 2] at h
  omega

/-- **The exact shape** (the reviewer's P4): over `K` a balanced interaction list is empty or one
interaction of multiplicity `0`. So Clean's `Ensemble.Statement` over `K` says that no listed
channel carries any message at all. -/
theorem clean_balance_K (l : List (Interaction K)) (h : BalancedInteractions l) :
    l = [] ∨ ∃ i, l = [i] ∧ i.mult = 0 := by
  obtain ⟨hlen, hb⟩ := h
  rw [ringChar.eq K 2] at hlen
  match l, hlen with
  | [], _ => exact Or.inl rfl
  | [i], _ => exact Or.inr ⟨i, rfl, by simpa [balanceOf] using hb i.msg⟩
  | _ :: _ :: _, hlen => simp at hlen

/-- **Clean's requirement split is value-based too**: `Channel.toRaw` obliges an interaction of
multiplicity `m` to establish the channel's guarantee only when `m ≠ -1` and `m ≠ 0`. In `K` a
push (`m = 1 = -1`) therefore never carries a requirement, so Clean's assume-guarantee soundness
argument has nothing to discharge on the push side. -/
theorem clean_push_requirement_vacuous {Message : TypeMap} [ProvableType Message]
    (ch : Channel K Message) (msg : Vector K ch.toRaw.arity) (data : ProverData K) :
    ch.toRaw.Requirements 1 msg data :=
  fun h _ => absurd (show (1 : K) = -1 from rfl) h

/-! ## Direction from Clean's constructors, not from values -/

/-- In `K`, `-1 = 1`: the value of a multiplicity cannot give the direction. -/
theorem neg_one_eq_one : (-1 : K) = 1 := rfl

/-- A message of variables. -/
def msgV : fieldTriple (Expression K) := (var ⟨0⟩, var ⟨1⟩, var ⟨2⟩)

/-- `pulled` (multiplicity `-1`, guarantees assumed) receives, selector `1`. -/
theorem readMult_pull : readMult (pulled (channel := FibChannel) msgV).toRaw = (false, 1) := by
  decide

/-- `pushed` (multiplicity `1`) sends, selector `1`. -/
theorem readMult_push : readMult (pushed (channel := FibChannel) msgV).toRaw = (true, 1) := by
  decide

/-- `pulledIf en` receives with selector `en`. -/
theorem readMult_pullIf :
    readMult (pulledIf (channel := FibChannel) (var ⟨3⟩) msgV).toRaw = (false, var ⟨3⟩) := by
  decide

/-- **S8-m1**: a push whose selector is written `(1 : K) · en` (the same syntax as `(-1) · en`
in `K`) stays a send. -/
theorem readMult_pushIf_one :
    readMult (pushedIf (channel := FibChannel) ((1 : K) * (var ⟨3⟩ : Expression K)) msgV).toRaw =
      (true, (1 : K) * (var ⟨3⟩ : Expression K)) := by
  decide

/-- An interaction that assumes guarantees with a multiplicity not written `(-1) · e` is no
constructor's output; `ShapeOK` (part of `Supported`) rejects it. -/
theorem shape_neg :
    ShapeOK (⟨FibChannel.toRaw, var ⟨3⟩, toElements msgV, true⟩ : AbstractInteraction K) =
      false := by
  decide

/-! ## Channel pairs through a `ChannelMap` (S8-A11) -/

/-- The pull side of a leanerVM-style channel pair. -/
def PullCh : Channel K fieldTriple where
  name := "fib.pull"
  Guarantees _ _ := True

/-- The push side. -/
def PushCh : Channel K fieldTriple where
  name := "fib.push"
  Guarantees _ _ := True

/-- The step, pulling on one channel and pushing on the other. -/
def stepP : GeneralFormalCircuit K fieldTriple unit where
  main := fun (n, x, y) => do
    PullCh.pull (n, x, y)
    PushCh.push (n * Expression.const gX, y, x + y)
  channelsWithRequirements := [PullCh.toRaw, PushCh.toRaw]
  Spec _ _ _ := True
  soundness := by circuit_proof_start [PullCh, PushCh]
  completeness := by circuit_proof_start [PullCh, PushCh]

/-- The verifier: pull the final state on the pull side, push `(1, 0, 1)` on the push side. -/
def verifierP : GeneralFormalCircuit K fieldTriple unit where
  main := fun fin => do
    PullCh.pull fin
    PushCh.push (1, 0, 1)
  channelsWithRequirements := [PushCh.toRaw]
  Spec _ _ _ := True
  soundness := by circuit_proof_start [PullCh, PushCh]
  completeness := by circuit_proof_start [PullCh, PushCh]

/-- The ensemble with the channel pair. -/
def ensP : Ensemble K fieldTriple where
  tables := [⟨stepP⟩]
  channels := [PullCh.toRaw, PushCh.toRaw]
  verifier := verifierP
  verifier_length_zero := by simp [circuit_norm, verifierP]

/-- The pair map: both sides on bus `0`, the pull side receiving, the push side sending. -/
def pairs : ChannelMap := fun nm =>
  if nm = "fib.pull" then some (0, false) else if nm = "fib.push" then some (0, true) else none

/-- A Clean witness of `ensP`. -/
def witP (rs : List (Vector K 3)) (pub : fieldTriple K) : EnsembleWitness ensP where
  tables := [⟨⟨stepP⟩, 3, rs.map Vector.toArray, data0, by simp⟩]
  data := data0
  publicInput := pub
  same_length := rfl
  same_circuits := by intro i hi; simp [ensP] at hi; subst hi; rfl
  same_data := by simp

theorem pair_buses : ∀ C ∈ (toLayout [] ensP pairs).chips, ∀ p ∈ C.ports, p.bus < 2 := by
  decide +kernel

/-- **With the pair map** the honest witness satisfies the translated layout. -/
theorem pair_rel :
    (toLayout [] ensP pairs).rel 6 (pubVec final) (toLayoutWit [] (witP rows final)) :=
  (relBelow_iff pair_buses _ _ _).mp (by decide +kernel)

/-- **By name** (the default map) the same witness fails: each side of the pair is its own bus,
with messages in one direction only. -/
theorem pair_byName_neg :
    ¬ (toLayout [] ensP).rel 6 (pubVec final) (toLayoutWit [] (witP rows final)) := fun h =>
  absurd ((relBelow_iff (N := 2) (by decide +kernel) _ _ _).mpr h) (by decide +kernel)

theorem pair_faithful : LookupsFaithful [] ensP := by
  intro c hc l hl
  simp only [Ensemble.allTables, ensP, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> simp [Ensemble.verifierTable, Component.rowOperations, verifierP,
    stepP, circuit_norm, Operations.lookups] at hl

/-- Through the bridge, with the pair map: Clean's statement with the ℕ-balance of bus `0`. -/
theorem pair_statement : StatementPerm pairs ensP final :=
  (statementPerm_iff (by decide) (by decide +kernel) pair_faithful final).mpr ⟨6, _, pair_rel⟩

/-! ## The hypotheses can fail (S8-m5) -/

/-- `LookupsFaithful` fails when the lookup's table is not registered. -/
theorem fibK_not_faithful_unregistered : ¬ LookupsFaithful [] ens := by
  intro h
  have hc : (⟨step⟩ : Component K) ∈ ens.allTables := by simp [Ensemble.allTables, ens]
  have hne : (⟨step⟩ : Component K).rowOperations.lookups ≠ [] := by
    simp [Component.rowOperations, step, circuit_norm, Operations.lookups]
  obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨t, ht, -⟩ := h _ hc l hl
  simp at ht

/-- A map that puts "b" on bus `0` while "a" keeps its default bus `0`: a silent merge, which
`ChannelMap.Separate` (part of `Supported`) rejects. -/
def mixedMap : ChannelMap := fun nm => if nm = "b" then some (0, true) else none

theorem mixedMap_not_separate : ¬ mixedMap.Separate ["a", "b"] := by decide

/-- The pair map is separate: its two names share bus `0` with opposite directions. -/
theorem pairs_separate : pairs.Separate ["fib.pull", "fib.push"] := by decide

/-- A component that asserts `var 5 = 1` at width 3: it reads beyond its own row. -/
def wide : GeneralFormalCircuit K fieldTriple unit where
  main := fun _ => assertZero ((var ⟨5⟩ : Expression K) - 1)
  ProverAssumptions _ _ _ := False
  Spec _ _ _ := True
  soundness := by circuit_proof_start
  completeness := by circuit_proof_start

/-- The ensemble of `wide` alone. -/
def ensWide : Ensemble K unit where
  tables := [⟨wide⟩]
  channels := []

/-- `Supported` fails: `wide` reads variable `5` at width `3`. -/
theorem wide_not_supported : ¬ Supported ChannelMap.byName ensWide := by decide +kernel

/-- A Clean witness whose one row has six cells, the sixth `1`. -/
def cwWide : EnsembleWitness ensWide where
  tables := [⟨⟨wide⟩, 6, [#[0, 0, 0, 0, 0, 1]], data0, by simp⟩]
  data := data0
  publicInput := ()
  same_length := rfl
  same_circuits := by intro i hi; simp [ensWide] at hi; subst hi; rfl
  same_data := by simp

/-- Clean accepts it: the row's sixth cell is `1`. -/
theorem wide_holdsPerm : HoldsPerm ChannelMap.byName cwWide := by
  refine ⟨fun t ht => ?_, fun b hb => absurd hb (by simp [ChannelMap.nBus, chNames, ensWide])⟩
  simp only [EnsembleWitness.allTables, cwWide, List.mem_cons, List.not_mem_nil, or_false] at ht
  rw [table_constraints_iff]
  rcases ht with rfl | rfl
  · intro r _
    simp [EnsembleWitness.verifierTable, ensWide, GeneralFormalCircuit.empty, circuit_norm,
      Component.rowOperations, Operations.constraints, Operations.lookups]
  · intro r hr
    obtain rfl : r = 0 := by simpa using hr
    simp [rowEnv, wide, circuit_norm, Component.rowOperations, Operations.constraints,
      Operations.lookups, Air.Flat.Table.environment]

/-- **`Supported` is needed for completeness**: the translation of that Clean witness is
rejected, because the layout reads `0` beyond the component's width where Clean reads the row's
sixth cell. -/
theorem wide_rejected :
    ¬ (toLayout [] ensWide).rel 6 (pubVec (PublicIO := unit) ()) (toLayoutWit [] cwWide) := fun h =>
  absurd ((relBelow_iff (N := 0) (by decide +kernel) _ _ _).mpr h) (by decide +kernel)

end RecursionFast.Clean.FibK

/-! ## Channels are names: why `ChannelsByName` is needed (S8-M1; the reviewer's P2) -/

namespace RecursionFast.Clean.Names

open RecursionFast Air.Flat

/-- The listed channel: name "c"; its guarantee is never established (pushed only). -/
def chA : Channel K field where
  name := "c"
  Guarantees _ _ := False

/-- An unlisted channel with the same name and a different guarantee. -/
def chB : Channel K field where
  name := "c"
  Guarantees _ _ := True

/-- The two raw channels differ (their guarantees differ at multiplicity `-1`). -/
theorem chA_ne_chB : chA.toRaw ≠ chB.toRaw := by
  intro h
  simp only [Channel.toRaw, RawChannel.mk.injEq] at h
  have := congrFun (congrFun (congrFun (eq_of_heq h.2.2.1) (-1)) #v[0]) (fun _ _ => #[])
  simp [chA, chB] at this

/-- The verifier: push the input on `chA`, pull it on the unlisted `chB`. -/
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

theorem buses : ∀ C ∈ (toLayout [] ens).chips, ∀ p ∈ C.ports, p.bus < 1 := by decide +kernel

/-- A Clean witness: no tables, public input `1`. -/
def wit : EnsembleWitness ens where
  tables := []
  data := data0
  publicInput := (1 : K)
  same_length := rfl
  same_circuits := by intro i hi; simp [ens] at hi
  same_data := by simp

theorem faithful : LookupsFaithful [] ens := by
  intro c hc l hl
  simp only [Ensemble.allTables, ens, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  simp [Ensemble.verifierTable, Component.rowOperations, verifier, circuit_norm,
    Operations.lookups] at hl

/-- `StatementPerm` (by name) holds for `1`: both interactions are on bus "c". -/
theorem statementPerm_one : StatementPerm ChannelMap.byName ens (1 : K) :=
  (statementPerm_iff (by decide) (by decide +kernel) faithful (1 : K)).mpr
    ⟨6, toLayoutWit [] wit, (relBelow_iff buses _ _ _).mp (by decide +kernel)⟩

/-- Clean's own `Statement` fails for every input: the listed `chA` carries one push of
multiplicity `1`, so its `balanceOf` is `1 ≠ 0` (one interaction: not the length condition). -/
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

/-- **Name merging weakens**: `StatementPerm` (by name) accepts `1`; Clean's `Statement` rejects
it. `ChannelsByName` fails here (the unlisted `chB` has the listed name). -/
theorem name_merge_weakens : StatementPerm ChannelMap.byName ens (1 : K) ∧ ¬ ens.Statement 1 :=
  ⟨statementPerm_one, not_statement 1⟩

/-- The verifier pushes its input on the unlisted `chB` only. -/
def verifier2 : GeneralFormalCircuit K field unit where
  main := fun x => chB.push x
  channelsWithRequirements := [chB.toRaw]
  Spec _ _ _ := True
  soundness := by circuit_proof_start [chB]
  completeness := by circuit_proof_start [chB]

def ens2 : Ensemble K field where
  tables := []
  channels := [chA.toRaw]
  verifier := verifier2
  verifier_length_zero := by simp [circuit_norm, verifier2]

/-- Clean's `Statement` holds for every input: the listed `chA` carries no interaction. -/
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
    · simp only [Tables.interactionsWith, EnsembleWitness.allTables, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      rw [Air.Flat.Table.interactionsWith_eq_filter]
      simp [Air.Flat.Table.interactions, Operations.interactionValues, Component.interactions_eq,
        Component.rowOperations, EnsembleWitness.verifierTable, ens2, verifier2, circuit_norm,
        Operations.interactions, AbstractInteraction.eval, balanceOf, chA_ne_chB.symm,
        ringChar.eq K 2]

/-- `StatementPerm` (by name) rejects every input: bus "c" carries the push of `chB` and nothing
receives it. -/
theorem not_statementPerm2 (x : field K) : ¬ StatementPerm ChannelMap.byName ens2 x := by
  rintro ⟨w, -, -, hbal⟩
  have hw : w.tables = [] := by
    have := w.same_length; simp [ens2] at this; exact List.eq_nil_of_length_eq_zero this.symm
  have h0 := hbal 0 (by decide)
  have hmem : [w.publicInput] ∈
      (w.allTables.map fun t => tableMsgs ChannelMap.byName (chNames ens2) t 0 true).sum := by
    simp [EnsembleWitness.allTables, hw, tableMsgs, EnsembleWitness.verifierTable, ens2, verifier2,
      circuit_norm, Component.interactions_eq, Component.rowOperations, Operations.interactions,
      OnBus, chNames, ChannelMap.bus, ChannelMap.dir, ChannelMap.byName, readMult, chB, chA,
      Air.Flat.Table.environment, toElements]
  rw [h0] at hmem
  simp [EnsembleWitness.allTables, hw, tableMsgs, EnsembleWitness.verifierTable, ens2, verifier2,
    circuit_norm, Component.interactions_eq, Component.rowOperations, Operations.interactions,
    OnBus, chNames, ChannelMap.bus, ChannelMap.dir, ChannelMap.byName, readMult, chB, chA] at hmem

/-- **Name merging strengthens**: Clean's `Statement` accepts `1`; `StatementPerm` (by name)
rejects it. Again `ChannelsByName` fails. -/
theorem name_merge_strengthens :
    ens2.Statement (1 : K) ∧ ¬ StatementPerm ChannelMap.byName ens2 (1 : K) :=
  ⟨statement2 1, not_statementPerm2 1⟩

/-- `ChannelsByName` fails for both: the unlisted `chB` shares the listed name "c". -/
theorem not_channelsByName : ¬ ChannelsByName ens := by
  rintro ⟨-, h⟩
  have hc : ens.verifierTable ∈ ens.allTables := Ensemble.mem_allTables_verifierTable
  have hch : ens.verifierTable.rowOperations.interactions.map (·.channel) =
      [chA.toRaw, chB.toRaw] := by
    simp [Ensemble.verifierTable, Component.rowOperations, ens, verifier, circuit_norm,
      Operations.interactions]
  obtain ⟨i, hi, hiB⟩ : ∃ i ∈ ens.verifierTable.rowOperations.interactions,
      i.channel = chB.toRaw := by
    have : chB.toRaw ∈ ens.verifierTable.rowOperations.interactions.map (·.channel) := by
      rw [hch]; simp
    simpa using this
  have := h _ hc i hi (by rw [hiB]; simp [chNames, ens, chA, chB, Channel.toRaw])
  simp only [ens, List.mem_singleton] at this
  exact chA_ne_chB (hiB ▸ this).symm

end RecursionFast.Clean.Names
