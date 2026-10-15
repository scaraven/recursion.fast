# Upstream note: Clean's channel balance in characteristic 2

**For:** Clean (`https://github.com/Verified-zkEVM/clean`), checked against revision `42fe4b26`.

**From:** recursion.fast Stage 8 (DESIGN §9.2, §12 O-5).

**Status:** a proposal only. Whether to open a PR is the user's decision; O-5 stays open and
points here.

## The problem

Clean balances a channel by summing multiplicities **in the field**
(`Clean/Air/Balance.lean`):

```lean
def balanceOf (interactions : List (Interaction F)) (msg : Array F) : F :=
  interactions.filter (·.msg = msg) |>.map (·.mult) |>.sum

def BalancedInteractions (interactions : List (Interaction F)) : Prop :=
  (interactions.length < ringChar F ∨ ringChar F = 0) ∧
  ∀ msg : Array F, balanceOf interactions msg = 0
```

This fails in a binary field `GF(2^n)`, where `ringChar = 2`, in three ways.

1. **The length side condition.**
   - The condition `interactions.length < ringChar F` makes every list of two or more
     interactions unbalanced.
   - Proved over our `K = GF(2^64)` as `RecursionFast/Clean/Examples.lean`:
     ```lean
     theorem clean_balance_vacuous (l : List (Interaction K)) (hl : 2 ≤ l.length) :
         ¬ BalancedInteractions l
     ```
   - **The exact shape is sharper** (`clean_balance_K`, same file): over `K` a balanced list is
     `[]` or a single interaction of multiplicity `0`.
     ```lean
     theorem clean_balance_K (l : List (Interaction K)) (h : BalancedInteractions l) :
         l = [] ∨ ∃ i, l = [i] ∧ i.mult = 0
     ```
   - As a result, `Ensemble.Statement` (`Clean/Air/FlatEnsemble.lean`, through
     `EnsembleWitness.BalancedChannels`) over a binary field says that **no listed channel
     carries any message at all** (beyond one silent interaction in the whole witness). It is
     unusable.
2. **The field sum.** Without the side condition, the sum would be wrong instead:
   - A message pushed twice and never pulled counts `1 + 1 = 0`, so it balances.
   - Our control `fibK_junk_neg` adds two copies of an unchained row. Its messages cancel in a
     field sum but are rejected by an ℕ count.
3. **Direction from the value.**
   - A pull is written with multiplicity `-1` and a push with `1`. In characteristic 2,
     `-1 = 1`, so the direction cannot be recovered from an evaluated `Interaction`.
   - The same reading drives the guarantee/requirement split in `Channel.toRaw`
     (`Clean/Circuit/Channel.lean`):
     ```lean
     Guarantees mult message data := mult = -1 → channel.Guarantees …
     Requirements mult message data := mult ≠ -1 → mult ≠ 0 → channel.Guarantees …
     ```
   - In `K` a push (`mult = 1 = -1`) has a vacuous requirement. Proved as:
     ```lean
     theorem clean_push_requirement_vacuous (ch : Channel K Message) (msg) (data) :
         ch.toRaw.Requirements 1 msg data
     ```
   - So Clean's assume-guarantee argument never obliges a pusher to establish the guarantee
     that pullers assume.
   - The composition theorems avoid this by assuming `[Fact (ringChar F ≠ 2)]`.
     `one_ne_neg_one` and `guarantees_of_requirements_of_requirements_of_guarantees` in
     `Balance.lean`, and `addVm_soundVmChannel_of_soundChannels` and `addVm` in `Vm.lean`,
     all carry it. They therefore do not apply to binary fields.

leanerVM found the same problem as its finding C2. It defines its own `BalancedPair` as a
`List.Perm` and takes the direction from the channel. recursion.fast defines `StatementPerm`
(below).

## What recursion.fast does instead (a working model of the fix)

The model is in `RecursionFast/Clean/{ToLayout,Semantics}.lean` (Stage 8, kernel-checked, no
`sorry`).

- **Direction from Clean's constructors.**
  - `readMult : AbstractInteraction F → Bool × Expression F` reads the constructor, never a
    value:
    - `pull`/`pulled(If)` set `assumeGuarantees` and write `(-1) · e`: receive, selector `e`;
    - `push`/`pushed(If)`/`emit` clear it: send, selector the multiplicity.
  - Any other shape is rejected by the bridge's `Supported` (`ShapeOK`).
  - In `K` a push written `pushedIf ((1 : K) · en)` stays a send (`readMult_pushIf_one`).
  - A `ChannelMap` can instead fix the direction per channel, as for leanerVM's pull/push
    channel pairs.
- **Selector semantics.** An interaction contributes its message once when its selector
  evaluates to `1`, and nothing otherwise.
- **Balance counted in ℕ.**
  ```lean
  def BalancedPerm (cm : ChannelMap) (w : EnsembleWitness ens) : Prop :=
    ∀ b < cm.nBus (chNames ens),
      (w.allTables.map fun t => tableMsgs cm (chNames ens) t b true).sum =
        (w.allTables.map fun t => tableMsgs cm (chNames ens) t b false).sum
  def StatementPerm cm ens x := ∃ w, w.publicInput = x ∧ w.Constraints ∧ BalancedPerm cm w
  ```
  Here `tableMsgs` is a `Multiset (List F)`. Under the default map with distinct channel names
  this is "every channel balances" (`balancedPerm_byName_iff`).
- **Exactness.** `toLayout_rel_iff` and `statementPerm_iff` show this is exactly the relation
  of the translated layout. That relation is a bus relation with `Multiset` balance, counted in
  ℕ.
- **Clean's channels.** `StatementPerm` identifies a channel by its name. Under `ChannelsByName`
  (distinct listed names, and no unlisted `RawChannel` sharing one), `statementRaw_iff` states
  the bridge for `StatementRaw`, which is Clean's `Ensemble.Statement` with the ℕ-balance per
  `RawChannel`, Clean's own filter.

## The proposed change to Clean

Either of two variants works; both are characteristic-independent.

### Variant A: a direction bit and ℕ-multiset balance

This mirrors `StatementPerm` and is the smaller semantic change.

- **`Clean/Circuit/Channel.lean`.**
  - Add `send : Bool` to `ChannelInteraction`, `AbstractInteraction` and `Interaction`. The
    `pulled`, `pulledIf`, `pull` and `pullIf` constructors set `false`; `pushed`, `pushedIf`,
    `push`, `pushIf` and `emit` set `true`.
  - Keep `mult` as the **selector** (`0`/`1` by the circuit's own constraint, as `pullIf`
    already intends).
  - Rewrite `Channel.toRaw` so that `Guarantees` and `Requirements` branch on `send`:
    ```lean
    Guarantees send mult message data := ¬send → mult = 1 → channel.Guarantees …
    Requirements send mult message data := send → mult = 1 → channel.Guarantees …
    ```
- **`Clean/Air/Balance.lean`.**
  - Replace `balanceOf` / `BalancedInteractions` by a multiset equality:
    ```lean
    def sent (is : List (Interaction F)) : Multiset (Array F) :=
      ((is.filter fun i => i.send ∧ i.mult = 1).map (·.msg) : Multiset _)
    def received (is : List (Interaction F)) : Multiset (Array F) :=
      ((is.filter fun i => ¬i.send ∧ i.mult = 1).map (·.msg) : Multiset _)
    def BalancedInteractions (is) : Prop := sent is = received is
    ```
  - `exists_push_of_pull` becomes `Multiset.mem` reasoning, with no `ringChar`.
  - `guarantees_of_requirements_of_requirements_of_guarantees` loses `[Fact (ringChar F ≠ 2)]`:
    it matches pulls to pushes by `Multiset` membership, not by field counting.
- **`Clean/Air/FlatEnsemble.lean`.** `BalancedChannel` and `BalancedChannels` are unchanged in
  shape, now over the new `BalancedInteractions`. `Statement`, `Soundness` and
  `TableSoundness` are unchanged.
- **`Clean/Air/Vm.lean`.** Drop the `Fact (ringChar F ≠ 2)` hypotheses. Every proof that used
  `one_ne_neg_one` to tell a push from a pull now reads `send` instead.
- **`Clean/Air/OrderedChannel.lean`.** It carries no `Fact (ringChar F ≠ 2)`. It case-splits on
  `ringChar F = 0` (the length side condition, around line 338), and that case split is adapted
  to the ℕ-multiset balance.
- **Cost.** The circuits keep compiling: `send` is set by the constructors, and multiplicities
  that were `±1` become selector `1`.
  - LogUp-style emitters with arbitrary counts (`emit m`, e.g. `pushBytes`) need either `m`
    interactions or a lookup.
  - **This is the one semantic loss.** A count in a field element is not a multiplicity in
    characteristic 2.

### Variant B: multiplicity in ℤ

- `Interaction.mult : ℤ`, with `pulled` as `-1` and `pushed` as `1`, and `balanceOf` summed
  in ℤ.
- **The obstacle.** The multiplicity is an `Expression F` evaluated in `F`, so a ℤ multiplicity
  must be a constant of the circuit (not a witness expression), or carry a ℕ-valued witness
  decomposition. This changes `ChannelInteraction.mult`'s type and every `*If` constructor.
- **Cost.** Larger than A, and still needs a bound on witness counts. A is recommended.

## Files touched in Clean `42fe4b26`

| File | Change |
|---|---|
| `Clean/Circuit/Channel.lean` | `send` field; constructors; `Channel.toRaw` guarantees/requirements by `send` |
| `Clean/Circuit/Basic.lean` | `Channel.pull/pullIf/push/pushIf/emit` set `send` |
| `Clean/Air/Balance.lean` | ℕ-multiset `BalancedInteractions`; drop `ringChar` side condition and the `Fact (ringChar F ≠ 2)` hypotheses |
| `Clean/Air/FlatEnsemble.lean` | none in statements (uses the new balance) |
| `Clean/Air/Vm.lean` | drop `Fact (ringChar F ≠ 2)`; direction from `send` |
| `Clean/Air/OrderedChannel.lean` | adapt the `ringChar F = 0` case split (the length side condition); it has no `Fact (ringChar F ≠ 2)` |
| `Clean/Air/FlatComponent.lean` | `Table.interactions` carries `send` (through `AbstractInteraction.eval`) |
| examples using `emit m` with counts (`Examples/FibonacciWithChannels.lean`, `pushBytes`) | rewrite the byte range check as a `lookup` into a `StaticTable` |

Diff sketch (Variant A, `Balance.lean` core):

```diff
-def balanceOf (interactions : List (Interaction F)) (msg : Array F) : F :=
-  interactions.filter (·.msg = msg) |>.map (·.mult) |>.sum
-
-def BalancedInteractions (interactions : List (Interaction F)) : Prop :=
-  (interactions.length < ringChar F ∨ ringChar F = 0) ∧
-  ∀ msg : Array F, balanceOf interactions msg = 0
+/-- Messages sent (resp. received): interactions in that direction whose selector is `1`. -/
+def sentMsgs (is : List (Interaction F)) : Multiset (Array F) :=
+  ((is.filter fun i => i.send && decide (i.mult = 1)).map (·.msg) : Multiset (Array F))
+def receivedMsgs (is : List (Interaction F)) : Multiset (Array F) :=
+  ((is.filter fun i => !i.send && decide (i.mult = 1)).map (·.msg) : Multiset (Array F))
+
+/-- Channel balance, counted in ℕ: the messages sent and received are equal as multisets. -/
+def BalancedInteractions (interactions : List (Interaction F)) : Prop :=
+  sentMsgs interactions = receivedMsgs interactions
```

## Evidence in this repository

All of the following are kernel-checked, with axioms within `propext`, `Classical.choice` and
`Quot.sound`.

- **Clean's failure modes:** `clean_balance_vacuous`, `clean_balance_K` (exact shape),
  `clean_push_requirement_vacuous`, `fibK_junk_neg`.
- **The model is exact:** `toLayout_rel_iff`, `statementPerm_iff`.
- **The model is usable:** `fibK_statement` and `pair_statement` give the statement on a K
  example.
- **Where to read more:** `docs/stages/S8-RESULT.md`, and amendments S8-A3, S8-A7 and S8-A11.
