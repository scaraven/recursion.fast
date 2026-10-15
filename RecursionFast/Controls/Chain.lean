/-
# Controls: the benchmark layout `L_chain` (Stage 6a, DESIGN §7.2, O-3)

The data are rendered from the generator's JSON (`harness/render-controls.sh` →
`Controls/ChainData.lean`); `harness/CHAIN-LAYOUT.md` documents the arithmetisation.

**What the kernel checks, and what it does not.** A compression is 160 rows of the G chip. With
`mul_fast` (the factors `0` and `1` short-cut) the kernel evaluates one G row in ≈ 1.8 s, so a
compression would take minutes and a chain far longer. The kernel therefore checks:
* *completeness* of the one-G-call harness on two calls of the chain: its honest witness satisfies
  `rel`, and the honest statement is `G` (`Blake2s.mix`);
* named single-cell faults, each rejected by the clause it names;
* the rot-7 wrap attack of the review (S6a-M1), rejected by the harness's byte check of the outputs;
* that the harness's G chip is the benchmark's (`G_link`), and the benchmark layout's caps.
It does **not** prove that the harness computes `G` (`rel → MixStmt`), nor anything about whole
chains. Soundness is tested by `harness/check-chain.py` on whole chains, where the next
decomposition range-checks every output, with one layout mutant per mechanism
(`docs/stages/S6a-RESULT.md`).

Positive (completeness and structure):
* `LG0_rel`, `LG79_rel`, `LG0_relK`: the one-G-call harness for G-calls 0 and 79 of the chain
  started at the example secret (bytes `00 … 1f`), add table trimmed to the rows the call uses;
  call 79 has a zero message word;
* `LG0_mix`, `LG79_mix`: the honest statements are `G` on their inputs (the contract's
  `Blake2s.mix`);
* `LGF_rel`: the harness for G-call 0 with the benchmark's full `2^17`-row `add8` table; the
  lookups into `add8` are certified row by row (`mem_traffic`, `add8Row`);
* `G_link`: the harness's G chip is `L_chain`'s G chip except for the last-row pin's constant;
  `harness_G`: the three harnesses share one G chip; `LG0_trim`: the trimmed tables consist of
  `add8` rows;
* `Lchain_admissible`, `LGF_admissible`: `L_chain(16)` and the harness are admissible at class 24
  (`L_chain(n)` depends on `n` only through three constants).

Negative:
* `LG0_neg_byte`: one input byte of the G row changed: the gadget constraint `in_A` fails;
* `LG0_neg_sum`: one add result byte changed (it occurs in no gadget constraint): the add lookups
  (bus 0) fail;
* `LG0_neg_out`: a wrong output word claimed by a consistent public table: the `eq` bus `GOUT`
  fails;
* `LG0_neg_wrap`, `LG0_wrap_rest`: the review's attack, a wrong rot-7 wrap nibble making `b'` a
  33-bit value `b' ⊕ (1 + X^32)`: only the byte check `PAIR` (bus 2) rejects it;
* `Lchain_not_admissible_23`, `LGF_not_admissible_23`: the `add8` table (786,432 cells) exceeds
  the fixed-table cap `2^(k-4)` below class 24, so `k_min = 24` for every chain length.
-/
import RecursionFast.Controls.ChainData
import RecursionFast.Library.Layout
import RecursionFast.Library.Field
import RecursionFast.Contract.Protocol
import RecursionFast.Contract.Hash.Blake2s
import Mathlib.Tactic.IntervalCases

namespace RecursionFast.Controls.Chain
open RecursionFast

/-- The gadget clause of `rel`: every row of every chip satisfies its gadget. -/
def GadgetsHold {F : Type} [Zero F] [One F] [Add F] [Mul F] [DecidableEq F] (L : Layout F)
    (w : List (Table F)) : Prop :=
  ∀ ct ∈ L.chips.zip w, ∀ r < ct.2.rows, ct.1.gadget.holds (view ct.1 ct.2 r)

/-- Decidable for any product on the carrier, as the contract's `relBelow` (so `mul_fast` can be
rewritten under it). -/
instance {F : Type} [Zero F] [One F] [Add F] [Mul F] [DecidableEq F] (L : Layout F)
    (w : List (Table F)) : Decidable (GadgetsHold L w) := by
  unfold GadgetsHold Gadget.holds; infer_instance

/-! ## Admissibility: the class floor of the benchmark -/

/-- The benchmark layout `L_chain(16)` is admissible at class 24 ... -/
theorem Lchain_admissible : Lchain.Admissible 24 := by decide +kernel

/-- ... and not at 23: its fixed tables (786,464 cells) exceed `2^(23-4)`. -/
theorem Lchain_not_admissible_23 : ¬ Lchain.Admissible 23 := by decide +kernel

theorem LGF_admissible : LGF.Admissible 24 := by decide +kernel

theorem LGF_not_admissible_23 : ¬ LGF.Admissible 23 := by decide +kernel

theorem LG0_admissible : LG0.Admissible 20 := by decide +kernel

/-! ## One G-call, add table trimmed: decided by the kernel -/

/-- The contract's product on `K` is the product with the factors `0` and `1` short-cut. The
kernel evaluates a `K` product as a 64-step loop plus two folds (tens of milliseconds, whatever the
factors), and most products of a G row have a factor `0` or `1` (a gate, a coefficient, a zero
cell), so `rel` is decided with this instance in place of the contract's. -/
theorem mul_fast : K.instMul =
    ⟨fun a b => if a = 0 ∨ b = 0 then 0 else if a = 1 then b else if b = 1 then a else a * b⟩ :=
  congrArg Mul.mk (funext₂ fun a b => show a * b = _ by split_ifs <;> simp_all)

/-- The harness for G-call 0 (add table trimmed) satisfies the relation, decided by the kernel. -/
theorem LG0_rel : LG0.rel 20 LG0_stmt LG0_wit := by
  rw [← relBelow_iff (N := 8) (by decide), mul_fast]; decide +kernel

theorem LG0_relK : ((LG0, LG0_stmt), LG0_wit) ∈ relK 20 := ⟨LG0_admissible, LG0_rel⟩

/-- The harness for G-call 79 (diagonal step of round 9; its `x` is a zero message word). -/
theorem LG79_rel : LG79.rel 20 LG79_stmt LG79_wit := by
  rw [← relBelow_iff (N := 8) (by decide), mul_fast]; decide +kernel

/-- Statement cell `i` as a 32-bit word. -/
def word (x : Fin 32 → K) (i : Fin 32) : UInt32 := (x i).bits.toNat.toUInt32

/-- The statement `(a, b, c, d, x, y, a', b', c', d', 0, …)` of a harness says `G` maps the inputs
to the outputs: the cells are 32-bit words and the contract's `Blake2s.mix` agrees. -/
def MixStmt (x : Fin 32 → K) : Prop :=
  (∀ i : Fin 10, (x (Fin.castLE (by omega) i)).bits.toNat < 2 ^ 32) ∧
  ((Blake2s.mix #v[word x 0, word x 1, word x 2, word x 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      0 1 2 3 (word x 4) (word x 5)).toList.take 4 = [word x 6, word x 7, word x 8, word x 9])

instance (x : Fin 32 → K) : Decidable (MixStmt x) := inferInstanceAs (Decidable (_ ∧ _))

theorem LG0_mix : MixStmt LG0_stmt := by decide +kernel

theorem LG79_mix : MixStmt LG79_stmt := by decide +kernel

/-- The `add8` row of an add lookup `(x, y, cin, …)`: `x + 2^8 y + 2^16 cin`. -/
def add8Row (m : List K) : ℕ :=
  (m.getD 0 0).bits.toNat + 256 * (m.getD 1 0).bits.toNat + 65536 * (m.getD 2 0).bits.toNat

/-- Every row of chip `C`'s fixed table is a row of `add8`: row `r` is `add8`'s row
`add8Row (cells 1, 2, 3 of r)`. -/
def trimOK (C : Chip K) : Bool :=
  match C.fixed with
  | some t => (List.range t.rows).all fun r =>
      let m := (List.range 6).map (t.cell r)
      decide (add8Row (m.drop 1) < 2 ^ 17) &&
        decide ((List.range 6).map (add8.cell (add8Row (m.drop 1))) = m)
  | none => false

/-- The trimmed add tables of the harnesses are made of `add8` rows: a lookup they serve is an
`add8` lookup. -/
theorem LG0_trim : trimOK LG0_chip2 = true ∧ trimOK LG79_chip2 = true := by decide +kernel

/-- The three harnesses have the same G chip (rendered separately from their JSON). -/
theorem harness_G : LG79_chip1 = LG0_chip1 ∧ LGF_chip1 = LG0_chip1 := ⟨rfl, rfl⟩

/-- Matrix `j` of a chip's gadget, its indices read as naturals. -/
def entsN (C : Chip K) (j : ℕ) : List (ℕ × ℕ × K) :=
  if h : j < C.gadget.t then (C.gadget.M ⟨j, h⟩).map fun e => (e.1.val, e.2.1.val, e.2.2) else []

/-- Term `i` of a chip's gadget: its matrix multiset and coefficient. -/
def termN (C : Chip K) (i : ℕ) : List ℕ × K :=
  if h : i < C.gadget.q then ((C.gadget.S ⟨i, h⟩).map Fin.val, C.gadget.c ⟨i, h⟩) else ([], 0)

/-- **The harness's G chip is the benchmark's** (review S6a-m1): same columns, ports, shape and
term, no fixed table, the same gate matrix, and the same linear matrix except entry 13, the
constant of `rho_last` (constraint 6): `γ^1` for one G-call, `γ^(160·16 − 1)` in `L_chain(16)`. -/
theorem G_link :
    LG0_chip1.cols = Lchain_chip1.cols ∧ LG0_chip1.ports = Lchain_chip1.ports ∧
    LG0_chip1.fixed.isNone ∧ Lchain_chip1.fixed.isNone ∧
    LG0_chip1.gadget.cons = Lchain_chip1.gadget.cons ∧ LG0_chip1.gadget.t = Lchain_chip1.gadget.t ∧
    LG0_chip1.gadget.q = Lchain_chip1.gadget.q ∧ termN LG0_chip1 0 = termN Lchain_chip1 0 ∧
    entsN LG0_chip1 0 = entsN Lchain_chip1 0 ∧
    (entsN LG0_chip1 1).eraseIdx 13 = (entsN Lchain_chip1 1).eraseIdx 13 ∧
    ((entsN LG0_chip1 1)[13]?).map (·.1) = some 6 ∧
    ((entsN Lchain_chip1 1)[13]?).map (·.1) = some 6 := by
  decide +kernel

/-! ## Negative controls -/

/-- `T` with cell `(r, c)` replaced by `v`. -/
def setCell (T : Table K) (r c : ℕ) (v : K) : Table K :=
  ⟨T.rows, fun r' c' => if r' = r ∧ c' = c then v else T.cell r' c'⟩

/-- The witness `w` with cell `(r, c)` of table `i` xored with `v`. -/
def xorAt (w : List (Table K)) (i r c : ℕ) (v : K) : List (Table K) :=
  w.mapIdx fun j T => if j = i then setCell T r c (T.cell r c + v) else T

/-- The witness `w` with cell `(r, c)` of table `i` xored with `1`. -/
def flip (w : List (Table K)) (i r c : ℕ) : List (Table K) := xorAt w i r c 1

/-- Byte 0 of the input `a` (G row 0, column `P0` = 11) changed: `in_A` fails. -/
theorem LG0_neg_byte : ¬ LG0.rel 20 LG0_stmt (flip LG0_wit 1 0 11) := fun h =>
  -- constraint 8 (`in_A`) of G row 0
  absurd (h.2.2.1 _ (List.getElem_mem (n := 1) (by decide)) 0 (by decide) ⟨8, by decide⟩)
    (by decide +kernel)

/-- Byte 0 of `a1 + b1` (G row 1, column `T0` = 31) changed. `T` occurs in no gadget constraint,
so only the add lookups (bus 0) see it. -/
theorem LG0_neg_sum : ¬ LG0.rel 20 LG0_stmt (flip LG0_wit 1 1 31) := fun h =>
  absurd (h.2.2.2.1 0) (by decide +kernel)

/-- The output `b'` (statement cell 7) claimed with its lowest bit flipped, the public table
agreeing with the claim (cell 7 and its byte `E7_0`, column 39): the G chip sends the true `b'` on
the `eq` bus `GOUT`. -/
theorem LG0_neg_out : ¬ LG0.rel 20 (fun i => if i.val = 7 then LG0_stmt i + 1 else LG0_stmt i)
    (flip (flip LG0_wit 0 0 7) 0 0 39) := fun h =>
  absurd (h.2.2.2.1 5) (by decide +kernel) -- bus 5 is `GOUT`

/-- `1 + X^32`: a wrong rot-7 wrap nibble `W ⊕ e` changes the packed `b'` by `(1 + X^32)·e`. -/
abbrev wrapE : K := kx 0x100000001

/-- The review's attack (S6a-M1) on G-call 0: the phase-1 wrap nibble `W` (G row 1, column 52)
xored with `1` and the output `b'` (column `B` = 6) with `1 + X^32`, the public table agreeing:
statement cell 7, and its bytes `E7_0` (column 39) and `E7_3` (column 42, now `≥ 2^8`). -/
def wrapWit : List (Table K) :=
  xorAt (xorAt (xorAt (xorAt (xorAt LG0_wit 1 1 52 1) 1 1 6 wrapE) 0 0 7 wrapE) 0 0 39 1)
    0 0 42 (kx 0x100)

/-- The statement of the attack: `b'` is the 33-bit value `b' ⊕ (1 + X^32)`, not `G`. -/
def wrapStmt : Fin 32 → K := fun i => if i.val = 7 then LG0_stmt i + wrapE else LG0_stmt i

theorem wrapStmt_not_mix : ¬ MixStmt wrapStmt := by decide +kernel

/-- The harness rejects the attack: the top byte of `b'` is not a byte, so the byte-pair lookup
`PAIR` (bus 2) fails. -/
theorem LG0_neg_wrap : ¬ LG0.rel 20 wrapStmt wrapWit := fun h =>
  absurd (h.2.2.2.1 2) (by decide +kernel) -- bus 2 is `PAIR`

/-- ... and only there: every gadget holds (the wrong `W` is a nibble and `b'` agrees with it),
and every other bus balances (`NIB` serves the nibble, `GOUT` carries the claimed `b'`). Without
the byte check the harness would accept it (the review's `A6_rel_not_mix`). -/
theorem LG0_wrap_rest : GadgetsHold LG0 wrapWit ∧ ∀ b < 8, b ≠ 2 →
      (LG0.bus b).Balanced (traffic LG0 wrapWit b true) (traffic LG0 wrapWit b false) := by
  rw [mul_fast]; decide +kernel

/-! ## One G-call with the full `add8` table -/

/-- Membership in a list sum of multisets. -/
theorem mem_list_sum {α : Type} {a : α} : ∀ {l : List (Multiset α)}, a ∈ l.sum ↔ ∃ s ∈ l, a ∈ s
  | [] => by simp
  | x :: l => by simp [List.sum_cons, Multiset.mem_add, mem_list_sum]

/-- A row of a sending port's table is on the bus: if row `r` of chip `C`'s table `T` selects
port `p`, its message is in `traffic L w p.bus p.send`. -/
theorem mem_traffic {L : Layout K} {w : List (Table K)} {C : Chip K} {T : Table K}
    (h : (C, T) ∈ L.chips.zip w) {p : Port} (hp : p ∈ C.ports) {r : ℕ} (hr : r < T.rows)
    (hsel : T.cell r p.sel = 1) : p.msg.map (T.cell r) ∈ traffic L w p.bus p.send := by
  refine mem_list_sum.2 ⟨_, List.mem_map.2 ⟨(C, T), h, rfl⟩, mem_list_sum.2 ⟨T.msgs p, ?_, ?_⟩⟩
  · exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, by simp⟩, rfl⟩
  · exact Multiset.mem_coe.2
      (List.mem_map.2 ⟨r, List.mem_filter.2 ⟨List.mem_range.2 hr, by simp [hsel]⟩, rfl⟩)

/-- Every lookup sent to bus `b` by the receiving ports is row `add8Row m` of `add8`, read through
the columns `cs` of the `add8` port on that bus. -/
theorem add8_sub {b : ℕ} {cs : List ℕ} (hp : (⟨b, true, 0, cs⟩ : Port) ∈ LGF_chip2.ports)
    (key : ∀ m ∈ traffic LGF LGF_wit b false,
      add8Row m < 2 ^ 17 ∧ cs.map (add8.cell (add8Row m)) = m) :
    ∀ m ∈ traffic LGF LGF_wit b false, m ∈ traffic LGF LGF_wit b true := by
  intro m hm
  obtain ⟨hr, he⟩ := key m hm
  rw [← he]
  exact mem_traffic (C := LGF_chip2) (T := add8)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) hp hr rfl

/-- The harness for G-call 0 with the benchmark's `add8` table satisfies the relation at class
24: the fixed clause holds because the witness table is `add8` itself, the `add8` lookups (buses
0, 1 and the output byte check 2) by `add8_sub`, everything else by the kernel. -/
theorem LGF_rel : LGF.rel 24 LGF_stmt LGF_wit := by
  rw [← relBelow_iff (N := 8) (by decide)]
  refine ⟨rfl, ?_, ?_, ?_, by decide +kernel, by decide +kernel⟩
  · -- fixed tables: chip 2's witness is `add8` itself, chip 3's is decided
    intro ct hct t ht
    simp only [LGF, LGF_wit, List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
      List.not_mem_nil, or_false] at hct
    rcases hct with rfl | rfl | rfl | rfl
    · exact absurd ht (Option.not_mem_none _)
    · exact absurd ht (Option.not_mem_none _)
    · obtain rfl := Option.some.inj (Option.mem_def.1 ht)
      exact ⟨rfl, fun _ _ _ _ => rfl⟩
    · obtain rfl := Option.some.inj (Option.mem_def.1 ht)
      decide +kernel
  · -- gadgets: chips 0, 1 and their tables are `LG0`'s (`LG0_rel`); chips 2 (`add8`) and 3
    -- (`NIB`) have no constraint
    intro ct hct r hr
    simp only [LGF, LGF_wit, List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
      List.not_mem_nil, or_false] at hct
    rcases hct with rfl | rfl | rfl | rfl
    · exact LG0_rel.2.2.1 _ List.mem_cons_self r hr
    · exact LG0_rel.2.2.1 _ (List.mem_cons_of_mem _ List.mem_cons_self) r hr
    all_goals exact fun i => i.elim0
  · -- buses: the `add8` lookups (buses 0, 1, 2) row by row, the others decided
    intro b hb
    interval_cases b
    · exact add8_sub (b := 0) (cs := [1, 2, 3, 4, 5]) (by decide) (by decide +kernel)
    · exact add8_sub (b := 1) (cs := [1, 2, 3, 4]) (by decide) (by decide +kernel)
    · exact add8_sub (b := 2) (cs := [1, 2]) (by decide) (by decide +kernel)
    all_goals decide +kernel

end RecursionFast.Controls.Chain
