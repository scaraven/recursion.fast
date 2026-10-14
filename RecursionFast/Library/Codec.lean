/-
  RecursionFast.Library.Codec  (UNTRUSTED, kernel-checked)

  Layouts and witnesses as lists of `K`-elements, for the toy protocol (`Controls/Toy.lean`) and
  the trivial baseline (DESIGN §7.3): serialisers (`eLayout`, `eWit`), parsers (`pLayout`,
  `pWit`), the round-trip theorems and the length bounds that fit them into the contract's
  oracle caps (index `2^(k+8)`, messages `2^(k+10)`, S1-A9).

  A number `n < 2^64` is stored as the element with bits `n`. A parser reads a prefix of a list
  and returns the rest; past the end it reads `0`, so an oracle (the serialisation followed by
  zeros) parses like the serialisation.

  * `pLayout_eLayout`: an admissible layout of class `k ≤ 28` parses back to itself up to what
    `rel` does not read (`Layout.normal`, `Library/Layout.lean`); `eLayout_length`: its
    serialisation has at most `2^(k+8)` elements when `20 ≤ k`.
  * `pWit_eWit`: a witness of such a layout parses back to itself up to what `rel` does not read
    (`Layout.trim`); `eWit_length`: at most `2^(k+10)` elements.
-/
import RecursionFast.Library.Layout
import RecursionFast.Contract.Shapes

namespace RecursionFast.Codec

open RecursionFast

/-! ## Numbers -/

/-- A number as an element of `K` (its low 64 bits). -/
def ofNat (n : ℕ) : K := ⟨BitVec.ofNat 64 n⟩

/-- An element of `K` as a number. -/
def toNat (a : K) : ℕ := a.bits.toNat

theorem toNat_ofNat {n : ℕ} (h : n < 2 ^ 64) : toNat (ofNat n) = n := by
  simp only [toNat, ofNat, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem K_zero_ne_one : (0 : K) ≠ 1 := by decide

/-! ## Serialisers -/

/-- An entry of a sparse matrix: row, column, value. -/
def eEntry {m n : ℕ} (e : Fin m × Fin n × K) : List K := [ofNat e.1, ofNat e.2.1, e.2.2]

/-- A sparse matrix: the number of entries, then the entries. -/
def eMat {m n : ℕ} (M : List (Fin m × Fin n × K)) : List K :=
  ofNat M.length :: (M.map eEntry).flatten

/-- A term's matrix list: its length, then the matrices. -/
def eS {t : ℕ} (S : List (Fin t)) : List K := ofNat S.length :: S.map fun j => ofNat j.val

/-- A gadget: `cons, t, q`, the matrices, the term lists, the coefficients. -/
def eGadget {w : ℕ} (g : Gadget K w) : List K :=
  [ofNat g.cons, ofNat g.t, ofNat g.q] ++ ((List.ofFn g.M).map eMat).flatten ++
    ((List.ofFn g.S).map eS).flatten ++ List.ofFn g.c

/-- A port: bus, direction, selector, message length, message columns. -/
def ePort (p : Port) : List K :=
  [ofNat p.bus, if p.send then 1 else 0, ofNat p.sel, ofNat p.msg.length] ++ p.msg.map ofNat

/-- A table of `cols` columns: its height, then its cells row by row. -/
def eTable (cols : ℕ) (T : Table K) : List K :=
  ofNat T.rows :: (List.range (T.rows * cols)).map fun q => T.cell (q / cols) (q % cols)

/-- An optional fixed table: `0`, or `1` and the table. -/
def eFixed (cols : ℕ) : Option (Table K) → List K
  | none => [0]
  | some t => 1 :: eTable cols t

/-- A chip: columns, gadget, ports (count, then each), fixed table. -/
def eChip (C : Chip K) : List K :=
  ofNat C.cols :: eGadget C.gadget ++ (ofNat C.ports.length :: (C.ports.map ePort).flatten) ++
    eFixed C.cols C.fixed

/-- **A layout**: chip count, public chip, the kinds of buses `0 … 255`, the chips. -/
def eLayout (L : Layout K) : List K :=
  [ofNat L.chips.length, ofNat L.pub] ++
    (List.range (2 ^ 8)).map (fun b => if L.bus b = .sub then 1 else 0) ++
    (L.chips.map eChip).flatten

/-- **A witness** of layout `L`: table `i` with chip `i`'s columns. -/
def eWit (L : Layout K) (w : List (Table K)) : List K :=
  ((L.chips.zip w).map fun ct => eTable ct.1.cols ct.2).flatten

/-! ## Parsers -/

/-- A parser reads a prefix of a list and returns the rest. -/
abbrev Parser (α : Type) := List K → α × List K

/-- One element (`0` past the end). -/
def pK : Parser K
  | [] => (0, [])
  | a :: l => (a, l)

/-- One number. -/
def pNat : Parser ℕ
  | [] => (0, [])
  | a :: l => (toNat a, l)

/-- `n` times `p`. -/
def pMany {α : Type} (p : Parser α) : ℕ → Parser (List α)
  | 0, l => ([], l)
  | n + 1, l => match p l with
    | (a, l) => match pMany p n l with
      | (as, l) => (a :: as, l)

/-- An entry of an `m × n` matrix; `none` if out of range. -/
def pEntry (m n : ℕ) : Parser (Option (Fin m × Fin n × K)) := fun l =>
  match pNat l with
  | (r, l) => match pNat l with
    | (c, l) => match pK l with
      | (v, l) => (if h : r < m ∧ c < n then some (⟨r, h.1⟩, ⟨c, h.2⟩, v) else none, l)

/-- A sparse `m × n` matrix (out-of-range entries dropped). -/
def pMat (m n : ℕ) : Parser (List (Fin m × Fin n × K)) := fun l =>
  match pNat l with
  | (len, l) => match pMany (pEntry m n) len l with
    | (es, l) => (es.filterMap id, l)

/-- A matrix index `< t`; `none` if out of range. -/
def pFin (t : ℕ) : Parser (Option (Fin t)) := fun l =>
  match pNat l with
  | (j, l) => (if h : j < t then some ⟨j, h⟩ else none, l)

/-- A term's matrix list (out-of-range indices dropped). -/
def pS (t : ℕ) : Parser (List (Fin t)) := fun l =>
  match pNat l with
  | (len, l) => match pMany (pFin t) len l with
    | (js, l) => (js.filterMap id, l)

/-- A gadget of width `w`. -/
def pGadget (w : ℕ) : Parser (Gadget K w) := fun l =>
  match pNat l with
  | (cons, l) => match pNat l with
    | (t, l) => match pNat l with
      | (q, l) => match pMany (pMat cons w) t l with
        | (Ms, l) => match pMany (pS t) q l with
          | (Ss, l) => match pMany pK q l with
            | (cs, l) => (⟨cons, t, fun j => Ms.getD j [], q, fun s => Ss.getD s [],
                fun s => cs.getD s 0⟩, l)

/-- A port. -/
def pPort : Parser Port := fun l =>
  match pNat l with
  | (bus, l) => match pK l with
    | (s, l) => match pNat l with
      | (sel, l) => match pNat l with
        | (len, l) => match pMany pNat len l with
          | (msg, l) => (⟨bus, s = 1, sel, msg⟩, l)

/-- A table of `cols` columns (cells outside `rows × cols` are `0`). -/
def pTable (cols : ℕ) : Parser (Table K) := fun l =>
  match pNat l with
  | (rows, l) => match pMany pK (rows * cols) l with
    | (cells, l) => (⟨rows, fun r c => if r < rows ∧ c < cols then cells.getD (r * cols + c) 0
        else 0⟩, l)

/-- An optional fixed table of `cols` columns. -/
def pFixed (cols : ℕ) : Parser (Option (Table K)) := fun l =>
  match pNat l with
  | (tag, l) => if tag = 1 then match pTable cols l with
      | (t, l) => (some t, l)
    else (none, l)

/-- A chip. -/
def pChip : Parser (Chip K) := fun l =>
  match pNat l with
  | (cols, l) => match pGadget (cols + cols + 3) l with
    | (g, l) => match pNat l with
      | (np, l) => match pMany pPort np l with
        | (ports, l) => match pFixed cols l with
          | (fixed, l) => (⟨cols, g, ports, fixed⟩, l)

/-- **A layout**. -/
def pLayout : Parser (Layout K) := fun l =>
  match pNat l with
  | (n, l) => match pNat l with
    | (pub, l) => match pMany pK (2 ^ 8) l with
      | (kinds, l) => match pMany pChip n l with
        | (chips, l) => (⟨chips, fun b => if b < 2 ^ 8 then
            (if kinds.getD b 0 = 1 then .sub else .eq) else .eq, pub⟩, l)

/-- **A witness** for chips of the given column counts. -/
def pWit : List ℕ → Parser (List (Table K))
  | [], l => ([], l)
  | c :: cs, l => match pTable c l with
    | (T, l) => match pWit cs l with
      | (Ts, l) => (T :: Ts, l)

/-! ## Round trips -/

section RoundTrip

theorem pNat_ofNat {n : ℕ} (h : n < 2 ^ 64) (l : List K) : pNat (ofNat n :: l) = (n, l) := by
  simp [pNat, toNat_ofNat h]

/-- `pMany p n` parses `n` serialised items back, if `p` parses each one. -/
theorem pMany_flatten {α β : Type} (p : Parser α) (e : β → List K) (f : β → α) (bs : List β)
    (h : ∀ b ∈ bs, ∀ rest, p (e b ++ rest) = (f b, rest)) (n : ℕ) (hn : bs.length = n)
    (rest : List K) : pMany p n ((bs.map e).flatten ++ rest) = (bs.map f, rest) := by
  subst hn
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, pMany,
      h b List.mem_cons_self, ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb')]

private theorem flatten_singletons {α β : Type} (f : α → β) (l : List α) :
    (l.map fun a => [f a]).flatten = l.map f := by
  induction l <;> simp_all

theorem pMany_pK (l rest : List K) : pMany pK l.length (l ++ rest) = (l, rest) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [pMany, pK, ih]

theorem pMany_pNat (l : List ℕ) (hl : ∀ a ∈ l, a < 2 ^ 64) (rest : List K) :
    pMany pNat l.length (l.map ofNat ++ rest) = (l, rest) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp [pMany, pNat_ofNat (hl a List.mem_cons_self),
      ih fun b hb => hl b (List.mem_cons_of_mem _ hb)]

theorem pMat_eMat {m n : ℕ} (M : List (Fin m × Fin n × K)) (hm : m < 2 ^ 64) (hn : n < 2 ^ 64)
    (hM : M.length < 2 ^ 64) (rest : List K) : pMat m n (eMat M ++ rest) = (M, rest) := by
  have he : ∀ e ∈ M, ∀ r, pEntry m n (eEntry e ++ r) = (some e, r) := fun e _ r => by
    simp [pEntry, eEntry, pNat_ofNat (e.1.isLt.trans hm), pNat_ofNat (e.2.1.isLt.trans hn), pK]
  simp [pMat, eMat, pNat_ofNat hM, pMany_flatten _ _ _ M he _ rfl]

theorem pS_eS {t : ℕ} (S : List (Fin t)) (ht : t < 2 ^ 64) (hS : S.length < 2 ^ 64)
    (rest : List K) : pS t (eS S ++ rest) = (S, rest) := by
  have he : ∀ j ∈ S, ∀ r, pFin t ([ofNat j.val] ++ r) = (some j, r) := fun j _ r => by
    simp [pFin, pNat_ofNat (j.isLt.trans ht)]
  have := pMany_flatten (β := Fin t) (pFin t) (fun j => [ofNat j.val]) some S he _ rfl rest
  rw [flatten_singletons (fun j : Fin t => ofNat j.val)] at this
  simp only [eS, List.cons_append]
  unfold pS
  rw [pNat_ofNat hS]; dsimp only
  rw [this]; dsimp only
  simp [List.filterMap_map]

theorem pGadget_eGadget {w : ℕ} (g : Gadget K w) (hw : w < 2 ^ 64)
    (hb : g.cons < 2 ^ 64 ∧ g.t < 2 ^ 64 ∧ g.q < 2 ^ 64)
    (hM : ∀ j, (g.M j).length < 2 ^ 64) (hS : ∀ s, (g.S s).length < 2 ^ 64) (rest : List K) :
    pGadget w (eGadget g ++ rest) = (g, rest) := by
  obtain ⟨cons, t, M, q, S, c⟩ := g
  obtain ⟨hc, ht, hq⟩ := hb
  have hMs := pMany_flatten (pMat cons w) eMat id (List.ofFn M)
    (fun Mj hMj r => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hMj
      exact pMat_eMat _ hc hw (hM j) r) t (by simp)
  have hSs := pMany_flatten (pS t) eS id (List.ofFn S)
    (fun Sj hSj r => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hSj
      exact pS_eS _ ht (hS j) r) q (by simp)
  have hcs := pMany_pK (List.ofFn c)
  simp only [List.length_ofFn] at hcs
  simp only [eGadget, List.append_assoc, List.cons_append, List.nil_append]
  unfold pGadget
  rw [pNat_ofNat hc]; dsimp only
  rw [pNat_ofNat ht]; dsimp only
  rw [pNat_ofNat hq]; dsimp only
  rw [hMs]; dsimp only
  rw [hSs]; dsimp only
  rw [hcs]; dsimp only
  simp [List.getD_eq_getElem?_getD]

theorem pPort_ePort (p : Port) (hp : p.bus < 2 ^ 64 ∧ p.sel < 2 ^ 64 ∧ p.msg.length < 2 ^ 64 ∧
    ∀ c ∈ p.msg, c < 2 ^ 64) (rest : List K) : pPort (ePort p ++ rest) = (p, rest) := by
  obtain ⟨bus, send, sel, msg⟩ := p
  obtain ⟨h1, h2, h3, h4⟩ := hp
  simp only [ePort, List.cons_append, List.nil_append, pPort,
    pNat_ofNat h1, pNat_ofNat h2, pNat_ofNat h3, pK, pMany_pNat msg h4]
  cases send <;> simp [K_zero_ne_one]

theorem pTable_eTable (cols : ℕ) (T : Table K) (hT : T.rows < 2 ^ 64) (rest : List K) :
    pTable cols (eTable cols T ++ rest) = (T.trim cols, rest) := by
  have hc := pMany_pK ((List.range (T.rows * cols)).map fun q => T.cell (q / cols) (q % cols))
  simp only [List.length_map, List.length_range] at hc
  simp only [eTable, List.cons_append, pTable, pNat_ofNat hT, hc, Table.trim, Prod.mk.injEq,
    Table.mk.injEq, true_and, and_true]
  funext r c
  by_cases h : r < T.rows ∧ c < cols
  · have hq : r * cols + c < T.rows * cols := by
      have := Nat.mul_le_mul_right cols (h.1 : r + 1 ≤ T.rows)
      rw [Nat.succ_mul] at this; omega
    have hpos : 0 < cols := by omega
    simp only [h, and_self, ↓reduceIte]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq]
    simp only [Option.map_some, Option.getD_some]
    congr 1
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt h.2, Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h.2]
  · simp [h]

theorem pFixed_eFixed (cols : ℕ) (f : Option (Table K)) (hf : ∀ t ∈ f, t.rows < 2 ^ 64)
    (rest : List K) : pFixed cols (eFixed cols f ++ rest) = (f.map (Table.trim cols), rest) := by
  cases f with
  | none =>
    have h0 : pNat ((0 : K) :: rest) = (0, rest) := rfl
    simp [pFixed, eFixed, h0]
  | some t =>
    have h1 : pNat (1 :: (eTable cols t ++ rest)) = (1, eTable cols t ++ rest) := rfl
    simp [pFixed, eFixed, h1, pTable_eTable cols t (hf t rfl)]

/-- A chip parses back with its fixed table cut (all its numbers below `2^64`). -/
theorem pChip_eChip (C : Chip K) (hC : C.Admissible) (he : C.entries < 2 ^ 64)
    (hf : ∀ t ∈ C.fixed, t.rows < 2 ^ 64) (rest : List K) :
    pChip (eChip C ++ rest) = ({ C with fixed := C.fixed.map (Table.trim C.cols) }, rest) := by
  obtain ⟨h1, h2, h3, h4, h5, hdeg, h7, hports⟩ := hC
  have hlen : ∀ j, (C.gadget.M j).length < 2 ^ 64 := fun j =>
    lt_of_le_of_lt (List.le_sum_of_mem (List.mem_ofFn.mpr ⟨j, rfl⟩)) he
  have hg := pGadget_eGadget C.gadget (by omega) ⟨by omega, by omega, by omega⟩ hlen
    (fun s => by have := hdeg s; omega)
  have hp := pMany_flatten pPort ePort id C.ports (fun p hp r => by
    obtain ⟨hb, hs, hm, hc⟩ := hports p hp
    exact pPort_ePort p ⟨by omega, by omega, by omega, fun c hc' => by have := hc c hc'; omega⟩ r)
    _ rfl
  have hfx := pFixed_eFixed C.cols C.fixed hf
  simp only [eChip, List.cons_append, List.append_assoc]
  unfold pChip
  rw [pNat_ofNat (by omega)]; dsimp only
  rw [hg]; dsimp only
  rw [pNat_ofNat (by omega)]; dsimp only
  rw [hp]; dsimp only
  rw [hfx]; simp

/-- **Round trip of a layout**: an admissible layout of class `k ≤ 28` parses back to itself up
to what `rel` does not read. -/
theorem pLayout_eLayout {k : ℕ} (hk : k ≤ 28) {L : Layout K} (h : L.Admissible k)
    (rest : List K) : pLayout (eLayout L ++ rest) = (L.normal (2 ^ 8), rest) := by
  obtain ⟨hlen, ⟨C0, hC0, -⟩, hent, hfix, hchips⟩ := h
  have hpub : L.pub < L.chips.length := (List.getElem?_eq_some_iff.mp hC0).1
  have hk' : 2 ^ (k + 4) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hk'' : 2 ^ (k - 4) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcs := pMany_flatten pChip eChip
    (fun C => { C with fixed := C.fixed.map (Table.trim C.cols) })
    L.chips (fun C hC r => by
      have he : C.entries ≤ 2 ^ (k + 4) :=
        le_trans (List.le_sum_of_mem (List.mem_map_of_mem hC)) hent
      have hf : C.fixedCells ≤ 2 ^ (k - 4) :=
        le_trans (List.le_sum_of_mem (List.mem_map_of_mem hC)) hfix
      refine pChip_eChip C (hchips C hC) (by omega) (fun t ht => ?_) r
      have h1 := (hchips C hC).1
      have : t.rows * C.cols ≤ 2 ^ (k - 4) := by
        rw [Option.mem_def] at ht; simpa [Chip.fixedCells, ht] using hf
      have : t.rows ≤ t.rows * C.cols := Nat.le_mul_of_pos_right _ h1
      omega) _ rfl
  have hkinds := pMany_pK ((List.range (2 ^ 8)).map fun b => if L.bus b = .sub then (1 : K) else 0)
  simp only [List.length_map, List.length_range] at hkinds
  simp only [eLayout, List.cons_append, List.nil_append, List.append_assoc]
  unfold pLayout
  rw [pNat_ofNat (by omega)]; dsimp only
  rw [pNat_ofNat (by omega)]; dsimp only
  rw [hkinds]; dsimp only
  rw [hcs]
  simp only [Layout.normal, Prod.mk.injEq, Layout.mk.injEq, true_and, and_true]
  funext b
  by_cases hb : b < 2 ^ 8
  · simp only [hb, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hb, Option.map_some, Option.getD_some]
    cases L.bus b <;> simp [K_zero_ne_one]
  · simp [show ¬ b < 256 from hb]

/-- **Round trip of a witness**: tables with heights below `2^64` parse back cut to their chips. -/
theorem pWit_eWit (L : Layout K) (w : List (Table K)) (hw : w.length = L.chips.length)
    (hr : ∀ T ∈ w, T.rows < 2 ^ 64) (rest : List K) :
    pWit (L.chips.map Chip.cols) (eWit L w ++ rest) = (L.trim w, rest) := by
  unfold eWit Layout.trim
  generalize L.chips = cs at hw ⊢
  induction cs generalizing w with
  | nil => cases w <;> rfl
  | cons C cs ih =>
    obtain _ | ⟨T, w⟩ := w
    · simp at hw
    · simp only [List.map_cons, List.zip_cons_cons, List.flatten_cons, List.append_assoc, pWit,
        pTable_eTable C.cols T (hr T List.mem_cons_self),
        ih w (fun T' hT' => hr T' (List.mem_cons_of_mem _ hT')) (by simpa using hw)]

/-! ## Lengths -/

private theorem eGadget_length {w : ℕ} (g : Gadget K w) :
    (eGadget g).length = 3 + (g.t + 3 * (List.ofFn fun j => (g.M j).length).sum) +
      (List.ofFn fun s => 1 + (g.S s).length).sum + g.q := by
  simp only [eGadget, List.length_append, List.length_cons, List.length_nil, List.length_flatten,
    List.map_map, List.length_ofFn, Function.comp_def, List.map_ofFn, Fin.sum_ofFn, eMat, eS,
    List.length_map]
  simp [Finset.sum_add_distrib, Finset.mul_sum, eEntry]
  have : ∑ x, (g.M x).length * 3 = ∑ i, 3 * (g.M i).length :=
    Finset.sum_congr rfl fun _ _ => Nat.mul_comm _ _
  omega

/-- A chip's serialisation is at most `3000 + 3·entries + fixed cells` long. -/
theorem eChip_length (C : Chip K) (hC : C.Admissible) :
    (eChip C).length ≤ 3000 + 3 * C.entries + C.fixedCells := by
  obtain ⟨h1, h2, h3, h4, h5, hdeg, h7, hports⟩ := hC
  have hS : (List.ofFn fun s => 1 + (C.gadget.S s).length).sum ≤ 2304 := by
    have := List.sum_le_length_nsmul (List.ofFn fun s => 1 + (C.gadget.S s).length) 9
      (fun x hx => by obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hx; have := hdeg s; omega)
    simp only [List.length_ofFn, smul_eq_mul] at this; omega
  have hP : ((C.ports.map ePort).map List.length).sum ≤ 320 := by
    have := List.sum_le_length_nsmul ((C.ports.map ePort).map List.length) 20 (fun x hx => by
      simp only [List.map_map, List.mem_map, Function.comp_apply] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      have := (hports p hp).2.2.1
      simp [ePort]; omega)
    simp only [List.length_map, smul_eq_mul] at this; omega
  have hF : (eFixed C.cols C.fixed).length ≤ 2 + C.fixedCells := by
    cases hf : C.fixed <;> simp [eFixed, eTable, Chip.fixedCells, hf]
    omega
  simp only [eChip, List.length_cons, List.length_append, List.length_flatten, eGadget_length,
    Chip.entries]
  omega

/-- **An admissible layout of class `20 ≤ k` serialises to at most `2^(k+8)` elements.** -/
theorem eLayout_length {k : ℕ} (hk : 20 ≤ k) {L : Layout K} (h : L.Admissible k) :
    (eLayout L).length ≤ 2 ^ (k + 8) := by
  obtain ⟨hlen, -, hent, hfix, hchips⟩ := h
  have hsum : ((L.chips.map eChip).map List.length).sum ≤
      3000 * L.chips.length + 3 * (L.chips.map Chip.entries).sum +
        (L.chips.map Chip.fixedCells).sum := by
    rw [List.map_map]
    refine le_trans (List.sum_le_sum (fun C hC => eChip_length C (hchips C hC))) ?_
    simp [List.sum_map_add, List.sum_map_mul_left]; omega
  have h20 : 2 ^ 20 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h4 : 2 ^ (k + 4) = 16 * 2 ^ k := by rw [pow_add]; ring
  have h8 : 2 ^ (k + 8) = 256 * 2 ^ k := by rw [pow_add]; ring
  have hm4 : 2 ^ (k - 4) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [eLayout, List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_range, List.length_flatten]
  omega

/-- **A witness of an admissible layout at class `k` serialises to at most `2^(k+10)`
elements.** -/
theorem eWit_length {k : ℕ} {L : Layout K} {x : Stmt} {w : List (Table K)} (hL : L.Admissible k)
    (h : L.rel k x w) : (eWit L w).length ≤ 2 ^ (k + 10) := by
  have hcells := h.2.2.2.2.2
  have hlen : ((L.chips.zip w).map fun _ => 1).sum ≤ 2 ^ 8 := by
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one, List.length_zip]
    have := hL.1; omega
  have h10 : 2 ^ (k + 10) = 1024 * 2 ^ k := by rw [pow_add]; ring
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  simp only [eWit, List.length_flatten, List.map_map, Function.comp_def, eTable, List.length_cons,
    List.length_map, List.length_range]
  simp only [List.sum_map_add] at hlen ⊢
  omega

/-- A witness of an admissible layout has tables of height at most `2^k`. -/
theorem rows_le_of_rel {k : ℕ} {L : Layout K} {x : Stmt} {w : List (Table K)}
    (hL : L.Admissible k) (h : L.rel k x w) : ∀ T ∈ w, T.rows ≤ 2 ^ k := by
  intro T hT
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hT
  have hiL : i < L.chips.length := h.1 ▸ hi
  have hmem : (L.chips[i], w[i]) ∈ L.chips.zip w := by
    rw [List.mem_iff_getElem]; exact ⟨i, by simp; omega, by simp⟩
  have hcell : w[i].rows * L.chips[i].cols ≤ 2 ^ k :=
    le_trans (List.le_sum_of_mem (List.mem_map_of_mem (f := fun ct => ct.2.rows * ct.1.cols) hmem))
      h.2.2.2.2.2
  exact le_trans (Nat.le_mul_of_pos_right _ (hL.2.2.2.2 _ (List.getElem_mem hiL)).1) hcell

end RoundTrip

/-! ## Oracles holding a serialisation -/

/-- The one-leaf oracle of `2^m` elements holding the list `l`, then zeros. -/
def toOracle (m : ℕ) (l : List K) : OVal ⟨m, m⟩ := fun p => l.getD p 0

theorem ofFn_toOracle {m : ℕ} {l : List K} (h : l.length ≤ 2 ^ m) :
    List.ofFn (toOracle m l) = l ++ List.replicate (2 ^ m - l.length) 0 := by
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  simp only [List.getElem_ofFn, toOracle]
  by_cases hi : i < l.length
  · simp [List.getElem_append_left hi, List.getElem?_eq_getElem hi]
  · rw [List.getElem_append_right (by omega)]
    simp [List.getElem?_eq_none (by omega : l.length ≤ i)]

/-- The only leaf of a one-leaf oracle is its whole contents. -/
theorem leaf_zero (m : ℕ) (v : OVal ⟨m, m⟩) : Oracle.leaf ⟨⟨m, m⟩, v⟩ 0 = List.ofFn v := by
  simp [Oracle.leaf, Oracle.get]

end RecursionFast.Codec
