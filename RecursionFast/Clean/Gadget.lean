/-
  RecursionFast.Clean.Gadget  (UNTRUSTED, kernel-checked; Stage 8)

  Polynomial constraints as a CCS row gadget (`Contract/Layout.lean`, `Gadget`).

  * `Lin F n`, `SOP F n`: a linear form on `Fin n → F` (sparse entries), a sum of products of
    linear forms. `ofExpr x one e` writes a Clean `Expression` as an `SOP`: a variable is the
    linear form `x v`, a constant `c` is `c · one`, a sum is the concatenation, a product with a
    variable-free side scales the other side (`(-1) · e` stays one product), and any other
    product distributes its two sides after merging each (`merge` collects all one-factor
    products into one linear form, so a linear side such as `x - 1` is one factor).
    `eval_ofExpr`, `eval_merge`: both preserve the value. `length_ofExpr_le`: every product has
    at most `max 1 (degreeBound e)` factors, `degreeBound` being Clean's syntactic degree
    (variable 1, constant 0, sum max, product sum).
  * `gadgetOf one Ps`: the gadget whose constraint `r` is `Ps[r] = 0`. With `D` the largest
    product length (at least 1) and `Q` the largest number of products of one constraint, it has
    `Q` terms of degree `D` and `Q · D` matrices: term `k` multiplies the factors `0 … D-1` of
    product `k` of each constraint, a product shorter than `D` padded with the constant form
    `one`, an absent product contributing empty (zero) rows. `holds_gadgetOf`: it holds iff every
    `Ps[r]` evaluates to `0`, given `one` evaluates to `1`.
-/
import RecursionFast.Library.Layout
import Clean.Circuit.Expression

namespace RecursionFast.Clean

open scoped BigOperators

theorem sum_flatMap' {α β : Type} [AddCommMonoid β] (l : List α) (f : α → List β) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l <;> simp [*]

/-- A list summed with zeros appended: `∑_{k < Q} (if k < len then g P[k] else 0) = ∑ g P`. -/
theorem sum_ofFn_dite {α β : Type} [AddCommMonoid β] (P : List α) (g : α → β) {Q : ℕ}
    (hQ : P.length ≤ Q) :
    (List.ofFn fun k : Fin Q => if h : (k : ℕ) < P.length then g P[k] else 0).sum =
      (P.map g).sum := by
  have : (List.ofFn fun k : Fin Q => if h : (k : ℕ) < P.length then g P[k] else 0) =
      P.map g ++ List.replicate (Q - P.length) 0 :=
    List.ext_getElem (by simp; omega) fun i _ _ => by simp [List.getElem_append]
  rw [this, List.sum_append, List.sum_replicate, smul_zero, add_zero]

section Lin
variable {F : Type} [CommRing F] {n : ℕ}

/-- A linear form on vectors `Fin n → F`: the sum of `a · z i` over its entries `(i, a)`. -/
abbrev Lin (F : Type) (n : ℕ) := List (Fin n × F)

/-- The value of a linear form. -/
def Lin.eval (L : Lin F n) (z : Fin n → F) : F := (L.map fun e => e.2 * z e.1).sum

/-- A sum of products of linear forms. -/
abbrev SOP (F : Type) (n : ℕ) := List (List (Lin F n))

/-- The value of a product of linear forms. -/
def prodEval (p : List (Lin F n)) (z : Fin n → F) : F := (p.map fun L => L.eval z).prod

/-- The value of a sum of products. -/
def SOP.eval (P : SOP F n) (z : Fin n → F) : F := (P.map fun p => prodEval p z).sum

/-- `c · L`. -/
def Lin.smul (c : F) (L : Lin F n) : Lin F n := L.map fun e => (e.1, c * e.2)

theorem Lin.eval_smul (c : F) (L : Lin F n) (z : Fin n → F) : (L.smul c).eval z = c * L.eval z := by
  simp only [Lin.smul, Lin.eval, List.map_map, Function.comp_def, mul_assoc, List.sum_map_mul_left]

theorem Lin.eval_append (L L' : Lin F n) (z : Fin n → F) :
    Lin.eval (L ++ L') z = L.eval z + L'.eval z := by
  simp [Lin.eval]

theorem Lin.eval_nil (z : Fin n → F) : Lin.eval ([] : Lin F n) z = 0 := rfl

theorem Lin.eval_single (i : Fin n) (a : F) (z : Fin n → F) : Lin.eval [(i, a)] z = a * z i := by
  simp [Lin.eval]

/-- A product scaled by `c`: its first factor times `c`; the empty product becomes `c · one`. -/
def scaleProd (one : Lin F n) (c : F) : List (Lin F n) → List (Lin F n)
  | [] => [one.smul c]
  | L :: p => L.smul c :: p

theorem prodEval_scaleProd {one : Lin F n} {z : Fin n → F} (h1 : one.eval z = 1) (c : F)
    (p : List (Lin F n)) : prodEval (scaleProd one c p) z = c * prodEval p z := by
  cases p <;> simp [scaleProd, prodEval, Lin.eval_smul, h1, mul_assoc]

theorem SOP.eval_append (P Q : SOP F n) (z : Fin n → F) :
    (P ++ Q).eval z = P.eval z + Q.eval z := by
  simp [SOP.eval]

theorem SOP.eval_scale {one : Lin F n} {z : Fin n → F} (h1 : one.eval z = 1) (c : F) (P : SOP F n) :
    SOP.eval (P.map (scaleProd one c)) z = c * P.eval z := by
  simp only [SOP.eval, List.map_map, Function.comp_def, prodEval_scaleProd h1,
    List.sum_map_mul_left]

/-- The product of two sums of products, distributed. -/
def SOP.mul (P Q : SOP F n) : SOP F n := P.flatMap fun p => Q.map fun q => p ++ q

theorem SOP.eval_mul (P Q : SOP F n) (z : Fin n → F) : (P.mul Q).eval z = P.eval z * Q.eval z := by
  simp only [SOP.mul, SOP.eval, List.map_flatMap, sum_flatMap', List.map_map,
    Function.comp_def, prodEval, List.map_append, List.prod_append]
  simp only [List.sum_map_mul_left, List.sum_map_mul_right]

/-- One linear form for all one-factor products, then the other products. -/
def SOP.merge (P : SOP F n) : SOP F n :=
  let lin := (P.filter fun p => p.length == 1).flatMap fun p => p.headD []
  let rest := P.filter fun p => !(p.length == 1)
  if lin.isEmpty then rest else [lin] :: rest

private theorem eval_lin_part (P : SOP F n) (z : Fin n → F) :
    Lin.eval ((P.filter fun p => p.length == 1).flatMap fun p => p.headD []) z =
      SOP.eval (P.filter fun p => p.length == 1) z := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    by_cases hp : p.length = 1
    · obtain ⟨L, rfl⟩ : ∃ L, p = [L] := List.length_eq_one_iff.mp hp
      simp only [List.filter_cons, List.length_singleton, beq_self_eq_true, ite_true,
        List.flatMap_cons, List.headD_cons, Lin.eval_append, ih]
      simp [SOP.eval, prodEval]
    · simpa only [List.filter_cons, beq_iff_eq, hp, ite_false] using ih

theorem SOP.eval_merge (P : SOP F n) (z : Fin n → F) : P.merge.eval z = P.eval z := by
  have hsplit : P.eval z = SOP.eval (P.filter fun p => p.length == 1) z +
      SOP.eval (P.filter fun p => !(p.length == 1)) z := by
    simpa [SOP.eval, Bool.beq_eq_decide_eq] using (List.sum_map_filter_add_sum_map_filter_not
      (fun p : List (Lin F n) => p.length = 1) (prodEval · z) P).symm
  rw [hsplit, ← eval_lin_part]
  simp only [SOP.merge]
  split_ifs with he
  · rw [List.isEmpty_iff.mp he, Lin.eval_nil, zero_add]
  · simp [SOP.eval, prodEval]

end Lin

/-! ## Clean expressions as sums of products -/

section Expr
variable {F : Type} [Field F] {n : ℕ}

/-- The value of an expression that mentions no variable (`none` if it mentions one). -/
def constVal? : Expression F → Option F
  | .var _ => none
  | .const c => some c
  | .add a b => match constVal? a, constVal? b with
    | some x, some y => some (x + y)
    | _, _ => none
  | .mul a b => match constVal? a, constVal? b with
    | some x, some y => some (x * y)
    | _, _ => none

theorem eval_of_constVal? {e : Expression F} {c : F} (h : constVal? e = some c)
    (env : Environment F) : e.eval env = c := by
  induction e generalizing c with
  | var v => simp [constVal?] at h
  | const c' => simpa [constVal?, Expression.eval] using h
  | add a b ha hb | mul a b ha hb =>
    cases ha' : constVal? a <;> cases hb' : constVal? b <;> simp [constVal?, ha', hb'] at h
    rw [Expression.eval, ha ha', hb hb', h]

/-- An expression as a sum of products of linear forms: variable `v` is the form `x v`, the
constant `c` is `c · one`; sums concatenate; a product with a variable-free side scales the
other side; any other product distributes the two sides, each first merged (`SOP.merge`) so
that a linear side, such as `x - 1` in `x · (x - 1)`, stays one factor. -/
def ofExpr (x : ℕ → Lin F n) (one : Lin F n) : Expression F → SOP F n
  | .var v => [[x v.index]]
  | .const c => [[one.smul c]]
  | .add a b => ofExpr x one a ++ ofExpr x one b
  | .mul a b =>
    match constVal? a, constVal? b with
    | some c, _ => (ofExpr x one b).map (scaleProd one c)
    | none, some c => (ofExpr x one a).map (scaleProd one c)
    | none, none => (ofExpr x one a).merge.mul (ofExpr x one b).merge

/-- **The translation preserves the value**: on a vector `z` where `x v` reads variable `v` of
the environment and `one` reads `1`. -/
theorem eval_ofExpr {x : ℕ → Lin F n} {one : Lin F n} {z : Fin n → F} {env : Environment F}
    (hx : ∀ v, (x v).eval z = env.get v) (h1 : one.eval z = 1) (e : Expression F) :
    (ofExpr x one e).eval z = e.eval env := by
  induction e with
  | var v => simp [ofExpr, SOP.eval, prodEval, hx, Expression.eval]
  | const c => simp [ofExpr, SOP.eval, prodEval, Lin.eval_smul, h1, Expression.eval]
  | add a b ha hb => rw [ofExpr, SOP.eval_append, ha, hb, Expression.eval]
  | mul a b ha hb =>
    rw [ofExpr, Expression.eval]
    rcases hca : constVal? a with _ | ca <;> rcases hcb : constVal? b with _ | cb
    · simp only [SOP.eval_mul, SOP.eval_merge, ha, hb]
    · simp only [SOP.eval_scale h1, ha, eval_of_constVal? hcb, mul_comm]
    all_goals simp only [SOP.eval_scale h1, hb, eval_of_constVal? hca]

/-- Clean's syntactic degree: a variable `1`, a constant `0`, a sum the larger, a product the
sum. -/
def degreeBound : Expression F → ℕ
  | .var _ => 1
  | .const _ => 0
  | .add a b => max (degreeBound a) (degreeBound b)
  | .mul a b => degreeBound a + degreeBound b

omit [Field F] in
theorem degreeBound_of_constVal? [Field F] {e : Expression F} {c : F} (h : constVal? e = some c) :
    degreeBound e = 0 := by
  induction e generalizing c with
  | var v => simp [constVal?] at h
  | const c' => rfl
  | add a b ha hb | mul a b ha hb =>
    cases ha' : constVal? a <;> cases hb' : constVal? b <;> simp [constVal?, ha', hb'] at h
    simp [degreeBound, ha ha', hb hb']

theorem one_le_degreeBound {e : Expression F} (h : constVal? e = none) : 1 ≤ degreeBound e := by
  induction e with
  | var v => rfl
  | const c => simp [constVal?] at h
  | add a b ha hb | mul a b ha hb =>
    simp only [degreeBound]
    cases ha' : constVal? a <;> cases hb' : constVal? b <;> simp [constVal?, ha', hb'] at h
    · have := ha ha'; omega
    · have := ha ha'; omega
    · have := hb hb'; omega

omit [Field F] in
theorem length_merge_le {P : SOP F n} {d : ℕ} (hd : 1 ≤ d) (h : ∀ p ∈ P, p.length ≤ d) :
    ∀ p ∈ P.merge, p.length ≤ d := by
  intro p hp
  simp only [SOP.merge] at hp
  split_ifs at hp
  · exact h p (List.mem_filter.mp hp).1
  · rcases List.mem_cons.mp hp with rfl | hp
    · simpa using hd
    · exact h p (List.mem_filter.mp hp).1

/-- **The degree limit**: every product of `ofExpr x one e` has at most
`max 1 (degreeBound e)` factors. -/
theorem length_ofExpr_le (x : ℕ → Lin F n) (one : Lin F n) (e : Expression F) :
    ∀ p ∈ ofExpr x one e, p.length ≤ max 1 (degreeBound e) := by
  induction e with
  | var v => simp [ofExpr, degreeBound]
  | const c => simp [ofExpr, degreeBound]
  | add a b ha hb =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact (ha p hp).trans (by simp only [degreeBound]; omega)
    · exact (hb p hp).trans (by simp only [degreeBound]; omega)
  | mul a b ha hb =>
    intro p hp
    simp only [ofExpr] at hp
    have hsc : ∀ (c : F) (q : List (Lin F n)), (scaleProd one c q).length ≤ max 1 q.length := by
      intro c q; cases q <;> simp [scaleProd]
    rcases hca : constVal? a with _ | ca <;> rcases hcb : constVal? b with _ | cb <;>
      simp only [hca, hcb] at hp
    · obtain ⟨q, hq, r, hr, rfl⟩ : ∃ q ∈ (ofExpr x one a).merge, ∃ r ∈ (ofExpr x one b).merge,
          p = q ++ r := by
        simpa [SOP.mul, List.mem_flatMap, eq_comm] using hp
      have h1 := length_merge_le (le_max_left _ _) ha q hq
      have h2 := length_merge_le (le_max_left _ _) hb r hr
      have h3 := one_le_degreeBound hca
      have h4 := one_le_degreeBound hcb
      simp only [List.length_append, degreeBound]
      omega
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have := hsc cb q
      have := ha q hq
      simp only [degreeBound, degreeBound_of_constVal? hcb, add_zero]
      omega
    all_goals
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have := hsc ca q
      have := hb q hq
      simp only [degreeBound, degreeBound_of_constVal? hca, zero_add]
      omega

end Expr

/-! ## Sums of products as a CCS gadget -/

section Gadget
variable {F : Type} [CommRing F] {n : ℕ}

/-- The largest product length of a list of sums of products, at least `1`. -/
def degOf (Ps : List (SOP F n)) : ℕ := max 1 ((Ps.flatMap fun P => P.map List.length).foldr max 0)

/-- The largest number of products of one of the sums. -/
def termsOf (Ps : List (SOP F n)) : ℕ := (Ps.map List.length).foldr max 0

/-- Factor `l` of product `k` of `P`, the product padded to `D` factors with `one`; empty (the
zero form) when `P` has no product `k`. -/
def factor (one : Lin F n) (D : ℕ) (P : SOP F n) (k l : ℕ) : Lin F n :=
  match P[k]? with
  | none => []
  | some p => (p ++ List.replicate (D - p.length) one)[l]?.getD []

theorem lt_mul_of_lt {k l Q D : ℕ} (hk : k < Q) (hl : l < D) : k * D + l < Q * D :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left hl _) (Nat.succ_mul k D ▸ Nat.mul_le_mul_right D hk)

/-- **The CCS gadget of a list of polynomial constraints** `Ps[r] = 0`: `termsOf Ps` terms of
degree `degOf Ps`, coefficient `1`; term `k`'s factor `l` is the matrix `k · D + l`, whose row
`r` is factor `l` of product `k` of `Ps[r]` (padded with `one`, zero when absent). -/
@[reducible] def gadgetOf (one : Lin F n) (Ps : List (SOP F n)) : Gadget F n where
  cons := Ps.length
  t := termsOf Ps * degOf Ps
  M j := (List.finRange Ps.length).flatMap fun r =>
    (factor one (degOf Ps) Ps[r] (j / degOf Ps) (j % degOf Ps)).map fun e => (r, e.1, e.2)
  q := termsOf Ps
  S k := List.ofFn fun l : Fin (degOf Ps) => ⟨k * degOf Ps + l, lt_mul_of_lt k.2 l.2⟩
  c _ := 1

theorem rowDot_tag {m : ℕ} (f : Fin m → Lin F n) (z : Fin n → F) (r : Fin m) :
    rowDot ((List.finRange m).flatMap fun r' => (f r').map fun e => (r', e.1, e.2)) z r =
      (f r).eval z := by
  unfold rowDot
  rw [List.filter_flatMap, List.map_flatMap, sum_flatMap']
  have : ∀ r', (((f r').map fun e => (r', e.1, e.2)).filter fun e => e.1 = r).map
      (fun e => e.2.2 * z e.2.1) = if r' = r then (f r').map fun e => e.2 * z e.1 else [] := by
    intro r'
    split_ifs with h <;> simp [List.filter_map, Function.comp_def, h]
  simp only [this]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  simp [apply_ite List.sum, Lin.eval]

omit [CommRing F] in
theorem degOf_pos (Ps : List (SOP F n)) : 0 < degOf Ps := by
  unfold degOf; omega

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

omit [CommRing F] in
theorem length_le_degOf {Ps : List (SOP F n)} {P : SOP F n} (hP : P ∈ Ps) {p : List (Lin F n)}
    (hp : p ∈ P) : p.length ≤ degOf Ps :=
  (le_foldr_max (List.mem_flatMap.mpr ⟨P, hP, List.mem_map.mpr ⟨p, hp, rfl⟩⟩)).trans
    (le_max_right _ _)

omit [CommRing F] in
theorem length_le_termsOf {Ps : List (SOP F n)} {P : SOP F n} (hP : P ∈ Ps) :
    P.length ≤ termsOf Ps :=
  le_foldr_max (List.mem_map.mpr ⟨P, hP, rfl⟩)

/-- The product of the `D` factors of product `k`: product `k` itself, or `0` when absent. -/
theorem prod_factor {one : Lin F n} {z : Fin n → F} (h1 : one.eval z = 1) {D : ℕ} (hD : 0 < D)
    {P : SOP F n} (hP : ∀ p ∈ P, p.length ≤ D) (k : ℕ) :
    (List.ofFn fun l : Fin D => (factor one D P k l).eval z).prod =
      if h : k < P.length then prodEval P[k] z else 0 := by
  unfold factor
  split_ifs with hk
  · rw [List.getElem?_eq_getElem hk]
    dsimp only
    set p := P[k]
    have hlen : (p ++ List.replicate (D - p.length) one).length = D := by
      simp [hP p (List.getElem_mem hk)]
    have : (List.ofFn fun l : Fin D => ((p ++ List.replicate (D - p.length) one)[(l : ℕ)]?.getD []).eval z)
        = (p ++ List.replicate (D - p.length) one).map fun L => L.eval z := by
      apply List.ext_getElem (by simp only [List.length_ofFn, List.length_map, hlen])
      intro i h1' h2'
      simp only [List.getElem_ofFn, List.getElem_map]
      rw [List.getElem?_eq_getElem (by simpa [hlen] using h1'), Option.getD_some]
    rw [this, List.map_append, List.prod_append, List.map_replicate, List.prod_replicate, h1,
      one_pow, mul_one]
    rfl
  · rw [List.getElem?_eq_none (by omega)]
    obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
    rw [List.ofFn_succ, List.prod_cons]
    simp [Lin.eval]

theorem rowDot_gadgetOf_M (one : Lin F n) (Ps : List (SOP F n)) (z : Fin n → F)
    (k : Fin (termsOf Ps)) (l : Fin (degOf Ps)) (r : Fin Ps.length) :
    rowDot ((gadgetOf one Ps).M ⟨k * degOf Ps + l, lt_mul_of_lt k.2 l.2⟩) z r =
      (factor one (degOf Ps) Ps[(r : ℕ)] k l).eval z := by
  have hD := degOf_pos Ps
  have h1 : (k * degOf Ps + l) / degOf Ps = k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt l.2, zero_add]
  have h2 : (k * degOf Ps + l) % degOf Ps = l := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt l.2]
  show rowDot ((List.finRange Ps.length).flatMap fun r' =>
    (factor one (degOf Ps) Ps[r'] ((k * degOf Ps + l) / degOf Ps) ((k * degOf Ps + l) % degOf Ps)).map
      fun e => (r', e.1, e.2)) z r = _
  rw [rowDot_tag, h1, h2, Fin.getElem_fin]

/-- **The gadget of `Ps` holds iff every constraint evaluates to `0`.** -/
theorem holds_gadgetOf {one : Lin F n} {z : Fin n → F} (h1 : one.eval z = 1) (Ps : List (SOP F n)) :
    (gadgetOf one Ps).holds z ↔ ∀ P ∈ Ps, P.eval z = 0 := by
  have hD := degOf_pos Ps
  have key : ∀ r : Fin Ps.length,
      (List.ofFn fun i : Fin (gadgetOf one Ps).q => (gadgetOf one Ps).c i *
        (((gadgetOf one Ps).S i).map fun j => rowDot ((gadgetOf one Ps).M j) z r).prod).sum =
      Ps[(r : ℕ)].eval z := by
    intro r
    have hS : ∀ i : Fin (termsOf Ps), (((gadgetOf one Ps).S i).map fun j =>
        rowDot ((gadgetOf one Ps).M j) z r).prod =
        if h : (i : ℕ) < Ps[(r : ℕ)].length then prodEval Ps[(r : ℕ)][(i : ℕ)] z else 0 := by
      intro i
      show ((List.ofFn fun l : Fin (degOf Ps) =>
        (⟨i * degOf Ps + l, lt_mul_of_lt i.2 l.2⟩ : Fin (termsOf Ps * degOf Ps))).map fun j =>
          rowDot ((gadgetOf one Ps).M j) z r).prod = _
      rw [List.map_ofFn, ← prod_factor h1 hD (fun p hp => length_le_degOf (List.getElem_mem r.2) hp) i]
      exact congrArg List.prod (congrArg List.ofFn (funext fun l => rowDot_gadgetOf_M one Ps z i l r))
    show (List.ofFn fun i : Fin (termsOf Ps) => 1 * (((gadgetOf one Ps).S i).map fun j =>
      rowDot ((gadgetOf one Ps).M j) z r).prod).sum = _
    simp only [one_mul, hS]
    exact sum_ofFn_dite Ps[(r : ℕ)] (fun p => prodEval p z)
      (length_le_termsOf (List.getElem_mem r.2))
  simp only [Gadget.holds]
  refine ⟨fun h P hP => ?_, fun h r => (key r).trans (h _ (List.getElem_mem r.2))⟩
  obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hP
  exact (key ⟨r, hr⟩).symm.trans (h ⟨r, hr⟩)

end Gadget

end RecursionFast.Clean
