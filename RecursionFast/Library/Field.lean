/-
  RecursionFast.Library.Field  (organiser library, UNTRUSTED: kernel-checked, never read for meaning)
  Ported from probes/r8-binary/RecursionFastLib/Field.lean (R8); E's `Neg`/`Sub` live here.

  * `Field K` with the contract's own `0, 1, +, -, *` as its data (pulled back along the
    computable bijection `K → BF64` whose `+`/`*` agree with CompPoly's by `rfl`).
  * `Fintype K`, `card K = 2^64`, `CharP K 2`.
  * `K_spec`: an explicit additive-multiplicative bijection onto Mathlib's
    `AdjoinRoot (X^64 + X^4 + X^3 + X + 1 : (ZMod 2)[X])`, and irreducibility of that polynomial.
  * `E = K[y]/(y^3 + y + 1)` as a 3-limb structure with the explicit 9-product multiplication,
    `Field E` (pulled back from CompPoly's `BF64.Ext3`), `card E = 2^192`, byte encoding (24 B).
-/
import RecursionFast.Contract.Field
import CompPoly.Fields.Binary.BF64
import CompPoly.Fields.Binary.BF64.Bytes
import Mathlib.Tactic.LinearCombination

namespace RecursionFast

open Polynomial CompPoly.Extension

namespace K

/-- The computable bijection to CompPoly's carrier (same bits). -/
def toBF64 (a : K) : BF64 := BF64.ofBitVec a.bits
def ofBF64 (a : BF64) : K := ⟨a.toBitVec⟩

theorem toBF64_injective : Function.Injective toBF64 := by
  intro a b h; cases a; cases b; cases h; rfl

/-! The contract's operations *are* CompPoly's, definitionally. -/
theorem toBF64_zero : toBF64 0 = 0 := rfl
theorem toBF64_one : toBF64 1 = 1 := rfl
theorem toBF64_add (a b : K) : toBF64 (a + b) = toBF64 a + toBF64 b := rfl
theorem toBF64_mul (a b : K) : toBF64 (a * b) = toBF64 a * toBF64 b := rfl
theorem toBF64_neg (a : K) : toBF64 (-a) = -toBF64 a := rfl
theorem toBF64_sub (a b : K) : toBF64 (a - b) = toBF64 a - toBF64 b := rfl

/-! Operations the contract does not define, transported (computably) from `BF64`. -/
instance : Inv K := ⟨fun a => ofBF64 (toBF64 a)⁻¹⟩
instance : Div K := ⟨fun a b => ofBF64 (toBF64 a / toBF64 b)⟩
instance : SMul ℕ K := ⟨fun n a => ofBF64 (n • toBF64 a)⟩
instance : SMul ℤ K := ⟨fun n a => ofBF64 (n • toBF64 a)⟩
instance : SMul ℚ≥0 K := ⟨fun q a => ofBF64 (q • toBF64 a)⟩
instance : SMul ℚ K := ⟨fun q a => ofBF64 (q • toBF64 a)⟩
instance : Pow K ℕ := ⟨fun a n => ofBF64 (toBF64 a ^ n)⟩
instance : Pow K ℤ := ⟨fun a n => ofBF64 (toBF64 a ^ n)⟩
instance : NatCast K := ⟨fun n => ofBF64 n⟩
instance : IntCast K := ⟨fun n => ofBF64 n⟩
instance : NNRatCast K := ⟨fun q => ofBF64 q⟩
instance : RatCast K := ⟨fun q => ofBF64 q⟩

instance instField : Field K :=
  toBF64_injective.field toBF64 rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

/-- The bijection as a ring isomorphism. -/
def ringEquivBF64 : K ≃+* BF64 :=
  { toFun := toBF64, invFun := ofBF64, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
    map_mul' := toBF64_mul, map_add' := toBF64_add }

instance : CharP K 2 := charP_of_injective_ringHom (f := ringEquivBF64.symm.toRingHom)
  ringEquivBF64.symm.injective 2

def equivFin : K ≃ Fin (2 ^ 64) where
  toFun a := a.bits.toFin
  invFun i := ⟨BitVec.ofFin i⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `K` is finite. Noncomputable on purpose (S6b): a computable instance is a closed term, which a
compiled executable evaluates when it initialises this module, i.e. it materialises all `2^64`
elements (the badge path's `verify` ran out of memory at start-up). Nothing executes it. -/
noncomputable instance : Fintype K := Fintype.ofEquiv _ equivFin.symm

theorem card_K : Fintype.card K = 2 ^ 64 := by
  rw [Fintype.card_congr equivFin, Fintype.card_fin]

/-- The defining polynomial, in Mathlib's notation. -/
noncomputable abbrev f64 : (ZMod 2)[X] := X ^ 64 + X ^ 4 + X ^ 3 + X + 1

theorem f64_irreducible : Irreducible f64 := BF64.basePoly_irreducible

theorem f64_eq_basePoly : f64 = BF64.basePoly := rfl

/-- **Specification of K** (statement readable without any instance on `K`): the contract's
`+, *, 0, 1` are those of `GF(2)[x]/(x^64+x^4+x^3+x+1)`, via an explicit bijection. -/
theorem K_spec : Irreducible f64 ∧ ∃ e : K ≃ AdjoinRoot f64,
    e 0 = 0 ∧ e 1 = 1 ∧ (∀ a b : K, e (a + b) = e a + e b) ∧ (∀ a b : K, e (a * b) = e a * e b) := by
  refine ⟨f64_irreducible, ?_⟩
  rw [f64_eq_basePoly]
  let g : K → AdjoinRoot f64 := fun a => BF64.toQuot (toBF64 a)
  have hinj : Function.Injective g := fun a b h => toBF64_injective (BF64.toQuot_injective h)
  have hsurj : Function.Surjective g := fun q => by
    obtain ⟨x, hx⟩ := BF64.toQuot_surjective q
    exact ⟨ofBF64 x, hx⟩
  refine ⟨Equiv.ofBijective g ⟨hinj, hsurj⟩, BF64.toQuot_zero, BF64.toQuot_one, ?_, ?_⟩
  · intro a b
    show BF64.toQuot (toBF64 (a + b)) = BF64.toQuot (toBF64 a) + BF64.toQuot (toBF64 b)
    rw [toBF64_add]; exact BF64.toQuot_add _ _
  · intro a b
    show BF64.toQuot (toBF64 (a * b)) = BF64.toQuot (toBF64 a) * BF64.toQuot (toBF64 b)
    rw [toBF64_mul]; exact BF64.toQuot_mul _ _

end K

/-! ## E = K[y]/(y^3 + y + 1) (structure and `0, 1, +, *` in the contract) -/

namespace E

instance : Neg E := ⟨fun a => a⟩
instance : Sub E := ⟨fun a b => ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2⟩⟩

abbrev X3 := BF64.Ext3

def lift (c0 c1 c2 : BF64) : X3 := Ext.ofVector #v[c0, c1, c2]

def toExt (a : E) : X3 := lift a.c0.toBF64 a.c1.toBF64 a.c2.toBF64
def ofExt (x : X3) : E :=
  ⟨K.ofBF64 x.coeffs[0], K.ofBF64 x.coeffs[1], K.ofBF64 x.coeffs[2]⟩

theorem toExt_injective : Function.Injective toExt := by
  intro a b h
  have h' := congrArg Ext.coeffs h
  simp only [toExt, lift] at h'
  have h0 : a.c0.toBF64 = b.c0.toBF64 := congrArg (·[0]) h'
  have h1 : a.c1.toBF64 = b.c1.toBF64 := congrArg (·[1]) h'
  have h2 : a.c2.toBF64 = b.c2.toBF64 := congrArg (·[2]) h'
  cases a; cases b
  simp only [mk.injEq]
  exact ⟨K.toBF64_injective h0, K.toBF64_injective h1, K.toBF64_injective h2⟩

theorem toExt_ofExt (x : X3) : toExt (ofExt x) = x := by
  obtain ⟨⟨⟨l⟩, hl⟩⟩ := x
  match l, hl with
  | [_, _, _], _ => rfl

local notation "ι" => (algebraMap BF64 X3)

/-- Limb `i` (the coefficient of `y^i`), with a `Fin 3` index. -/
abbrev limb (x : X3) (i : Fin 3) : BF64 := Ext.coeff x i

theorem limb_lift_0 (c0 c1 c2 : BF64) : limb (lift c0 c1 c2) 0 = c0 := rfl
theorem limb_lift_1 (c0 c1 c2 : BF64) : limb (lift c0 c1 c2) 1 = c1 := rfl
theorem limb_lift_2 (c0 c1 c2 : BF64) : limb (lift c0 c1 c2) 2 = c2 := rfl

/-- Every `lift` is its limbs in the basis `1, y, y²` (cf. leanerVM `E.eq_sum_limbs`). -/
theorem lift_eq (c0 c1 c2 : BF64) :
    lift c0 c1 c2 = ι c0 + ι c1 * BF64.ext3Gen + ι c2 * BF64.ext3Gen ^ 2 := by
  apply Ext.toQuot_injective
  have hx : Ext.toQuot (lift c0 c1 c2) = ∑ i : Fin 3,
      algebraMap BF64 (AdjoinRoot BF64.ext3Params.poly) (limb (lift c0 c1 c2) i) *
        Ext.rt BF64.ext3Params ^ (i : ℕ) := rfl
  rw [hx, Fin.sum_univ_three, limb_lift_0, limb_lift_1, limb_lift_2]
  simp only [Ext.toQuot_add, Ext.toQuot_mul, Ext.toQuot_pow, BF64.toQuot_ext3Gen,
    Ext.algebraMap_eq_ofBase, Ext.toQuot_ofBase]
  simp

theorem lift_mul (a0 a1 a2 b0 b1 b2 : BF64) :
    lift a0 a1 a2 * lift b0 b1 b2 =
      lift (a0 * b0 + (a1 * b2 + a2 * b1))
        (a0 * b1 + a1 * b0 + (a1 * b2 + a2 * b1) + a2 * b2)
        (a0 * b2 + a1 * b1 + a2 * b0 + a2 * b2) := by
  simp only [lift_eq, map_add, map_mul]
  linear_combination (ι a1 * ι b2 + ι a2 * ι b1 + ι a2 * ι b2 * BF64.ext3Gen) *
    BF64.ext3Gen_pow_three

theorem toExt_mul (a b : E) : toExt (a * b) = toExt a * toExt b := by
  simp only [toExt, lift_mul]; rfl

theorem toExt_add (a b : E) : toExt (a + b) = toExt a + toExt b := by
  apply Ext.ext; intro i; fin_cases i <;> rfl

theorem toExt_zero : toExt 0 = 0 := by apply Ext.ext; intro i; fin_cases i <;> rfl
theorem toExt_one : toExt 1 = 1 := by apply Ext.ext; intro i; fin_cases i <;> rfl
theorem toExt_neg (a : E) : toExt (-a) = -toExt a := by
  apply Ext.ext; intro i; fin_cases i <;> rfl
theorem toExt_sub (a b : E) : toExt (a - b) = toExt a - toExt b := by
  apply Ext.ext; intro i; fin_cases i <;> rfl

instance : Inv E := ⟨fun a => ofExt (toExt a)⁻¹⟩
instance : Div E := ⟨fun a b => ofExt (toExt a / toExt b)⟩
instance : SMul ℕ E := ⟨fun n a => ofExt (n • toExt a)⟩
instance : SMul ℤ E := ⟨fun n a => ofExt (n • toExt a)⟩
instance : SMul ℚ≥0 E := ⟨fun q a => ofExt (q • toExt a)⟩
instance : SMul ℚ E := ⟨fun q a => ofExt (q • toExt a)⟩
instance : Pow E ℕ := ⟨fun a n => ofExt (toExt a ^ n)⟩
instance : Pow E ℤ := ⟨fun a n => ofExt (toExt a ^ n)⟩
instance : NatCast E := ⟨fun n => ofExt n⟩
instance : IntCast E := ⟨fun n => ofExt n⟩
instance : NNRatCast E := ⟨fun q => ofExt q⟩
instance : RatCast E := ⟨fun q => ofExt q⟩

instance instField : Field E :=
  toExt_injective.field toExt toExt_zero toExt_one toExt_add toExt_mul toExt_neg toExt_sub
    (fun _ => toExt_ofExt _) (fun _ _ => toExt_ofExt _) (fun _ _ => toExt_ofExt _)
    (fun _ _ => toExt_ofExt _) (fun _ _ => toExt_ofExt _) (fun _ _ => toExt_ofExt _)
    (fun _ _ => toExt_ofExt _) (fun _ _ => toExt_ofExt _) (fun _ => toExt_ofExt _)
    (fun _ => toExt_ofExt _) (fun _ => toExt_ofExt _) (fun _ => toExt_ofExt _)

def equivK3 : E ≃ K × K × K where
  toFun a := (a.c0, a.c1, a.c2)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `E` is finite. Noncomputable on purpose, as `Fintype K` (S6b): no compiled executable may
enumerate `2^192` elements at start-up. -/
noncomputable instance : Fintype E := Fintype.ofEquiv _ equivK3.symm

theorem card_E : Fintype.card E = 2 ^ 192 := by
  rw [Fintype.card_congr equivK3, Fintype.card_prod, Fintype.card_prod, K.card_K]; norm_num

/-- `K ↪ E` as the `y^0` limb is a ring hom. -/
def ofK : K →+* E where
  toFun a := ⟨a, 0, 0⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' a b := by
    show (⟨a + b, 0, 0⟩ : E) = ⟨a + b, 0 + 0, 0 + 0⟩
    simp
  map_mul' a b := by
    show (⟨a * b, 0, 0⟩ : E) = ⟨_, _, _⟩
    simp

instance : Algebra K E := ofK.toAlgebra

end E

end RecursionFast
