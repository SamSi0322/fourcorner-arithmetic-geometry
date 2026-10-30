import HilbertArithmeticHigh11
import Mathlib.NumberTheory.Padics.PadicVal.Basic
namespace FourCorner.HilbertOddFormulaHigh11
open HilbertArithmeticHigh11 HilbertArithmeticHigh11.Atom

/-- The q-adic order of one prime generator. -/
def atomOrder (q : OddPrime) : Atom → ℕ
  | prime p => if p=q then 1 else 0
  | _ => 0

/-- Its literal integer q-unit, after removing q. -/
def atomUnit (q : OddPrime) : Atom → ℤ
  | negOne => -1
  | two => 2
  | prime p => if p=q then 1 else p.val

def order (q : OddPrime) (xs : List Atom) := (xs.map (atomOrder q)).sum
def unit (q : OddPrime) (xs : List Atom) := (xs.map (atomUnit q)).prod

def formula (q : OddPrime) (r : ℕ) (u : ℤ) (s : ℕ) (v : ℤ) : ℤ :=
  (-1)^(r*s*(q.val/2)) * (legendreSym q.val u)^s * (legendreSym q.val v)^r

private theorem neg_one_legendre (q : OddPrime) : legendreSym q.val (-1)=(-1)^(q.val/2) := by
  rw [legendreSym.at_neg_one q.property.2,
    ZMod.χ₄_eq_neg_one_pow ((Nat.Prime.mod_two_eq_one_iff_ne_two q.property.1).mpr q.property.2)]

/-- The odd-prime Hilbert formula on the actual signed prime generators. -/
theorem generator_odd_formula (q : OddPrime) (x y : Atom) :
    generatorSign x y q.val=formula q (atomOrder q x) (atomUnit q x)
      (atomOrder q y) (atomUnit q y) := by
  have hq0 : q.val≠0 := q.property.1.ne_zero
  have hq2 : q.val≠2 := q.property.2
  cases x <;> cases y <;>
    simp only [generatorSign,singleSign,atomOrder,atomUnit,formula]
  · simp [hq0,hq2]
  · simp
  · rename_i p
    by_cases h : p=q
    · subst p; simp [hq2,neg_one_legendre]
    · have hv : q.val≠p.val := fun hh => h (Subtype.ext hh.symm)
      simp [h,hv,hq2]
  · simp
  · simp
  · rename_i p
    by_cases h : p=q
    · subst p; simp [hq2]
    · have hv : q.val≠p.val := fun hh => h (Subtype.ext hh.symm)
      simp [h,hv,hq2]
  · rename_i p
    by_cases h : p=q
    · subst p; simp [hq2,neg_one_legendre]
    · have hv : q.val≠p.val := fun hh => h (Subtype.ext hh.symm)
      simp [h,hv,hq2]
  · rename_i p
    by_cases h : p=q
    · subst p; simp [hq2]
    · have hv : q.val≠p.val := fun hh => h (Subtype.ext hh.symm)
      simp [h,hv,hq2]
  · rename_i p r
    by_cases hp : p=q <;> by_cases hr : r=q
    · subst p; subst r; simp [hq2,neg_one_legendre]
    · subst p
      have hqr : q≠r := Ne.symm hr
      have hv : q.val≠r.val := fun hh => hqr (Subtype.ext hh)
      simp [hr,hqr,hv,hq2]
    · subst r
      have hv : q.val≠p.val := fun hh => hp (Subtype.ext hh.symm)
      simp [hp,hv,hq2]
    · have hvp : q.val≠p.val := fun hh => hp (Subtype.ext hh.symm)
      have hvr : q.val≠r.val := fun hh => hr (Subtype.ext hh.symm)
      by_cases hpr : p=r <;> simp [hp,hr,hvp,hvr,hq2,hpr]

private theorem formula_mul_left (q : OddPrime) (r r' s : ℕ) (u u' v : ℤ) :
    formula q (r+r') (u*u') s v = formula q r u s v * formula q r' u' s v := by
  simp only [formula,Nat.add_mul,pow_add,legendreSym.mul,mul_pow]
  ring

private theorem formula_mul_right (q : OddPrime) (r s s' : ℕ) (u v v' : ℤ) :
    formula q r u (s+s') (v*v') = formula q r u s v * formula q r u s' v' := by
  simp only [formula,Nat.mul_add,Nat.add_mul,pow_add,legendreSym.mul,mul_pow]
  ring

private theorem row_odd_formula (q : OddPrime) (x : Atom) (ys : List Atom) :
    rowSign x ys q.val = formula q (atomOrder q x) (atomUnit q x) (order q ys) (unit q ys) := by
  induction ys with
  | nil => simp [rowSign,order,unit,formula]
  | cons y ys ih =>
    simp only [rowSign,order,unit,List.map_cons,List.sum_cons,List.prod_cons]
    rw [generator_odd_formula,ih,← formula_mul_right]
    rfl

/-- The literal standard odd-prime formula on every finite signed prime
presentation, with actual exponent and actual integer unit part. -/
theorem presentation_odd_formula (q : OddPrime) (xs ys : List Atom) :
    presentationSign xs ys q.val = formula q (order q xs) (unit q xs) (order q ys) (unit q ys) := by
  induction xs with
  | nil => simp [presentationSign,order,unit,formula]
  | cons x xs ih =>
    simp only [presentationSign,order,unit,List.map_cons,List.sum_cons,List.prod_cons]
    rw [row_odd_formula,ih,← formula_mul_left]
    rfl

/-- Literal factorization of each rational generator into its q-power and unit. -/
theorem atom_factorization (q : OddPrime) (x : Atom) :
    value x=(q.val : ℚ)^(atomOrder q x)*(atomUnit q x : ℚ) := by
  cases x with
  | negOne => simp [value,atomOrder,atomUnit]
  | two => simp [value,atomOrder,atomUnit]
  | prime p => by_cases h : p=q <;> simp [value,atomOrder,atomUnit,h]

/-- Literal q-power/unit factorization of an arbitrary rational presentation. -/
theorem presentation_factorization (q : OddPrime) (xs : List Atom) :
    evalPresentation xs=(q.val : ℚ)^(order q xs)*(unit q xs : ℚ) := by
  induction xs with
  | nil => simp [evalPresentation,order,unit]
  | cons x xs ih =>
    simp only [evalPresentation,List.map_cons,List.prod_cons]
    change value x*evalPresentation xs=_
    rw [atom_factorization,ih]
    simp only [order,unit,List.map_cons,List.sum_cons,List.prod_cons,Int.cast_mul,pow_add]
    ring

theorem atomUnit_residue_nonzero (q : OddPrime) (x : Atom) :
    (atomUnit q x : ZMod q.val) ≠ 0 := by
  cases x with
  | negOne => simp [atomUnit]
  | two =>
    simp only [atomUnit]
    have h2 : ¬ q.val ∣ 2 := by
      intro hd
      exact q.property.2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left q.property.1.ne_one)
    have hh : (2 : ZMod q.val) ≠ 0 := fun h => h2 ((ZMod.natCast_eq_zero_iff 2 q.val).mp h)
    simpa using hh
  | prime p =>
    by_cases h : p=q
    · simp [atomUnit,h]
    · simp only [atomUnit,if_neg h,Int.cast_natCast]
      intro hh
      have hd : q.val ∣ p.val := (ZMod.natCast_eq_zero_iff p.val q.val).mp hh
      have he := (Nat.prime_dvd_prime_iff_eq q.property.1 p.property.1).mp hd
      exact h (Subtype.ext he.symm)

theorem unit_residue_nonzero (q : OddPrime) (xs : List Atom) :
    (unit q xs : ZMod q.val) ≠ 0 := by
  induction xs with
  | nil => simp [unit]
  | cons x xs ih =>
    simpa only [unit,List.map_cons,List.prod_cons,Int.cast_mul] using
      mul_ne_zero (atomUnit_residue_nonzero q x) ih

theorem unit_ne_zero (q : OddPrime) (xs : List Atom) : unit q xs ≠ 0 := by
  intro hh
  exact unit_residue_nonzero q xs (by rw [hh]; simp)

/-- The displayed unit is an actual q-adic unit, not just a formal label. -/
theorem unit_valuation (q : OddPrime) (xs : List Atom) :
    padicValRat q.val (unit q xs : ℚ)=0 := by
  rw [padicValRat.of_int]
  simp only [Nat.cast_eq_zero]
  exact padicValInt.eq_zero_of_not_dvd (fun hd => unit_residue_nonzero q xs
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd))

theorem evalPresentation_ne_zero (xs : List Atom) : evalPresentation xs ≠ 0 := by
  induction xs with
  | nil => simp [evalPresentation]
  | cons x xs ih =>
    have hx : value x ≠ 0 := by
      cases x with
      | negOne => norm_num [value]
      | two => norm_num [value]
      | prime p =>
        change (p.val : ℚ) ≠ 0
        exact_mod_cast p.property.1.ne_zero
    simpa only [evalPresentation,List.map_cons,List.prod_cons] using mul_ne_zero hx ih

/-- The exponent in the odd-prime formula is the actual rational valuation
of the literal prime presentation. -/
theorem order_valuation (q : OddPrime) (xs : List Atom) :
    padicValRat q.val (evalPresentation xs)=(order q xs : ℤ) := by
  rw [presentation_factorization]
  have hpq : (q.val : ℚ) ≠ 0 := by exact_mod_cast q.property.1.ne_zero
  have hu : (unit q xs : ℚ) ≠ 0 := by exact_mod_cast unit_ne_zero q xs
  rw [padicValRat.mul (pow_ne_zero _ hpq) hu,padicValRat.pow,
    padicValRat.self q.property.1.one_lt,unit_valuation]
  simp

/-- Arbitrary rational square factors change the actual valuation by twice
an integer, at every depth, including negative valuations. -/
theorem rational_presentation_valuation (q : OddPrime) (xs : List Atom) (s r : ℚ)
    (hs : s≠0) (hr : r=evalPresentation xs*s^2) :
    padicValRat q.val r=(order q xs : ℤ)+2*padicValRat q.val s := by
  rw [hr,padicValRat.mul (evalPresentation_ne_zero xs) (pow_ne_zero _ hs),
    order_valuation,padicValRat.pow]
  norm_num

#print axioms generator_odd_formula
#print axioms presentation_odd_formula
#print axioms presentation_factorization
#print axioms unit_valuation
#print axioms order_valuation
#print axioms rational_presentation_valuation
end FourCorner.HilbertOddFormulaHigh11
