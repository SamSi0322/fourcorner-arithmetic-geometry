import ThetaCoverClassPortable.LaurentGluingCover
import ThetaCoverClassPortable.PolynomialLatticeTwistGenerators
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Algebra.Module.LocalizedModule.Submodule

noncomputable section
set_option autoImplicit false
open Polynomial LaurentPolynomial
universe u
namespace FourCorner.FiniteMapCohomology
variable {R : Type u} [CommRing R]

/-- The actual Laurent coordinate unit, with the specified inverse. -/
def laurentVariableUnit : (LaurentPolynomial R)ˣ where
  val := T 1
  inv := T (-1)
  val_inv := by rw [←T_add]; norm_num
  inv_val := by rw [←T_add]; norm_num

@[simp] theorem laurentVariableUnit_pow (n : ℕ) :
    ((laurentVariableUnit (R := R) ^ n : (LaurentPolynomial R)ˣ) : LaurentPolynomial R) = T (n:ℤ) := by
  change (T 1 : LaurentPolynomial R)^n = _
  rw [T_pow,mul_one]

@[simp] theorem laurentVariableUnit_inv_pow (n : ℕ) :
    (((laurentVariableUnit (R := R))⁻¹ ^ n : (LaurentPolynomial R)ˣ) : LaurentPolynomial R) = T (-(n:ℤ)) := by
  change (T (-1) : LaurentPolynomial R)^n = _
  rw [T_pow,mul_neg_one]

/-- Restriction to the positive chart is genuinely polynomial-linear under
its actual positive Laurent scalar action. -/
def positiveRestriction (S : TwoChartCech.Sections (laurentCover R)) :
    letI : Module R[X] S.M01 := Module.compHom S.M01 (Polynomial.toLaurent : R[X] →+* LaurentPolynomial R)
    S.M1 →ₗ[R[X]] S.M01 := by
  letI : Module R[X] S.M01 := Module.compHom S.M01 (Polynomial.toLaurent : R[X] →+* LaurentPolynomial R)
  exact { toFun := S.r1, map_add' := map_add S.r1, map_smul' := fun p x => S.r1_smul p x }

def negativeRestriction (S : TwoChartCech.Sections (laurentCover R)) :
    letI : Module R[X] S.M01 := Module.compHom S.M01
      (LaurentPolynomial.invert.toRingHom.comp (Polynomial.toLaurent : R[X] →+* LaurentPolynomial R))
    S.M0 →ₗ[R[X]] S.M01 := by
  letI : Module R[X] S.M01 := Module.compHom S.M01
    (LaurentPolynomial.invert.toRingHom.comp (Polynomial.toLaurent : R[X] →+* LaurentPolynomial R))
  exact { toFun := S.r0, map_add' := map_add S.r0, map_smul' := fun p x => S.r0_smul p x }

/-- These are ordinary native module-localization predicates on the two
actual restrictions. They contain NO finiteness of cohomology or presentation. -/
def PositiveLocalizes (S : TwoChartCech.Sections (laurentCover R)) : Prop :=
  letI : Module R[X] S.M01 := Module.compHom S.M01 (Polynomial.toLaurent : R[X] →+* LaurentPolynomial R)
  IsLocalizedModule.Away (X : R[X]) (positiveRestriction S)

def NegativeLocalizes (S : TwoChartCech.Sections (laurentCover R)) : Prop :=
  letI : Module R[X] S.M01 := Module.compHom S.M01
    (LaurentPolynomial.invert.toRingHom.comp (Polynomial.toLaurent : R[X] →+* LaurentPolynomial R))
  IsLocalizedModule.Away (X : R[X]) (negativeRestriction S)

 theorem positive_power_compat (S : TwoChartCech.Sections (laurentCover R)) (n : ℕ) (x : S.M1) :
    S.r1 ((X^n : R[X]) • x) = (laurentVariableUnit (R := R)^n : (LaurentPolynomial R)ˣ) • S.r1 x := by
  rw [S.r1_smul]
  change Polynomial.toLaurent (X^n : R[X]) • S.r1 x = _
  rw [Polynomial.toLaurent_X_pow]
  change T (n:ℤ) • S.r1 x =
    (((laurentVariableUnit (R := R)^n : (LaurentPolynomial R)ˣ) : LaurentPolynomial R)) • S.r1 x
  rw [laurentVariableUnit_pow]

 theorem negative_power_compat (S : TwoChartCech.Sections (laurentCover R)) (n : ℕ) (x : S.M0) :
    S.r0 ((X^n : R[X]) • x) = ((laurentVariableUnit (R := R))⁻¹^n : (LaurentPolynomial R)ˣ) • S.r0 x := by
  rw [S.r0_smul]
  change LaurentPolynomial.invert (Polynomial.toLaurent (X^n : R[X])) • S.r0 x = _
  rw [Polynomial.toLaurent_X_pow,LaurentPolynomial.invert_T]
  change T (-(n:ℤ)) • S.r0 x =
    ((((laurentVariableUnit (R := R))⁻¹^n : (LaurentPolynomial R)ˣ) : LaurentPolynomial R)) • S.r0 x
  rw [laurentVariableUnit_inv_pow]

 theorem positive_clearing (S : TwoChartCech.Sections (laurentCover R)) (h : PositiveLocalizes S) :
    ∀ z : S.M01, ∃ (n : ℕ) (x : S.M1), S.r1 x = (laurentVariableUnit (R := R)^n : (LaurentPolynomial R)ˣ) • z := by
  letI : Module R[X] S.M01 := Module.compHom S.M01 (Polynomial.toLaurent : R[X] →+* LaurentPolynomial R)
  letI : IsLocalizedModule.Away (X : R[X]) (positiveRestriction S) := h
  intro z
  obtain ⟨n,x,hx⟩ := IsLocalizedModule.Away.surj (r := (X : R[X])) (positiveRestriction S) z
  refine ⟨n,x,?_⟩
  change S.r1 x = (((laurentVariableUnit (R := R)^n : (LaurentPolynomial R)ˣ) : LaurentPolynomial R)) • z
  rw [laurentVariableUnit_pow]
  change (positiveRestriction S) x = (T (n:ℤ) : LaurentPolynomial R) • z
  rw [←Polynomial.toLaurent_X_pow]
  exact hx.symm

 theorem negative_clearing (S : TwoChartCech.Sections (laurentCover R)) (h : NegativeLocalizes S) :
    ∀ z : S.M01, ∃ (n : ℕ) (y : S.M0), S.r0 y = ((laurentVariableUnit (R := R))⁻¹^n : (LaurentPolynomial R)ˣ) • z := by
  letI : Module R[X] S.M01 := Module.compHom S.M01
    (LaurentPolynomial.invert.toRingHom.comp (Polynomial.toLaurent : R[X] →+* LaurentPolynomial R))
  letI : IsLocalizedModule.Away (X : R[X]) (negativeRestriction S) := h
  intro z
  obtain ⟨n,y,hy⟩ := IsLocalizedModule.Away.surj (r := (X : R[X])) (negativeRestriction S) z
  refine ⟨n,y,?_⟩
  change S.r0 y = ((((laurentVariableUnit (R := R))⁻¹^n : (LaurentPolynomial R)ˣ) : LaurentPolynomial R)) • z
  rw [laurentVariableUnit_inv_pow]
  change (negativeRestriction S) y = (T (-(n:ℤ)) : LaurentPolynomial R) • z
  rw [←LaurentPolynomial.invert_T,←Polynomial.toLaurent_X_pow]
  exact hy.symm

 theorem laurent_common_twist_generators (S : TwoChartCech.Sections (laurentCover R))
    [Module.Finite R[X] S.M0] [Module.Finite R[X] S.M1]
    (h0 : NegativeLocalizes S) (h1 : PositiveLocalizes S) :
    ∃ (n a b : ℕ) (x : Fin a ⊕ Fin b → S.M1) (y : Fin a ⊕ Fin b → S.M0),
      (∀ i, S.r1 (x i) = (laurentVariableUnit (R := R)^n : (LaurentPolynomial R)ˣ) • S.r0 (y i)) ∧
      Submodule.span R[X] (Set.range x) = ⊤ ∧ Submodule.span R[X] (Set.range y) = ⊤ :=
  finite_polynomial_generators_lift_at_common_twist laurentVariableUnit S.r1 S.r0
    (positive_power_compat S) (negative_power_compat S) (positive_clearing S h1) (negative_clearing S h0)
end FourCorner.FiniteMapCohomology
