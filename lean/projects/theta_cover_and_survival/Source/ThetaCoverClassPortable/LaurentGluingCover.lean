import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.Algebra.Polynomial.Laurent

noncomputable section
set_option autoImplicit false
open Polynomial LaurentPolynomial
namespace FourCorner.FiniteMapCohomology
universe u

/-- The literal (negative,positive) polynomial cover over the Laurent ring.
This records honest scalar rings/maps; no Scheme or cohomology predicate is
inserted into the construction. -/
@[reducible] def laurentCover (R : Type u) [CommRing R] : TwoChartCech.Cover R where
  A0 := R[X]
  A1 := R[X]
  A01 := LaurentPolynomial R
  ρ0 := LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg
  ρ1 := Polynomial.toLaurentAlg

instance negativePolynomialModule {R : Type u} [CommRing R]
    (S : TwoChartCech.Sections (laurentCover R)) : Module R[X] S.M0 := S.M0_moduleA
instance positivePolynomialModule {R : Type u} [CommRing R]
    (S : TwoChartCech.Sections (laurentCover R)) : Module R[X] S.M1 := S.M1_moduleA
instance overlapLaurentModule {R : Type u} [CommRing R]
    (S : TwoChartCech.Sections (laurentCover R)) : Module (LaurentPolynomial R) S.M01 := S.M01_moduleA
instance negativePolynomialTower {R : Type u} [CommRing R]
    (S : TwoChartCech.Sections (laurentCover R)) : IsScalarTower R R[X] S.M0 := S.M0_tower
instance positivePolynomialTower {R : Type u} [CommRing R]
    (S : TwoChartCech.Sections (laurentCover R)) : IsScalarTower R R[X] S.M1 := S.M1_tower
instance overlapLaurentTower {R : Type u} [CommRing R]
    (S : TwoChartCech.Sections (laurentCover R)) : IsScalarTower R (LaurentPolynomial R) S.M01 := S.M01_tower

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The actual overlap unit gives its real Laurent-polynomial action. -/
def laurentEvaluation (t : Aˣ) : LaurentPolynomial R →ₐ[R] A where
  toRingHom := LaurentPolynomial.eval₂ (algebraMap R A) t
  commutes' a := by
    change LaurentPolynomial.eval₂ (algebraMap R A) t (LaurentPolynomial.C a) = _
    exact LaurentPolynomial.eval₂_C _ _ _

@[simp] theorem laurentEvaluation_C (t : Aˣ) (a : R) :
    laurentEvaluation t (LaurentPolynomial.C a) = algebraMap R A a :=
  LaurentPolynomial.eval₂_C _ _ _

@[simp] theorem laurentEvaluation_T (t : Aˣ) (n : ℤ) :
    laurentEvaluation (R := R) t (T n) = (t ^ n : Aˣ) :=
  LaurentPolynomial.eval₂_T _ _ _

@[simp] theorem laurentEvaluation_plus (t : Aˣ) (p : R[X]) :
    laurentEvaluation t (Polynomial.toLaurent p) = Polynomial.aeval (t:A) p := by
  exact LaurentPolynomial.eval₂_toLaurent _ _ _

/-- Negative-chart evaluation is at the SAME inverse overlap unit. -/
theorem laurentEvaluation_minus (t : Aˣ) (p : R[X]) :
    laurentEvaluation t (LaurentPolynomial.invert (Polynomial.toLaurent p)) =
      Polynomial.aeval ((t⁻¹:Aˣ):A) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial n a =>
    rw [Polynomial.toLaurent_C_mul_T,map_mul,LaurentPolynomial.invert_C,
      LaurentPolynomial.invert_T,map_mul]
    simp only [laurentEvaluation_C,laurentEvaluation_T,
      Polynomial.aeval_monomial,zpow_neg,zpow_natCast,Units.val_inv_eq_inv_val,
      Units.val_pow_eq_pow_val,Units.inv_pow_eq_pow_inv]

end FourCorner.FiniteMapCohomology
