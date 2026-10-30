import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.Tactic

/-!
# The different of a quadratic extension with unit radicand

A primitive square root of a unit has unit minimal-polynomial derivative when two
is invertible. Consequently the different of the integral closure is the unit ideal.
-/

noncomputable section

namespace FourCorner.QuadraticDifferentUnit

open Polynomial Module

variable {A F B E : Type*} [CommRing A] [IsDomain A] [Field F]
  [CommRing B] [Field E] [Algebra A F] [Algebra B E] [Algebra A B]
  [Algebra F E] [Algebra A E] [IsScalarTower A F E] [IsScalarTower A B E]
  [IsFractionRing A F] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [IsIntegralClosure B A E] [IsIntegrallyClosed A] [IsDedekindDomain B]
  [IsTorsionFree A B]

omit [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [IsIntegralClosure B A E] [IsTorsionFree A B] in
theorem minpoly_eq_quadratic (x : B) (u : A) (hx : IsIntegral A x)
    (hxsq : x ^ 2 = algebraMap A B u)
    (htop : Algebra.adjoin F {algebraMap B E x} = ⊤)
    (hdim : Module.finrank F E = 2) :
    minpoly A x = X ^ 2 - C u := by
  have hy : IsIntegral F (algebraMap B E x) :=
    (hx.map (IsScalarTower.toAlgHom A B E)).tower_top
  have hdeg : (minpoly F (algebraMap B E x)).natDegree = 2 := by
    exact (PowerBasis.ofAdjoinEqTop hy htop).finrank.symm.trans hdim
  have hsq : (algebraMap B E x) ^ 2 = algebraMap F E (algebraMap A F u) := by
    rw [← map_pow, hxsq]
    rw [← IsScalarTower.algebraMap_apply A B E, ← IsScalarTower.algebraMap_apply A F E]
  have hm : minpoly F (algebraMap B E x) = X ^ 2 - C (algebraMap A F u) := by
    symm
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hy)
      (monic_X_pow_sub_C _ (by decide))
    · exact minpoly.dvd F _ (by simp [hsq])
    · simp [hdeg]
  apply Polynomial.map_injective (algebraMap A F) (IsFractionRing.injective A F)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions F E hx, hm]
  simp

/-- A quadratic unit radicand makes the different the unit ideal, once its
minimal polynomial has been identified. -/
theorem differentIdeal_eq_top_of_minpoly_eq
    (x : B) (u : A)
    (hgen : Algebra.adjoin F {algebraMap B E x} = ⊤)
    (hroot : x ^ 2 = algebraMap A B u)
    (hu : IsUnit u) (htwo : IsUnit (2 : A))
    (hmin : minpoly A x = X ^ 2 - C u) :
    differentIdeal A B = ⊤ := by
  have hxunit : IsUnit x := (isUnit_pow_iff (by decide : 2 ≠ 0)).mp (by
    rw [hroot]
    exact hu.map (algebraMap A B))
  have hderiv : (2 : B) * x ∈ differentIdeal A B := by
    have hd := aeval_derivative_mem_differentIdeal A F E x hgen
    rw [hmin] at hd
    simpa only [derivative_sub, derivative_pow, derivative_X, derivative_C,
      sub_zero, Nat.reduceSub, pow_one, mul_one, aeval_mul, aeval_natCast, aeval_C, map_natCast, Nat.cast_ofNat, map_ofNat, aeval_X] using hd
  apply Ideal.eq_top_of_isUnit_mem _ hderiv
  have htwoB : IsUnit (2 : B) := by simpa only [map_ofNat] using htwo.map (algebraMap A B)
  exact htwoB.mul hxunit

/-- Any annihilating polynomial at a primitive integral element has derivative
in the different; divisibility by the minimal polynomial supplies the proof. -/
theorem aeval_derivative_mem_of_aeval_eq_zero
    (x : B) (p : A[X])
    (hgen : Algebra.adjoin F {algebraMap B E x} = ⊤)
    (hp : aeval x p = 0) :
    aeval x p.derivative ∈ differentIdeal A B := by
  obtain ⟨q, rfl⟩ := minpoly.isIntegrallyClosed_dvd
    (IsIntegralClosure.isIntegral A E x) hp
  simpa only [derivative_mul, map_add, map_mul, minpoly.aeval, zero_mul, zero_add, add_zero] using
    (differentIdeal A B).mul_mem_right (aeval x q)
      (aeval_derivative_mem_differentIdeal A F E x hgen)

/-- A primitive square root of a unit has trivial different when two is a unit.
This includes a trivial square-root adjunction and requires no degree assumption. -/
theorem differentIdeal_eq_top_of_unit_root
    (x : B) (u : A)
    (hgen : Algebra.adjoin F {algebraMap B E x} = ⊤)
    (hroot : x ^ 2 = algebraMap A B u)
    (hu : IsUnit u) (htwo : IsUnit (2 : A)) :
    differentIdeal A B = ⊤ := by
  have hxunit : IsUnit x := (isUnit_pow_iff (by decide : 2 ≠ 0)).mp (by
    rw [hroot]
    exact hu.map (algebraMap A B))
  have hderiv : (2 : B) * x ∈ differentIdeal A B := by
    have hd := aeval_derivative_mem_of_aeval_eq_zero x (X ^ 2 - C u) hgen
      (by simp [hroot])
    simpa only [derivative_sub, derivative_pow, derivative_X, derivative_C,
      sub_zero, Nat.reduceSub, pow_one, mul_one, aeval_mul, aeval_natCast,
      aeval_C, map_natCast, Nat.cast_ofNat, map_ofNat, aeval_X] using hd
  apply Ideal.eq_top_of_isUnit_mem _ hderiv
  have htwoB : IsUnit (2 : B) := by simpa only [map_ofNat] using htwo.map (algebraMap A B)
  exact htwoB.mul hxunit

/-- In actual degree two, the root relation and generation prove the minimal
polynomial, so no polynomial-identification hypothesis is required. -/
theorem differentIdeal_eq_top_of_quadratic_unit
    (x : B) (u : A)
    (hgen : Algebra.adjoin F {algebraMap B E x} = ⊤)
    (hroot : x ^ 2 = algebraMap A B u)
    (hu : IsUnit u) (htwo : IsUnit (2 : A))
    (hdegree : Module.finrank F E = 2) :
    differentIdeal A B = ⊤ := by
  apply differentIdeal_eq_top_of_minpoly_eq x u hgen hroot hu htwo
  exact minpoly_eq_quadratic x u (IsIntegralClosure.isIntegral A E x)
    hroot hgen hdegree

end FourCorner.QuadraticDifferentUnit

#print axioms FourCorner.QuadraticDifferentUnit.differentIdeal_eq_top_of_minpoly_eq

#print axioms FourCorner.QuadraticDifferentUnit.minpoly_eq_quadratic
#print axioms FourCorner.QuadraticDifferentUnit.differentIdeal_eq_top_of_quadratic_unit

#print axioms FourCorner.QuadraticDifferentUnit.aeval_derivative_mem_of_aeval_eq_zero
#print axioms FourCorner.QuadraticDifferentUnit.differentIdeal_eq_top_of_unit_root
