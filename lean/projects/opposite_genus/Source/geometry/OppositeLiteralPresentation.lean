import geometry.OppositeCoordinatePolynomials

noncomputable section
open Polynomial
namespace FourCorner.OppositeLiteralPresentation
open OppositePolynomials OppositeCoordinatePolynomials
variable {K : Type*} [Field K] [CharZero K]

/-- A unit row operation on the original first relation. -/
theorem polynomial_zero_relation (mu nu : K) (hA : A mu nu ≠ 0) :
    C (A mu nu) * (coefficient mu nu 0 - C (2 * nu^2)) = X^2 := by
  apply IsFractionRing.injective K[X] (RatFunc K)
  simpa only [map_mul, map_sub, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
    map_coefficient, ← RatFunc.algebraMap_eq_C, map_ofNat] using
    OppositeNormalizedField.value_zero_equation mu nu hA

theorem polynomial_plus_relation (mu nu : K) (hA : A mu nu ≠ 0) :
    coefficient mu nu 1 = coefficient mu nu 0 + C (mu^2) + C 2 * X := by
  apply IsFractionRing.injective K[X] (RatFunc K)
  simpa only [map_add, map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
    map_coefficient, ← RatFunc.algebraMap_eq_C, map_ofNat] using
    OppositeNormalizedField.value_plus_equation mu nu hA

theorem polynomial_minus_relation (mu nu : K) (hA : A mu nu ≠ 0) :
    coefficient mu nu 2 = coefficient mu nu 0 + C (mu^2) - C 2 * X := by
  apply IsFractionRing.injective K[X] (RatFunc K)
  simpa only [map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
    map_coefficient, ← RatFunc.algebraMap_eq_C, map_ofNat] using
    OppositeNormalizedField.value_minus_equation mu nu hA

/-- Over every K-algebra, including rings with zero divisors, the original
three equations and the three defining monic quotient relations are equivalent.
This verifies the literal affine presentation, not merely equations at one
selected field-valued point. -/
theorem equations_iff {T : Type*} [CommRing T] [Algebra K T]
    (mu nu : K) (hA : A mu nu ≠ 0) (z p q r : T) :
    (z^2 = algebraMap K T (A mu nu) * (p^2 - 2*(algebraMap K T nu)^2) ∧
      q^2 = p^2 + (algebraMap K T mu)^2 + 2*z ∧
      r^2 = p^2 + (algebraMap K T mu)^2 - 2*z) ↔
    (p^2 = aeval z (coefficient mu nu 0) ∧
      q^2 = aeval z (coefficient mu nu 1) ∧
      r^2 = aeval z (coefficient mu nu 2)) := by
  have h0 := congrArg (aeval z : K[X] →ₐ[K] T) (polynomial_zero_relation mu nu hA)
  have h1 := congrArg (aeval z : K[X] →ₐ[K] T) (polynomial_plus_relation mu nu hA)
  have h2 := congrArg (aeval z : K[X] →ₐ[K] T) (polynomial_minus_relation mu nu hA)
  simp only [map_mul, map_sub, map_add, map_pow, aeval_C, aeval_X, map_ofNat] at h0 h1 h2
  have hu : IsUnit (algebraMap K T (A mu nu)) :=
    (isUnit_iff_ne_zero.mpr hA).map (algebraMap K T)
  constructor
  · rintro ⟨hp, hq, hr⟩
    have hp' : p^2 = aeval z (coefficient mu nu 0) := by
      have hcancel := hu.mul_left_cancel (hp.symm.trans h0.symm)
      linear_combination hcancel
    refine ⟨hp', ?_, ?_⟩
    · rw [h1, ← hp']
      exact hq
    · rw [h2, ← hp']
      exact hr
  · rintro ⟨hp, hq, hr⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hp]
      exact h0.symm
    · rw [hq, h1, hp]
    · rw [hr, h2, hp]

#print axioms polynomial_zero_relation
#print axioms polynomial_plus_relation
#print axioms polynomial_minus_relation
#print axioms equations_iff
end FourCorner.OppositeLiteralPresentation
