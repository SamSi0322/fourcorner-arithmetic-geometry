import geometry.OppositeNormalizedField

noncomputable section
set_option linter.unusedSectionVars false
open Polynomial
open scoped BigOperators
namespace FourCorner.OppositeCoordinatePolynomials
open OppositePolynomials
variable {K : Type*} [Field K] [CharZero K]

/-- Polynomial coefficients for the literal equations P²=g₀,Q²=g₁,R²=g₂
in the coordinate ring over K[Z]. The only denominator is a nonzero constant. -/
def coefficient (mu nu : K) (i : Fin 3) : K[X] :=
  C ((A mu nu)⁻¹) * radicand mu nu i

private theorem constant_unit {mu nu : K} (hA : A mu nu ≠ 0) :
    IsUnit (C ((A mu nu)⁻¹) : K[X]) :=
  Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hA))

theorem coefficient_associated {mu nu : K} (hA : A mu nu ≠ 0) (i : Fin 3) :
    Associated (coefficient mu nu i) (radicand mu nu i) :=
  associated_unit_mul_left _ _ (constant_unit hA)

theorem coefficient_squarefree {mu nu : K} (hmu : mu ≠ 0) (hnu : nu ≠ 0)
    (hA : A mu nu ≠ 0) (i : Fin 3) : Squarefree (coefficient mu nu i) :=
  (coefficient_associated hA i).squarefree_iff.mpr (radicand_squarefree hmu hnu hA i)

theorem coefficient_not_isUnit (mu nu : K) (i : Fin 3) :
    ¬ IsUnit (coefficient mu nu i) := by
  intro h
  apply radicand_not_isUnit mu nu i
  exact isUnit_of_dvd_unit (show radicand mu nu i ∣ coefficient mu nu i from
    ⟨C ((A mu nu)⁻¹), by simp only [coefficient, mul_comm]⟩) h

theorem coefficient_isCoprime {mu nu : K} (hA : A mu nu ≠ 0)
    (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) {i j : Fin 3} (hij : i ≠ j) :
    IsCoprime (coefficient mu nu i) (coefficient mu nu j) :=
  (isCoprime_mul_units_left (constant_unit hA) (constant_unit hA) _ _).mpr
    (radicand_isCoprime hA hB hS hij)

/-- The coordinate polynomial maps to the literal normalized rational function. -/
theorem map_coefficient (mu nu : K) (i : Fin 3) :
    algebraMap K[X] (RatFunc K) (coefficient mu nu i) =
      OppositeNormalizedField.value mu nu i := by
  simp only [coefficient, map_mul, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C,
    map_inv₀, OppositeNormalizedField.value, OppositeFunctionField.radicandValue,
    div_eq_mul_inv, mul_comm]

/-- Independence of the literal coordinate polynomials holds over every
characteristic-zero constant field, without an algebraic-closure assumption. -/
theorem nonempty_product_nonsquare {mu nu : K} (hmu : mu ≠ 0) (hnu : nu ≠ 0)
    (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0)
    (s : Finset (Fin 3)) (hne : s.Nonempty) :
    ¬ IsSquare (∏ i ∈ s, algebraMap K[X] (RatFunc K) (coefficient mu nu i)) := by
  have h := CoverFields.polynomial_prod_not_isSquare_ratFunc s (coefficient mu nu) hne
    (fun i _ j _ hij => (coefficient_isCoprime hA hB hS hij).isRelPrime)
    (fun i _ => coefficient_squarefree hmu hnu hA i)
    (fun i _ => coefficient_not_isUnit mu nu i)
  simpa only [map_prod] using h

/-- Coefficient extension preserves the exact polynomial presentation. -/
theorem coefficient_map {L : Type*} [Field L] [CharZero L] (f : K →+* L)
    (mu nu : K) (i : Fin 3) :
    (coefficient mu nu i).map f = coefficient (f mu) (f nu) i := by
  fin_cases i <;>
    simp [coefficient, radicand, fZero, fPlus, fMinus, A, map_inv₀, map_ofNat]

#print axioms coefficient_squarefree
#print axioms coefficient_isCoprime
#print axioms map_coefficient
#print axioms nonempty_product_nonsquare
#print axioms coefficient_map
end FourCorner.OppositeCoordinatePolynomials
