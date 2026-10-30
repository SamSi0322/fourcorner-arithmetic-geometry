import ThetaCoverClassPortable.geometry.SquarefreeRatFunc
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Polynomial

noncomputable section

namespace FourCorner.AdjacentConicQuotient

/-- The quadratic radicand obtained from the affine adjacent conic equation. -/
def radicand {K : Type*} [Field K] (c A : K) : K[X] :=
  C A - C (A / c ^ 2) * X ^ 2

/-- The radicand is a unit multiple of a separable, nonconstant quadratic. -/
theorem radicand_factor {K : Type*} [Field K]
    (c A : K) (hc : c ≠ 0) :
    radicand c A = (X ^ 2 - C (c ^ 2)) * C (-A / c ^ 2) := by
  have heq : c ^ 2 * (A / c ^ 2) = A := by field_simp
  simp only [radicand, neg_div, map_neg, sub_mul, mul_neg, ← C_mul, heq]
  ring

/-- The adjacent conic radicand is nonsquare in the actual rational function
field. The hypotheses are precisely the nondegeneracy of its two parameters. -/
theorem radicand_not_isSquare {K : Type*} [Field K] [CharZero K]
    (c A : K) (hc : c ≠ 0) (hA : A ≠ 0) :
    ¬ IsSquare (algebraMap K[X] (RatFunc K) (radicand c A)) := by
  rw [radicand_factor c A hc]
  apply FourCorner.CoverFields.squarefree_not_isSquare_fraction
  · exact ((separable_X_pow_sub_C (c ^ 2) (by norm_num) (pow_ne_zero _ hc)).mul_unit
      (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (div_ne_zero (neg_ne_zero.mpr hA)
        (pow_ne_zero _ hc))))).squarefree
  · intro h
    have hu : IsUnit (X ^ 2 - C (c ^ 2)) := isUnit_of_mul_isUnit_left h
    rw [isUnit_iff_degree_eq_zero, degree_X_pow_sub_C (by decide)] at hu
    norm_num at hu

#print axioms radicand_factor
#print axioms radicand_not_isSquare

end FourCorner.AdjacentConicQuotient
