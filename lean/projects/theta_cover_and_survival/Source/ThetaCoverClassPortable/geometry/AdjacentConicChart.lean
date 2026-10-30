import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
The explicit rational chart of the adjacent conic
`(c² - 1) U² + c² V² = c² (c² - 1)`.
The inverse is `V / (c - U)`, and its only omitted affine point is `(c, 0)`.
-/

noncomputable section

namespace FourCorner.AdjacentConic.Chart

variable {K : Type*} [Field K]

/-- The common denominator of the conic chart. -/
def denominator (c t : K) : K := c ^ 2 * t ^ 2 + c ^ 2 - 1

/-- The first coordinate of the conic chart. -/
def u (c t : K) : K := c * (c ^ 2 * t ^ 2 - c ^ 2 + 1) / denominator c t

/-- The second coordinate of the conic chart. -/
def v (c t : K) : K := 2 * c * (c ^ 2 - 1) * t / denominator c t

/-- Every parameter for which the chart is defined lies on the conic. -/
theorem conic_identity (c t : K) (hD : denominator c t ≠ 0) :
    (c ^ 2 - 1) * (u c t) ^ 2 + c ^ 2 * (v c t) ^ 2 -
      c ^ 2 * (c ^ 2 - 1) = 0 := by
  unfold u v
  field_simp
  unfold denominator
  ring

/-- The linear factor excluded by the inverse, expressed in the parameter. -/
theorem c_sub_u (c t : K) (hD : denominator c t ≠ 0) :
    c - u c t = 2 * c * (c ^ 2 - 1) / denominator c t := by
  unfold u
  field_simp
  unfold denominator
  ring

variable [CharZero K]

theorem c_sub_u_ne_zero (c t : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0)
    (hD : denominator c t ≠ 0) : c - u c t ≠ 0 := by
  rw [c_sub_u c t hD]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hc) hA) hD

/-- The chart recovers its parameter by the stated rational inverse. -/
theorem inverse (c t : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0)
    (hD : denominator c t ≠ 0) : v c t / (c - u c t) = t := by
  rw [c_sub_u c t hD]
  unfold v
  field_simp

omit [CharZero K] in
/-- The common denominator at the inverse parameter has a simple expression. -/
theorem denominator_inverse (c U V : K)
    (hconic : (c ^ 2 - 1) * U ^ 2 + c ^ 2 * V ^ 2 - c ^ 2 * (c ^ 2 - 1) = 0)
    (hU : c - U ≠ 0) :
    denominator c (V / (c - U)) = 2 * c * (c ^ 2 - 1) / (c - U) := by
  unfold denominator
  field_simp
  linear_combination hconic

/-- Every conic point away from `(c, 0)` gives a valid chart parameter. -/
theorem denominator_inverse_ne_zero (c U V : K) (hc : c ≠ 0)
    (hA : c ^ 2 - 1 ≠ 0)
    (hconic : (c ^ 2 - 1) * U ^ 2 + c ^ 2 * V ^ 2 - c ^ 2 * (c ^ 2 - 1) = 0)
    (hU : c - U ≠ 0) : denominator c (V / (c - U)) ≠ 0 := by
  rw [denominator_inverse c U V hconic hU]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hc) hA) hU

/-- Reconstruction of the first coordinate from a conic point. -/
theorem u_inverse (c U V : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0)
    (hconic : (c ^ 2 - 1) * U ^ 2 + c ^ 2 * V ^ 2 - c ^ 2 * (c ^ 2 - 1) = 0)
    (hU : c - U ≠ 0) : u c (V / (c - U)) = U := by
  unfold u
  rw [denominator_inverse c U V hconic hU]
  field_simp
  linear_combination hconic

/-- Reconstruction of the second coordinate from a conic point. -/
theorem v_inverse (c U V : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0)
    (hconic : (c ^ 2 - 1) * U ^ 2 + c ^ 2 * V ^ 2 - c ^ 2 * (c ^ 2 - 1) = 0)
    (hU : c - U ≠ 0) : v c (V / (c - U)) = V := by
  unfold v
  rw [denominator_inverse c U V hconic hU]
  field_simp

omit [CharZero K] in
/-- A conic point with first coordinate `c` necessarily has second coordinate zero. -/
theorem omitted_point (c U V : K) (hc : c ≠ 0)
    (hconic : (c ^ 2 - 1) * U ^ 2 + c ^ 2 * V ^ 2 - c ^ 2 * (c ^ 2 - 1) = 0)
    (hU : U = c) : V = 0 := by
  subst U
  have h : c ^ 2 * V ^ 2 = 0 := by linear_combination hconic
  exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp
    ((mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hc))

end FourCorner.AdjacentConic.Chart
