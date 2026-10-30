import Mathlib.Tactic

set_option autoImplicit false

namespace FourCorner

section AxisIdentities

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- Exact discriminant factorization for an affine line parallel to a coordinate
axis. All quantities are the literal coefficients of the restricted quartic. -/
theorem theta_axis_discriminant_factor (u : K) :
    (19598 - 39592 * u ^ 2) ^ 2 -
      4 * 9801 * (9801 - 39592 * u ^ 2 + 39984 * u ^ 4) =
      -3136 * (u ^ 2 - 50) * (2 * u ^ 2 - 1) := by
  ring

omit [CharZero K] in
/-- Exact discriminant factorization for the vertical restriction. -/
theorem theta_vertical_discriminant_factor (t : K) :
    (-39592 * (t ^ 2 + 1)) ^ 2 -
      4 * 39984 * (9801 * (t ^ 4 + 1) + 19598 * t ^ 2) =
      -6272 * (t ^ 4 - 100 * t ^ 2 + 1) := by
  ring

/-- Vanishing of the affine-axis discriminant gives the two exact square
values, without making any choice of their square roots. -/
theorem theta_axis_square_values {u : K}
    (h : (19598 - 39592 * u ^ 2) ^ 2 -
      4 * 9801 * (9801 - 39592 * u ^ 2 + 39984 * u ^ 4) = 0) :
    u ^ 2 = 1 / 2 ∨ u ^ 2 = 50 := by
  rw [theta_axis_discriminant_factor] at h
  have hp : (u ^ 2 - 50) * (2 * u ^ 2 - 1) = 0 := by
    apply (mul_eq_zero.mp (show (-3136 : K) *
      ((u ^ 2 - 50) * (2 * u ^ 2 - 1)) = 0 by
        simpa only [mul_assoc] using h)).resolve_left
    norm_num
  rcases mul_eq_zero.mp hp with h50 | hhalf
  · exact Or.inr (sub_eq_zero.mp h50)
  · apply Or.inl
    apply (eq_div_iff (by norm_num : (2 : K) ≠ 0)).mpr
    calc
      u ^ 2 * 2 = 2 * u ^ 2 := mul_comm _ _
      _ = 1 := sub_eq_zero.mp hhalf

/-- Vanishing of the vertical discriminant gives its literal reciprocal
quartic equation. -/
theorem theta_vertical_square_values {t : K}
    (h : (-39592 * (t ^ 2 + 1)) ^ 2 -
      4 * 39984 * (9801 * (t ^ 4 + 1) + 19598 * t ^ 2) = 0) :
    t ^ 4 - 100 * t ^ 2 + 1 = 0 := by
  rw [theta_vertical_discriminant_factor] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

omit [CharZero K] in
/-- At the coordinate axis itself the first discriminant is nonzero. -/
theorem theta_axis_zero_discriminant_value :
    (19598 - 39592 * (0 : K) ^ 2) ^ 2 -
      4 * 9801 * (9801 - 39592 * (0 : K) ^ 2 + 39984 * (0 : K) ^ 4) =
      -156800 := by
  ring

omit [CharZero K] in
/-- At the other coordinate axis the vertical discriminant is nonzero. -/
theorem theta_vertical_zero_discriminant_value :
    (-39592 * ((0 : K) ^ 2 + 1)) ^ 2 -
      4 * 39984 * (9801 * ((0 : K) ^ 4 + 1) + 19598 * (0 : K) ^ 2) =
      -6272 := by
  ring

/-- No zero affine-axis parameter can satisfy the discriminant condition. -/
theorem theta_axis_parameter_ne_zero {u : K}
    (h : (19598 - 39592 * u ^ 2) ^ 2 -
      4 * 9801 * (9801 - 39592 * u ^ 2 + 39984 * u ^ 4) = 0) :
    u ≠ 0 := by
  intro hu
  rw [hu, theta_axis_zero_discriminant_value] at h
  norm_num at h

/-- No zero vertical parameter can satisfy the discriminant condition. -/
theorem theta_vertical_parameter_ne_zero {t : K}
    (h : (-39592 * (t ^ 2 + 1)) ^ 2 -
      4 * 39984 * (9801 * (t ^ 4 + 1) + 19598 * t ^ 2) = 0) :
    t ≠ 0 := by
  intro ht
  rw [ht, theta_vertical_zero_discriminant_value] at h
  norm_num at h

end AxisIdentities

#print axioms theta_axis_discriminant_factor
#print axioms theta_vertical_discriminant_factor
#print axioms theta_axis_square_values
#print axioms theta_vertical_square_values
#print axioms theta_axis_zero_discriminant_value
#print axioms theta_vertical_zero_discriminant_value
#print axioms theta_axis_parameter_ne_zero
#print axioms theta_vertical_parameter_ne_zero

end FourCorner
