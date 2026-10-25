import FourCorner.FermatSymmetry
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Abs

set_option autoImplicit false

namespace FourCorner

/-- The products of opposite radii are norms of two rational Gaussian
numbers whose imaginary parts differ by one. -/
theorem four_squares_opposite_products {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : FourSquares x y r₀ r₁ r₂ r₃) :
    (r₀ * r₃) ^ 2 = ((x - y) * (x + y - 1)) ^ 2 + (2 * x * y - x - y) ^ 2 ∧
    (r₁ * r₂) ^ 2 = ((x - y) * (x + y - 1)) ^ 2 + (2 * x * y - x - y + 1) ^ 2 := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := h
  constructor
  · calc
      (r₀ * r₃) ^ 2 = r₀ ^ 2 * r₃ ^ 2 := by ring
      _ = (x ^ 2 + y ^ 2) * ((1 - x) ^ 2 + (1 - y) ^ 2) := by rw [h₀, h₃]
      _ = _ := by ring
  · calc
      (r₁ * r₂) ^ 2 = r₁ ^ 2 * r₂ ^ 2 := by ring
      _ = ((1 - x) ^ 2 + y ^ 2) * (x ^ 2 + (1 - y) ^ 2) := by rw [h₁, h₂]
      _ = _ := by ring

/-- Two positive norms with a common nonzero real component and imaginary
components separated by one have sum strictly greater than one. -/
lemma norm_pair_sum_gt_one {a b u v : ℚ} (ha : 0 < a) (hb : 0 < b)
    (hu : u ≠ 0) (h₀ : a ^ 2 = u ^ 2 + v ^ 2)
    (h₁ : b ^ 2 = u ^ 2 + (v + 1) ^ 2) : 1 < a + b := by
  have hu_sq : 0 < u ^ 2 := sq_pos_of_ne_zero hu
  have hv : v ^ 2 < a ^ 2 := by linarith
  have hv1 : (v + 1) ^ 2 < b ^ 2 := by linarith
  have hav : -a < v := (abs_lt_of_sq_lt_sq' hv ha.le).1
  have hbv : v + 1 < b := (abs_lt_of_sq_lt_sq' hv1 hb.le).2
  linarith

/-- The kernel parameter built from the four actual positive rational radii
is strictly greater than one. Strictness follows from the rational diagonal
exclusions, rather than being imposed as a separate hypothesis. -/
theorem strict_point_kernel_gt_one {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) : 1 < r₀ * r₃ + r₁ * r₂ := by
  have hd := strict_point_not_diagonal h
  have ha := strict_point_not_antidiagonal h
  have hu : (x - y) * (x + y - 1) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hd) (sub_ne_zero.mpr ha)
  obtain ⟨_, _, _, _, hr₀, hr₁, hr₂, hr₃, hs⟩ := h
  obtain ⟨h₀, h₁⟩ := four_squares_opposite_products hs
  exact norm_pair_sum_gt_one (mul_pos hr₀ hr₃) (mul_pos hr₁ hr₂) hu h₀ h₁

end FourCorner

#print axioms FourCorner.four_squares_opposite_products
#print axioms FourCorner.norm_pair_sum_gt_one
#print axioms FourCorner.strict_point_kernel_gt_one
