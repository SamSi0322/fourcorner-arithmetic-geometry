import FourCorner.RadiusModel
import FourCorner.FermatSymmetry
import UniformCurve

/-! Strict interval bounds for the pair-parameter image, derived from the
original labelled rational-distance point without choosing a chamber. -/

namespace FourCorner.UniformTorsion

theorem strict_point_opposite_radius_sq_sum_lt_two {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) : r₀ ^ 2 + r₃ ^ 2 < 2 := by
  rcases h with ⟨hx₀, hx₁, hy₀, hy₁, _, _, _, _, h₀, _, _, h₃⟩
  have hx := mul_pos hx₀ (sub_pos.mpr hx₁)
  have hy := mul_pos hy₀ (sub_pos.mpr hy₁)
  nlinarith

/-- The positive interval follows from the original strict point and either
sign choice in the parameter relation. -/
theorem strict_point_pair_parameter_interval {x y r₀ r₁ r₂ r₃ mu nu eps : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) (hnu : 0 < nu)
    (heps : eps = 1 ∨ eps = -1) (hmu : mu = nu * (r₃ + eps * r₀)) :
    0 < (nu * (r₃ - eps * r₀)) ^ 2 ∧
      (nu * (r₃ - eps * r₀)) ^ 2 < 4 * nu ^ 2 - mu ^ 2 := by
  have hsum := strict_point_opposite_radius_sq_sum_lt_two h
  have hanti := strict_point_not_antidiagonal h
  rcases h with ⟨_, _, _, _, hr₀, _, _, hr₃, h₀, _, _, h₃⟩
  have hrne : r₃ ≠ r₀ := by
    intro heq
    apply hanti
    rw [heq] at h₃
    linear_combination (1 / 2 : ℚ) * (h₃ - h₀)
  have hd : r₃ - eps * r₀ ≠ 0 := by
    rcases heps with rfl | rfl
    · simpa only [one_mul] using sub_ne_zero.mpr hrne
    · intro heq
      nlinarith only [hr₀, hr₃, heq]
  have hnu2 : 0 < nu ^ 2 := sq_pos_of_pos hnu
  have hidentity : (nu * (r₃ - eps * r₀)) ^ 2 + mu ^ 2 =
      2 * nu ^ 2 * (r₀ ^ 2 + r₃ ^ 2) := by
    rw [hmu]
    rcases heps with rfl | rfl <;> ring
  have hu := mul_lt_mul_of_pos_left hsum (mul_pos (show (0 : ℚ) < 2 by norm_num) hnu2)
  refine ⟨sq_pos_of_ne_zero (mul_ne_zero hnu.ne' hd), ?_⟩
  calc
    (nu * (r₃ - eps * r₀)) ^ 2 =
        2 * nu ^ 2 * (r₀ ^ 2 + r₃ ^ 2) - mu ^ 2 := eq_sub_of_add_eq hidentity
    _ < 2 * nu ^ 2 * 2 - mu ^ 2 := sub_lt_sub_right hu _
    _ = 4 * nu ^ 2 - mu ^ 2 := by ring

/-- Integer parameters use the same interval, with upper endpoint the shared
coefficient `B`. -/
theorem strict_point_integer_pair_parameter_interval {x y r₀ r₁ r₂ r₃ eps : ℚ}
    {mu nu : ℤ} (h : StrictPoint x y r₀ r₁ r₂ r₃) (hnu : 0 < nu)
    (heps : eps = 1 ∨ eps = -1)
    (hmu : (mu : ℚ) = (nu : ℚ) * (r₃ + eps * r₀)) :
    0 < ((nu : ℚ) * (r₃ - eps * r₀)) ^ 2 ∧
      ((nu : ℚ) * (r₃ - eps * r₀)) ^ 2 < (B mu nu : ℚ) := by
  have hi := strict_point_pair_parameter_interval h (by exact_mod_cast hnu) heps hmu
  simpa only [B, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] using hi

end FourCorner.UniformTorsion

#print axioms FourCorner.UniformTorsion.strict_point_opposite_radius_sq_sum_lt_two
#print axioms FourCorner.UniformTorsion.strict_point_pair_parameter_interval
#print axioms FourCorner.UniformTorsion.strict_point_integer_pair_parameter_interval
