import FourCorner.ThetaLocalReal

namespace FourCorner

theorem real_theta_source_iff_four_squares {P Q R z : ℝ} :
    RealThetaSource P Q R z ↔
      RealFourSquares ((50 - P - 7 * z) / 100) ((50 - P + 7 * z) / 100)
        ((P - 1) / 10) (Q / 10) (R / 10) ((P + 1) / 10) := by
  constructor
  · rintro ⟨hP, hQ, hR⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination (49 / 5000 : ℝ) * hP
    · linear_combination (1 / 100 : ℝ) * hQ - (1 / 5000 : ℝ) * hP
    · linear_combination (1 / 100 : ℝ) * hR - (1 / 5000 : ℝ) * hP
    · linear_combination (49 / 5000 : ℝ) * hP
  · rintro ⟨h₀, h₁, h₂, h₃⟩
    refine ⟨?_, ?_, ?_⟩
    · linear_combination (5000 / 49 : ℝ) * h₀
    · linear_combination 100 * h₁ + (100 / 49 : ℝ) * h₀
    · linear_combination 100 * h₂ + (100 / 49 : ℝ) * h₀

theorem real_theta_opposite_radius_difference (P : ℝ) :
    (P + 1) / 10 - (P - 1) / 10 = (1 / 5 : ℝ) := by ring

theorem real_theta_positive_source_iff_strict_point {P Q R z : ℝ} :
    RealThetaPositiveSource P Q R z ↔
    RealStrictPoint ((50 - P - 7 * z) / 100) ((50 - P + 7 * z) / 100)
      ((P - 1) / 10) (Q / 10) (R / 10) ((P + 1) / 10) := by
  constructor
  · exact real_theta_positive_source_to_strict_point
  · rintro ⟨hx, hx', hy, hy', h₀, h₁, h₂, h₃, hs⟩
    refine ⟨real_theta_source_iff_four_squares.mpr hs, ?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
    · rcases le_total 0 z with hz | hz
      · rw [abs_of_nonneg hz]
        linarith
      · rw [abs_of_nonpos hz]
        linarith

/-- The inverse uses the actual four labelled radii of the same strict point. -/
theorem real_strict_point_difference_inverse_coordinates {x y r₀ r₁ r₂ r₃ : ℝ}
    (h : RealStrictPoint x y r₀ r₁ r₂ r₃) (hd : r₃ - r₀ = 1 / 5) :
    x = (50 - 5 * (r₃ + r₀) - 7 * (50 * (y - x) / 7)) / 100 ∧
    y = (50 - 5 * (r₃ + r₀) + 7 * (50 * (y - x) / 7)) / 100 ∧
    r₀ = (5 * (r₃ + r₀) - 1) / 10 ∧
    r₃ = (5 * (r₃ + r₀) + 1) / 10 := by
  obtain ⟨hx, hx', hy, hy', hr₀, hr₁, hr₂, hr₃, h₀, h₁, h₂, h₃⟩ := h
  have hr : r₃ = r₀ + 1 / 5 := by linarith
  have hsum : x + y = 1 - (r₀ + r₃) / 10 := by
    rw [hr] at h₃ ⊢
    nlinarith [h₀, h₃]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals linarith

theorem real_strict_point_difference_to_theta_positive_source {x y r₀ r₁ r₂ r₃ : ℝ}
    (h : RealStrictPoint x y r₀ r₁ r₂ r₃) (hd : r₃ - r₀ = 1 / 5) :
    RealThetaPositiveSource (5 * (r₃ + r₀)) (10 * r₁) (10 * r₂)
      (50 * (y - x) / 7) := by
  apply real_theta_positive_source_iff_strict_point.mpr
  obtain ⟨hx, hy, h₀, h₃⟩ := real_strict_point_difference_inverse_coordinates h hd
  rw [← hx, ← hy, ← h₀, ← h₃]
  norm_num
  exact h


#print axioms real_theta_source_iff_four_squares
#print axioms real_theta_positive_source_iff_strict_point
#print axioms real_theta_opposite_radius_difference
#print axioms real_strict_point_difference_inverse_coordinates
#print axioms real_strict_point_difference_to_theta_positive_source
end FourCorner
