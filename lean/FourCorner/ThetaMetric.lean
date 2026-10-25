import FourCorner.RadiusModel
import Mathlib.Tactic.Ring

namespace FourCorner

/-- The complete ordered affine source at opposite radius difference `1/5`. -/
def ThetaSource (P Q R z : ℚ) : Prop :=
  P ^ 2 = z ^ 2 + 50 ∧
  Q ^ 2 = z ^ 2 + 14 * z + 51 ∧
  R ^ 2 = z ^ 2 - 14 * z + 51

/-- The source inequalities retain all four positive radii and the open square. -/
def ThetaPositiveSource (P Q R z : ℚ) : Prop :=
  ThetaSource P Q R z ∧ 1 < P ∧ 0 < Q ∧ 0 < R ∧ P + 7 * |z| < 50

theorem theta_source_iff_four_squares {P Q R z : ℚ} :
    ThetaSource P Q R z ↔
      FourSquares ((50 - P - 7 * z) / 100) ((50 - P + 7 * z) / 100)
        ((P - 1) / 10) (Q / 10) (R / 10) ((P + 1) / 10) := by
  constructor
  · rintro ⟨hP, hQ, hR⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination (49 / 5000 : ℚ) * hP
    · linear_combination (1 / 100 : ℚ) * hQ - (1 / 5000 : ℚ) * hP
    · linear_combination (1 / 100 : ℚ) * hR - (1 / 5000 : ℚ) * hP
    · linear_combination (49 / 5000 : ℚ) * hP
  · rintro ⟨h₀, h₁, h₂, h₃⟩
    refine ⟨?_, ?_, ?_⟩
    · linear_combination (5000 / 49 : ℚ) * h₀
    · linear_combination 100 * h₁ + (100 / 49 : ℚ) * h₀
    · linear_combination 100 * h₂ + (100 / 49 : ℚ) * h₀

theorem theta_positive_source_to_strict_point {P Q R z : ℚ}
    (h : ThetaPositiveSource P Q R z) :
    StrictPoint ((50 - P - 7 * z) / 100) ((50 - P + 7 * z) / 100)
      ((P - 1) / 10) (Q / 10) (R / 10) ((P + 1) / 10) := by
  rcases h with ⟨hs, hP, hQ, hR, hstrict⟩
  have habs₁ := le_abs_self z
  have habs₂ := neg_le_abs z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, theta_source_iff_four_squares.mp hs⟩
  all_goals linarith

theorem theta_opposite_radius_difference (P : ℚ) :
    (P + 1) / 10 - (P - 1) / 10 = (1 / 5 : ℚ) := by ring

theorem theta_positive_source_iff_strict_point {P Q R z : ℚ} :
    ThetaPositiveSource P Q R z ↔
    StrictPoint ((50 - P - 7 * z) / 100) ((50 - P + 7 * z) / 100)
      ((P - 1) / 10) (Q / 10) (R / 10) ((P + 1) / 10) := by
  constructor
  · exact theta_positive_source_to_strict_point
  · rintro ⟨hx, hx', hy, hy', h₀, h₁, h₂, h₃, hs⟩
    refine ⟨theta_source_iff_four_squares.mpr hs, ?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
    · rcases le_total 0 z with hz | hz
      · rw [abs_of_nonneg hz]
        linarith
      · rw [abs_of_nonpos hz]
        linarith

/-- The inverse uses the actual four labelled radii of the same strict point. -/
theorem strict_point_difference_inverse_coordinates {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) (hd : r₃ - r₀ = 1 / 5) :
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

theorem strict_point_difference_to_theta_positive_source {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) (hd : r₃ - r₀ = 1 / 5) :
    ThetaPositiveSource (5 * (r₃ + r₀)) (10 * r₁) (10 * r₂)
      (50 * (y - x) / 7) := by
  apply theta_positive_source_iff_strict_point.mpr
  obtain ⟨hx, hy, h₀, h₃⟩ := strict_point_difference_inverse_coordinates h hd
  rw [← hx, ← hy, ← h₀, ← h₃]
  norm_num
  exact h

#print axioms theta_source_iff_four_squares
#print axioms theta_positive_source_to_strict_point
#print axioms theta_opposite_radius_difference
#print axioms theta_positive_source_iff_strict_point
#print axioms strict_point_difference_inverse_coordinates
#print axioms strict_point_difference_to_theta_positive_source
end FourCorner
