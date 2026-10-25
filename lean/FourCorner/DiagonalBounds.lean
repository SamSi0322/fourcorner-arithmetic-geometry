import FourCorner.RadiusModel

/-! Exact diagonal triangle bounds for the strict rational radius model. -/
namespace FourCorner

/-- The sum of distances to opposite corners is at least the diagonal. -/
theorem diagonal_sum_square_ge_two {x y a b : ℚ}
    (hx₀ : 0 < x) (hx₁ : x < 1) (hy₀ : 0 < y) (hy₁ : y < 1)
    (ha : 0 < a) (hb : 0 < b)
    (ha₂ : a ^ 2 = x ^ 2 + y ^ 2)
    (hb₂ : b ^ 2 = (1 - x) ^ 2 + (1 - y) ^ 2) :
    2 ≤ (a + b) ^ 2 := by
  have hinner : 0 ≤ x * (1 - x) + y * (1 - y) := by positivity
  have hprod : 0 ≤ a * b := le_of_lt (mul_pos ha hb)
  have hgram : (a * b) ^ 2 =
      (x * (1 - x) + y * (1 - y)) ^ 2 + (x - y) ^ 2 := by
    linear_combination b ^ 2 * ha₂ + (x ^ 2 + y ^ 2) * hb₂
  have hsq : (x * (1 - x) + y * (1 - y)) ^ 2 ≤ (a * b) ^ 2 := by
    nlinarith only [hgram, sq_nonneg (x - y)]
  have hinner_le := (sq_le_sq₀ hinner hprod).mp hsq
  nlinarith only [ha₂, hb₂, hinner_le]

/-- Both diagonal sums satisfy the triangle inequality, without chamber hypotheses. -/
theorem strict_point_diagonal_sums {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) :
    2 ≤ (r₀ + r₃) ^ 2 ∧ 2 ≤ (r₁ + r₂) ^ 2 := by
  rcases h with ⟨hx₀, hx₁, hy₀, hy₁, hr₀, hr₁, hr₂, hr₃, h₀, h₁, h₂, h₃⟩
  constructor
  · exact diagonal_sum_square_ge_two hx₀ hx₁ hy₀ hy₁ hr₀ hr₃ h₀ h₃
  · apply diagonal_sum_square_ge_two (x := 1 - x) (y := y)
        (by linarith) (by linarith) hy₀ hy₁ hr₁ hr₂ h₁
    nlinarith only [h₂]

/-- Squared differences of opposite-corner distances are bounded by coordinates. -/
theorem strict_point_diagonal_difference_bound {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) :
    (r₀ - r₃) ^ 2 + (r₂ - r₁) ^ 2 ≤
      2 * ((x + y - 1) ^ 2 + (x - y) ^ 2) := by
  obtain ⟨hs, ht⟩ := strict_point_diagonal_sums h
  rcases h with ⟨hx₀, hx₁, hy₀, hy₁, hr₀, hr₁, hr₂, hr₃, h₀, h₁, h₂, h₃⟩
  have hd : (r₀ + r₃) * (r₀ - r₃) = 2 * (x + y - 1) := by
    linear_combination h₀ - h₃
  have he : (r₁ + r₂) * (r₂ - r₁) = 2 * (x - y) := by
    linear_combination h₂ - h₁
  have hd₂ : (r₀ + r₃) ^ 2 * (r₀ - r₃) ^ 2 = 4 * (x + y - 1) ^ 2 := by
    nlinarith only [congrArg (fun z : ℚ => z ^ 2) hd]
  have he₂ : (r₁ + r₂) ^ 2 * (r₂ - r₁) ^ 2 = 4 * (x - y) ^ 2 := by
    nlinarith only [congrArg (fun z : ℚ => z ^ 2) he]
  have hdb := mul_le_mul_of_nonneg_right hs (sq_nonneg (r₀ - r₃))
  have heb := mul_le_mul_of_nonneg_right ht (sq_nonneg (r₂ - r₁))
  nlinarith only [hd₂, he₂, hdb, heb]

/-- The open square gives a strict upper bound for the coordinate expression. -/
theorem strict_square_diagonal_coordinate_bound {x y : ℚ}
    (hx₀ : 0 < x) (hx₁ : x < 1) (hy₀ : 0 < y) (hy₁ : y < 1) :
    2 * ((x + y - 1) ^ 2 + (x - y) ^ 2) < 2 := by
  nlinarith [mul_pos hx₀ (sub_pos.mpr hx₁), mul_pos hy₀ (sub_pos.mpr hy₁)]

/-- Positive diagonal parameters and the sharp coordinate bound in the chamber. -/
theorem strict_point_diagonal_bounds {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃)
    (hsum : 1 < x + y) (hdiff : y < x) :
    0 < r₀ - r₃ ∧ 0 < r₂ - r₁ ∧
    0 < r₀ + r₃ ∧ 0 < r₁ + r₂ ∧
    2 ≤ (r₀ + r₃) ^ 2 ∧ 2 ≤ (r₁ + r₂) ^ 2 ∧
    (r₀ - r₃) ^ 2 + (r₂ - r₁) ^ 2 ≤
      2 * ((x + y - 1) ^ 2 + (x - y) ^ 2) ∧
    2 * ((x + y - 1) ^ 2 + (x - y) ^ 2) < 2 := by
  obtain ⟨hs, ht⟩ := strict_point_diagonal_sums h
  have hb := strict_point_diagonal_difference_bound h
  rcases h with ⟨hx₀, hx₁, hy₀, hy₁, hr₀, hr₁, hr₂, hr₃, h₀, h₁, h₂, h₃⟩
  have hd : r₃ < r₀ := (sq_lt_sq₀ (le_of_lt hr₃) (le_of_lt hr₀)).mp (by
    nlinarith only [h₀, h₃, hsum])
  have he : r₁ < r₂ := (sq_lt_sq₀ (le_of_lt hr₁) (le_of_lt hr₂)).mp (by
    nlinarith only [h₁, h₂, hdiff])
  exact ⟨sub_pos.mpr hd, sub_pos.mpr he, add_pos hr₀ hr₃, add_pos hr₁ hr₂,
    hs, ht, hb, strict_square_diagonal_coordinate_bound hx₀ hx₁ hy₀ hy₁⟩

/-- Every strict point satisfies the strict diagonal-difference bound. -/
theorem strict_point_diagonal_difference_lt_two {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) :
    (r₀ - r₃) ^ 2 + (r₂ - r₁) ^ 2 < 2 := by
  exact lt_of_le_of_lt (strict_point_diagonal_difference_bound h)
    (strict_square_diagonal_coordinate_bound h.1 h.2.1 h.2.2.1 h.2.2.2.1)

end FourCorner
