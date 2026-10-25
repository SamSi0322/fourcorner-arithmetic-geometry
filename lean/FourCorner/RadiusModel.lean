import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-! Exact ordered four-distance equations and the strict radius model.
The quantified points and radii are rational. All four positivity conditions
and all four open-square inequalities are retained in the equivalence. -/
namespace FourCorner

/-- The original four labelled square identities. -/
def FourSquares (x y r₀ r₁ r₂ r₃ : ℚ) : Prop :=
  r₀ ^ 2 = x ^ 2 + y ^ 2 ∧
  r₁ ^ 2 = (1 - x) ^ 2 + y ^ 2 ∧
  r₂ ^ 2 = x ^ 2 + (1 - y) ^ 2 ∧
  r₃ ^ 2 = (1 - x) ^ 2 + (1 - y) ^ 2

/-- A strict point with its four positive labelled rational radii. -/
def StrictPoint (x y r₀ r₁ r₂ r₃ : ℚ) : Prop :=
  0 < x ∧ x < 1 ∧ 0 < y ∧ y < 1 ∧
  0 < r₀ ∧ 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃ ∧
  FourSquares x y r₀ r₁ r₂ r₃

/-- The two radius equations and the exact strict inequalities. -/
def RadiusCriterion (r₀ r₁ r₂ r₃ : ℚ) : Prop :=
  r₀ ^ 2 + r₃ ^ 2 = r₁ ^ 2 + r₂ ^ 2 ∧
  (1 + r₀ ^ 2 - r₁ ^ 2) ^ 2 + (1 + r₀ ^ 2 - r₂ ^ 2) ^ 2 = 4 * r₀ ^ 2 ∧
  -1 < r₀ ^ 2 - r₁ ^ 2 ∧ r₀ ^ 2 - r₁ ^ 2 < 1 ∧
  -1 < r₀ ^ 2 - r₂ ^ 2 ∧ r₀ ^ 2 - r₂ ^ 2 < 1

theorem recover_coordinates {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : FourSquares x y r₀ r₁ r₂ r₃) :
    2 * x = 1 + r₀ ^ 2 - r₁ ^ 2 ∧
    2 * y = 1 + r₀ ^ 2 - r₂ ^ 2 := by
  rcases h with ⟨h₀, h₁, h₂, h₃⟩
  constructor
  · linear_combination h₁ - h₀
  · linear_combination h₂ - h₀

theorem four_squares_unique {x y x' y' r₀ r₁ r₂ r₃ : ℚ}
    (h : FourSquares x y r₀ r₁ r₂ r₃)
    (h' : FourSquares x' y' r₀ r₁ r₂ r₃) : x = x' ∧ y = y' := by
  obtain ⟨hx, hy⟩ := recover_coordinates h
  obtain ⟨hx', hy'⟩ := recover_coordinates h'
  constructor <;> linarith

theorem strict_point_to_radius_criterion {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) : RadiusCriterion r₀ r₁ r₂ r₃ := by
  rcases h with ⟨hx₀, hx₁, hy₀, hy₁, hr₀, hr₁, hr₂, hr₃, hs⟩
  obtain ⟨hx, hy⟩ := recover_coordinates hs
  rcases hs with ⟨h₀, h₁, h₂, h₃⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h₀ + h₃ - h₁ - h₂
  · rw [← hx, ← hy]
    linear_combination -4 * h₀
  all_goals linarith

theorem radius_criterion_to_strict_point {r₀ r₁ r₂ r₃ : ℚ}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₃ : 0 < r₃)
    (h : RadiusCriterion r₀ r₁ r₂ r₃) :
    StrictPoint ((1 + r₀ ^ 2 - r₁ ^ 2) / 2)
      ((1 + r₀ ^ 2 - r₂ ^ 2) / 2) r₀ r₁ r₂ r₃ := by
  rcases h with ⟨hb, hq, hx₀, hx₁, hy₀, hy₁⟩
  refine ⟨?_, ?_, ?_, ?_, hr₀, hr₁, hr₂, hr₃, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-1 / 4 : ℚ) * hq
  · linear_combination (-1 / 4 : ℚ) * hq
  · linear_combination (-1 / 4 : ℚ) * hq
  · linear_combination hb - (1 / 4 : ℚ) * hq

/-- Three rational radii already force real coordinates to be rational. -/
theorem real_coordinates_rational {x y : ℝ} {r₀ r₁ r₂ : ℚ}
    (h₀ : (r₀ : ℝ) ^ 2 = x ^ 2 + y ^ 2)
    (h₁ : (r₁ : ℝ) ^ 2 = (1 - x) ^ 2 + y ^ 2)
    (h₂ : (r₂ : ℝ) ^ 2 = x ^ 2 + (1 - y) ^ 2) :
    ∃ u v : ℚ, (u : ℝ) = x ∧ (v : ℝ) = y := by
  have hx : 2 * x = 1 + (r₀ : ℝ) ^ 2 - (r₁ : ℝ) ^ 2 := by
    linear_combination h₁ - h₀
  have hy : 2 * y = 1 + (r₀ : ℝ) ^ 2 - (r₂ : ℝ) ^ 2 := by
    linear_combination h₂ - h₀
  refine ⟨(1 + r₀ ^ 2 - r₁ ^ 2) / 2, (1 + r₀ ^ 2 - r₂ ^ 2) / 2, ?_, ?_⟩
  · push_cast
    linarith
  · push_cast
    linarith

/-- Proposition prop:int:radius-model, including uniqueness and strictness. -/
theorem radius_model_iff_unique {r₀ r₁ r₂ r₃ : ℚ}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₃ : 0 < r₃) :
    (∃! p : ℚ × ℚ, StrictPoint p.1 p.2 r₀ r₁ r₂ r₃) ↔
      RadiusCriterion r₀ r₁ r₂ r₃ := by
  constructor
  · rintro ⟨p, hp, _⟩
    exact strict_point_to_radius_criterion hp
  · intro h
    let p : ℚ × ℚ := ((1 + r₀ ^ 2 - r₁ ^ 2) / 2, (1 + r₀ ^ 2 - r₂ ^ 2) / 2)
    have hp : StrictPoint p.1 p.2 r₀ r₁ r₂ r₃ :=
      radius_criterion_to_strict_point hr₀ hr₁ hr₂ hr₃ h
    refine ⟨p, hp, ?_⟩
    intro q hq
    apply Prod.ext
    · exact (four_squares_unique hq.2.2.2.2.2.2.2.2 hp.2.2.2.2.2.2.2.2).1
    · exact (four_squares_unique hq.2.2.2.2.2.2.2.2 hp.2.2.2.2.2.2.2.2).2

#print axioms real_coordinates_rational
#print axioms recover_coordinates
#print axioms four_squares_unique
#print axioms strict_point_to_radius_criterion
#print axioms radius_criterion_to_strict_point
#print axioms radius_model_iff_unique
end FourCorner
