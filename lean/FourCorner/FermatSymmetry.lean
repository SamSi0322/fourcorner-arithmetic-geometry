import FourCorner.RadiusModel
import FourCorner.SquareArea
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace FourCorner

/-- The rational number 2 is not a square. -/
theorem rational_sq_ne_two (q : ℚ) : q ^ 2 ≠ 2 := by
  intro h
  have hs : IsSquare (2 : ℚ) := ⟨q, by nlinarith⟩
  have hn : IsSquare (2 : ℕ) := Rat.isSquare_natCast_iff.mp hs
  obtain ⟨n, hn⟩ := hn
  have hn1 : n ≤ 1 := by nlinarith
  have hn01 : n = 0 ∨ n = 1 := by omega
  rcases hn01 with rfl | rfl <;> norm_num at hn

/-- The coordinate diagonal does not contain a strict rational-distance point. -/
theorem strict_point_not_diagonal {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) : x ≠ y := by
  intro hxy
  rcases h with ⟨hx, _, _, _, _, _, _, _, h₀, _, _, _⟩
  have hx0 : x ≠ 0 := ne_of_gt hx
  apply rational_sq_ne_two (r₀ / x)
  field_simp
  nlinarith [hxy]

/-- The other diagonal does not contain a strict rational-distance point. -/
theorem strict_point_not_antidiagonal {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) : x + y ≠ 1 := by
  intro hxy
  rcases h with ⟨_, hx, hy, _, _, _, _, _, _, h₁, _, _⟩
  have hy0 : y ≠ 0 := ne_of_gt hy
  apply rational_sq_ne_two (r₁ / y)
  field_simp
  nlinarith [hxy]

/-- Exchange the two coordinates and the two adjacent corner labels. -/
theorem strict_point_exchange {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) :
    StrictPoint y x r₀ r₂ r₁ r₃ := by
  rcases h with ⟨hx₀, hx₁, hy₀, hy₁, hr₀, hr₁, hr₂, hr₃, h₀, h₁, h₂, h₃⟩
  refine ⟨hy₀, hy₁, hx₀, hx₁, hr₀, hr₂, hr₁, hr₃, ?_, ?_, ?_, ?_⟩
  all_goals nlinarith

/-- A midpoint-line pair of rational distances produces a square-area triangle.
This helper isolates the geometric reduction from the independent descent. -/
theorem midline_reduces_to_square_area {x r₀ r₁ : ℚ}
    (h₀ : r₀ ^ 2 = x ^ 2 + (1 / 2 : ℚ) ^ 2)
    (h₁ : r₁ ^ 2 = (1 - x) ^ 2 + (1 / 2 : ℚ) ^ 2) :
    ∃ a b c k : ℚ, 0 < a ∧ 0 < b ∧ 0 < k ∧
      a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b / 2 = k ^ 2 := by
  let u : ℚ := 2 * x - 1
  let p : ℚ := 2 * r₀
  let q : ℚ := 2 * r₁
  have hp : p ^ 2 = u ^ 2 + 2 * u + 2 := by
    dsimp [u, p]
    nlinarith
  have hq : q ^ 2 = u ^ 2 - 2 * u + 2 := by
    dsimp [u, q]
    nlinarith
  have hu : u ≠ 0 := by
    intro hu
    apply rational_sq_ne_two p
    rw [hu] at hp
    norm_num at hp ⊢
    exact hp
  have hpq : (p * q) ^ 2 = u ^ 4 + 4 := by
    calc
      (p * q) ^ 2 = p ^ 2 * q ^ 2 := by ring
      _ = (u ^ 2 + 2 * u + 2) * (u ^ 2 - 2 * u + 2) := by rw [hp, hq]
      _ = u ^ 4 + 4 := by ring
  refine ⟨u ^ 2, 2, p * q, |u|, sq_pos_of_ne_zero hu, by norm_num,
    abs_pos.mpr hu, ?_, ?_⟩
  · rw [hpq]
    ring
  · rw [sq_abs]
    ring

/-- Neither half-height line can support rational distances to its endpoints. -/
theorem strict_point_not_horizontal_midline {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) : y ≠ 1 / 2 := by
  intro hy
  rcases h with ⟨_, _, _, _, _, _, _, _, h₀, h₁, _, _⟩
  rw [hy] at h₀ h₁
  obtain ⟨a, b, c, k, ha, hb, hk, ht, hs⟩ := midline_reduces_to_square_area h₀ h₁
  exact rational_right_triangle_not_square_area ha hb hk ht hs

/-- Neither half-width line can support a strict rational-distance point. -/
theorem strict_point_not_vertical_midline {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) : x ≠ 1 / 2 :=
  strict_point_not_horizontal_midline (strict_point_exchange h)

/-- The six inequalities retain the four original corner labels. -/
theorem strict_point_six_radius_inequalities {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) :
    r₀ ≠ r₁ ∧ r₀ ≠ r₂ ∧ r₀ ≠ r₃ ∧ r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₂ ≠ r₃ := by
  have hx := strict_point_not_vertical_midline h
  have hy := strict_point_not_horizontal_midline h
  have hd := strict_point_not_diagonal h
  have ha := strict_point_not_antidiagonal h
  rcases h with ⟨_, _, _, _, _, _, _, _, h₀, h₁, h₂, h₃⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro he
    apply hx
    nlinarith
  · intro he
    apply hy
    nlinarith
  · intro he
    apply ha
    nlinarith
  · intro he
    apply hd
    nlinarith
  · intro he
    apply hy
    nlinarith
  · intro he
    apply hx
    nlinarith

/-- Lemma lem:int:symmetry: exclusion of all four symmetry lines together
with pairwise distinctness of the four positive rational radii. -/
theorem strict_point_symmetry {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) :
    x ≠ 1 / 2 ∧ y ≠ 1 / 2 ∧ x ≠ y ∧ x + y ≠ 1 ∧
      List.Pairwise (· ≠ ·) [r₀, r₁, r₂, r₃] := by
  refine ⟨strict_point_not_vertical_midline h, strict_point_not_horizontal_midline h,
    strict_point_not_diagonal h, strict_point_not_antidiagonal h, ?_⟩
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := strict_point_six_radius_inequalities h
  simp [List.pairwise_cons, h01, h02, h03, h12, h13, h23]

end FourCorner
#print axioms FourCorner.rational_sq_ne_two
#print axioms FourCorner.strict_point_not_diagonal
#print axioms FourCorner.strict_point_not_antidiagonal

#print axioms FourCorner.midline_reduces_to_square_area
#print axioms FourCorner.strict_point_not_horizontal_midline
#print axioms FourCorner.strict_point_not_vertical_midline
#print axioms FourCorner.strict_point_six_radius_inequalities
#print axioms FourCorner.strict_point_symmetry
