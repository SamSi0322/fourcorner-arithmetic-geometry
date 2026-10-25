import FourCorner.PureSource
import FourCorner.DiagonalBounds

namespace FourCorner

/-- The complete polynomial identities in the four diagonal sums and differences. -/
theorem fourSquares_diagonal_identities {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : FourSquares x y r₀ r₁ r₂ r₃) :
    (r₀ + r₃) * (r₀ - r₃) = 2 * (x + y - 1) ∧
    (r₁ + r₂) * (r₂ - r₁) = 2 * (x - y) ∧
    (r₀ + r₃)^2 + (r₀ - r₃)^2 = (r₁ + r₂)^2 + (r₂ - r₁)^2 ∧
    ((r₀ + r₃)^2 - 2) * (2 - (r₀ - r₃)^2) =
      (r₁ + r₂)^2 * (r₂ - r₁)^2 := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := h
  have hsd : (r₀ + r₃) * (r₀ - r₃) = 2 * (x + y - 1) := by
    linear_combination h₀ - h₃
  have hte : (r₁ + r₂) * (r₂ - r₁) = 2 * (x - y) := by
    linear_combination h₂ - h₁
  refine ⟨hsd, hte, ?_, ?_⟩
  · linear_combination 2 * (h₀ + h₃ - h₁ - h₂)
  · have hn : ((r₀ + r₃)^2 - 2) * (2 - (r₀ - r₃)^2) -
        (r₁ + r₂)^2 * (r₂ - r₁)^2 =
        4 * (r₀^2 + r₃^2) - 4 -
        ((r₀ + r₃) * (r₀ - r₃))^2 - ((r₁ + r₂) * (r₂ - r₁))^2 := by ring
    rw [hsd, hte] at hn
    have hz : 4 * (r₀^2 + r₃^2) - 4 -
        (2 * (x + y - 1))^2 - (2 * (x - y))^2 = 0 := by
      linear_combination 4 * h₀ + 4 * h₃
    rw [hz] at hn
    exact sub_eq_zero.mp hn

/-- Algebraic change from the diagonal model to the four simultaneous squares. -/
theorem diagonal_to_pure_equations {s d τ e : ℚ}
    (hd : d ≠ 0) (he : 2 - e^2 ≠ 0)
    (hA : s^2 + d^2 = τ^2 + e^2)
    (hB : (s^2 - 2) * (2 - d^2) = τ^2 * e^2) :
    (s / d)^2 = ((2 - e^2) / d^2) * (s^2 / (2 - e^2)) ∧
    (2 * e / d)^2 = 2 * ((2 - e^2) / d^2 - 1) * (s^2 / (2 - e^2) - 1) ∧
    (2 * τ / d)^2 = 2 * ((2 - e^2) / d^2 + 1) * (s^2 / (2 - e^2) + 1) ∧
    (2 / d)^2 = ((2 - e^2) / d^2 - 1) * (s^2 / (2 - e^2)) +
      (2 - e^2) / d^2 + 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp
  · field_simp
    linear_combination -(hB - e^2 * hA)
  · field_simp
    linear_combination (hB - (4 - e^2) * hA)
  · field_simp
    linear_combination -(hB - e^2 * hA)

/-- The signs, strict metric and diagonal equations imply all pure-source conditions. -/
theorem diagonal_to_pure_coordinates {s d τ e : ℚ}
    (hs : 0 < s) (hd : 0 < d) (ht : 0 < τ) (he : 0 < e)
    (hs2 : 2 ≤ s^2) (hde : d^2 + e^2 < 2)
    (hA : s^2 + d^2 = τ^2 + e^2)
    (hB : (s^2 - 2) * (2 - d^2) = τ^2 * e^2)
    (hm : s*d + τ*e < 2) :
    PureCoordinates ((2-e^2)/d^2) (s^2/(2-e^2))
      (s/d) (2*e/d) (2*τ/d) (2/d) := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hden : 0 < 2 - e^2 := by nlinarith [sq_nonneg d]
  have he0 : 2 - e^2 ≠ 0 := ne_of_gt hden
  have hdsq : 0 < d^2 := sq_pos_of_pos hd
  obtain ⟨hU,hV,hW,hT⟩ := diagonal_to_pure_equations hd0 he0 hA hB
  refine ⟨?_, ?_, div_pos hs hd, div_pos (mul_pos (by norm_num) he) hd,
    div_pos (mul_pos (by norm_num) ht) hd, div_pos (by norm_num) hd,
    hU,hV,hW,hT, ?_⟩
  · apply (one_lt_div hdsq).mpr
    linarith
  · apply (one_lt_div hden).mpr
    nlinarith [sq_pos_of_pos he]
  · have hn : (4 * (s/d) + (2*τ/d)*(2*e/d)) / (2/d)^2 = s*d + τ*e := by
      field_simp
      ring
    rwa [hn]

/-- A strict point in the diagonal chamber determines the complete pure source. -/
theorem strictPoint_pureCoordinates {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃)
    (hsum : 1 < x+y) (hdiff : y<x) :
    PureCoordinates (radiusPureP r₀ r₁ r₂ r₃) (radiusPureBeta r₀ r₁ r₂ r₃)
      (radiusPureU r₀ r₃) (radiusPureV r₀ r₁ r₂ r₃)
      (radiusPureW r₀ r₁ r₂ r₃) (radiusPureT r₀ r₃) := by
  obtain ⟨hd,he,hs,ht,hs2,ht2,hbd,hlt⟩ := strict_point_diagonal_bounds h hsum hdiff
  obtain ⟨hsd,hte,hA,hB⟩ := fourSquares_diagonal_identities h.2.2.2.2.2.2.2.2
  unfold radiusPureP radiusPureBeta radiusPureU radiusPureV radiusPureW radiusPureT
  apply diagonal_to_pure_coordinates hs hd ht he hs2 (lt_of_le_of_lt hbd hlt) hA hB
  rw [hsd,hte]
  linarith [h.2.1]

/-- The diagonal coordinate change returns every labelled radius exactly. -/
theorem radiusPure_recover_radii {r₀ r₁ r₂ r₃ : ℚ} (hd : r₀ - r₃ ≠ 0) :
    pureR0 (radiusPureU r₀ r₃) (radiusPureT r₀ r₃) = r₀ ∧
    pureR1 (radiusPureV r₀ r₁ r₂ r₃) (radiusPureW r₀ r₁ r₂ r₃)
      (radiusPureT r₀ r₃) = r₁ ∧
    pureR2 (radiusPureV r₀ r₁ r₂ r₃) (radiusPureW r₀ r₁ r₂ r₃)
      (radiusPureT r₀ r₃) = r₂ ∧
    pureR3 (radiusPureU r₀ r₃) (radiusPureT r₀ r₃) = r₃ := by
  unfold pureR0 pureR1 pureR2 pureR3 radiusPureU radiusPureV radiusPureW radiusPureT
  constructor
  · field_simp
    ring
  constructor
  · field_simp
    ring
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- The diagonal change returns the original point as well as all four radii. -/
theorem radiusPure_recover_coordinates {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : FourSquares x y r₀ r₁ r₂ r₃) (hd : r₀ - r₃ ≠ 0) :
    pureX (radiusPureU r₀ r₃) (radiusPureV r₀ r₁ r₂ r₃)
      (radiusPureW r₀ r₁ r₂ r₃) (radiusPureT r₀ r₃) = x ∧
    pureY (radiusPureU r₀ r₃) (radiusPureV r₀ r₁ r₂ r₃)
      (radiusPureW r₀ r₁ r₂ r₃) (radiusPureT r₀ r₃) = y := by
  obtain ⟨hsd,hte,hA,hB⟩ := fourSquares_diagonal_identities h
  have hx : (r₀+r₃)*(r₀-r₃)+(r₁+r₂)*(r₂-r₁)=4*x-2 := by linarith
  have hy : (r₀+r₃)*(r₀-r₃)-(r₁+r₂)*(r₂-r₁)=4*y-2 := by linarith
  unfold pureX pureY radiusPureU radiusPureV radiusPureW radiusPureT
  constructor
  · field_simp
    nlinarith only [hx]
  · field_simp
    nlinarith only [hy]

#print axioms fourSquares_diagonal_identities
#print axioms diagonal_to_pure_equations
#print axioms diagonal_to_pure_coordinates
#print axioms strictPoint_pureCoordinates
#print axioms radiusPure_recover_radii
#print axioms radiusPure_recover_coordinates
end FourCorner
