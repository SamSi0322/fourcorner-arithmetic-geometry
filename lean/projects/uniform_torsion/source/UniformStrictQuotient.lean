import UniformTorsion
import UniformRankZero
import UniformStrictInterval
import FourCorner.PurePointEquiv

namespace FourCorner.UniformTorsion

def strictP (nu : ℤ) (eps r₀ r₃ : ℚ) : ℚ := (nu:ℚ)*(r₃-eps*r₀)
def strictQ (nu : ℤ) (r₁ : ℚ) : ℚ := 2*(nu:ℚ)*r₁
def strictR (nu : ℤ) (r₂ : ℚ) : ℚ := 2*(nu:ℚ)*r₂

/-- A polynomial consequence of the original four same-point identities. -/
theorem opposite_fourth_identity {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : FourSquares x y r₀ r₁ r₂ r₃) :
    16*r₁^2*r₂^2=8*(r₀^2)^2+8*(r₃^2)^2-16*(r₀^2+r₃^2)+16 := by
  obtain ⟨h0,h1,h2,h3⟩ := h
  rw [h0,h1,h2,h3]
  ring

/-- The quotient point lies on the literal family equation; all four radii
are from the original same point, and both opposite-pair signs are included. -/
theorem strict_quotient_equation {x y r₀ r₁ r₂ r₃ eps : ℚ} {mu nu : ℤ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) (heps : eps=1 ∨ eps= -1)
    (hmu : (mu:ℚ)=(nu:ℚ)*(r₃+eps*r₀)) :
    (curve mu nu).toAffine.Equation ((strictP nu eps r₀ r₃)^2)
      (strictP nu eps r₀ r₃ * strictQ nu r₁ * strictR nu r₂) := by
  rw [curve_equation_iff]
  have hi := opposite_fourth_identity h.2.2.2.2.2.2.2.2
  simp only [strictP, strictQ, strictR, alpha, B, Int.cast_mul, Int.cast_sub,
    Int.cast_pow, Int.cast_ofNat]
  rw [hmu]
  rcases heps with rfl | rfl
  · linear_combination (nu:ℚ)^6*(r₃-r₀)^2*hi
  · linear_combination (nu:ℚ)^6*(r₃+r₀)^2*hi

/-- The literal quotient's abscissa has the strict interval required to
exclude all four actual rational torsion points. -/
theorem strict_quotient_interval {x y r₀ r₁ r₂ r₃ eps : ℚ} {mu nu : ℤ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) (hnu : 0<nu)
    (heps : eps=1 ∨ eps= -1) (hmu : (mu:ℚ)=(nu:ℚ)*(r₃+eps*r₀)) :
    0<((strictP nu eps r₀ r₃)^2) ∧ ((strictP nu eps r₀ r₃)^2)<(B mu nu:ℚ) :=
  strict_point_integer_pair_parameter_interval h hnu heps hmu

/-- The actual quotient is nonsingular, by ellipticity of the odd-parameter family. -/
theorem strict_quotient_nonsingular {x y r₀ r₁ r₂ r₃ eps : ℚ} {mu nu : ℤ}
    (hm : Odd mu) (hn : Odd nu) (h : StrictPoint x y r₀ r₁ r₂ r₃)
    (heps : eps=1 ∨ eps= -1) (hmu : (mu:ℚ)=(nu:ℚ)*(r₃+eps*r₀)) :
    (curve mu nu).toAffine.Nonsingular ((strictP nu eps r₀ r₃)^2)
      (strictP nu eps r₀ r₃ * strictQ nu r₁ * strictR nu r₂) := by
  letI := curve_isElliptic hm hn
  exact WeierstrassCurve.Affine.equation_iff_nonsingular.mp (strict_quotient_equation h heps hmu)

/-- The actual rational group point attached to the complete strict source. -/
def strictQuotientPoint {x y r₀ r₁ r₂ r₃ eps : ℚ} {mu nu : ℤ}
    (hm : Odd mu) (hn : Odd nu) (h : StrictPoint x y r₀ r₁ r₂ r₃)
    (heps : eps=1 ∨ eps= -1) (hmu : (mu:ℚ)=(nu:ℚ)*(r₃+eps*r₀)) :
    (curve mu nu).toAffine.Point :=
  .some ((strictP nu eps r₀ r₃)^2)
    (strictP nu eps r₀ r₃ * strictQ nu r₁ * strictR nu r₂)
    (strict_quotient_nonsingular hm hn h heps hmu)

/-- The second sentence of thm:ell-torsion, beginning with the literal strict
four-corner point rather than a presumed elliptic point in an interval. -/
theorem strict_quotient_infinite_order {x y r₀ r₁ r₂ r₃ eps : ℚ} {mu nu : ℤ}
    (hm : Odd mu) (hn : Odd nu) (hnu : 0<nu)
    (h : StrictPoint x y r₀ r₁ r₂ r₃) (heps : eps=1 ∨ eps= -1)
    (hmu : (mu:ℚ)=(nu:ℚ)*(r₃+eps*r₀)) :
    ¬ IsOfFinAddOrder (strictQuotientPoint hm hn h heps hmu) := by
  obtain ⟨hlo,hhi⟩ := strict_quotient_interval h hnu heps hmu
  exact point_between_nontorsion hm hn (strict_quotient_nonsingular hm hn h heps hmu) hlo hhi

/-- Positive quotient notation is converted to the exact source relation. -/
theorem strict_quotient_infinite_order_of_pair_value
    {x y r₀ r₁ r₂ r₃ eps : ℚ} {mu nu : ℤ}
    (hm : Odd mu) (hn : Odd nu) (hnu : 0<nu)
    (h : StrictPoint x y r₀ r₁ r₂ r₃) (heps : eps=1 ∨ eps= -1)
    (hvalue : r₃+eps*r₀=(mu:ℚ)/(nu:ℚ)) :
    ∃ hN : (curve mu nu).toAffine.Nonsingular ((strictP nu eps r₀ r₃)^2)
      (strictP nu eps r₀ r₃ * strictQ nu r₁ * strictR nu r₂),
      ¬ IsOfFinAddOrder (WeierstrassCurve.Affine.Point.some ((strictP nu eps r₀ r₃)^2)
        (strictP nu eps r₀ r₃ * strictQ nu r₁ * strictR nu r₂) hN) := by
  have hnq : (nu:ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hnu)
  have he : (mu:ℚ)=(nu:ℚ)*(r₃+eps*r₀) := by rw [hvalue]; field_simp
  exact ⟨strict_quotient_nonsingular hm hn h heps he,
    strict_quotient_infinite_order hm hn hnu h heps he⟩

/-- Rank zero excludes both signed opposite-pair values on the actual strict square. -/
theorem rank_zero_excludes_signed_opposite_pair
    {x y r₀ r₁ r₂ r₃ eps : ℚ} {mu nu : ℤ}
    (hm : Odd mu) (hn : Odd nu) (hnu : 0<nu)
    (hRank : Module.finrank ℤ (curve mu nu).toAffine.Point=0)
    (h : StrictPoint x y r₀ r₁ r₂ r₃) (heps : eps=1 ∨ eps= -1) :
    r₃+eps*r₀ ≠ (mu:ℚ)/(nu:ℚ) := by
  intro hvalue
  have hnq : (nu:ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hnu)
  have he : (mu:ℚ)=(nu:ℚ)*(r₃+eps*r₀) := by rw [hvalue]; field_simp
  obtain ⟨hlo,hhi⟩ := strict_quotient_interval h hnu heps he
  apply rank_zero_no_equation_between hm hn hRank
  exact ⟨_, _, strict_quotient_equation h heps he, hlo, hhi⟩

/-- Opposite sums and absolute differences have an actual signed source,
using only the square's central rotation when the difference has the other sign. -/
theorem strict_opposite_value_yields_nontorsion
    {x y r₀ r₁ r₂ r₃ : ℚ} {mu nu : ℤ}
    (hm : Odd mu) (hn : Odd nu) (hnu : 0<nu)
    (h : StrictPoint x y r₀ r₁ r₂ r₃)
    (hvalue : r₀+r₃=(mu:ℚ)/(nu:ℚ) ∨ |r₀-r₃|=(mu:ℚ)/(nu:ℚ)) :
    ∃ P : (curve mu nu).toAffine.Point, ¬ IsOfFinAddOrder P := by
  rcases hvalue with hsum | hdiff
  · have he : r₃+(1:ℚ)*r₀=(mu:ℚ)/(nu:ℚ) := by simpa only [one_mul, add_comm] using hsum
    obtain ⟨hN,hord⟩ := strict_quotient_infinite_order_of_pair_value hm hn hnu h (Or.inl rfl) he
    exact ⟨_,hord⟩
  · rcases le_total r₀ r₃ with hle | hle
    · have he : r₃+(-1:ℚ)*r₀=(mu:ℚ)/(nu:ℚ) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hdiff
        linarith only [hdiff]
      obtain ⟨hN,hord⟩ := strict_quotient_infinite_order_of_pair_value hm hn hnu h (Or.inr rfl) he
      exact ⟨_,hord⟩
    · have he : r₀+(-1:ℚ)*r₃=(mu:ℚ)/(nu:ℚ) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hle)] at hdiff
        linarith only [hdiff]
      obtain ⟨hN,hord⟩ := strict_quotient_infinite_order_of_pair_value hm hn hnu
        (strictPoint_centralRotation h) (Or.inr rfl) he
      exact ⟨_,hord⟩

/-- Reflection interchanges the two opposite vertex pairs with their actual roots. -/
theorem strict_point_reflect_first_coordinate {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) : StrictPoint (1-x) y r₁ r₀ r₃ r₂ := by
  rcases h with ⟨hx0,hx1,hy0,hy1,h0,h1,h2,h3,hs0,hs1,hs2,hs3⟩
  refine ⟨by linarith, by linarith, hy0, hy1, h1,h0,h3,h2,?_,?_,?_,?_⟩
  all_goals nlinarith only [hs0,hs1,hs2,hs3]

/-- Both opposite vertex pairs, with either a sum or an absolute difference,
produce an actual point of infinite order on the stated odd-parameter curve. -/
theorem strict_any_opposite_value_yields_nontorsion
    {x y r₀ r₁ r₂ r₃ : ℚ} {mu nu : ℤ}
    (hm : Odd mu) (hn : Odd nu) (hnu : 0<nu)
    (h : StrictPoint x y r₀ r₁ r₂ r₃)
    (hvalue : r₀+r₃=(mu:ℚ)/(nu:ℚ) ∨ |r₀-r₃|=(mu:ℚ)/(nu:ℚ) ∨
      r₁+r₂=(mu:ℚ)/(nu:ℚ) ∨ |r₁-r₂|=(mu:ℚ)/(nu:ℚ)) :
    ∃ P : (curve mu nu).toAffine.Point, ¬ IsOfFinAddOrder P := by
  rcases hvalue with h0 | h1 | h2 | h3
  · exact strict_opposite_value_yields_nontorsion hm hn hnu h (Or.inl h0)
  · exact strict_opposite_value_yields_nontorsion hm hn hnu h (Or.inr h1)
  · exact strict_opposite_value_yields_nontorsion hm hn hnu
      (strict_point_reflect_first_coordinate h) (Or.inl h2)
  · exact strict_opposite_value_yields_nontorsion hm hn hnu
      (strict_point_reflect_first_coordinate h) (Or.inr h3)

/-- Corollary cor:ell-rank-zero, including both opposite pairs and both absolute
orientations. The rank is the integer-module rank of the actual rational group. -/
theorem rank_zero_excludes_all_opposite_values
    {x y r₀ r₁ r₂ r₃ : ℚ} {mu nu : ℤ}
    (hm : Odd mu) (hn : Odd nu) (hnu : 0<nu)
    (hRank : Module.finrank ℤ (curve mu nu).toAffine.Point=0)
    (h : StrictPoint x y r₀ r₁ r₂ r₃) :
    r₀+r₃≠(mu:ℚ)/(nu:ℚ) ∧ |r₀-r₃|≠(mu:ℚ)/(nu:ℚ) ∧
      r₁+r₂≠(mu:ℚ)/(nu:ℚ) ∧ |r₁-r₂|≠(mu:ℚ)/(nu:ℚ) := by
  have hnot : ¬ (r₀+r₃=(mu:ℚ)/(nu:ℚ) ∨ |r₀-r₃|=(mu:ℚ)/(nu:ℚ) ∨
      r₁+r₂=(mu:ℚ)/(nu:ℚ) ∨ |r₁-r₂|=(mu:ℚ)/(nu:ℚ)) := by
    intro hv
    obtain ⟨P,hP⟩ := strict_any_opposite_value_yields_nontorsion hm hn hnu h hv
    letI := curve_isElliptic hm hn
    exact hP (numberField_isOfFinAddOrder_of_finrank_zero (curve mu nu).toAffine hRank P)
  simpa only [not_or] using hnot

#print axioms strict_any_opposite_value_yields_nontorsion
#print axioms rank_zero_excludes_all_opposite_values
#print axioms strict_quotient_equation
#print axioms strict_quotient_interval
#print axioms strict_quotient_nonsingular
#print axioms strict_quotient_infinite_order
#print axioms strict_quotient_infinite_order_of_pair_value
#print axioms rank_zero_excludes_signed_opposite_pair
end FourCorner.UniformTorsion
