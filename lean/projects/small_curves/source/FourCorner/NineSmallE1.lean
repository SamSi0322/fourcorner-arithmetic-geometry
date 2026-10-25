import FourCorner.SquareArea
import FourCorner.NineFlexGroup

set_option autoImplicit false
namespace FourCorner

/-- A nonzero ordinate on E1 would yield a positive rational right triangle
of area one, contradicting the proved square-area infinite descent. -/
theorem small_E1_affine_points {x y : ℚ} (h : y^2=x^3-x) :
    y=0 ∧ (x=0 ∨ x=1 ∨ x= -1) := by
  have hy : y=0 := by
    by_contra hy
    have hx : x≠0 := by
      intro hx
      rw [hx] at h
      norm_num at h
      exact hy h
    have hxx : x^2-1≠0 := by
      intro hxx
      have hyy : y^2=0 := by linear_combination h + x*hxx
      exact hy (sq_eq_zero_iff.mp hyy)
    have ha : 0 < |(x^2-1)/y| := abs_pos.mpr (div_ne_zero hxx hy)
    have hb : 0 < |2*x/y| := abs_pos.mpr (div_ne_zero (mul_ne_zero (by norm_num) hx) hy)
    have ht : |(x^2-1)/y|^2+|2*x/y|^2=((x^2+1)/y)^2 := by
      rw [sq_abs,sq_abs]
      field_simp
      ring
    have hab : ((x^2-1)/y)*(2*x/y)=2 := by
      field_simp
      nlinarith only [h]
    have harea : |(x^2-1)/y| * |2*x/y|/2=(1:ℚ)^2 := by
      rw [← abs_mul,hab]
      norm_num
    exact rational_right_triangle_not_square_area ha hb (by norm_num : (0:ℚ)<1) ht harea
  refine ⟨hy,?_⟩
  have hz : x*(x-1)*(x+1)=0 := by rw [hy] at h; nlinarith [h]
  rcases mul_eq_zero.mp hz with hz|hz
  · rcases mul_eq_zero.mp hz with hz|hz
    · exact Or.inl hz
    · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

/-- Complete affine classification, with the converse for every listed point. -/
theorem small_E1_affine_iff (x y : ℚ) :
    y^2=x^3-x ↔ y=0 ∧ (x=0 ∨ x=1 ∨ x= -1) := by
  constructor
  · exact small_E1_affine_points
  · rintro ⟨rfl,rfl|rfl|rfl⟩ <;> norm_num

/-- Each listed root is a nonsingular point of the actual curve. -/
theorem small_E1_root_nonsingular {x : ℚ} (hx : x=0 ∨ x=1 ∨ x= -1) :
    (splitCurve 1 (-1)).toAffine.Nonsingular x 0 := by
  rcases hx with rfl|rfl|rfl <;>
    norm_num [WeierstrassCurve.Affine.nonsingular_iff',
      WeierstrassCurve.Affine.equation_iff,splitCurve]

def smallE1ZeroRoot : (splitCurve 1 (-1)).toAffine.Point :=
  .some 0 0 (small_E1_root_nonsingular (Or.inl rfl))
def smallE1PositiveRoot : (splitCurve 1 (-1)).toAffine.Point :=
  .some 1 0 (small_E1_root_nonsingular (Or.inr (Or.inl rfl)))
def smallE1NegativeRoot : (splitCurve 1 (-1)).toAffine.Point :=
  .some (-1) 0 (small_E1_root_nonsingular (Or.inr (Or.inr rfl)))

/-- The actual rational point group of E1 consists of exactly the four
listed points; the identity is the proper point at infinity. -/
theorem small_E1_point_list (P : (splitCurve 1 (-1)).toAffine.Point) :
    P=0 ∨ P=smallE1ZeroRoot ∨ P=smallE1PositiveRoot ∨ P=smallE1NegativeRoot := by
  cases P with
  | zero => exact Or.inl rfl
  | some x y hxy =>
    have heq := (splitCurve_equation_iff 1 (-1) x y).mp hxy.1
    have hpoly : y^2=x^3-x := by nlinarith [heq]
    obtain ⟨rfl,hx⟩ := small_E1_affine_points hpoly
    rcases hx with rfl|rfl|rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

/-- Every rational point of E1 is killed by two. -/
theorem small_E1_two_torsion (P : (splitCurve 1 (-1)).toAffine.Point) : 2 • P=0 := by
  cases P with
  | zero => change 2 • (0 : (splitCurve 1 (-1)).toAffine.Point) = 0; simp
  | some x y hxy =>
    have heq := (splitCurve_equation_iff 1 (-1) x y).mp hxy.1
    have hy := (small_E1_affine_points (show y^2=x^3-x by nlinarith [heq])).1
    rw [two_nsmul]
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    simp [splitCurve,WeierstrassCurve.Affine.negY,hy]

end FourCorner
#print axioms FourCorner.small_E1_affine_iff
#print axioms FourCorner.small_E1_point_list
#print axioms FourCorner.small_E1_two_torsion
