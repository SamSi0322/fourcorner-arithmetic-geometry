import FourCorner.NineSmallE1
import FourCorner.NineSmallE2
import SmallAComplete
import E0Complete

set_option autoImplicit false
namespace FourCorner

/-- The four complete rational affine point classifications in
manuscript lem:nine-small-curves, with both directions of each list. -/
theorem nine_small_curves_affine :
    (∀ x y : ℚ, y^2=x^3-x ↔ y=0 ∧ (x=0 ∨ x=1 ∨ x= -1)) ∧
    (∀ x y : ℚ, y^2=x^3-4*x ↔ y=0 ∧ (x=0 ∨ x=2 ∨ x= -2)) ∧
    (∀ x y : ℚ, y^2=x*(x-6)*(x-8) ↔ y=0 ∧ (x=0 ∨ x=6 ∨ x=8)) ∧
    (∀ x y : ℚ, y^2=x*(x+1)*(x+4) ↔
      (x=0 ∧ y=0) ∨ (x= -1 ∧ y=0) ∨ (x= -4 ∧ y=0) ∨
      (x=2 ∧ (y=6 ∨ y= -6)) ∨ (x= -2 ∧ (y=2 ∨ y= -2))) :=
  ⟨small_E1_affine_iff,small_E2_affine_iff,
    NineSmallA.complete_affine_iff,NineSmallE0.rational_point_iff⟩

/-- Manuscript lem:nine-small-curves on the actual four rational elliptic
point groups. Each list includes the genuine identity at infinity, and every
listed finite point has its equation and nonsingularity proved at construction. -/
theorem nine_small_curves_complete :
    (∀ P : (splitCurve 1 (-1)).toAffine.Point,
      P=0 ∨ P=smallE1ZeroRoot ∨ P=smallE1PositiveRoot ∨ P=smallE1NegativeRoot) ∧
    (∀ P : (splitCurve 2 (-2)).toAffine.Point,
      P=0 ∨ P=smallE2ZeroRoot ∨ P=smallE2PositiveRoot ∨ P=smallE2NegativeRoot) ∧
    (∀ P : (splitCurve 6 8).toAffine.Point,
      P=0 ∨ P=smallAZeroRoot ∨ P=smallASixRoot ∨ P=smallAEightRoot) ∧
    (∀ P : (splitCurve (-1) (-4)).toAffine.Point,
      P ∈ NineSmallE0.listed) :=
  ⟨small_E1_point_list,small_E2_point_list,
    NineSmallA.complete_point_list,NineSmallE0.complete_point_group⟩

end FourCorner

#check FourCorner.nine_small_curves_affine
#check FourCorner.nine_small_curves_complete
#print axioms FourCorner.nine_small_curves_affine
#print axioms FourCorner.nine_small_curves_complete
