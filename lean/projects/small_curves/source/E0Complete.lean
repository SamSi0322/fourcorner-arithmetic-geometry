import E0KummerImage
import ActualKummerFinite
import SmallTorsionBounds

namespace FourCorner.NineSmallE0
open FourCorner.OrderedSplit

local instance curve_elliptic_complete : Curve.IsElliptic :=
  splitCurve_isElliptic (-1) (-4) (by norm_num) (by norm_num) (by norm_num)

/-- Finiteness follows from actual Mordell--Weil, the actual doubling kernel,
and the proved four-row bound on every rational point. -/
theorem finite_point_group : Finite Curve.Point :=
  FGKummer.finite_points_of_ordered_image
    (splitRoots (-1) (-4))
    (splitRoots_injective (-1) (-4) (by norm_num) (by norm_num) (by norm_num))
    (splitCurve_f_factorization (-1) (-4)) rows delta_mem rows_card_le

theorem all_points_torsion (P : Curve.Point) : IsOfFinAddOrder P := by
  let _ := finite_point_group
  exact isOfFinAddOrder_of_finite P

theorem card_point_group_le_eight : Nat.card Curve.Point ≤ 8 :=
  SmallReduction.smallE0_card_le_eight_of_all_torsion all_points_torsion

/-- The eight listed points are the entire actual rational elliptic group. -/
theorem complete_point_group (P : Curve.Point) : P ∈ listed := by
  let _ := finite_point_group
  exact mem_listed_of_card_le card_point_group_le_eight P

/-- Complete rational affine-point classification, with no rank or local
certificate hypothesis. -/
theorem complete_rational_points {x y : ℚ} (h : y^2=x*(x+1)*(x+4)) :
    (x=0 ∧ y=0) ∨ (x= -1 ∧ y=0) ∨ (x= -4 ∧ y=0) ∨
    (x=2 ∧ (y=6 ∨ y= -6)) ∨ (x= -2 ∧ (y=2 ∨ y= -2)) := by
  let _ := finite_point_group
  exact coordinates_of_card_le card_point_group_le_eight h

theorem rational_point_iff (x y : ℚ) :
    y^2=x*(x+1)*(x+4) ↔
    (x=0 ∧ y=0) ∨ (x= -1 ∧ y=0) ∨ (x= -4 ∧ y=0) ∨
    (x=2 ∧ (y=6 ∨ y= -6)) ∨ (x= -2 ∧ (y=2 ∨ y= -2)) := by
  constructor
  · exact complete_rational_points
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl | rfl⟩ | ⟨rfl,rfl | rfl⟩)
    all_goals norm_num

theorem card_point_group : Nat.card Curve.Point = 8 := by
  let _ := finite_point_group
  let _ := Fintype.ofFinite Curve.Point
  have hl : 8 ≤ Nat.card Curve.Point := by
    rw [← listed_card, Nat.card_eq_fintype_card]
    exact Finset.card_le_univ _
  exact le_antisymm card_point_group_le_eight hl

end FourCorner.NineSmallE0

#print axioms FourCorner.NineSmallE0.finite_point_group
#print axioms FourCorner.NineSmallE0.complete_point_group
#print axioms FourCorner.NineSmallE0.complete_rational_points
#print axioms FourCorner.NineSmallE0.rational_point_iff
#print axioms FourCorner.NineSmallE0.card_point_group
