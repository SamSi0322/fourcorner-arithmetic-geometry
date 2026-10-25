import FourCorner.NineFlexGroup
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

namespace FourCorner.NineSmallE0

abbrev Curve := (splitCurve (-1) (-4)).toAffine

lemma discriminant_ne_zero : Curve.Δ ≠ 0 := by
  change (splitCurve (-1) (-4)).Δ ≠ 0
  rw [splitCurve_discriminant]
  norm_num

lemma nonsingular_of_equation {x y : ℚ} (h : y^2=x*(x+1)*(x+4)) :
    Curve.Nonsingular x y := by
  apply (Curve.equation_iff_nonsingular_of_Δ_ne_zero discriminant_ne_zero).mp
  apply (splitCurve_equation_iff (-1) (-4) x y).mpr
  simpa using h

def pointZero : Curve.Point := .some 0 0 (nonsingular_of_equation (by norm_num))
def pointNegOne : Curve.Point := .some (-1) 0 (nonsingular_of_equation (by norm_num))
def pointNegFour : Curve.Point := .some (-4) 0 (nonsingular_of_equation (by norm_num))
def pointTwoPlus : Curve.Point := .some 2 6 (nonsingular_of_equation (by norm_num))
def pointTwoMinus : Curve.Point := .some 2 (-6) (nonsingular_of_equation (by norm_num))
def pointNegTwoPlus : Curve.Point := .some (-2) 2 (nonsingular_of_equation (by norm_num))
def pointNegTwoMinus : Curve.Point := .some (-2) (-2) (nonsingular_of_equation (by norm_num))

def listed : Finset Curve.Point :=
  {0, pointZero, pointNegOne, pointNegFour, pointTwoPlus, pointTwoMinus,
    pointNegTwoPlus, pointNegTwoMinus}

lemma listed_card : listed.card = 8 := by
  decide

/-- With the independently obtained cardinal bound, the eight explicit points
exhaust the actual point group. -/
lemma mem_listed_of_card_le [Finite Curve.Point] (hc : Nat.card Curve.Point ≤ 8)
    (P : Curve.Point) : P ∈ listed := by
  classical
  let _ := Fintype.ofFinite Curve.Point
  have hEq : (Finset.univ : Finset Curve.Point) = listed := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ listed)
    simpa [listed_card, Nat.card_eq_fintype_card] using hc
  rw [← hEq]
  exact Finset.mem_univ P

lemma coordinates_of_card_le [Finite Curve.Point] (hc : Nat.card Curve.Point ≤ 8)
    {x y : ℚ} (h : y^2=x*(x+1)*(x+4)) :
    (x=0 ∧ y=0) ∨ (x= -1 ∧ y=0) ∨ (x= -4 ∧ y=0) ∨
    (x=2 ∧ (y=6 ∨ y= -6)) ∨ (x= -2 ∧ (y=2 ∨ y= -2)) := by
  have hm := mem_listed_of_card_le hc
    (WeierstrassCurve.Affine.Point.some x y (nonsingular_of_equation h))
  simp only [listed, Finset.mem_insert, Finset.mem_singleton, pointZero, pointNegOne,
    pointNegFour, pointTwoPlus, pointTwoMinus, pointNegTwoPlus, pointNegTwoMinus,
    WeierstrassCurve.Affine.Point.some_ne_zero, false_or,
    WeierstrassCurve.Affine.Point.some.injEq] at hm
  tauto

end FourCorner.NineSmallE0

#print axioms FourCorner.NineSmallE0.listed_card
#print axioms FourCorner.NineSmallE0.mem_listed_of_card_le
#print axioms FourCorner.NineSmallE0.coordinates_of_card_le
