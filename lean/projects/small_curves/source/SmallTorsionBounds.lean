import SmallReduction
import FourCorner.NineSmallFiniteFive

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace FourCorner.SmallReduction
open WeierstrassCurve.Affine
local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Literal integral Weierstrass model of y²=x(x-6)(x-8). -/
def smallAIntegral : WeierstrassCurve ℤ := ⟨0, -14, 0, 48, 0⟩
/-- Literal integral Weierstrass model of y²=x(x+1)(x+4). -/
def smallE0Integral : WeierstrassCurve ℤ := ⟨0, 5, 0, 4, 0⟩

theorem smallA_rational_model :
    rationalCurve smallAIntegral = (splitCurve 6 8).toAffine := by
  ext <;> norm_num [rationalCurve, smallAIntegral, splitCurve, WeierstrassCurve.map]

theorem smallE0_rational_model :
    rationalCurve smallE0Integral = (splitCurve (-1) (-4)).toAffine := by
  ext <;> norm_num [rationalCurve, smallE0Integral, splitCurve, WeierstrassCurve.map]

theorem smallA_finite_model :
    finiteCurve smallAIntegral = NineSmallFiniteFive.smallA.toAffine := by
  ext <;> norm_num [finiteCurve, smallAIntegral, NineSmallFiniteFive.smallA, WeierstrassCurve.map]

theorem smallE0_finite_model :
    finiteCurve smallE0Integral = NineSmallFiniteFive.smallE0.toAffine := by
  ext <;> norm_num [finiteCurve, smallE0Integral, NineSmallFiniteFive.smallE0, WeierstrassCurve.map]

local instance smallA_rational_elliptic : (rationalCurve smallAIntegral).IsElliptic := by
  rw [smallA_rational_model, WeierstrassCurve.isElliptic_iff]
  apply isUnit_iff_ne_zero.mpr
  change (splitCurve 6 8).Δ ≠ 0
  rw [splitCurve_discriminant]
  norm_num

local instance smallE0_rational_elliptic : (rationalCurve smallE0Integral).IsElliptic := by
  rw [smallE0_rational_model, WeierstrassCurve.isElliptic_iff]
  apply isUnit_iff_ne_zero.mpr
  change (splitCurve (-1) (-4)).Δ ≠ 0
  rw [splitCurve_discriminant]
  norm_num

local instance smallA_good_five : (redCurve primeFive smallAIntegral).IsElliptic := by
  apply good_reduction_five
  rw [smallA_finite_model]
  exact NineSmallFiniteFive.smallA.isUnit_Δ.ne_zero

local instance smallE0_good_five : (redCurve primeFive smallE0Integral).IsElliptic := by
  apply good_reduction_five
  rw [smallE0_finite_model]
  exact NineSmallFiniteFive.smallE0.isUnit_Δ.ne_zero

/-- Finiteness is independently recorded so the natural-cardinality bounds
cannot be read vacuously on an infinite subtype. -/
theorem smallA_torsion_finite :
    Finite (AddCommGroup.torsion (splitCurve 6 8).toAffine.Point) := by
  rw [← smallA_rational_model]
  exact torsion_finite smallAIntegral

theorem smallE0_torsion_finite :
    Finite (AddCommGroup.torsion (splitCurve (-1) (-4)).toAffine.Point) := by
  rw [← smallE0_rational_model]
  exact torsion_finite smallE0Integral

/-- The complete rational torsion subgroup of A has at most four elements,
by actual good reduction at five. No rank or finiteness premise is used. -/
theorem smallA_torsion_card_le_four :
    Nat.card (AddCommGroup.torsion (splitCurve 6 8).toAffine.Point) ≤ 4 := by
  rw [← smallA_rational_model]
  have h := torsion_card_le_finite smallAIntegral
  rw [smallA_finite_model, NineSmallFiniteFive.card_smallA] at h
  exact h

/-- The complete rational torsion subgroup of E0 has at most eight elements,
by actual good reduction at five. No rank or finiteness premise is used. -/
theorem smallE0_torsion_card_le_eight :
    Nat.card (AddCommGroup.torsion (splitCurve (-1) (-4)).toAffine.Point) ≤ 8 := by
  rw [← smallE0_rational_model]
  have h := torsion_card_le_finite smallE0Integral
  rw [smallE0_finite_model, NineSmallFiniteFive.card_smallE0] at h
  exact h

variable (W₀ : WeierstrassCurve ℤ)
  [(rationalCurve W₀).IsElliptic] [(redCurve primeFive W₀).IsElliptic]

/-- When every actual rational point is torsion, the same genuine reduction
map bounds the cardinality of the whole rational point group. -/
theorem rational_card_le_finite_of_all_torsion
    (ht : ∀ P : (rationalCurve W₀).Point, IsOfFinAddOrder P) :
    Nat.card (rationalCurve W₀).Point ≤ Nat.card (finiteCurve W₀).Point := by
  apply Nat.card_le_card_of_injective (reduceFive W₀)
  intro P Q h
  have h' := reduceFive_torsion_injective W₀
    (a₁ := ⟨P, ht P⟩) (a₂ := ⟨Q, ht Q⟩) h
  exact congrArg Subtype.val h'

/-- The all-torsion conclusion supplied by descent implies the literal point
cardinality bound, with no assumed reduction injection. -/
theorem smallA_card_le_four_of_all_torsion
    (ht : ∀ P : (splitCurve 6 8).toAffine.Point, IsOfFinAddOrder P) :
    Nat.card (splitCurve 6 8).toAffine.Point ≤ 4 := by
  rw [← smallA_rational_model] at ht ⊢
  have h := rational_card_le_finite_of_all_torsion smallAIntegral ht
  rw [smallA_finite_model, NineSmallFiniteFive.card_smallA] at h
  exact h

/-- The all-torsion conclusion supplied by descent implies the literal point
cardinality bound, with no assumed reduction injection. -/
theorem smallE0_card_le_eight_of_all_torsion
    (ht : ∀ P : (splitCurve (-1) (-4)).toAffine.Point, IsOfFinAddOrder P) :
    Nat.card (splitCurve (-1) (-4)).toAffine.Point ≤ 8 := by
  rw [← smallE0_rational_model] at ht ⊢
  have h := rational_card_le_finite_of_all_torsion smallE0Integral ht
  rw [smallE0_finite_model, NineSmallFiniteFive.card_smallE0] at h
  exact h

#print axioms smallA_torsion_finite
#print axioms smallE0_torsion_finite
#print axioms smallA_torsion_card_le_four
#print axioms smallE0_torsion_card_le_eight
#print axioms smallA_card_le_four_of_all_torsion
#print axioms smallE0_card_le_eight_of_all_torsion
end FourCorner.SmallReduction
