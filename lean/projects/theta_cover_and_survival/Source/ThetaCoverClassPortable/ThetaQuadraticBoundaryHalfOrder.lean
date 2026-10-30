import ThetaCoverClassPortable.ThetaQuadraticHalfUnweighted

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory

namespace FourCorner.ThetaQuadraticBoundaryHalfOrder
open ThetaQuadraticCurve ThetaQuadraticField ThetaQuadraticPlacePullback
open ThetaQuadraticHalfDivisor ThetaQuadraticHalfUnweighted SmoothProperClosedPointPlaces
abbrev K := ThetaDGeometricModel.K
local instance : IsIntegral curve := curve_integral
local instance : IsProper toBase := curve_proper
local instance : SmoothOfRelativeDimension 1 toBase := curve_smooth
local instance : Algebra F functionField := ThetaQuadraticCurve.fieldAlgebra
local instance : IsIntegral ThetaDGeometricModel.geometricD := ThetaDGeometricModel.geometric_integral
local instance : IsProper ThetaDGeometricModel.toBase := ThetaDGeometricModel.geometric_proper
local instance : SmoothOfRelativeDimension 1 ThetaDGeometricModel.toBase := ThetaDGeometricModel.geometric_smooth
local instance : Algebra K ThetaDGeometricModel.field := ThetaDGeometricModel.fieldAlgebra
local instance : IsCurveOver K ThetaDGeometricModel.field := ThetaDGeometricModel.field_isCurveOver
local instance : Algebra.EssFiniteType K ThetaDGeometricModel.field := ThetaDGeometricModel.field_essFiniteType

abbrev Signs := ThetaCoverBoundaryPoints.Signs
def geometricBoundary (s : Signs) : closedPoints ThetaDGeometricModel.geometricD :=
  SchemePointStalkEvaluation.closedPointOfPoint ThetaDGeometricModel.toBase
    (ThetaCoverBoundaryPoints.point s).val (ThetaCoverBoundaryPoints.point s).property

theorem geometricBoundary_place (s : Signs) :
    geometricPlace (geometricBoundary s)=ThetaCoverBoundaryPoints.place s := rfl

theorem geometricBoundary_source (s : Signs) :
    sourcePlace (geometricBoundary s)=ThetaQuadraticBoundary.place s := by
  change placeOfClosedPoint toBase (imageClosedPoint (geometricBoundary s))=
    placeOfClosedPoint toBase (SchemePointStalkEvaluation.closedPointOfPoint toBase
      (ThetaQuadraticBoundary.point s) (ThetaQuadraticBoundary.point_over s))
  apply congrArg (placeOfClosedPoint toBase)
  apply Subtype.ext
  have h := congrArg (fun f : Spec (.of K) ⟶ curve => f (IsLocalRing.closedPoint K))
    (ThetaQuadraticBoundary.geometric_point_basechange s)
  change geometricProjection ((ThetaCoverBoundaryPoints.point s).val (IsLocalRing.closedPoint K))=
    ThetaQuadraticBoundary.point s (extensionMap (IsLocalRing.closedPoint K)) at h
  rw [show extensionMap (IsLocalRing.closedPoint K)=IsLocalRing.closedPoint F from Subsingleton.elim _ _] at h
  exact h

theorem geometric_boundary_half_one (s : Signs) :
    (ThetaCoverBoundaryPoints.boundarySum-ThetaDCanonicalInfinityDivisor.infinitySum)
      (ThetaCoverBoundaryPoints.place s)=1 := by
  classical
  have hE : ThetaCoverBoundaryPoints.boundarySum (ThetaCoverBoundaryPoints.place s)=1 := by
    rw [ThetaCoverBoundaryPoints.boundarySum_apply,if_pos ⟨s,rfl⟩]
  have hh := congrArg (fun D : Divisor K ThetaDGeometricModel.field =>
    D (ThetaCoverBoundaryPoints.place s)) ThetaCoverDivisor.actual_divisor_h
  simp only [Finsupp.sub_apply,Finsupp.smul_apply,nsmul_eq_mul,Nat.cast_ofNat,
    DivisorPicClassification.principalDivisor_apply,hE] at hh
  have hb := ThetaCoverBoundaryOrders.boundary_h_order s
  have hH := ThetaCoverDivisor.infinitySum_effective (ThetaCoverBoundaryPoints.place s)
  simp only [Finsupp.zero_apply] at hH
  simp only [Finsupp.sub_apply,hE]
  omega

theorem half_boundary_one (s : Signs) : halfDivisor (ThetaQuadraticBoundary.place s)=1 := by
  have h := actual_half_pullback_coefficient (geometricBoundary s)
  rw [geometricBoundary_place,geometricBoundary_source,geometric_boundary_half_one] at h
  exact h.symm

theorem half_positive_iff_boundary (w : Place F functionField) :
    0<halfDivisor w ↔ ∃s : Signs,ThetaQuadraticBoundary.place s=w := by
  constructor
  · intro hw
    obtain ⟨x,rfl⟩ := sourcePlace_surjective w
    have hp : 0<(ThetaCoverBoundaryPoints.boundarySum-ThetaDCanonicalInfinityDivisor.infinitySum)
        (geometricPlace x) := by rw [actual_half_pullback_coefficient];exact hw
    have hH := ThetaCoverDivisor.infinitySum_effective (geometricPlace x)
    simp only [Finsupp.zero_apply] at hH
    have hE : 0<ThetaCoverBoundaryPoints.boundarySum (geometricPlace x) := by
      simp only [Finsupp.sub_apply] at hp
      omega
    classical
    rw [ThetaCoverBoundaryPoints.boundarySum_apply] at hE
    split_ifs at hE with he
    · obtain ⟨s,hs⟩ := he
      have hx : x=geometricBoundary s := by
        apply placeOfClosedPoint_injective ThetaDGeometricModel.toBase
        exact hs.symm.trans (geometricBoundary_place s).symm
      refine ⟨s,?_⟩
      rw [hx,geometricBoundary_source]
    · omega
  · rintro ⟨s,rfl⟩
    rw [half_boundary_one]
    norm_num

/-- The positive Weil part is exactly the four ACTUAL F-boundary points;
all native F-places are included in the argument. -/
theorem positive_half_is_E2 : halfDivisor ⊔ 0=ThetaQuadraticBoundary.E2 := by
  classical
  apply Finsupp.ext
  intro w
  by_cases he : ∃s : Signs,ThetaQuadraticBoundary.place s=w
  · obtain ⟨s,rfl⟩ := he
    simp only [Finsupp.sup_apply,Finsupp.zero_apply,half_boundary_one,sup_eq_left.mpr (by norm_num : (0:ℤ)≤1)]
    rw [ThetaQuadraticBoundaryDistinct.E2_apply,if_pos ⟨s,rfl⟩]
  · have hn : halfDivisor w≤0 := le_of_not_gt (by
      intro hp
      exact he ((half_positive_iff_boundary w).mp hp))
    simp only [Finsupp.sup_apply,Finsupp.zero_apply,sup_eq_right.mpr hn]
    rw [ThetaQuadraticBoundaryDistinct.E2_apply,if_neg he]

end FourCorner.ThetaQuadraticBoundaryHalfOrder
