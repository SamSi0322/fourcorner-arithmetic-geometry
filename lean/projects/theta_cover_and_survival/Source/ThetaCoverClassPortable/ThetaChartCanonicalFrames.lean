import ThetaCoverClassPortable.ThetaHalfCanonicalRootSupport

namespace FourCorner.ThetaChartCanonicalFrames
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaDPlaneChartSections ThetaDFieldCoordinates ThetaDExactChartTransitions ThetaDActualDifferential
open ThetaDChartPlaceRegularity ThetaDHyperplaneLocalOrders ThetaDProjectiveInfinityCover
open ThetaContactDifferentialDivisors ThetaDPlaneRegularForms ThetaDGlobalCanonicalCandidate
open SmoothProperClosedPointPlaces SmoothProperRationalPointPlaces SchemePointStalkEvaluation
open ThetaGeometricPointCoordinateEvaluation ThetaGeometricResidueCoordinates
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : ∀w : Place K field,w.DCoordGenerates := dCoordGenerates_of_isCurveOver

 theorem ord_zero_of_inverse_regular (w : Place K field) (f : field) (hf : f≠0)
    (hr : f∈w.toValuationSubring) (hi : f⁻¹∈w.toValuationSubring) : w.ord f=0 := by
  have hp := w.ord_nonneg_of_mem hr
  have hn := w.ord_nonneg_of_mem hi
  rw [w.ord_inv] at hn
  omega

 theorem x_order_infinity (p : closedPoints geometricD) (hp : p.val∉geoU 2) :
    (placeOfClosedPoint toBase p).ord x = -1 := by
  have hv := local_Z_over_X_order_one p hp
  rw [XZ_transition.2,Place.ord_inv] at hv
  omega

 theorem X_frame (p : closedPoints geometricD) (hp : p.val∈geoU 0) :
    (placeOfClosedPoint toBase p).ordDifferential (x • omega)=0 := by
  let w := placeOfClosedPoint toBase p
  rw [w.ordDifferential_smul x_ne_zero (coefficient_ne_zero omega_ne_zero w)]
  by_cases hz : p.val∈geoU 2
  · have hx : w.ord x=0 := ord_zero_of_inverse_regular w x x_ne_zero
      (coordinate_regular_at_chart 2 p hz 0)
      (by rw [←XZ_transition.2];exact coordinate_regular_at_chart 0 p hp 1)
    rw [hx,finite_order_zero p hz,zero_add]
  · rw [x_order_infinity p hz,infinity_order_one p hz]
    norm_num

 theorem Y_frame (p : closedPoints geometricD) (hp : p.val∈geoU 1) :
    (placeOfClosedPoint toBase p).ordDifferential (y • omega)=0 := by
  let w := placeOfClosedPoint toBase p
  have hy := ThetaActualLineDifferentials.y_ne_zero
  rw [w.ordDifferential_smul hy (coefficient_ne_zero omega_ne_zero w)]
  by_cases hz : p.val∈geoU 2
  · have ho : w.ord y=0 := ord_zero_of_inverse_regular w y hy
      (coordinate_regular_at_chart 2 p hz 1)
      (by rw [←YZ_transition.2];exact coordinate_regular_at_chart 1 p hp 1)
    rw [ho,finite_order_zero p hz,zero_add]
  · have hu : 0≤w.ord (y/x) := w.ord_nonneg_of_mem (by
      rw [←XZ_transition.1]
      exact coordinate_regular_at_chart 0 p (infinity_in_X p.val hz) 0)
    have hv : 0≤w.ord (x/y) := w.ord_nonneg_of_mem (by
      rw [←YZ_transition.1]
      exact coordinate_regular_at_chart 1 p hp 0)
    simp only [div_eq_mul_inv,w.ord_mul hy (inv_ne_zero x_ne_zero),
      w.ord_mul x_ne_zero (inv_ne_zero hy),w.ord_inv] at hu hv
    have hx : w.ord x = -1 := x_order_infinity p hz
    have ho : w.ord y = -1 := by omega
    rw [ho,infinity_order_one p hz]
    norm_num

 theorem Z_frame (p : closedPoints geometricD) (hp : p.val∈geoU 2) :
    (placeOfClosedPoint toBase p).ordDifferential omega=0 := finite_order_zero p hp

 theorem rational_X_frame (vals : Fin 2→K)
    (hv : ∀i : Fin 1,MvPolynomial.aeval vals (ThetaDGeometricChartPoints.equation 0 i)=0) :
    (rationalPlace 0 vals hv).val.ordDifferential (x • omega)=0 := by
  exact X_frame (closedPointOfPoint toBase (chartPoint 0 vals hv).val (chartPoint 0 vals hv).property)
    (geometric_point_in_chart 0 vals hv)

 theorem rational_Y_frame (vals : Fin 2→K)
    (hv : ∀i : Fin 1,MvPolynomial.aeval vals (ThetaDGeometricChartPoints.equation 1 i)=0) :
    (rationalPlace 1 vals hv).val.ordDifferential (y • omega)=0 := by
  exact Y_frame (closedPointOfPoint toBase (chartPoint 1 vals hv).val (chartPoint 1 vals hv).property)
    (geometric_point_in_chart 1 vals hv)

 theorem rational_Z_frame (vals : Fin 2→K)
    (hv : ∀i : Fin 1,MvPolynomial.aeval vals (ThetaDGeometricChartPoints.equation 2 i)=0) :
    (rationalPlace 2 vals hv).val.ordDifferential omega=0 := by
  exact Z_frame (closedPointOfPoint toBase (chartPoint 2 vals hv).val (chartPoint 2 vals hv).property)
    (geometric_point_in_chart 2 vals hv)

#print axioms X_frame
#print axioms Y_frame
#print axioms rational_X_frame
#print axioms rational_Y_frame
#print axioms rational_Z_frame
end
end FourCorner.ThetaChartCanonicalFrames
