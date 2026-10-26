import CriticalChartGenericFunctions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicCurve MvPolynomial
universe u
namespace FourCorner.CriticalFixedChartCoordinates
open CriticalProj23 CriticalStandardCharts CriticalChartBase CriticalHomogeneousEvaluation CriticalRadicalField
variable {k:Type u} [Field k]
local instance baseConstants (i:k):Algebra k (CriticalLiteralDouble.base k i):=CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k):Module k (CriticalLiteralDouble.base k i):=(baseConstants i).toModule

theorem base_coordinates (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
 letI:=CriticalProjectiveIntegral.projective_integral i hi h2
 letI:=SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
 let φ:=CriticalDoubleOriginalMap.baseFieldEquiv i hi h2
 φ (a k i)=CriticalChartGenericFunctions.genericMap i 0 (affineEvaluation i 0 (X 1)) ∧
 φ (b k i)=CriticalChartGenericFunctions.genericMap i 0 (affineEvaluation i 0 (X 2)) ∧
 φ (c k i)=CriticalChartGenericFunctions.genericMap i 0 (affineEvaluation i 0 (X 3)) := by
  letI:=CriticalAffineDomain.ring_isDomain i hi h2
  letI:=CriticalProjectiveIntegral.projective_integral i hi h2
  letI:=SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
  let f:=CriticalSignPoints.literalEvaluation i (fun _=>false)
  letI : IsIntegral (Proj (criticalGrading i)) :=CriticalProjectiveIntegral.projective_integral i hi h2
  let U:(criticalCurve i).Opens:=Proj.basicOpen (criticalGrading i) (coordinate i 0)
  have hf (r:CriticalAffineGeometry.ring i):
      CriticalProjectiveField.fieldEquiv i hi h2 (algebraMap _ (FractionRing (CriticalAffineGeometry.ring i)) r)=
      ChartSectionGeneric.genericMap U (zeroChartIso i) r := by
    exact (AffineChartStalkFunctions.fieldEquiv_chartLocalFunction (criticalToSpec i)
      (CriticalProjectiveField.nativeChart i) (CriticalProjectiveField.nativeChart_over_base i) f r).trans
      (ChartSectionGeneric.genericMap_local U (zeroChartIso i) f r).symm
  have ht (r:CriticalAffineGeometry.ring i):
      ChartSectionGeneric.genericMap U (zeroChartIso i) r=
      CriticalChartGenericFunctions.genericMap i 0 ((zeroEquiv i).symm r) := by
    change (criticalCurve i).germToFunctionField U
      (ChartSectionGeneric.chartSection U (zeroChartIso i) r)=_
    rw [zeroChartIso,ChartSectionGeneric.chartSection_trans]
    rfl
  have hc:=CriticalOriginalFieldCoordinates.coordinates k i hi h2
  constructor
  · change CriticalProjectiveField.fieldEquiv i hi h2
      (CriticalOriginalFieldCoordinates.affineEquiv k i hi h2 (a k i))=_
    rw [hc.1,CriticalAffineFieldBridge.coordinate,hf,ht]
    congr 1
    apply (zeroEquiv i).injective
    rw [RingEquiv.apply_symm_apply,affineEvaluation_X]
    rfl
  constructor
  · change CriticalProjectiveField.fieldEquiv i hi h2
      (CriticalOriginalFieldCoordinates.affineEquiv k i hi h2 (b k i))=_
    rw [hc.2.1,CriticalAffineFieldBridge.coordinate,hf,ht]
    congr 1
    apply (zeroEquiv i).injective
    rw [RingEquiv.apply_symm_apply,affineEvaluation_X]
    rfl
  · change CriticalProjectiveField.fieldEquiv i hi h2
      (CriticalOriginalFieldCoordinates.affineEquiv k i hi h2 (c k i))=_
    rw [hc.2.2,CriticalAffineFieldBridge.coordinate,hf,ht]
    congr 1
    apply (zeroEquiv i).injective
    rw [RingEquiv.apply_symm_apply,affineEvaluation_X]
    rfl

/-- Exact ORIGINAL V1-chart ratios under the SAME fixed field comparison. -/
theorem pole_coordinates (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
 letI:=CriticalProjectiveIntegral.projective_integral i hi h2
 letI:=SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
 let φ:=CriticalDoubleOriginalMap.baseFieldEquiv i hi h2
 φ ((a k i)⁻¹)=CriticalChartGenericFunctions.genericMap i 1 (affineEvaluation i 1 (X 0)) ∧
 φ (b k i/a k i)=CriticalChartGenericFunctions.genericMap i 1 (affineEvaluation i 1 (X 2)) ∧
 φ (c k i/a k i)=CriticalChartGenericFunctions.genericMap i 1 (affineEvaluation i 1 (X 3)) := by
  letI:=CriticalProjectiveIntegral.projective_integral i hi h2
  letI:=SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
  let φ:=CriticalDoubleOriginalMap.baseFieldEquiv i hi h2
  have hc:=base_coordinates i hi h2
  have hn:φ (a k i)≠0:=(map_ne_zero φ).mpr (CriticalBadUnits.ordered_nonzero i hi h2).1
  have hz:=CriticalChartGenericFunctions.genericCoordinate_mul i 1 0 0
  rw [CriticalChartGenericFunctions.genericCoordinate_self,hc.1.symm] at hz
  have he:CriticalChartGenericFunctions.genericMap i 1 (affineEvaluation i 1 (X 0))=(φ (a k i))⁻¹ :=
    eq_inv_of_mul_eq_one_left hz
  constructor
  · rw [map_inv₀,he]
  constructor
  · have h:=CriticalChartGenericFunctions.genericCoordinate_mul i 1 0 2
    rw [hc.1.symm,hc.2.1.symm] at h
    rw [map_div₀]
    exact (eq_div_iff hn).mpr h |>.symm
  · have h:=CriticalChartGenericFunctions.genericCoordinate_mul i 1 0 3
    rw [hc.1.symm,hc.2.2.symm] at h
    rw [map_div₀]
    exact (eq_div_iff hn).mpr h |>.symm

#print axioms base_coordinates
#print axioms pole_coordinates
end FourCorner.CriticalFixedChartCoordinates
