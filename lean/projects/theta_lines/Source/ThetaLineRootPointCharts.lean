import ThetaRestrictionHasTwoRoots

namespace FourCorner.ThetaLineRootPointCharts
open AlgebraicGeometry AlgebraicCurve CategoryTheory MvPolynomial
open ThetaLiteralModels ThetaProjectiveModel ThetaDGeometricModel ThetaDPlaneChartSections
open ThetaDCoordinateBasicOpens ThetaGeometricPointCoordinateEvaluation ThetaGeometricContactPoints
open SmoothProperRationalPointPlaces
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

 theorem X_relations (u v : K) (h : thetaF 1 u v=0) :
    ∀a : Fin 1,MvPolynomial.aeval ![u,v] (ThetaDGeometricChartPoints.equation 0 a)=0 := by
  intro a;fin_cases a
  simpa [ThetaDGeometricChartPoints.equation,ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,
    targetEquation,targetPolynomial,ThetaActualPoints.target_drop,thetaF,map_ofNat,mul_assoc] using h

 theorem Y_relations (u v : K) (h : thetaF u 1 v=0) :
    ∀a : Fin 1,MvPolynomial.aeval ![u,v] (ThetaDGeometricChartPoints.equation 1 a)=0 := by
  intro a;fin_cases a
  simpa [ThetaDGeometricChartPoints.equation,ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,
    targetEquation,targetPolynomial,ThetaActualPoints.target_drop,thetaF,map_ofNat,mul_assoc] using h

 theorem Z_relations (u v : K) (h : thetaF u v 1=0) :
    ∀a : Fin 1,MvPolynomial.aeval ![u,v] (ThetaDGeometricChartPoints.equation 2 a)=0 := by
  intro a;fin_cases a
  simpa [ThetaDGeometricChartPoints.equation,ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,
    targetEquation,targetPolynomial,ThetaActualPoints.target_drop,thetaF,map_ofNat,mul_assoc] using h

 def finiteChart : ThetaLine K → Fin 3
  | .affine _ _ => 1
  | .vertical _ => 2
  | .yzero => 2

/-- Every finite parameter root maps directly to an ACTUAL original QQ
chart and its true categorical Qbar pullback K-point. -/
def finiteRootPoint (L : ThetaLine K) (t : K) (ht : L.restrict t 1=0) : RationalPoint toBase := by
  cases L with
  | affine α β => exact affinePoint α β t (by simpa [ThetaLine.restrict] using ht)
  | vertical u => exact verticalPoint u t ht
  | yzero =>
    have h : thetaF t 0 1=0 := ht
    exact ⟨ThetaDGeometricChartPoints.point 2 ![t,0] (Z_relations t 0 h),
      ThetaDGeometricChartPoints.point_over _ _ _⟩

/-- The actual infinity parameter is retained. Its image is [1:0:alpha]
for affine lines and [t:1:0] for vertical lines. The yzero infinity root
would be [1:0:0], excluded by the true original equation 9801!=0. -/
def infinityRootPoint (L : ThetaLine K) (ht : L.restrict 1 0=0) : RationalPoint toBase := by
  cases L with
  | affine α β =>
    have h : thetaF 1 0 α=0 := by simpa [ThetaLine.restrict] using ht
    exact ⟨ThetaDGeometricChartPoints.point 0 ![0,α] (X_relations 0 α h),
      ThetaDGeometricChartPoints.point_over _ _ _⟩
  | vertical t =>
    have h : thetaF t 1 0=0 := by simpa [ThetaLine.restrict] using ht
    exact ⟨ThetaDGeometricChartPoints.point 1 ![t,0] (Y_relations t 0 h),
      ThetaDGeometricChartPoints.point_over _ _ _⟩
  | yzero => norm_num [ThetaLine.restrict,thetaF] at ht

 theorem coordinate_zero_not_other_open (j : Fin 3) (vals : Fin 2 → K)
    (hv : ∀a : Fin 1,MvPolynomial.aeval vals (ThetaDGeometricChartPoints.equation j a)=0)
    (a : Fin 2) (ha : vals a=0) :
    ThetaDGeometricChartPoints.point j vals hv (IsLocalRing.closedPoint K)∉
      geoU (ThetaAmbientChart.insert 2 j a) := by
  let p := ThetaDGeometricChartPoints.point j vals hv
  have hp : p (IsLocalRing.closedPoint K)∈geoU j := geometric_point_in_chart j vals hv
  intro ho
  have hb : p (IsLocalRing.closedPoint K)∈geometricD.basicOpen (coordinateSection j a) := by
    rw [coordinateSection_basicOpen]
    exact ⟨hp,ho⟩
  have hu := (geometricD.mem_basicOpen _ _ hp).mp hb
  have hm := hu.map (Scheme.stalkClosedPointTo p).hom
  have he : Scheme.stalkClosedPointTo p
      (geometricD.presheaf.germ (geoU j) (p (IsLocalRing.closedPoint K)) hp (coordinateSection j a))=0 :=
    (coordinate_stalk_evaluation j vals hv a).trans ha
  have hz : IsUnit (0:K) := he ▸ hm
  exact not_isUnit_zero hz

 theorem finiteRootPoint_mem (L : ThetaLine K) (t : K) (ht : L.restrict t 1=0) :
    (finiteRootPoint L t ht).val (IsLocalRing.closedPoint K)∈geoU (finiteChart L) := by
  cases L with
  | affine α β => exact geometric_point_in_chart _ _ _
  | vertical u => exact geometric_point_in_chart _ _ _
  | yzero => exact geometric_point_in_chart _ _ _

 theorem infinityRootPoint_not_finite (L : ThetaLine K) (ht : L.restrict 1 0=0) :
    (infinityRootPoint L ht).val (IsLocalRing.closedPoint K)∉geoU (finiteChart L) := by
  cases L with
  | affine α β => exact coordinate_zero_not_other_open 0 _ _ 0 rfl
  | vertical t => exact coordinate_zero_not_other_open 1 _ _ 1 rfl
  | yzero => norm_num [ThetaLine.restrict,thetaF] at ht

 theorem finiteRootPoint_injective (L : ThetaLine K) (r s : K) (hr hs)
    (he : finiteRootPoint L r hr=finiteRootPoint L s hs) : r=s := by
  cases L with
  | affine α β =>
    have hr' : thetaF r 1 (α*r+β)=0 := by simpa [ThetaLine.restrict] using hr
    have hs' : thetaF s 1 (α*s+β)=0 := by simpa [ThetaLine.restrict] using hs
    change affinePoint α β r hr'=affinePoint α β s hs' at he
    exact affinePoint_injective α β r s hr' hs' he
  | vertical t => exact verticalPoint_injective t r s hr hs he
  | yzero =>
    have hh := ThetaDGeometricChartPoints.point_injective 2 _ _ _ _ (congrArg Subtype.val he)
    exact congrFun hh 0

 theorem infinityRootPoint_ne_finite (L : ThetaLine K) (r : K) (hi hr) :
    infinityRootPoint L hi≠finiteRootPoint L r hr := by
  intro he
  have hm := finiteRootPoint_mem L r hr
  have hn := infinityRootPoint_not_finite L hi
  rw [←he] at hm
  exact hn hm

#print axioms finiteRootPoint_mem
#print axioms infinityRootPoint_not_finite
#print axioms finiteRootPoint_injective
#print axioms infinityRootPoint_ne_finite
end
end FourCorner.ThetaLineRootPointCharts
