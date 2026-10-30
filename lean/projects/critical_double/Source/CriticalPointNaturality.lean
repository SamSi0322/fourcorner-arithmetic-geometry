import CriticalSchemePointPlaces
import CriticalPointTransportValuation
import CriticalNormalizationDiagram
import AbstractPresentationPlaceTransport
import CriticalCoverGenericField
import BundledPointPlaceNaturality

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 40000
open AlgebraicGeometry CategoryTheory AlgebraicCurve
universe u
namespace FourCorner.CriticalPointNaturality
variable {k:Type u} [Field k]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants i).toModule
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants i).toModule
local instance relative (i:k) : Algebra (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.relativeAlgebra k i
local instance relativeModule (i:k) : Module (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := (relative i).toModule
local instance tower (i:k) : IsScalarTower k (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.constants_base_tower k i

def imagePoint (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (p:CriticalSchemePointPlaces.CoverPoints (k:=k)) : CriticalSchemePointPlaces.BasePoints i :=
  ⟨p.val ≫ CriticalDoubleOriginalMap.map i hi h2,by
    rw [Category.assoc,CriticalDoubleOriginalMap.map_over_base i hi h2]
    exact p.property⟩

/-- On the actual native generic stalks, the SAME image point has exactly
this valuation-ring comap. The native degree2 premise is proved internally. -/
theorem native_comap (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (p:CriticalSchemePointPlaces.CoverPoints (k:=k)) :
    letI:=CriticalAffineDomain.ring_isDomain i hi h2
    letI:=CriticalProjectiveIntegral.projective_integral i hi h2
    letI:=EllipticQuarticModel.integral k
    letI:=CriticalProjectiveSmooth.projective_smooth i hi h2
    letI:=EllipticQuarticModel.smooth k h2
    letI:=CriticalProj23.criticalToSpec_isProper i
    letI:=EllipticQuarticModel.proper k
    letI:=SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
    letI:=SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
    ((SmoothProperRationalPointPlaces.pointEquivRationalPlace (CriticalProj23.criticalToSpec i)
      (imagePoint i hi h2 p)).val).toValuationSubring=
    ((SmoothProperRationalPointPlaces.pointEquivRationalPlace (EllipticQuarticModel.toBase k) p).val).toValuationSubring.comap
      (CriticalDoubleOriginalMap.pullback i hi h2).toRingHom := by
  letI:=CriticalAffineDomain.ring_isDomain i hi h2
  letI:=CriticalProjectiveIntegral.projective_integral i hi h2
  letI:=EllipticQuarticModel.integral k
  letI:=CriticalProjectiveSmooth.projective_smooth i hi h2
  letI:=EllipticQuarticModel.smooth k h2
  letI:=CriticalProj23.criticalToSpec_isProper i
  letI:=EllipticQuarticModel.proper k
  letI:=SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
  letI:=SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
  exact BundledPointPlaceNaturality.point_valuation_comap_of_pullback
    (EllipticQuarticModel.toBase k) (CriticalProj23.criticalToSpec i)
    (CriticalDoubleOriginalMap.pullback i hi h2)
    (CriticalCoverGenericField.actual_generic_degree_two i hi h2).1
    (CriticalDoubleOriginalMap.map i hi h2) (CriticalDoubleOriginalMap.map_over_base i hi h2)
    (CriticalDoubleOriginalMap.map_generic i hi h2) p

/-- Actual Scheme image under the specified cover corresponds to restriction
of the SAME source place in the ORIGINAL literal field presentations. -/
theorem image_place (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (p:CriticalSchemePointPlaces.CoverPoints (k:=k)) :
    (CriticalSchemePointPlaces.baseEquiv i hi h2 (imagePoint i hi h2 p)).val=
      (CriticalSchemePointPlaces.coverEquiv i hi h2 p).val.restrict (CriticalLiteralDouble.base k i) := by
  letI:=CriticalAffineDomain.ring_isDomain i hi h2
  letI:=CriticalProjectiveIntegral.projective_integral i hi h2
  letI:=EllipticQuarticModel.integral k
  letI:=CriticalProjectiveSmooth.projective_smooth i hi h2
  letI:=EllipticQuarticModel.smooth k h2
  letI:=CriticalProj23.criticalToSpec_isProper i
  letI:=EllipticQuarticModel.proper k
  letI:=SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
  letI:=SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
  let e:=CriticalDoubleOriginalMap.baseFieldEquiv i hi h2
  let g:=CriticalDoubleModel.fieldEquiv i hi h2
  let Xp:=SmoothProperRationalPointPlaces.pointEquivRationalPlace (EllipticQuarticModel.toBase k) p
  let Yp:=SmoothProperRationalPointPlaces.pointEquivRationalPlace (CriticalProj23.criticalToSpec i) (imagePoint i hi h2 p)
  have hn:Yp.val.toValuationSubring=Xp.val.toValuationSubring.comap
      (CriticalDoubleOriginalMap.pullback i hi h2).toRingHom := native_comap i hi h2 p
  have hY:(CriticalSchemePointPlaces.baseEquiv i hi h2 (imagePoint i hi h2 p)).val.toValuationSubring=
      Yp.val.toValuationSubring.comap e.toRingHom :=
    CriticalPointTransportValuation.valuation (CriticalProj23.criticalToSpec i) e (imagePoint i hi h2 p)
  have hX:(CriticalSchemePointPlaces.coverEquiv i hi h2 p).val.toValuationSubring=
      Xp.val.toValuationSubring.comap g.toRingHom :=
    CriticalPointTransportValuation.valuation (EllipticQuarticModel.toBase k) g p
  exact AbstractPresentationPlaceTransport.place_eq_restrict_of_comaps
    (CriticalDoubleOriginalMap.pullback i hi h2) e g Xp.val Yp.val
    (CriticalSchemePointPlaces.coverEquiv i hi h2 p).val
    (CriticalSchemePointPlaces.baseEquiv i hi h2 (imagePoint i hi h2 p)).val
    hn hY hX (CriticalNormalizationDiagram.field_diagram i hi h2)

end FourCorner.CriticalPointNaturality
#print axioms FourCorner.CriticalPointNaturality.native_comap
#print axioms FourCorner.CriticalPointNaturality.image_place
