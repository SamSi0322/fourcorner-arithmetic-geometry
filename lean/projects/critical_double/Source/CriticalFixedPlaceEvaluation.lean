import FixedAffinePointEvaluation
import CriticalSchemePointPlaces
import CriticalBoundaryEight

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 40000
open AlgebraicGeometry CategoryTheory AlgebraicCurve
universe u
namespace FourCorner.CriticalFixedPlaceEvaluation
open CriticalProj23 CriticalStandardCharts CriticalProjectiveField CriticalSignPoints CriticalRadicalField
open AffineChartPlaceEvaluation FixedAffinePointEvaluation ResiduePlaceEvaluation
variable {k:Type u} [Field k]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants i).toModule

def signedPoint (i:k) (e:Fin 3→Bool) : CriticalSchemePointPlaces.BasePoints i :=
  ⟨point i e,point_over i e⟩

/-- The supplied literal V0 affine evaluation gives exactly the accepted
ORIGINAL signed Scheme point, not an abstract isomorphic replacement. -/
theorem chartPoint_signed (i:k) (hi:i^2= -1) (h2:(2:k)≠0) (e:Fin 3→Bool) :
    letI:=CriticalAffineDomain.ring_isDomain i hi h2
    letI:=CriticalProjectiveIntegral.projective_integral i hi h2
    letI:=CriticalProjectiveSmooth.projective_smooth i hi h2
    letI:=CriticalProj23.criticalToSpec_isProper i
    chartPoint (criticalToSpec i) (nativeChart i) (nativeChart_over_base i) (literalEvaluation i e)=signedPoint i e := by
  letI:=CriticalAffineDomain.ring_isDomain i hi h2
  letI:=CriticalProjectiveIntegral.projective_integral i hi h2
  letI:=CriticalProjectiveSmooth.projective_smooth i hi h2
  letI:=CriticalProj23.criticalToSpec_isProper i
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom (literalEvaluation i e).toRingHom)≫nativeChart i=point i e
  change Spec.map (CommRingCat.ofHom (literalEvaluation i e).toRingHom)≫
    Spec.map (CommRingCat.ofHom (zeroEquiv i).toRingHom)≫
      (chartIso i 0).inv≫(Proj.basicOpen (criticalGrading i) (coordinate i 0)).ι=point i e
  rw [←Category.assoc,←Spec.map_comp]
  rfl

 theorem literal_coordinate (i:k) (e:Fin 3→Bool) (j:Fin 3) :
    literalEvaluation i e (CriticalAffineGeometry.coordinate i j)=CriticalElliptic23.sign (e j) := by
  have h:=evaluation_ax i e j
  change literalEvaluation i e (zeroAlgEquiv i (CriticalChartJacobian.ax i 0 j))=_ at h
  rwa [zeroAlgEquiv_ax] at h

/-- Actual a,b,c are regular and have their original three signs under the
FIXED CriticalSchemePointPlaces.baseEquiv, by the reviewed affine annex. -/
theorem signed_coordinates (i:k) (hi:i^2= -1) (h2:(2:k)≠0) (e:Fin 3→Bool) :
    let w:=CriticalSchemePointPlaces.baseEquiv i hi h2 (signedPoint i e)
    ∃A B C:w.val.toValuationSubring,
      (A:CriticalLiteralDouble.base k i)=a k i ∧
      (B:CriticalLiteralDouble.base k i)=b k i ∧
      (C:CriticalLiteralDouble.base k i)=c k i ∧
      evaluate w.val w.property A=CriticalElliptic23.sign (e 0) ∧
      evaluate w.val w.property B=CriticalElliptic23.sign (e 1) ∧
      evaluate w.val w.property C=CriticalElliptic23.sign (e 2) := by
  letI:=CriticalAffineDomain.ring_isDomain i hi h2
  letI:=CriticalProjectiveIntegral.projective_integral i hi h2
  letI:=CriticalProjectiveSmooth.projective_smooth i hi h2
  letI:=CriticalProj23.criticalToSpec_isProper i
  letI:=SmoothCurveExtension.fieldAlgebra (criticalToSpec i)
  let af:=CriticalOriginalFieldCoordinates.affineEquiv k i hi h2
  have hc:=CriticalOriginalFieldCoordinates.coordinates k i hi h2
  have all (x:CriticalLiteralDouble.base k i) (j:Fin 3)
      (hx:af x=CriticalAffineFieldBridge.coordinate i j) :
      let w:=CriticalSchemePointPlaces.baseEquiv i hi h2 (signedPoint i e)
      ∃R:w.val.toValuationSubring,(R:CriticalLiteralDouble.base k i)=x ∧
        evaluate w.val w.property R=CriticalElliptic23.sign (e j) := by
    have h:=chart_transport_evaluate (criticalToSpec i) (nativeChart i) (nativeChart_over_base i)
      (literalEvaluation i e) af x (CriticalAffineGeometry.coordinate i j) hx
    rw [chartPoint_signed i hi h2 e] at h
    change ∃R:(CriticalSchemePointPlaces.baseEquiv i hi h2 (signedPoint i e)).val.toValuationSubring,
      (R:CriticalLiteralDouble.base k i)=x ∧
      evaluate _ _ R=literalEvaluation i e (CriticalAffineGeometry.coordinate i j) at h
    rwa [literal_coordinate] at h
  obtain ⟨A,hA,ha⟩:=all (a k i) 0 hc.1
  obtain ⟨B,hB,hb⟩:=all (b k i) 1 hc.2.1
  obtain ⟨C,hC,hd⟩:=all (c k i) 2 hc.2.2
  exact ⟨A,B,C,hA,hB,hC,ha,hb,hd⟩

#print axioms chartPoint_signed
#print axioms signed_coordinates
end FourCorner.CriticalFixedPlaceEvaluation
