import CriticalDoubleOriginalMap
import SmoothProperPointPlaceTransport

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 40000
open AlgebraicGeometry CategoryTheory AlgebraicCurve
universe u
namespace FourCorner.CriticalSchemePointPlaces
variable {k:Type u} [Field k]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants i).toModule
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants i).toModule

abbrev BasePoints (i:k) := {p:Spec (.of k) ⟶ CriticalProj23.criticalCurve i //
  p ≫ CriticalProj23.criticalToSpec i=𝟙 _}
abbrev CoverPoints := {p:Spec (.of k) ⟶ EllipticQuarticModel.curve k //
  p ≫ EllipticQuarticModel.toBase k=𝟙 _}

/-- Genuine original Ci Scheme points are transported using the FIXED
coordinate-preserving actual generic-stalk comparison. -/
def baseEquiv (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    BasePoints i ≃ {v:Place k (CriticalLiteralDouble.base k i) //v.IsRational} := by
  letI:=CriticalAffineDomain.ring_isDomain i hi h2
  letI:=CriticalProjectiveIntegral.projective_integral i hi h2
  letI:=CriticalProjectiveSmooth.projective_smooth i hi h2
  letI:=CriticalProj23.criticalToSpec_isProper i
  exact SmoothProperPointPlaceTransport.pointEquivRationalPlace_of_fieldEquiv
    (CriticalProj23.criticalToSpec i) (CriticalDoubleOriginalMap.baseFieldEquiv i hi h2)

/-- Genuine points on the SAME proper model of the EXACT literal product
extension correspond to its actual rational places, including finite k. -/
def coverEquiv (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    CoverPoints (k:=k) ≃ {w:Place k (CriticalLiteralDouble.field k i) //w.IsRational} := by
  letI:=EllipticQuarticModel.integral k
  letI:=EllipticQuarticModel.smooth k h2
  letI:=EllipticQuarticModel.proper k
  exact SmoothProperPointPlaceTransport.pointEquivRationalPlace_of_fieldEquiv
    (EllipticQuarticModel.toBase k) (CriticalDoubleModel.fieldEquiv i hi h2)

theorem base_card (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    Nat.card (BasePoints i)=Nat.card {v:Place k (CriticalLiteralDouble.base k i) //v.IsRational} :=
  Nat.card_congr (baseEquiv i hi h2)
theorem cover_card (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    Nat.card (CoverPoints (k:=k))=Nat.card {w:Place k (CriticalLiteralDouble.field k i) //w.IsRational} :=
  Nat.card_congr (coverEquiv i hi h2)

end FourCorner.CriticalSchemePointPlaces
#print axioms FourCorner.CriticalSchemePointPlaces.baseEquiv
#print axioms FourCorner.CriticalSchemePointPlaces.coverEquiv
#print axioms FourCorner.CriticalSchemePointPlaces.base_card
#print axioms FourCorner.CriticalSchemePointPlaces.cover_card
