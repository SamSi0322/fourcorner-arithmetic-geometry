import SmoothProperPointPlaceTransport

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory AlgebraicCurve
universe u
namespace FourCorner.CriticalPointTransportValuation
variable {k F:Type u} [Field k] [Field F] [Algebra k F]
  {X:Scheme.{u}} [IsIntegral X] (c:X⟶Spec (.of k))
  [SmoothOfRelativeDimension 1 c] [IsProper c]

theorem valuation (e:letI:=SmoothProperClosedPointPlaces.fieldAlgebra c;F≃ₐ[k]X.functionField)
    (p:SmoothProperRationalPointPlaces.RationalPoint c) :
    letI:=SmoothProperClosedPointPlaces.fieldAlgebra c
    (SmoothProperPointPlaceTransport.pointEquivRationalPlace_of_fieldEquiv c e p).val.toValuationSubring=
      (SmoothProperRationalPointPlaces.pointEquivRationalPlace c p).val.toValuationSubring.comap e.toRingHom := by
  letI:=SmoothProperClosedPointPlaces.fieldAlgebra c
  rfl

end FourCorner.CriticalPointTransportValuation
#print axioms FourCorner.CriticalPointTransportValuation.valuation
