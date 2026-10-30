import BundledPointPlaceNaturality

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u
namespace FourCorner.AbstractPresentationPlaceTransport
open SmoothProperClosedPointPlaces SmoothProperRationalPointPlaces SmoothProperPointPlaceTransport

/-- Pure abstract presentation transport. All fields, valuation rings and
maps remain variables in this proof, preventing expansion of concrete
function-field equivalence records at its later application site. -/
theorem valuation_comap_transport {F E FY FX : Type u}
    [Field F] [Field E] [Field FY] [Field FX]
    (τ : FY →+* FX) (e : F →+* FY) (g : E →+* FX) (φ : F →+* E)
    (V : ValuationSubring FX) (W : ValuationSubring FY)
    (hnative : W=V.comap τ) (hcomm : τ.comp e=g.comp φ) :
    W.comap e=(V.comap g).comap φ := by
  rw [hnative,ValuationSubring.comap_comap,ValuationSubring.comap_comap,hcomm]

variable {K F E FY FX : Type u} [Field K] [Field F] [Field E] [Field FY] [Field FX]
    [Algebra K F] [Algebra K E] [Algebra K FY] [Algebra K FX]

/-- Presentation-level Place equality from genuine native naturality and
actual supplied-field valuation transport. No Scheme or concrete field
record is unfolded inside this abstract theorem. -/
theorem place_eq_restrict_of_comaps [Algebra F E] [Algebra.IsIntegral F E] [IsScalarTower K F E]
    (τ : FY →ₐ[K] FX) (e : F ≃ₐ[K] FY) (g : E ≃ₐ[K] FX)
    (V : Place K FX) (W : Place K FY) (v : Place K E) (w : Place K F)
    (hnative : W.toValuationSubring=V.toValuationSubring.comap τ.toRingHom)
    (he : w.toValuationSubring=W.toValuationSubring.comap e.toRingHom)
    (hg : v.toValuationSubring=V.toValuationSubring.comap g.toRingHom)
    (hcomm : τ.toRingHom.comp e.toRingHom=g.toRingHom.comp (algebraMap F E)) :
    w=v.restrict F := by
  apply Place.ext
  change w.toValuationSubring=v.toValuationSubring.comap (algebraMap F E)
  exact he.trans ((valuation_comap_transport τ.toRingHom e.toRingHom g.toRingHom
    (algebraMap F E) V.toValuationSubring W.toValuationSubring hnative hcomm).trans
      (congrArg (fun A : ValuationSubring E => A.comap (algebraMap F E)) hg).symm)

section SameScheme
variable {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 c] [IsProper c]

/-- Definitional valuation transport along the SUPPLIED field presentation.
Its proof is compiled with e abstract, rather than normalizing a later deep
concrete radical-field equivalence. -/
theorem point_valuation (e : letI := fieldAlgebra c; F ≃ₐ[K] X.functionField)
    (p : RationalPoint c) :
    letI := fieldAlgebra c
    (pointEquivRationalPlace_of_fieldEquiv c e p).val.toValuationSubring=
      (pointEquivRationalPlace c p).val.toValuationSubring.comap e.toRingHom := rfl
end SameScheme

#print axioms valuation_comap_transport
#print axioms place_eq_restrict_of_comaps
#print axioms point_valuation
end FourCorner.AbstractPresentationPlaceTransport
