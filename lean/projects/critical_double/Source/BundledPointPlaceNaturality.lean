import SmoothProperPlaceNaturality

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u
namespace FourCorner.BundledPointPlaceNaturality
open SmoothProperClosedPointPlaces SmoothProperRationalPointPlaces SmoothProperPlaceNaturality
variable {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K))

def inducedAlgebra (τ : letI := fieldAlgebra cX;letI := fieldAlgebra cY;
    Y.functionField →ₐ[K] X.functionField) : Algebra Y.functionField X.functionField := by
  letI := fieldAlgebra cX
  letI := fieldAlgebra cY
  exact τ.toRingHom.toAlgebra

theorem inducedTower (τ : letI := fieldAlgebra cX;letI := fieldAlgebra cY;
    Y.functionField →ₐ[K] X.functionField) :
    letI := fieldAlgebra cX;letI := fieldAlgebra cY;letI := inducedAlgebra cX cY τ
    IsScalarTower K Y.functionField X.functionField := by
  letI := fieldAlgebra cX
  letI := fieldAlgebra cY
  letI := inducedAlgebra cX cY τ
  exact IsScalarTower.of_algebraMap_eq (fun a => (τ.commutes a).symm)

variable [SmoothOfRelativeDimension 1 cX] [SmoothOfRelativeDimension 1 cY] [IsProper cX] [IsProper cY]

/-- Exact valuation-ring naturality for the GIVEN base-compatible native
pullback τ. Its relative algebra and scalar tower are constructed from τ. -/
theorem point_valuation_comap_of_pullback
    (τ : letI := fieldAlgebra cX;letI := fieldAlgebra cY;Y.functionField →ₐ[K] X.functionField)
    (hfin : letI := inducedAlgebra cX cY τ;FiniteDimensional Y.functionField X.functionField)
    (π : X ⟶ Y) (hπ : π ≫ cY=cX)
    (hgeneric : letI := fieldAlgebra cX;letI := fieldAlgebra cY
      X.fromSpecStalk (genericPoint X) ≫ π=Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
        Y.fromSpecStalk (genericPoint Y)) (p : RationalPoint cX) :
    letI := fieldAlgebra cX;letI := fieldAlgebra cY
    ((pointEquivRationalPlace cY (mappedPoint cX cY π hπ p)).val).toValuationSubring=
      ((pointEquivRationalPlace cX p).val).toValuationSubring.comap τ.toRingHom := by
  letI := fieldAlgebra cX
  letI := fieldAlgebra cY
  letI := inducedAlgebra cX cY τ
  letI : FiniteDimensional Y.functionField X.functionField := hfin
  exact point_valuation_comap cX cY (inducedTower cX cY τ) π hπ hgeneric p

/-- Exact actual Place restriction, with all native field instances induced
by the supplied τ, and every genuine Scheme K-section retained. -/
theorem point_place_restrict_of_pullback
    (τ : letI := fieldAlgebra cX;letI := fieldAlgebra cY;Y.functionField →ₐ[K] X.functionField)
    (hfin : letI := inducedAlgebra cX cY τ;FiniteDimensional Y.functionField X.functionField)
    (π : X ⟶ Y) (hπ : π ≫ cY=cX)
    (hgeneric : letI := fieldAlgebra cX;letI := fieldAlgebra cY
      X.fromSpecStalk (genericPoint X) ≫ π=Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
        Y.fromSpecStalk (genericPoint Y)) (p : RationalPoint cX) :
    letI := fieldAlgebra cX;letI := fieldAlgebra cY;letI := inducedAlgebra cX cY τ
    letI := inducedTower cX cY τ;letI : FiniteDimensional Y.functionField X.functionField := hfin
    (pointEquivRationalPlace cX p).val.restrict Y.functionField=
      (pointEquivRationalPlace cY (mappedPoint cX cY π hπ p)).val := by
  letI := fieldAlgebra cX
  letI := fieldAlgebra cY
  letI := inducedAlgebra cX cY τ
  letI : FiniteDimensional Y.functionField X.functionField := hfin
  exact point_place_restrict cX cY (inducedTower cX cY τ) π hπ hgeneric p

#print axioms inducedAlgebra
#print axioms inducedTower
#print axioms point_valuation_comap_of_pullback
#print axioms point_place_restrict_of_pullback
end FourCorner.BundledPointPlaceNaturality
