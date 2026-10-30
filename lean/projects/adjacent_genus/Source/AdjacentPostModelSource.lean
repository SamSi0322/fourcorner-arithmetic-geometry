import AdjacentPostAffineSmooth

noncomputable section
namespace FourCorner.AdjacentPostModelSource
open CategoryTheory AlgebraicGeometry AlgebraicCurve Slot03HighAdjacentProjective Slot03Adjacent
universe u
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]

/-- The literal affine comparison respects the original coefficient field. -/
def affineLiteralAlgEquiv (c : K) : affineRing c ≃ₐ[K] literalR c :=
  { affineLiteralEquiv c with commutes' := affineToLiteral_aC c }

def affineLiteralSchemeIso (c : K) : Spec (.of (affineRing c)) ≅ Spec (.of (literalR c)) :=
  Scheme.Spec.mapIso ((affineLiteralAlgEquiv c).symm.toRingEquiv.toCommRingCatIso.op)

theorem affineLiteralSchemeIso_over (c : K) :
    (affineLiteralSchemeIso c).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K (literalR c))) =
      Spec.map (CommRingCat.ofHom (algebraMap K (affineRing c))) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact (affineLiteralAlgEquiv c).symm.commutes a

/-- The actual literal conic/two-AdjoinRoot source is a smooth affine curve. -/
theorem literal_smooth (c : K) (h : AdjacentPolynomials.Admissible c) :
    SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap K (literalR c)))) := by
  have hs : SmoothOfRelativeDimension 1 ((affineLiteralSchemeIso c).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (literalR c)))) := by
    rw [affineLiteralSchemeIso_over]
    exact AdjacentPostSmooth.affine_smooth c h
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1)
    (affineLiteralSchemeIso c).hom _).mp hs

/-- This is the existing integral-closure-chart model, with its original field algebra fixed. -/
abbrev canonicalScheme (c : K) := (model c).C

def canonicalFieldEquiv (c : K) : adjacentField c ≃+* (canonicalScheme c).functionField :=
  (model c).ffEquiv

def literalGenericFieldEquiv (c : K) (h : AdjacentPolynomials.Admissible c) :
    letI := AdjacentCoordinateAlgebra.coordinateRing_isDomain c h
    (Spec (.of (literalR c))).functionField ≃+* (canonicalScheme c).functionField := by
  letI := AdjacentCoordinateAlgebra.coordinateRing_isDomain c h
  letI : Algebra (literalR c) (Spec (.of (literalR c))).functionField :=
    instAlgebraCarrierFunctionFieldSpec (.of (literalR c))
  haveI : IsFractionRing (literalR c) (Spec (.of (literalR c))).functionField :=
    functionField_isFractionRing_of_affine (.of (literalR c))
  let e : FractionRing (literalR c) ≃ₐ[literalR c] (Spec (.of (literalR c))).functionField :=
    FractionRing.algEquiv (literalR c) (Spec (.of (literalR c))).functionField
  exact e.symm.toRingEquiv.trans ((literalFieldRingEquiv c h.c_ne_zero h).trans (canonicalFieldEquiv c))

/-- The true generic-point morphism into the proper normalized-chart model. -/
def literalGenericMap (c : K) (h : AdjacentPolynomials.Admissible c) :
    letI := AdjacentCoordinateAlgebra.coordinateRing_isDomain c h
    Spec (Spec (.of (literalR c))).functionField ⟶ canonicalScheme c := by
  letI := AdjacentCoordinateAlgebra.coordinateRing_isDomain c h
  exact Spec.map (CommRingCat.ofHom (literalGenericFieldEquiv c h).symm.toRingHom) ≫
    (canonicalScheme c).fromSpecStalk (genericPoint (canonicalScheme c))

#print axioms affineLiteralAlgEquiv
#print axioms affineLiteralSchemeIso_over
#print axioms literal_smooth
#print axioms literalGenericFieldEquiv
#print axioms literalGenericMap
end FourCorner.AdjacentPostModelSource
