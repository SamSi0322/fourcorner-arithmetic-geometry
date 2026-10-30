import ThetaCoverClassPortable.Slot02QuotientMap
import ThetaCoverClassPortable.geometry.ProjectiveClosedImmersion

/-!
Compatibility check with the genuine projective-spectrum map. This is the
generic homogeneous-ideal quotient construction, not a particular curve model.
-/

noncomputable section

namespace FourCorner.ProjectiveQuotient

open AlgebraicGeometry HomogeneousIdealQuotientGrading

universe u
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] (J : HomogeneousIdeal 𝒜)

/-- The actual projective map induced by the homogeneous quotient. -/
def quotientMap : (Proj (quotGrading 𝒜 J.toIdeal)).Hom (Proj 𝒜) :=
  Proj.map (quotientGradedMap 𝒜 J)
    (ProjectiveClosedImmersion.irrelevant_le_map_of_surjective
      (quotientGradedMap 𝒜 J) (quotientGradedMap_surjective 𝒜 J))

/-- A homogeneous ideal quotient gives a genuine closed immersion of projective schemes. -/
theorem quotientMap_isClosedImmersion : IsClosedImmersion (quotientMap 𝒜 J) :=
  ProjectiveClosedImmersion.isClosedImmersion_map_of_surjective
    (quotientGradedMap 𝒜 J) (quotientGradedMap_surjective 𝒜 J)

end FourCorner.ProjectiveQuotient

#print axioms FourCorner.ProjectiveQuotient.quotientMap
#print axioms FourCorner.ProjectiveQuotient.quotientMap_isClosedImmersion
