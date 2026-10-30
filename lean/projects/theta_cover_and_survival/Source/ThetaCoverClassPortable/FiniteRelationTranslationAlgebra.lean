import ThetaCoverClassPortable.FiniteRelationTranslation

namespace FourCorner.FiniteRelationQuotient
open CategoryTheory
noncomputable section
universe u
variable {A B : Type u} [CommRing A] [CommRing B]

abbrev sourcePairAlgebra (s : A →+* B) : Algebra B (sourcePair s) := (sourceLeft s).hom.toAlgebra
abbrev composableAlgebra (s t : A →+* B) : Algebra B (composableObject s t) := (pairLeft s t).hom.toAlgebra

/-- The previously proved native translation is an ACTUAL B-algebra
isomorphism for the original first projection on both base changes. -/
def translationAlgEquiv (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    letI := sourcePairAlgebra s
    letI := composableAlgebra s t
    sourcePair s ≃ₐ[B] composableObject s t := by
  letI := sourcePairAlgebra s
  letI := composableAlgebra s t
  apply AlgEquiv.ofRingEquiv (f:=(translationIso s t hgen heq).commRingCatIsoToRingEquiv)
  intro b
  exact congrArg (fun f : CommRingCat.of B ⟶ composableObject s t=>f.hom b)
    (translation_over_base s t hgen heq)

/-- Target-coordinate preservation on every actual ring element, not
merely a field-point or reduced-support identity. -/
theorem translation_target_element (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) (a : A) :
    translationAlgEquiv s t hgen heq ((sourceRight s).hom (t a))=(pairRight s t).hom (t a) := by
  exact congrArg (fun f : CommRingCat.of A ⟶ composableObject s t=>f.hom a)
    (translation_target_coordinate s t hgen heq)

/-- Actual multiplication operators by the original target coordinate
intertwine under the proved OVER-B translation. No intertwining premise
is added for subsequent norm/characteristic-polynomial arguments. -/
theorem translation_multiplication (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) (a : A) :
    letI := sourcePairAlgebra s
    letI := composableAlgebra s t
    (translationAlgEquiv s t hgen heq).toLinearMap.comp (LinearMap.mulLeft B ((sourceRight s).hom (t a)))=
      (LinearMap.mulLeft B ((pairRight s t).hom (t a))).comp (translationAlgEquiv s t hgen heq).toLinearMap := by
  letI := sourcePairAlgebra s
  letI := composableAlgebra s t
  apply LinearMap.ext
  intro x
  change translationAlgEquiv s t hgen heq ((sourceRight s).hom (t a)*x)=
    (pairRight s t).hom (t a)*translationAlgEquiv s t hgen heq x
  rw [map_mul,translation_target_element]

#print axioms translationAlgEquiv
#print axioms translation_target_element
#print axioms translation_multiplication
end
end FourCorner.FiniteRelationQuotient
