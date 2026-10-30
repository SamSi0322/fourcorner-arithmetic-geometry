import ThetaCoverClassPortable.FiniteRelationComposition

namespace FourCorner.FiniteRelationQuotient
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u
variable {A B : Type u} [CommRing A] [CommRing B]

/-- The actual coordinate ring of composable arrows: the native categorical
pushout of t:A→B and s:A→B, not a newly postulated tensor or fibre product. -/
abbrev composableObject (s t : A →+* B) : CommRingCat.{u} :=
  pushout (CommRingCat.ofHom t) (CommRingCat.ofHom s)

theorem composable_condition (s t : A →+* B) :
    (pushout.inl (CommRingCat.ofHom t) (CommRingCat.ofHom s)).hom.comp t=
      (pushout.inr (CommRingCat.ofHom t) (CommRingCat.ofHom s)).hom.comp s :=
  congrArg CommRingCat.Hom.hom (pushout.condition (f:=CommRingCat.ofHom t) (g:=CommRingCat.ofHom s))

/-- The all-ring transitivity hypothesis constructs the ACTUAL ring
co-composition B→O(R×X R), using that pushout itself as the test ring. -/
def comultiplication (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    CommRingCat.of B ⟶ composableObject s t :=
  CommRingCat.ofHom (compose s t hgen heq
    (pushout.inl (CommRingCat.ofHom t) (CommRingCat.ofHom s)).hom
    (pushout.inr (CommRingCat.ofHom t) (CommRingCat.ofHom s)).hom (composable_condition s t))

theorem comultiplication_source (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    CommRingCat.ofHom s ≫ comultiplication s t hgen heq=
      CommRingCat.ofHom s ≫ pushout.inl (CommRingCat.ofHom t) (CommRingCat.ofHom s) := by
  apply CommRingCat.hom_ext
  exact compose_source s t hgen heq _ _ (composable_condition s t)

theorem comultiplication_target (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    CommRingCat.ofHom t ≫ comultiplication s t hgen heq=
      CommRingCat.ofHom t ≫ pushout.inr (CommRingCat.ofHom t) (CommRingCat.ofHom s) := by
  apply CommRingCat.hom_ext
  exact compose_target s t hgen heq _ _ (composable_condition s t)

/-- Co-composition is uniquely determined as a native ring-category map
by the actual source and target faces. -/
theorem comultiplication_unique (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (d : CommRingCat.of B ⟶ composableObject s t)
    (hs : CommRingCat.ofHom s ≫ d=CommRingCat.ofHom s ≫ pushout.inl _ _)
    (ht : CommRingCat.ofHom t ≫ d=CommRingCat.ofHom t ≫ pushout.inr _ _) :
    d=comultiplication s t hgen heq := by
  apply CommRingCat.hom_ext
  apply joint_ext s t hgen
  · exact (congrArg CommRingCat.Hom.hom hs).trans (compose_source s t hgen heq _ _ (composable_condition s t)).symm
  · exact (congrArg CommRingCat.Hom.hom ht).trans (compose_target s t hgen heq _ _ (composable_condition s t)).symm

#print axioms comultiplication
#print axioms comultiplication_source
#print axioms comultiplication_target
#print axioms comultiplication_unique
end
end FourCorner.FiniteRelationQuotient
