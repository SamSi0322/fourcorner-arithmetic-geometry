import ThetaCoverClassPortable.P2M.Sol.S_AlgebraicGeometry_AffineLimit_presheafULift_isOpenImmersion_and_isLocallySurjective_of_locallyOfFiniteType
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.AffineLimit

/-- Genuine all-test extension of finite-type cartesian local charts. The
sheaf/LFP/finite-type-chart inputs stay explicit; no actual Picard atlas is
assumed or constructed merely by this generic supporting theorem. -/
theorem presheafULift_isOpenImmersion_and_isLocallySurjective_of_locallyOfFiniteType
    (R : Type u) [CommRing R] (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u+1))
    (hG : Presieve.IsSheaf Scheme.zariskiTopology G.overTotal)
    (hsurj : IsLFPSurj G) (hinj : IsLFPInj G)
    {ι : Type u} (X : ι → Scheme.{u})
    (f : ∀i,uliftYoneda.{u+1}.obj (X i) ⟶ G.overTotal)
    (hX : ∀i,HomIsLFP (uliftYonedaEquiv (f i)).1)
    (H : ∀⦃T : Scheme.{u}⦄ (x : uliftYoneda.{u+1}.obj T ⟶ G.overTotal),
      LocallyOfFiniteType (uliftYonedaEquiv x).1 →
      ∃ (U : ι → T.Opens) (φ : ∀i,(↑(U i):Scheme.{u}) ⟶ X i),
        (⨆i,U i)=⊤ ∧ ∀i,
          uliftYoneda.{u+1}.map (φ i) ≫ f i=uliftYoneda.{u+1}.map (U i).ι ≫ x ∧
          ∀⦃T' : Scheme.{u}⦄ (ψ : T' ⟶ T) (φ' : T' ⟶ X i),
            LocallyOfFiniteType (ψ ≫ (uliftYonedaEquiv x).1) →
            uliftYoneda.{u+1}.map φ' ≫ f i=uliftYoneda.{u+1}.map ψ ≫ x →
            ∃χ:T' ⟶ ↑(U i),χ ≫ (U i).ι=ψ ∧χ ≫ φ i=φ') :
    (∀i,MorphismProperty.presheafULift.{u+1} @IsOpenImmersion (f i)) ∧
      Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) :=
  P2MW.S_AlgebraicGeometry_AffineLimit_presheafULift_isOpenImmersion_and_isLocallySurjective_of_locallyOfFiniteType.solution
    R G hG hsurj hinj X f hX H

end AlgebraicGeometry.AffineLimit
#print axioms AlgebraicGeometry.AffineLimit.presheafULift_isOpenImmersion_and_isLocallySurjective_of_locallyOfFiniteType
