import ThetaCoverClassPortable.TildeComponentFormal
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite

namespace AlgebraicGeometry.tilde
universe u
attribute [local irreducible] tilde.functorCompPullbackSpecIso tilde.pullbackSpecIso
  Scheme.Modules.pullbackComp Scheme.Modules.pullbackCongr ModuleCat.extendScalarsComp
/-- Composition coherence for the actual adjunction-defined tilde/pullback
comparison. Both sides retain the literal pullback and scalar-extension
comparison maps used by affine faithfully-flat descent. -/
theorem pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom
    {R S T : CommRingCat.{u}} (φ : R ⟶ S) (δ : S ⟶ T) (M : ModuleCat.{u} R) :
    (Scheme.Modules.pullback (Spec.map δ)).map (tilde.pullbackSpecIso φ M).hom ≫
      (tilde.pullbackSpecIso δ ((ModuleCat.extendScalars φ.hom).obj M)).hom =
    (Scheme.Modules.pullbackComp (Spec.map δ) (Spec.map φ)).hom.app (tilde M) ≫
      (Scheme.Modules.pullbackCongr (Spec.map_comp φ δ).symm).hom.app (tilde M) ≫
      (tilde.pullbackSpecIso (φ≫δ) M).hom ≫
      tilde.map ((ModuleCat.extendScalarsComp φ.hom δ.hom).hom.app M) := by
  exact FourCorner.TildeComposition.component_of_nat φ δ M
    (tilde.functorCompPullbackSpecIso φ) (tilde.functorCompPullbackSpecIso δ)
    (tilde.functorCompPullbackSpecIso (φ≫δ))
    (Scheme.Modules.pullbackComp (Spec.map δ) (Spec.map φ))
    (Scheme.Modules.pullbackCongr (Spec.map_comp φ δ).symm)
    (ModuleCat.extendScalarsComp φ.hom δ.hom)
    (tilde.pullbackSpecIso φ M) (tilde.pullbackSpecIso δ ((ModuleCat.extendScalars φ.hom).obj M))
    (tilde.pullbackSpecIso (φ≫δ) M)
    (tilde.functorCompPullbackSpecIso_app φ M)
    (tilde.functorCompPullbackSpecIso_app δ ((ModuleCat.extendScalars φ.hom).obj M))
    (tilde.functorCompPullbackSpecIso_app (φ≫δ) M)
    (FourCorner.TildeComposition.beta_path_eq_composite φ δ)
#print axioms pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom
end AlgebraicGeometry.tilde
