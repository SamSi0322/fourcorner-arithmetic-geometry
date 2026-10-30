import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_tilde_pullbackSpecIso_unit
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.tilde

theorem pullbackSpecIso_hom_app_top_unit_toOpen {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (M : ModuleCat.{u} R) (m : M) :
    ((tilde.pullbackSpecIso φ M).hom.app ((Spec.map φ) ⁻¹ᵁ ⊤))
      ((((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)).app ⊤)
        (tilde.toOpen M ⊤ m : Γ(tilde M, ⊤))) =
    (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ((Spec.map φ) ⁻¹ᵁ ⊤)
      ((1 : S) ⊗ₜ[R] m) : Γ(tilde ((ModuleCat.extendScalars φ.hom).obj M), (Spec.map φ) ⁻¹ᵁ ⊤)) := by
  have h := congrArg (fun f => f.hom m) (tilde.pullbackSpecIso_unit φ M)
  exact h
#print axioms pullbackSpecIso_hom_app_top_unit_toOpen
end AlgebraicGeometry.tilde
