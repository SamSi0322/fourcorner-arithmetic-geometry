import ThetaCoverClassPortable.RigidifiedFFIsoCoherence
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.Scheme.Modules
universe u
namespace FourCorner.RigidifiedFFIsoHeadFormal
variable {X X₀ X₁ X₂ Y Y₀ Y₁ Y₂ : Scheme.{u}}

theorem solution
    (a₁ : X₀ ⟶ X₁) (b₁ : X₁ ⟶ X) (a₂ : X₀ ⟶ X₂) (b₂ : X₂ ⟶ X) (d : X₀ ⟶ X)
    (e₁ : a₁ ≫ b₁ = d) (e₂ : a₂ ≫ b₂ = d)
    (s₀ : Y₀ ⟶ X₀) (s₁ : Y₁ ⟶ X₁) (s₂ : Y₂ ⟶ X₂) (s : Y ⟶ X)
    (r₁ : Y₀ ⟶ Y₁) (p₁ : Y₁ ⟶ Y) (r₂ : Y₀ ⟶ Y₂) (p₂ : Y₂ ⟶ Y) (m : Y₀ ⟶ Y)
    (G₁ : r₁ ≫ p₁ = m) (G₂ : r₂ ≫ p₂ = m)
    (E₁ : s₀ ≫ a₁ = r₁ ≫ s₁) (F₁ : s₁ ≫ b₁ = p₁ ≫ s)
    (E₂ : s₀ ≫ a₂ = r₂ ≫ s₂) (F₂ : s₂ ≫ b₂ = p₂ ≫ s)
    (M : X.Modules)
    (raw : (Scheme.Modules.pullback a₁).obj ((Scheme.Modules.pullback b₁).obj M) ⟶
      (Scheme.Modules.pullback a₂).obj ((Scheme.Modules.pullback b₂).obj M))
    (l₁ : (Scheme.Modules.pullback s₀).obj
        ((Scheme.Modules.pullback a₁).obj ((Scheme.Modules.pullback b₁).obj M)) ≅
      (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback s).obj M))
    (l₂ : (Scheme.Modules.pullback s₀).obj
        ((Scheme.Modules.pullback a₂).obj ((Scheme.Modules.pullback b₂).obj M)) ≅
      (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback s).obj M))
    (hraw : raw = (Scheme.Modules.pullbackComp a₁ b₁).hom.app M ≫
      (Scheme.Modules.pullbackCongr e₁).hom.app M ≫
      (Scheme.Modules.pullbackCongr e₂.symm).hom.app M ≫
      (Scheme.Modules.pullbackComp a₂ b₂).inv.app M)
    (hl₁ : l₁ = (sqIso E₁).app ((Scheme.Modules.pullback b₁).obj M) ≪≫
      (Scheme.Modules.pullback r₁).mapIso ((sqIso F₁).app M) ≪≫
      (τ r₁ p₁ m G₁).app ((Scheme.Modules.pullback s).obj M))
    (hl₂ : l₂ = (sqIso E₂).app ((Scheme.Modules.pullback b₂).obj M) ≪≫
      (Scheme.Modules.pullback r₂).mapIso ((sqIso F₂).app M) ≪≫
      (τ r₂ p₂ m G₂).app ((Scheme.Modules.pullback s).obj M)) :
    (Scheme.Modules.pullback s₀).map raw ≫ l₂.hom = l₁.hom := by
  rw [hraw,hl₁,hl₂]
  simp only [Iso.trans_hom,Iso.app_hom,Functor.mapIso_hom,Category.assoc]
  exact head' a₁ b₁ a₂ b₂ d e₁ e₂ s₀ s₁ s₂ s r₁ p₁ r₂ p₂ m G₁ G₂ E₁ F₁ E₂ F₂ M

end FourCorner.RigidifiedFFIsoHeadFormal
