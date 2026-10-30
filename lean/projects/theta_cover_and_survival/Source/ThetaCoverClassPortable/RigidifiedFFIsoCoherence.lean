import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.DescentDataPrimeComputation
import ThetaCoverClassPortable.DescentDataPrimeIsoLifting
import ThetaCoverClassPortable.DescentFunctorCoherence
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_iso_map_pullback_rigSection_comp_eq
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pseudofunctor Surjective Scheme.Modules.pullback Scheme.Pullback.range_fst Spec Scheme Flat Scheme.Modules.pullbackCongr flat_and_surjective_SpecMap_iff Scheme.Modules IsAffineHom Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso RelPicard.RigidifiedLineBundle Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom RelPicard.RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pseudofunctor ringCatSheaf Modules.pullback Γ Pullback.range_fst Modules.pullbackCongr Modules Modules.pullbackComp Modules.IsInvertible Modules.pullbackUnitIso TwoAffineOpenCover TwoAffineOpenCover.specMap TwoAffineOpenCover.algebraOfHom Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective Modules.pullbackComp_pullbackCongr_pasteSquares_app"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pseudofunctor pullback pullbackCongr pullbackComp IsInvertible pullbackUnitIso IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective pullbackComp_pullbackCongr_pasteSquares_app"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X₀ X₁ X₂ X₃ : Scheme.{u}}

noncomputable def τ (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) : pullback g ⋙ pullback f ≅ pullback m :=
  pullbackComp f g ≪≫ pullbackCongr e

theorem τ_hom_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) (M : X₂.Modules) :
    (τ f g m e).hom.app M = (pullbackComp f g).hom.app M ≫ eqToHom (by rw [e]) := by
  subst e
  simp [τ, pullbackCongr]

theorem τ_inv_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) (M : X₂.Modules) :
    (τ f g m e).inv.app M = eqToHom (by rw [e]) ≫ (pullbackComp f g).inv.app M := by
  subst e
  simp [τ, pullbackCongr]

noncomputable def sqIso {W X Y Z : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z}
    (e : f ≫ g = h ≫ k) : pullback g ⋙ pullback f ≅ pullback k ⋙ pullback h :=
  pullbackComp f g ≪≫ pullbackCongr e ≪≫ (pullbackComp h k).symm

theorem sqIso_hom_app {W X Y Z : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z}
    (e : f ≫ g = h ≫ k) (M : Z.Modules) :
    (sqIso e).hom.app M = (τ f g (h ≫ k) e).hom.app M ≫ (τ h k (h ≫ k) rfl).inv.app M := by
  simp only [sqIso, τ, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, NatTrans.comp_app, pullbackCongr, eqToIso_refl,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp,
    Category.comp_id, Category.assoc]

section Route

variable {X X₀' X₁' Y Y₀ Y₁ : Scheme.{u}}
  (a : X₀' ⟶ X₁') (b : X₁' ⟶ X) (d : X₀' ⟶ X) (e : a ≫ b = d)
  (s₀ : Y₀ ⟶ X₀') (s₁ : Y₁ ⟶ X₁') (s : Y ⟶ X)
  (r : Y₀ ⟶ Y₁) (p : Y₁ ⟶ Y) (m : Y₀ ⟶ Y) (G : r ≫ p = m)
  (E : s₀ ≫ a = r ≫ s₁) (F : s₁ ≫ b = p ≫ s)

include e G E F in
theorem route_comm : s₀ ≫ d = m ≫ s := by
  rw [← e, ← Category.assoc, E, Category.assoc, F, ← Category.assoc, G]

theorem route (M : X.Modules) :
    (sqIso E).hom.app ((pullback b).obj M) ≫ (pullback r).map ((sqIso F).hom.app M) ≫
        (τ r p m G).hom.app ((pullback s).obj M) =
      (pullback s₀).map ((τ a b d e).hom.app M) ≫
        (τ s₀ d (m ≫ s) (route_comm a b d e s₀ s₁ s r p m G E F)).hom.app M ≫
          (τ m s (m ≫ s) rfl).inv.app M := by
  exact (AlgebraicGeometry.Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app a b d e s₀ s₁ s r p m G E F
    (route_comm a b d e s₀ s₁ s r p m G E F) M).trans
    (congrArg (fun k => (pullback s₀).map ((τ a b d e).hom.app M) ≫ k)
      (sqIso_hom_app (route_comm a b d e s₀ s₁ s r p m G E F) M))

end Route

section Head

variable {X X₀' X₁' X₂' Y Y₀ Y₁ Y₂ : Scheme.{u}}
  (a₁ : X₀' ⟶ X₁') (b₁ : X₁' ⟶ X) (a₂ : X₀' ⟶ X₂') (b₂ : X₂' ⟶ X) (d : X₀' ⟶ X)
  (e₁ : a₁ ≫ b₁ = d) (e₂ : a₂ ≫ b₂ = d)
  (s₀ : Y₀ ⟶ X₀') (s₁ : Y₁ ⟶ X₁') (s₂ : Y₂ ⟶ X₂') (s : Y ⟶ X)
  (r₁ : Y₀ ⟶ Y₁) (p₁ : Y₁ ⟶ Y) (r₂ : Y₀ ⟶ Y₂) (p₂ : Y₂ ⟶ Y) (m : Y₀ ⟶ Y)
  (G₁ : r₁ ≫ p₁ = m) (G₂ : r₂ ≫ p₂ = m)
  (E₁ : s₀ ≫ a₁ = r₁ ≫ s₁) (F₁ : s₁ ≫ b₁ = p₁ ≫ s) (E₂ : s₀ ≫ a₂ = r₂ ≫ s₂) (F₂ : s₂ ≫ b₂ = p₂ ≫ s)

theorem head (M : X.Modules) :
    (pullback s₀).map ((τ a₁ b₁ d e₁).hom.app M ≫ (τ a₂ b₂ d e₂).inv.app M) ≫
      (sqIso E₂).hom.app ((pullback b₂).obj M) ≫ (pullback r₂).map ((sqIso F₂).hom.app M) ≫
        (τ r₂ p₂ m G₂).hom.app ((pullback s).obj M) =
      (sqIso E₁).hom.app ((pullback b₁).obj M) ≫ (pullback r₁).map ((sqIso F₁).hom.app M) ≫
        (τ r₁ p₁ m G₁).hom.app ((pullback s).obj M) := by
  have h₁ := route a₁ b₁ d e₁ s₀ s₁ s r₁ p₁ m G₁ E₁ F₁ M
  have h₂ := route a₂ b₂ d e₂ s₀ s₂ s r₂ p₂ m G₂ E₂ F₂ M
  have h₂' := (Iso.inv_comp_eq ((pullback s₀).mapIso ((τ a₂ b₂ d e₂).app M))).mpr h₂
  simp only [Functor.map_comp, Category.assoc]
  exact (congrArg (fun k => (pullback s₀).map ((τ a₁ b₁ d e₁).hom.app M) ≫ k) h₂').trans h₁.symm

end Head

section HeadRaw

variable {X X₀' X₁' X₂' : Scheme.{u}}
  (a₁ : X₀' ⟶ X₁') (b₁ : X₁' ⟶ X) (a₂ : X₀' ⟶ X₂') (b₂ : X₂' ⟶ X) (d : X₀' ⟶ X)
  (e₁ : a₁ ≫ b₁ = d) (e₂ : a₂ ≫ b₂ = d)

theorem τ_hom_app_comp_τ_inv_app (M : X.Modules) :
    (τ a₁ b₁ d e₁).hom.app M ≫ (τ a₂ b₂ d e₂).inv.app M =
      (pullbackComp a₁ b₁).hom.app M ≫ (pullbackCongr e₁).hom.app M ≫ (pullbackCongr e₂.symm).hom.app M ≫
        (pullbackComp a₂ b₂).inv.app M := by
  subst e₁
  simp [τ, pullbackCongr]

variable {Y Y₀ Y₁ Y₂ : Scheme.{u}}
  (s₀ : Y₀ ⟶ X₀') (s₁ : Y₁ ⟶ X₁') (s₂ : Y₂ ⟶ X₂') (s : Y ⟶ X)
  (r₁ : Y₀ ⟶ Y₁) (p₁ : Y₁ ⟶ Y) (r₂ : Y₀ ⟶ Y₂) (p₂ : Y₂ ⟶ Y) (m : Y₀ ⟶ Y)
  (G₁ : r₁ ≫ p₁ = m) (G₂ : r₂ ≫ p₂ = m)
  (E₁ : s₀ ≫ a₁ = r₁ ≫ s₁) (F₁ : s₁ ≫ b₁ = p₁ ≫ s) (E₂ : s₀ ≫ a₂ = r₂ ≫ s₂) (F₂ : s₂ ≫ b₂ = p₂ ≫ s)

theorem head' (M : X.Modules) :
    (pullback s₀).map ((pullbackComp a₁ b₁).hom.app M ≫ (pullbackCongr e₁).hom.app M ≫
        (pullbackCongr e₂.symm).hom.app M ≫ (pullbackComp a₂ b₂).inv.app M) ≫
      (sqIso E₂).hom.app ((pullback b₂).obj M) ≫ (pullback r₂).map ((sqIso F₂).hom.app M) ≫
        (τ r₂ p₂ m G₂).hom.app ((pullback s).obj M) =
      (sqIso E₁).hom.app ((pullback b₁).obj M) ≫ (pullback r₁).map ((sqIso F₁).hom.app M) ≫
        (τ r₁ p₁ m G₁).hom.app ((pullback s).obj M) := by
  have h := head a₁ b₁ a₂ b₂ d e₁ e₂ s₀ s₁ s₂ s r₁ p₁ r₂ p₂ m G₁ G₂ E₁ F₁ E₂ F₂ M
  rw [τ_hom_app_comp_τ_inv_app] at h
  exact h

end HeadRaw

end AlgebraicGeometry.Scheme.Modules
end P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections
