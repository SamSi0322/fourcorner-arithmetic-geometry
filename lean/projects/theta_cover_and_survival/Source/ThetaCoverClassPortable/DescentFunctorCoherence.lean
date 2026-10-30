import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Functor.Category

set_option autoImplicit false
open CategoryTheory
universe u₀ u₁ u₂ u₃ u₄ u₅ v₀ v₁ v₂ v₃ v₄ v₅
namespace FourCorner.DescentFunctorCoherence

variable {A : Type u₀} {B : Type u₁} {C : Type u₂} {D : Type u₃} {E : Type u₄} {F : Type u₅}
  [Category.{v₀} A] [Category.{v₁} B] [Category.{v₂} C] [Category.{v₃} D] [Category.{v₄} E] [Category.{v₅} F]

/-- A naturality square in abstract categories, kept opaque before the
large Scheme.Modules functors are instantiated. -/
theorem map_map_conjugation
    (L : A ⥤ B) (P : B ⥤ C) (H : C ⥤ F) (Q : B ⥤ E)
    (T : A ⥤ D) (U : D ⥤ E) (R : E ⥤ F) (V : D ⥤ F)
    (β : P ⋙ H ≅ Q ⋙ R) (α : L ⋙ Q ≅ T ⋙ U) (γ : U ⋙ R ≅ V)
    {M₁ M₂ : A} {Z : D} {Z' : E}
    (e₁ : T.obj M₁ ≅ Z) (e₂ : T.obj M₂ ≅ Z) (d : U.obj Z ≅ Z')
    (φ : L.obj M₁ ⟶ L.obj M₂)
    (hφ : Q.map φ = (α.app M₁ ≪≫ U.mapIso e₁ ≪≫ d).hom ≫
      (α.app M₂ ≪≫ U.mapIso e₂ ≪≫ d).inv) :
    H.map (P.map φ) =
      (β.app (L.obj M₁) ≪≫ R.mapIso (α.app M₁) ≪≫ γ.app (T.obj M₁)).hom ≫
      V.map (e₁.hom ≫ e₂.inv) ≫
      (β.app (L.obj M₂) ≪≫ R.mapIso (α.app M₂) ≪≫ γ.app (T.obj M₂)).inv := by
  have n1 := (NatIso.naturality_2 β φ).symm
  have n2 := (NatIso.naturality_2 γ (e₁.hom ≫ e₂.inv)).symm
  dsimp only [Functor.comp_obj,Functor.comp_map] at n1 n2
  rw [n1,hφ]
  simp only [Iso.trans_hom,Iso.trans_inv,Iso.app_hom,Iso.app_inv,Functor.mapIso_hom,
    Functor.mapIso_inv,Functor.map_comp,Category.assoc,Iso.hom_inv_id_assoc]
  simp only [Functor.map_comp,Category.assoc] at n2
  rw [reassoc_of% n2]

end FourCorner.DescentFunctorCoherence
