import ThetaCoverClassPortable.TildeCompositionCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
namespace FourCorner.TildeComposition
universe u
lemma component_of_nat {R S T : CommRingCat.{u}} (φ : R ⟶ S) (δ : S ⟶ T) (M : ModuleCat.{u} R)
    (Bφ : tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅ ModuleCat.extendScalars φ.hom ⋙ tilde.functor S)
    (Bδ : tilde.functor S ⋙ Scheme.Modules.pullback (Spec.map δ) ≅ ModuleCat.extendScalars δ.hom ⋙ tilde.functor T)
    (Bφδ : tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map (φ≫δ)) ≅ ModuleCat.extendScalars (φ≫δ).hom ⋙ tilde.functor T)
    (c : Scheme.Modules.pullback (Spec.map φ) ⋙ Scheme.Modules.pullback (Spec.map δ) ≅
      Scheme.Modules.pullback (Spec.map δ≫Spec.map φ))
    (g : Scheme.Modules.pullback (Spec.map δ≫Spec.map φ) ≅ Scheme.Modules.pullback (Spec.map (φ≫δ)))
    (e : ModuleCat.extendScalars (φ≫δ).hom ≅ ModuleCat.extendScalars φ.hom ⋙ ModuleCat.extendScalars δ.hom)
    (bφ : (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ≅ tilde ((ModuleCat.extendScalars φ.hom).obj M))
    (bδ : (Scheme.Modules.pullback (Spec.map δ)).obj (tilde ((ModuleCat.extendScalars φ.hom).obj M)) ≅
      tilde ((ModuleCat.extendScalars δ.hom).obj ((ModuleCat.extendScalars φ.hom).obj M)))
    (bφδ : (Scheme.Modules.pullback (Spec.map (φ≫δ))).obj (tilde M) ≅ tilde ((ModuleCat.extendScalars (φ≫δ).hom).obj M))
    (hφ : Bφ.app M=bφ) (hδ : Bδ.app ((ModuleCat.extendScalars φ.hom).obj M)=bδ) (hφδ : Bφδ.app M=bφδ)
    (Hnat :
    whiskerRight Bφ.hom (Scheme.Modules.pullback (Spec.map δ)) ≫
       (Functor.associator (ModuleCat.extendScalars φ.hom) (tilde.functor S) (Scheme.Modules.pullback (Spec.map δ))).hom ≫
       whiskerLeft (ModuleCat.extendScalars φ.hom) Bδ.hom ≫
       (Functor.associator (ModuleCat.extendScalars φ.hom) (ModuleCat.extendScalars δ.hom) (tilde.functor T)).inv =
    (Functor.associator (tilde.functor R) (Scheme.Modules.pullback (Spec.map φ)) (Scheme.Modules.pullback (Spec.map δ))).hom ≫
       whiskerLeft (tilde.functor R)
        (c.hom ≫
          g.hom) ≫
       Bφδ.hom ≫
       whiskerRight e.hom (tilde.functor T)) :
    (Scheme.Modules.pullback (Spec.map δ)).map bφ.hom ≫ bδ.hom =
      c.hom.app (tilde M) ≫ g.hom.app (tilde M) ≫ bφδ.hom ≫ tilde.map (e.hom.app M) := by
  have H := congr_app Hnat M
  simp only [NatTrans.comp_app,Functor.whiskerRight_app,Functor.whiskerLeft_app,
    Functor.associator_hom_app,Functor.associator_inv_app,Functor.comp_obj,
    Category.id_comp,Category.comp_id,Category.assoc] at H
  rw [←Iso.app_hom Bφ M,←Iso.app_hom Bδ ((ModuleCat.extendScalars φ.hom).obj M),←Iso.app_hom Bφδ M,
    hφ,hδ,hφδ] at H
  simpa only [Functor.comp_obj,tilde.functor_obj,tilde.functor_map] using H
end FourCorner.TildeComposition
