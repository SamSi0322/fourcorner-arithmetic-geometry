import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesTildePullback
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.CompositionIso

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite

namespace FourCorner.TildeComposition
lemma conjugate_leftAdjointUniq_ofNatIsoRight
    {C D : Type*} [Category C] [Category D] {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : R₂ ≅ R₁) :
    conjugateEquiv b a (Adjunction.leftAdjointUniq a (b.ofNatIsoRight e)).hom = e.hom := by
  ext X
  simp only [conjugateEquiv_apply_app]
  rw [←Category.assoc,Adjunction.unit_leftAdjointUniq_hom_app]
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  rw [←e.hom.naturality,←Category.assoc,b.right_triangle_components,Category.id_comp]

lemma conjugate_inv_of_hom
    {C D : Type*} [Category C] [Category D] {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (eL : L₂≅L₁) (eR : R₁≅R₂)
    (h : conjugateEquiv a b eL.hom=eR.hom) : conjugateEquiv b a eL.inv=eR.inv := by
  have H := conjugateEquiv_comm a b eL.inv_hom_id
  rw [h] at H
  exact (Iso.hom_comp_eq_id eR).mp H

universe u
lemma conjugate_beta {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    conjugateEquiv ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R:=S)))
      ((tilde.adjunction (R:=R)).comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)))
      (tilde.functorCompPullbackSpecIso φ).hom = (Scheme.Modules.pushforwardSpecCompΓIso φ).inv :=
  conjugate_leftAdjointUniq_ofNatIsoRight _ _ _

lemma conjugate_pullbackComp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (f≫g))
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp (Scheme.Modules.pullbackPushforwardAdjunction f))
      (Scheme.Modules.pullbackComp f g).hom = (Scheme.Modules.pushforwardComp f g).inv :=
  conjugate_inv_of_hom _ _ (Scheme.Modules.pullbackComp f g).symm
    (Scheme.Modules.pushforwardComp f g) (Scheme.Modules.conjugateEquiv_pullbackComp_inv f g)

lemma conjugate_pullbackComp_hom_congr {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (hh : f≫g=h) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction h)
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp (Scheme.Modules.pullbackPushforwardAdjunction f))
      ((Scheme.Modules.pullbackComp f g).hom ≫ (Scheme.Modules.pullbackCongr hh).hom) =
      (Scheme.Modules.pushforwardCongr hh).inv ≫ (Scheme.Modules.pushforwardComp f g).inv := by
  subst h
  have hi : (Scheme.Modules.pushforwardCongr (rfl : f≫g=f≫g)).inv = 𝟙 _ := by
    apply NatTrans.ext
    funext N
    apply Scheme.Modules.hom_ext
    intro U
    ext x
    simp
  rw [hi]
  simpa [Scheme.Modules.pullbackCongr] using conjugate_pullbackComp_hom f g

lemma conjugate_extendScalarsComp {R S T : CommRingCat.{u}} (φ : R ⟶ S) (δ : S ⟶ T) :
    conjugateEquiv ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (ModuleCat.extendRestrictScalarsAdj δ.hom))
      (ModuleCat.extendRestrictScalarsAdj (φ≫δ).hom)
      (ModuleCat.extendScalarsComp φ.hom δ.hom).hom = (ModuleCat.restrictScalarsComp φ.hom δ.hom).inv := by
  simp [ModuleCat.extendScalarsComp,CommRingCat.hom_comp]

lemma gamma_map_apply {R : CommRingCat.{u}} {M N : (Spec R).Modules} (f : M ⟶ N)
    (x : (moduleSpecΓFunctor (R:=R)).obj M) :
    ((moduleSpecΓFunctor (R:=R)).map f).hom x = f.app ⊤ x := rfl

lemma conjugate_associator_inv
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₀ : A ⥤ B} {G₀ : B ⥤ A} {L₁ : B ⥤ C} {G₁ : C ⥤ B} {L₂ : C ⥤ D} {G₂ : D ⥤ C}
    (a : L₀ ⊣ G₀) (b : L₁ ⊣ G₁) (c : L₂ ⊣ G₂) :
    conjugateEquiv ((a.comp b).comp c) (a.comp (b.comp c))
      (Functor.associator L₀ L₁ L₂).inv = (Functor.associator G₂ G₁ G₀).inv :=
  conjugate_inv_of_hom _ _ _ _ (conjugateEquiv_associator_hom a b c)

lemma conjugate_beta_path {R S T : CommRingCat.{u}} (φ : R ⟶ S) (δ : S ⟶ T) :
    conjugateEquiv
      (((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (ModuleCat.extendRestrictScalarsAdj δ.hom)).comp (tilde.adjunction (R:=T)))
      (((tilde.adjunction (R:=R)).comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map δ)))
      (whiskerRight (tilde.functorCompPullbackSpecIso φ).hom (Scheme.Modules.pullback (Spec.map δ)) ≫
       (Functor.associator (ModuleCat.extendScalars φ.hom) (tilde.functor S) (Scheme.Modules.pullback (Spec.map δ))).hom ≫
       whiskerLeft (ModuleCat.extendScalars φ.hom) (tilde.functorCompPullbackSpecIso δ).hom ≫
       (Functor.associator (ModuleCat.extendScalars φ.hom) (ModuleCat.extendScalars δ.hom) (tilde.functor T)).inv) =
      (Functor.associator (moduleSpecΓFunctor (R:=T)) (ModuleCat.restrictScalars δ.hom) (ModuleCat.restrictScalars φ.hom)).inv ≫
      whiskerRight (Scheme.Modules.pushforwardSpecCompΓIso δ).inv (ModuleCat.restrictScalars φ.hom) ≫
      (Functor.associator (Scheme.Modules.pushforward (Spec.map δ)) (moduleSpecΓFunctor (R:=S)) (ModuleCat.restrictScalars φ.hom)).hom ≫
      whiskerLeft (Scheme.Modules.pushforward (Spec.map δ)) (Scheme.Modules.pushforwardSpecCompΓIso φ).inv := by
  let a0 := ((tilde.adjunction (R:=R)).comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map δ))
  let a1 := ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R:=S))).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map δ))
  let a2 := (ModuleCat.extendRestrictScalarsAdj φ.hom).comp ((tilde.adjunction (R:=S)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map δ)))
  let a3 := (ModuleCat.extendRestrictScalarsAdj φ.hom).comp ((ModuleCat.extendRestrictScalarsAdj δ.hom).comp
    (tilde.adjunction (R:=T)))
  let a4 := ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (ModuleCat.extendRestrictScalarsAdj δ.hom)).comp
    (tilde.adjunction (R:=T))
  simp only [←Category.assoc]
  rw [←conjugateEquiv_comp a4 a3 a0 _ _,←conjugateEquiv_comp a3 a2 a0 _ _,←conjugateEquiv_comp a2 a1 a0 _ _]
  rw [conjugate_associator_inv,conjugateEquiv_whiskerLeft,conjugateEquiv_associator_hom,
    conjugateEquiv_whiskerRight,conjugate_beta,conjugate_beta]
  simp only [Category.assoc]

lemma conjugate_composite_path {R S T : CommRingCat.{u}} (φ : R ⟶ S) (δ : S ⟶ T) :
    conjugateEquiv
      (((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (ModuleCat.extendRestrictScalarsAdj δ.hom)).comp (tilde.adjunction (R:=T)))
      (((tilde.adjunction (R:=R)).comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map δ)))
      ((Functor.associator (tilde.functor R) (Scheme.Modules.pullback (Spec.map φ)) (Scheme.Modules.pullback (Spec.map δ))).hom ≫
       whiskerLeft (tilde.functor R)
        ((Scheme.Modules.pullbackComp (Spec.map δ) (Spec.map φ)).hom ≫
          (Scheme.Modules.pullbackCongr (Spec.map_comp φ δ).symm).hom) ≫
       (tilde.functorCompPullbackSpecIso (φ≫δ)).hom ≫
       whiskerRight (ModuleCat.extendScalarsComp φ.hom δ.hom).hom (tilde.functor T)) =
      whiskerLeft (moduleSpecΓFunctor (R:=T)) (ModuleCat.restrictScalarsComp φ.hom δ.hom).inv ≫
      (Scheme.Modules.pushforwardSpecCompΓIso (φ≫δ)).inv ≫
      whiskerRight ((Scheme.Modules.pushforwardCongr (Spec.map_comp φ δ).symm).inv ≫
        (Scheme.Modules.pushforwardComp (Spec.map δ) (Spec.map φ)).inv) (moduleSpecΓFunctor (R:=R)) ≫
      (Functor.associator (Scheme.Modules.pushforward (Spec.map δ)) (Scheme.Modules.pushforward (Spec.map φ))
        (moduleSpecΓFunctor (R:=R))).hom := by
  let a0 := ((tilde.adjunction (R:=R)).comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map δ))
  let a1 := (tilde.adjunction (R:=R)).comp
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map δ)))
  let a2 := (tilde.adjunction (R:=R)).comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (φ≫δ)))
  let a3 := (ModuleCat.extendRestrictScalarsAdj (φ≫δ).hom).comp (tilde.adjunction (R:=T))
  let a4 := ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (ModuleCat.extendRestrictScalarsAdj δ.hom)).comp
    (tilde.adjunction (R:=T))
  simp only [←Category.assoc]
  rw [←conjugateEquiv_comp a4 a3 a0 _ _,←conjugateEquiv_comp a3 a2 a0 _ _,←conjugateEquiv_comp a2 a1 a0 _ _]
  rw [conjugateEquiv_whiskerRight,conjugate_extendScalarsComp,conjugate_beta,
    conjugateEquiv_whiskerLeft,conjugate_pullbackComp_hom_congr,conjugateEquiv_associator_hom]
  simp only [Category.assoc]

lemma beta_path_eq_composite {R S T : CommRingCat.{u}} (φ : R ⟶ S) (δ : S ⟶ T) :
    whiskerRight (tilde.functorCompPullbackSpecIso φ).hom (Scheme.Modules.pullback (Spec.map δ)) ≫
       (Functor.associator (ModuleCat.extendScalars φ.hom) (tilde.functor S) (Scheme.Modules.pullback (Spec.map δ))).hom ≫
       whiskerLeft (ModuleCat.extendScalars φ.hom) (tilde.functorCompPullbackSpecIso δ).hom ≫
       (Functor.associator (ModuleCat.extendScalars φ.hom) (ModuleCat.extendScalars δ.hom) (tilde.functor T)).inv =
    (Functor.associator (tilde.functor R) (Scheme.Modules.pullback (Spec.map φ)) (Scheme.Modules.pullback (Spec.map δ))).hom ≫
       whiskerLeft (tilde.functor R)
        ((Scheme.Modules.pullbackComp (Spec.map δ) (Spec.map φ)).hom ≫
          (Scheme.Modules.pullbackCongr (Spec.map_comp φ δ).symm).hom) ≫
       (tilde.functorCompPullbackSpecIso (φ≫δ)).hom ≫
       whiskerRight (ModuleCat.extendScalarsComp φ.hom δ.hom).hom (tilde.functor T) := by
  apply (conjugateEquiv
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (ModuleCat.extendRestrictScalarsAdj δ.hom)).comp (tilde.adjunction (R:=T)))
    (((tilde.adjunction (R:=R)).comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map δ)))).injective
  rw [conjugate_beta_path,conjugate_composite_path]
  apply NatTrans.ext
  funext N
  apply ModuleCat.hom_ext
  ext x
  dsimp [Scheme.Modules.pushforwardSpecCompΓIso,ModuleCat.restrictScalarsComp]
  rw [gamma_map_apply]
  simp [Scheme.Modules.Hom.comp_app]

#print axioms conjugate_beta
end FourCorner.TildeComposition
