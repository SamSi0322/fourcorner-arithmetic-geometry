import ThetaCoverClassPortable.NativeSinglePoleCharts

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace FourCorner.NativeSinglePoleCharts
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (i : X ≅ Y) (e : Y.functionField ≃+* X.functionField)
  (hg : X.fromSpecStalk (genericPoint X) ≫ i.hom =
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y))

include hg in
theorem generic_stalk_compatibility (x : X) :
    (algebraMap (X.presheaf.stalk x) X.functionField).comp (i.hom.stalkMap x).hom =
      e.toRingHom.comp (algebraMap (Y.presheaf.stalk (i.hom x)) Y.functionField) := by
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  rw [← cancel_mono (Y.fromSpecStalk (i.hom x))]
  change Spec.map (i.hom.stalkMap x ≫ CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ Y.fromSpecStalk (i.hom x) =
    Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (i.hom x)) Y.functionField) ≫
      CommRingCat.ofHom e.toRingHom) ≫ Y.fromSpecStalk (i.hom x)
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
    ← Category.assoc]
  change (Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫
    X.fromSpecStalk x) ≫ i.hom = _
  rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk, hg, Spec.map_comp, Category.assoc]
  change _ = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    (Spec.map (Y.presheaf.stalkSpecializes (genericPoint_specializes (i.hom x))) ≫
      Y.fromSpecStalk (i.hom x))
  rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

include hg in
theorem iso_stalk_range (x : X) :
    (e.toRingHom.comp (algebraMap (Y.presheaf.stalk (i.hom x)) Y.functionField)).range =
      (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  rw [← generic_stalk_compatibility i e hg x]
  ext z
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨_,rfl⟩
  · rintro ⟨a,rfl⟩
    obtain ⟨b,hb⟩ := (ConcreteCategory.bijective_of_isIso (i.hom.stalkMap x)).2 a
    exact ⟨b,congrArg (algebraMap (X.presheaf.stalk x) X.functionField) hb⟩
end FourCorner.NativeSinglePoleCharts
