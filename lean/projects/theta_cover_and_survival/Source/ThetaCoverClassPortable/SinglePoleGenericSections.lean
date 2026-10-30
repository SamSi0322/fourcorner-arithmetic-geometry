import ThetaCoverClassPortable.IsoNativeStalkRange
import ThetaCoverClassPortable.SinglePoleChartOverlap

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 30000
open CategoryTheory AlgebraicGeometry AlgebraicCurve IntermediateField
namespace FourCorner.NativeSinglePoleCharts
universe u
section General
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (i : X ≅ Y) (e : Y.functionField ≃+* X.functionField)
  (hg : X.fromSpecStalk (genericPoint X) ≫ i.hom =
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y))
include hg in
theorem inverse_generic_diagram : Y.fromSpecStalk (genericPoint Y) ≫ i.inv =
    Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ X.fromSpecStalk (genericPoint X) := by
  have he : CommRingCat.ofHom e.toRingHom ≫ CommRingCat.ofHom e.symm.toRingHom=𝟙 _ := by
    ext a
    exact e.symm_apply_apply a
  have hs0 : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom e.toRingHom)=𝟙 _ := by
    rw [← Spec.map_comp,he,Spec.map_id]
  calc
    Y.fromSpecStalk (genericPoint Y) ≫ i.inv =
        (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
          Spec.map (CommRingCat.ofHom e.toRingHom)) ≫ Y.fromSpecStalk (genericPoint Y) ≫ i.inv := by rw [hs0,Category.id_comp]
    _ = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ X.fromSpecStalk (genericPoint X) := by
      rw [Category.assoc,← Category.assoc (Spec.map (CommRingCat.ofHom e.toRingHom))
        (Y.fromSpecStalk (genericPoint Y)) i.inv,← hg]
      simp only [Category.assoc,i.hom_inv_id,Category.comp_id]

theorem stalkMap_germ_image {A : Type u} [CommRing A]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j] (τ : Γ(Spec (.of A),⊤))
    (p : Spec (.of A)) :
    j.stalkMap p (X.presheaf.germ (j ''ᵁ ⊤) (j p) ⟨p,trivial,rfl⟩ ((j.appIso ⊤).inv τ))=
      (Spec (.of A)).presheaf.germ ⊤ p trivial τ := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  have hh : j.app (j ''ᵁ ⊤) ((j.appIso ⊤).inv τ)=
      (Spec (.of A)).presheaf.map (eqToHom (j.preimage_image_eq ⊤)).op τ := by
    rw [← CommRingCat.comp_apply,Scheme.Hom.appIso_inv_app]
  rw [hh,TopCat.Presheaf.germ_res_apply]
end General

section Model
open CurveModel
variable {K : Type u} [Field K] [CharZero K] {X : Scheme.{u}} [IsIntegral X]
  [Algebra K X.functionField] (t : X.functionField) [Fact (t≠0)]
  [FiniteDimensional K⟮t⟯ X.functionField] [FiniteDimensional K⟮t⁻¹⟯ X.functionField]
  (i : X ≅ glued K t)
  (hg : X.fromSpecStalk (genericPoint X) ≫ i.hom =
    Spec.map (CommRingCat.ofHom (gluedFunctionFieldEquiv K t).symm.toRingHom) ≫
      (glued K t).fromSpecStalk (genericPoint (glued K t)))

local instance : IsOpenImmersion (Spec.map (CommRingCat.ofHom (incl₀ K t).toRingHom)) :=
  isOpenImmersion_f₀ K t

include hg in
theorem zero_theta_stalk (p : X₀ K t) (a : X.presheaf.stalk ((jZero t i).base p)) :
    thetaHom K t (chartRing K ({t}:Set X.functionField)) (incl₀ K t) p (((jZero t i).stalkMap p).hom a)=
      algebraMap (X.presheaf.stalk ((jZero t i).base p)) X.functionField a := by
  change thetaHom K t (chartRing K ({t}:Set X.functionField)) (incl₀ K t) p
    (((ι₀ K t ≫ i.inv).stalkMap p) a)=_
  rw [Scheme.Hom.stalkMap_comp,CommRingCat.comp_apply]
  rw [← ffEquiv_symm_algebraMap_stalk K t (chartRing K ({t}:Set X.functionField)) (incl₀ K t) (ι₀ K t) rfl p]
  have hc := congrArg (fun h => h a)
    (generic_stalk_compatibility i.symm (gluedFunctionFieldEquiv K t)
      (inverse_generic_diagram i (gluedFunctionFieldEquiv K t).symm hg) ((ι₀ K t).base p))
  exact (congrArg (gluedFunctionFieldEquiv K t).symm hc).trans
    ((gluedFunctionFieldEquiv K t).symm_apply_apply _)

include hg in
theorem zero_generic_value (s : Γ(X,U t i)) :
    (X.germToFunctionField (U t i)) s=(zeroSectionsEquiv t i s : X.functionField) := by
  let p := genericPoint (X₀ K t)
  have hsp : genericPoint X ⤳ (jZero t i).base p := genericPoint_specializes _
  have he := ConcreteCategory.congr_hom
    (TopCat.Presheaf.germ_stalkSpecializes X.presheaf (U:=U t i) ⟨p,trivial,rfl⟩ hsp) s
  rw [CommRingCat.comp_apply] at he
  have he' : algebraMap (X.presheaf.stalk ((jZero t i).base p)) X.functionField
      (X.presheaf.germ (U t i) ((jZero t i).base p) ⟨p,trivial,rfl⟩ s)=
        (X.germToFunctionField (U t i)) s := he
  rw [← he',← zero_theta_stalk t i hg p]
  have hs : s=((jZero t i).appIso ⊤).inv
      ((Scheme.ΓSpecIso (.of (chartRing K ({t}:Set X.functionField)))).inv (zeroSectionsEquiv t i s)) := by
    exact ((zeroSectionsEquiv t i).symm_apply_apply s).symm
  conv_lhs => rw [hs]
  have hj := stalkMap_germ_image (jZero t i)
    ((Scheme.ΓSpecIso (.of (chartRing K ({t}:Set X.functionField)))).inv (zeroSectionsEquiv t i s)) p
  exact (congrArg (thetaHom K t (chartRing K ({t}:Set X.functionField)) (incl₀ K t) p) hj).trans
    (thetaHom_toStalk K t (chartRing K ({t}:Set X.functionField)) (incl₀ K t)
      (fun a => coe_chartIncl K _ a) p _)
local instance : IsOpenImmersion (Spec.map (CommRingCat.ofHom (inclInf K t).toRingHom)) :=
  isOpenImmersion_fInf K t

include hg in
theorem infinity_theta_stalk (p : XInf K t) (a : X.presheaf.stalk ((jInfinity t i).base p)) :
    thetaHom K t (chartRing K ({t⁻¹}:Set X.functionField)) (inclInf K t) p (((jInfinity t i).stalkMap p).hom a)=
      algebraMap (X.presheaf.stalk ((jInfinity t i).base p)) X.functionField a := by
  change thetaHom K t (chartRing K ({t⁻¹}:Set X.functionField)) (inclInf K t) p
    (((ιInf K t ≫ i.inv).stalkMap p) a)=_
  rw [Scheme.Hom.stalkMap_comp,CommRingCat.comp_apply]
  rw [← ffEquiv_symm_algebraMap_stalk K t (chartRing K ({t⁻¹}:Set X.functionField)) (inclInf K t) (ιInf K t) (glue_condition K t).symm p]
  have hc := congrArg (fun h => h a)
    (generic_stalk_compatibility i.symm (gluedFunctionFieldEquiv K t)
      (inverse_generic_diagram i (gluedFunctionFieldEquiv K t).symm hg) ((ιInf K t).base p))
  exact (congrArg (gluedFunctionFieldEquiv K t).symm hc).trans
    ((gluedFunctionFieldEquiv K t).symm_apply_apply _)

include hg in
theorem infinity_generic_value (s : Γ(X,V t i)) :
    (X.germToFunctionField (V t i)) s=(infinitySectionsEquiv t i s : X.functionField) := by
  let p := genericPoint (XInf K t)
  have hsp : genericPoint X ⤳ (jInfinity t i).base p := genericPoint_specializes _
  have he := ConcreteCategory.congr_hom
    (TopCat.Presheaf.germ_stalkSpecializes X.presheaf (U:=V t i) ⟨p,trivial,rfl⟩ hsp) s
  rw [CommRingCat.comp_apply] at he
  have he' : algebraMap (X.presheaf.stalk ((jInfinity t i).base p)) X.functionField
      (X.presheaf.germ (V t i) ((jInfinity t i).base p) ⟨p,trivial,rfl⟩ s)=
        (X.germToFunctionField (V t i)) s := he
  rw [← he',← infinity_theta_stalk t i hg p]
  have hs : s=((jInfinity t i).appIso ⊤).inv
      ((Scheme.ΓSpecIso (.of (chartRing K ({t⁻¹}:Set X.functionField)))).inv (infinitySectionsEquiv t i s)) := by
    exact ((infinitySectionsEquiv t i).symm_apply_apply s).symm
  conv_lhs => rw [hs]
  have hj := stalkMap_germ_image (jInfinity t i)
    ((Scheme.ΓSpecIso (.of (chartRing K ({t⁻¹}:Set X.functionField)))).inv (infinitySectionsEquiv t i s)) p
  exact (congrArg (thetaHom K t (chartRing K ({t⁻¹}:Set X.functionField)) (inclInf K t) p) hj).trans
    (thetaHom_toStalk K t (chartRing K ({t⁻¹}:Set X.functionField)) (inclInf K t)
      (fun a => coe_chartIncl K _ a) p _)
include hg in
theorem reciprocal_sections :
    (X.presheaf.map (homOfLE (inf_le_left : U t i ⊓ V t i ≤ U t i)).op (fSection t i)) *
      (X.presheaf.map (homOfLE (inf_le_right : U t i ⊓ V t i ≤ V t i)).op (gSection t i))=1 := by
  have hη : genericPoint X∈U t i ⊓ V t i := ⟨generic_mem_U t i,generic_mem_V t i⟩
  apply germ_injective_of_isIntegral X (genericPoint X) hη
  rw [map_mul,map_one,TopCat.Presheaf.germ_res_apply,TopCat.Presheaf.germ_res_apply]
  change (X.germToFunctionField (U t i) (fSection t i)) *
    (X.germToFunctionField (V t i) (gSection t i))=1
  rw [zero_generic_value t i hg,infinity_generic_value t i hg,
    zeroSectionsEquiv_fSection,infinitySectionsEquiv_gSection,coe_tChart,coe_tInvChart]
  exact mul_inv_cancel₀ (Fact.out : t≠0)

end Model
end FourCorner.NativeSinglePoleCharts
