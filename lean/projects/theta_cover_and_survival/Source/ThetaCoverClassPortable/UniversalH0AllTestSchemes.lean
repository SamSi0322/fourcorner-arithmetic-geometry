import ThetaCoverClassPortable.ProjectionAppTopLocal

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange
universe u
namespace FourCorner.UniversalH0AllTestSchemes
open Scheme.TwoAffineOpenCover
variable {R:Type u} [CommRing R] {C T:Scheme.{u}} (c:C⟶Spec (.of R)) (t:T⟶Spec (.of R))

lemma affine_structural (U:T.Opens) (hU:IsAffineOpen U) :
 letI:=algebraOfHom t U
 hU.isoSpec.hom≫specMap R Γ(T,U)=U.ι≫t := by
  letI:=algebraOfHom t U
  rw [show specMap R Γ(T,U)=hU.fromSpec≫t from specMap_algebraMap_eq t U hU]
  rw [←hU.isoSpec_inv_ι]
  simp only [Category.assoc,Iso.hom_inv_id_assoc]

def localPullbackIso (U:T.Opens) (hU:IsAffineOpen U) :
 letI:=algebraOfHom t U
 ((pullback.snd c t) ⁻¹ᵁ U).toScheme≅pullback c (specMap R Γ(T,U)) := by
  letI:=algebraOfHom t U
  exact (pullbackRestrictIsoRestrict (pullback.snd c t) U).symm ≪≫
   pullbackLeftPullbackSndIso c t U.ι ≪≫
   asIso (pullback.map c (U.ι≫t) c (specMap R Γ(T,U)) (𝟙 C) hU.isoSpec.hom (𝟙 _)
    (by simp) (by simpa only [Category.comp_id] using (affine_structural t U hU).symm))

lemma restrict_snd (U:T.Opens) :
 (pullbackRestrictIsoRestrict (pullback.snd c t) U).inv≫pullback.snd (pullback.snd c t) U.ι=
   (pullback.snd c t) ∣_ U := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc,←pullback.condition]
  rw [←Category.assoc,pullbackRestrictIsoRestrict_inv_fst,morphismRestrict_ι]

lemma localPullbackIso_snd (U:T.Opens) (hU:IsAffineOpen U) :
 letI:=algebraOfHom t U
 (localPullbackIso c t U hU).hom≫pullback.snd c (specMap R Γ(T,U))=
  ((pullback.snd c t) ∣_ U)≫hU.isoSpec.hom := by
  letI:=algebraOfHom t U
  simp only [localPullbackIso,Iso.trans_hom,Iso.symm_hom,asIso_hom,Category.assoc,pullback.lift_snd,
    pullbackLeftPullbackSndIso_hom_snd_assoc]
  rw [←Category.assoc,restrict_snd]

lemma affine_projection_bijective
 (hH0:∀(A:Type u)[CommRing A][Algebra R A],
   letI:=algebraOfHom (pullback.snd c (specMap R A)) ⊤
   Function.Bijective (algebraMap A Γ(pullback c (specMap R A),⊤)))
 (A:Type u)[CommRing A][Algebra R A] :
 Function.Bijective (pullback.snd c (specMap R A)).appTop := by
  letI:=algebraOfHom (pullback.snd c (specMap R A)) ⊤
  have h:=hH0 A
  change Function.Bijective (algebraMap A Γ(pullback c (specMap R A),⊤)) at h
  have hh (a:A):algebraMap A Γ(pullback c (specMap R A),⊤) a=
      (pullback.snd c (specMap R A)).appTop ((Scheme.ΓSpecIso (.of A)).inv a) := by
    rw [algebraMap_algebraOfHom]
    simp [Scheme.Hom.appLE]
  have he:(algebraMap A Γ(pullback c (specMap R A),⊤))=
      ((pullback.snd c (specMap R A)).appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom) := by
    ext a
    exact hh a
  rw [he] at h
  change Function.Bijective ((pullback.snd c (specMap R A)).appTop ∘(Scheme.ΓSpecIso (.of A)).inv) at h
  exact (Function.Bijective.of_comp_iff _
    ((ConcreteCategory.isIso_iff_bijective _).mp (inferInstance:IsIso (Scheme.ΓSpecIso (.of A)).inv))).mp h

/-- Actual universal affine-algebra H0 base change forces the ACTUAL global
projection ring map to be bijective for EVERY test scheme, with no affineness
or quasi-compactness hypothesis on that test scheme. -/
theorem bijective_appTop_pullback_snd
 (hH0:∀(A:Type u)[CommRing A][Algebra R A],
   letI:=algebraOfHom (pullback.snd c (specMap R A)) ⊤
   Function.Bijective (algebraMap A Γ(pullback c (specMap R A),⊤))) :
 Function.Bijective (pullback.snd c t).appTop := by
  apply ProjectionAppTopLocal.bijective_appTop_of_affine_local
  intro U hU
  letI:=algebraOfHom t U
  let e:=localPullbackIso c t U hU
  let q:=pullback.snd c (specMap R Γ(T,U))
  let f:=(pullback.snd c t) ∣_ U
  haveI:IsIso q.appTop:=(ConcreteCategory.isIso_iff_bijective _).mpr
    (affine_projection_bijective c hH0 Γ(T,U))
  haveI:IsIso e.hom.appTop:=inferInstance
  haveI:IsIso hU.isoSpec.hom.appTop:=inferInstance
  have he:q.appTop≫e.hom.appTop=hU.isoSpec.hom.appTop≫f.appTop := by
    have hh:=congrArg (fun g:((pullback.snd c t) ⁻¹ᵁ U).toScheme⟶Spec (.of Γ(T,U))=>g.appTop)
      (localPullbackIso_snd c t U hU)
    simpa only [Scheme.Hom.comp_appTop] using hh
  have hf:f.appTop=inv hU.isoSpec.hom.appTop≫q.appTop≫e.hom.appTop := by
    apply (cancel_epi hU.isoSpec.hom.appTop).mp
    rw [←Category.assoc,IsIso.hom_inv_id,Category.id_comp]
    exact he.symm
  haveI:IsIso f.appTop:=by rw [hf];infer_instance
  have hi:IsIso ((pullback.snd c t).app U) := by
    rw [←topIso_morphismRestrict_appTop_topIso (pullback.snd c t) U]
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).mp hi

#print axioms bijective_appTop_pullback_snd
end FourCorner.UniversalH0AllTestSchemes
