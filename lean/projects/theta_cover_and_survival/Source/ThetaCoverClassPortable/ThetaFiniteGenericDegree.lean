import ThetaCoverClassPortable.ThetaNativeFunctionFieldMap
import ThetaCoverClassPortable.ThetaGenericRankFraction

namespace FourCorner.ThetaFiniteGenericDegree
open AlgebraicGeometry CategoryTheory AlgebraicCurve ThetaNativeFunctionFieldMap ThetaGenericRankFraction
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [Surjective f]

 theorem fromSpec_generic (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    Spec.map (Y.germToFunctionField U) ≫ hU.fromSpec=Y.fromSpecStalk (genericPoint Y) := by
  have hη : genericPoint Y ∈ U := by
    obtain ⟨y,hy⟩ := (show (U : Set Y).Nonempty from by simpa using (inferInstance : Nonempty U))
    exact (genericPoint_specializes y).mem_open U.isOpen hy
  exact hU.fromSpecStalk_eq_fromSpecStalk hη

 theorem sections_field_naturality (U : Y.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen (f ⁻¹ᵁ U)) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] (a : Γ(Y,U)) :
    fieldMap f ((Y.germToFunctionField U).hom a)=
      (X.germToFunctionField (f ⁻¹ᵁ U)).hom ((f.app U).hom a) := by
  have hh : CommRingCat.ofHom ((fieldMap f).comp (Y.germToFunctionField U).hom)=
      CommRingCat.ofHom ((X.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom) := by
    apply Spec.map_injective
    apply (cancel_mono hU.fromSpec).mp
    rw [CommRingCat.ofHom_comp,CommRingCat.ofHom_comp,Spec.map_comp,Spec.map_comp]
    simp only [CommRingCat.ofHom_hom,Category.assoc]
    rw [fromSpec_generic U hU,generic_diagram]
    rw [← fromSpec_generic (Y:=X) (f ⁻¹ᵁ U) hV,Category.assoc,
      ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV (le_refl _)]
    simp only [Scheme.Hom.app_eq_appLE]
  exact congrArg (fun g : Γ(Y,U) ⟶ X.presheaf.stalk (genericPoint X) => g.hom a) hh

variable [IsFinite f] [Flat f]

 theorem chart_pullback (U : Y.Opens) (hU : IsAffineOpen U) :
    IsPullback (hU.preimage f).fromSpec (Spec.map (f.app U)) f hU.fromSpec := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · simpa only [Scheme.Hom.app_eq_appLE] using (IsAffineOpen.SpecMap_appLE_fromSpec f hU (hU.preimage f) (le_refl _)).symm
  · rw [hU.opensRange_fromSpec,(hU.preimage f).opensRange_fromSpec]

 theorem ring_rank_at_generic (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    (f.app U).hom.finrank (genericPrime Γ(Y,U))=f.finrank (genericPoint Y) := by
  have h := Scheme.Hom.finrank_of_isPullback (hU.preimage f).fromSpec
    (Spec.map (f.app U)) f hU.fromSpec (chart_pullback f U hU) (genericPrime Γ(Y,U))
  have hg : hU.fromSpec (genericPrime Γ(Y,U))=genericPoint Y := by
    rw [show genericPrime Γ(Y,U)=genericPoint (Spec Γ(Y,U)) from (genericPoint_eq_bot_of_affine _).symm]
    exact genericPoint_eq_of_isOpenImmersion _
  rw [hg] at h
  rw [Scheme.Hom.finrank_SpecMap_eq_finrank (f.finite_app U hU)
    (by simpa only [Scheme.Hom.app_eq_appLE] using f.flat_appLE hU (hU.preimage f) (le_refl _))] at h
  exact h

/-- A native finite flat surjective constant-rank-two morphism of actual
integral schemes has degree TWO on its actual native function fields. -/
theorem degree_two (hrank : ∀y,f.finrank y=2) :
    letI : Algebra Y.functionField X.functionField := (fieldMap f).toAlgebra
    Module.finrank Y.functionField X.functionField=2 := by
  let U := Y.affineOpenCover.X (Y.affineOpenCover.idx (genericPoint Y))
  let V := Y.affineOpenCover.f (Y.affineOpenCover.idx (genericPoint Y))
  let W := V.opensRange
  have hW : IsAffineOpen W := isAffineOpen_opensRange V
  haveI : Nonempty W := by
    obtain ⟨x,hx⟩ := Y.affineOpenCover.covers (genericPoint Y)
    exact ⟨⟨genericPoint Y,by rw [←hx];exact ⟨x,rfl⟩⟩⟩
  haveI : Nonempty (f ⁻¹ᵁ W) := by
    obtain ⟨y,hy⟩ := f.surjective (Classical.choice (inferInstance : Nonempty W)).val
    refine ⟨⟨y,?_⟩⟩
    change f y ∈ W
    rw [hy]
    exact (Classical.choice (inferInstance : Nonempty W)).property
  let R := Γ(Y,W)
  let S := Γ(X,f ⁻¹ᵁ W)
  letI : Algebra R S := (f.app W).hom.toAlgebra
  letI : Algebra Y.functionField X.functionField := (fieldMap f).toAlgebra
  letI : Algebra R X.functionField := ((algebraMap S X.functionField).comp (f.app W).hom).toAlgebra
  letI : IsScalarTower R S X.functionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower R Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a => (sections_field_naturality f W hW (hW.preimage f) a).symm)
  letI := functionField_isFractionRing_of_isAffineOpen Y W hW
  letI := functionField_isFractionRing_of_isAffineOpen X (f ⁻¹ᵁ W) (hW.preimage f)
  rw [field_finrank_eq_generic_rank R Y.functionField S X.functionField]
  change (f.app W).hom.finrank (genericPrime R)=2
  rw [ring_rank_at_generic f W hW,hrank]

#print axioms sections_field_naturality
#print axioms chart_pullback
#print axioms ring_rank_at_generic
#print axioms degree_two
end
end FourCorner.ThetaFiniteGenericDegree
