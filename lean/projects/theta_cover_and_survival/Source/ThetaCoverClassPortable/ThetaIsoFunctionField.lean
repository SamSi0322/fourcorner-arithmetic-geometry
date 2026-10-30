import ThetaCoverClassPortable.SmoothCurveFieldIso
noncomputable section
namespace FourCorner.ThetaIsoFunctionField
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
def stalkIso (e : X ≅ Y) : Y.functionField ≅ X.functionField :=
  Y.presheaf.stalkCongr (.of_eq (genericPoint_eq_of_isOpenImmersion e.hom).symm) ≪≫
    asIso (e.hom.stalkMap (genericPoint X))
def ringEquiv (e : X ≅ Y) : Y.functionField ≃+* X.functionField :=
  (stalkIso e).commRingCatIsoToRingEquiv
lemma generic_diagram (e : X ≅ Y) :
    Spec.map (CommRingCat.ofHom (ringEquiv e).toRingHom) ≫ Y.fromSpecStalk (genericPoint Y)=
      X.fromSpecStalk (genericPoint X) ≫ e.hom := by
  change Spec.map ((stalkIso e).hom) ≫ Y.fromSpecStalk (genericPoint Y)=_
  simp only [stalkIso,Iso.trans_hom,asIso_hom,Spec.map_comp,Category.assoc,
    TopCat.Presheaf.stalkCongr_hom,Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk e.hom
lemma base_compatibility (c : X ⟶ Spec (.of K)) (d : Y ⟶ Spec (.of K))
    (e : X ≅ Y) (he : e.hom ≫ d=c) (a : K) :
    ringEquiv e (SmoothCurveExtension.baseMap d a)=SmoothCurveExtension.baseMap c a := by
  have h : CommRingCat.ofHom ((ringEquiv e).toRingHom.comp (SmoothCurveExtension.baseMap d))=
      CommRingCat.ofHom (SmoothCurveExtension.baseMap c) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp,Spec.map_comp]
    rw [←SmoothCurveExtension.generic_comp_to_base d,←Category.assoc,generic_diagram,
      Category.assoc,he,SmoothCurveExtension.generic_comp_to_base]
  exact congrArg (fun g=>g.hom a) h
def algEquiv (c : X ⟶ Spec (.of K)) (d : Y ⟶ Spec (.of K))
    (e : X ≅ Y) (he : e.hom ≫ d=c) :
    letI := SmoothCurveExtension.fieldAlgebra c
    letI := SmoothCurveExtension.fieldAlgebra d
    Y.functionField ≃ₐ[K] X.functionField := by
  letI := SmoothCurveExtension.fieldAlgebra c
  letI := SmoothCurveExtension.fieldAlgebra d
  exact AlgEquiv.ofRingEquiv (f:=ringEquiv e) (base_compatibility c d e he)
end FourCorner.ThetaIsoFunctionField
#print axioms FourCorner.ThetaIsoFunctionField.algEquiv
