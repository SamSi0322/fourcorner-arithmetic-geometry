import ThetaDGeometricModel

namespace FourCorner.ThetaNativeFunctionFieldMap
open AlgebraicGeometry CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [Surjective f]

theorem image_generic : f (genericPoint X)=genericPoint Y := by
  have hy : Specializes (f (genericPoint X)) (genericPoint Y) := by
    obtain ⟨x,hx⟩ := f.surjective (genericPoint Y)
    rw [← hx]
    exact (genericPoint_specializes x).map f.continuous
  exact (hy.antisymm (genericPoint_specializes _)).eq

/-- The actual generic-stalk map of the specified native morphism. -/
def fieldMap : Y.functionField →+* X.functionField :=
  ((Y.presheaf.stalkCongr (.of_eq (image_generic f).symm)).hom ≫
    f.stalkMap (genericPoint X)).hom

theorem generic_diagram :
    Spec.map (CommRingCat.ofHom (fieldMap f)) ≫ Y.fromSpecStalk (genericPoint Y)=
      X.fromSpecStalk (genericPoint X) ≫ f := by
  change Spec.map (((Y.presheaf.stalkCongr (.of_eq (image_generic f).symm)).hom ≫
    f.stalkMap (genericPoint X))) ≫ _=_
  simp only [Spec.map_comp,Category.assoc,TopCat.Presheaf.stalkCongr_hom,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk f

variable {K : Type} [Field K] (cX : X ⟶ Spec (.of K)) (cY : Y ⟶ Spec (.of K))

theorem base_compatibility (he : f ≫ cY=cX) (a : K) :
    fieldMap f (SmoothCurveExtension.baseMap cY a)=SmoothCurveExtension.baseMap cX a := by
  have h : CommRingCat.ofHom ((fieldMap f).comp (SmoothCurveExtension.baseMap cY))=
      CommRingCat.ofHom (SmoothCurveExtension.baseMap cX) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp,Spec.map_comp]
    rw [← SmoothCurveExtension.generic_comp_to_base cY,← Category.assoc,generic_diagram,
      Category.assoc,he,SmoothCurveExtension.generic_comp_to_base]
  exact congrArg (fun g=>g.hom a) h

/-- The real structural-K homomorphism on the two actual function fields. -/
def fieldAlgHom (he : f ≫ cY=cX) :
    letI := SmoothCurveExtension.fieldAlgebra cX
    letI := SmoothCurveExtension.fieldAlgebra cY
    Y.functionField →ₐ[K] X.functionField := by
  letI := SmoothCurveExtension.fieldAlgebra cX
  letI := SmoothCurveExtension.fieldAlgebra cY
  exact ⟨fieldMap f,base_compatibility f cX cY he⟩

#print axioms image_generic
#print axioms fieldMap
#print axioms generic_diagram
#print axioms fieldAlgHom
end
end FourCorner.ThetaNativeFunctionFieldMap
