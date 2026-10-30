import ThetaCoverClassPortable.ThetaNativeFunctionFieldMap

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FourCorner.NativeFunctionFieldFunctor
open ThetaNativeFunctionFieldMap

variable {X Y Z : Scheme} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

/-- Functoriality of the ACTUAL generic-stalk maps. It follows from the
actual generic Spec diagrams and the monomorphism of the generic stalk. -/
theorem fieldMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f] [Surjective g] :
    fieldMap (f ≫ g)=(fieldMap f).comp (fieldMap g) := by
  have he : CommRingCat.ofHom (fieldMap (f ≫ g))=
      CommRingCat.ofHom ((fieldMap f).comp (fieldMap g)) := by
    apply Spec.map_injective
    apply (cancel_mono (Z.fromSpecStalk (genericPoint Z))).mp
    rw [generic_diagram,CommRingCat.ofHom_comp,Spec.map_comp]
    simp only [Category.assoc,generic_diagram]
    simpa only [Category.assoc] using (congrArg (fun h=>h ≫ g) (generic_diagram f)).symm
  exact congrArg CommRingCat.Hom.hom he

 theorem fieldMap_id : fieldMap (𝟙 X)=RingHom.id X.functionField := by
  have he : CommRingCat.ofHom (fieldMap (𝟙 X))=CommRingCat.ofHom (RingHom.id X.functionField) := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
    rw [generic_diagram]
    simp
  exact congrArg CommRingCat.Hom.hom he

/-- A scheme isomorphism gives an actual generic-stalk ring isomorphism;
no basis, generators or presumed function-field identification are used. -/
def fieldRingEquiv (f : X ⟶ Y) [IsIso f] : Y.functionField ≃+* X.functionField := by
  let m : Y.presheaf.stalk (genericPoint Y) ⟶ X.presheaf.stalk (genericPoint X) :=
    (Y.presheaf.stalkCongr (.of_eq (image_generic f).symm)).hom ≫ f.stalkMap (genericPoint X)
  haveI : IsIso m := by dsimp [m];infer_instance
  exact (asIso m).commRingCatIsoToRingEquiv

 theorem fieldRingEquiv_toRingHom (f : X ⟶ Y) [IsIso f] :
    (fieldRingEquiv f).toRingHom=fieldMap f := rfl

/-- Semilinear compatibility is DERIVED from the actual base Spec diagram. -/
theorem semilinear_base_compatibility {K : Type} [Field K]
    (f : X ⟶ Y) [Surjective f] (cX : X ⟶ Spec (.of K)) (cY : Y ⟶ Spec (.of K))
    (σ : K ≃+* K) (he : f ≫ cY=cX ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
    (a : K) :
    fieldMap f (AlgebraicCurve.baseToFunctionField cY a)=
      AlgebraicCurve.baseToFunctionField cX (σ a) := by
  have h : CommRingCat.ofHom ((fieldMap f).comp (AlgebraicCurve.baseToFunctionField cY))=
      CommRingCat.ofHom ((AlgebraicCurve.baseToFunctionField cX).comp σ.toRingHom) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp,Spec.map_comp,CommRingCat.ofHom_comp,Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (fieldMap f)) ≫
        Spec.map (CommRingCat.ofHom (SmoothCurveExtension.baseMap cY))=_
    rw [←SmoothCurveExtension.generic_comp_to_base cY,←Category.assoc,generic_diagram,
      Category.assoc,he,←Category.assoc,SmoothCurveExtension.generic_comp_to_base]
    rfl
  exact congrArg (fun h=>h.hom a) h

#print axioms fieldMap_comp
#print axioms fieldRingEquiv
#print axioms semilinear_base_compatibility
end FourCorner.NativeFunctionFieldFunctor
