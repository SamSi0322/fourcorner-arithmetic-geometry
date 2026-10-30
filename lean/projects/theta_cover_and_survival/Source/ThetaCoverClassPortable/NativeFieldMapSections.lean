import ThetaCoverClassPortable.ThetaNativeFunctionFieldMap
import ThetaCoverClassPortable.KummerUnitCocycle

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
namespace FourCorner.NativeFieldMapSections
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [Surjective f]

lemma fieldMap_germ (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] (s : Γ(Y,U)) :
    ThetaNativeFunctionFieldMap.fieldMap f (algebraMap Γ(Y,U) Y.functionField s)=
      algebraMap Γ(X,f ⁻¹ᵁ U) X.functionField (f.app U s) := by
  change (f.stalkMap (genericPoint X))
    ((Y.presheaf.stalkCongr (.of_eq (ThetaNativeFunctionFieldMap.image_generic f).symm)).hom
      (Y.germToFunctionField U s))=X.germToFunctionField (f ⁻¹ᵁ U) (f.app U s)
  simp only [TopCat.Presheaf.stalkCongr_hom,Scheme.germToFunctionField,
    Y.presheaf.germ_stalkSpecializes]
  erw [Y.presheaf.germ_stalkSpecializes_apply]
  exact f.germ_stalkMap_apply U (genericPoint X) _ s

#print axioms fieldMap_germ
end FourCorner.NativeFieldMapSections
