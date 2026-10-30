import ThetaCoverClassPortable.ThetaSingleOriginPole
import ThetaCoverClassPortable.geometry.SchemeModelFiniteExtension
import ThetaCoverClassPortable.SmoothCurveFieldIso

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicCurve
namespace FourCorner.ThetaRationalPicardInput
open ThetaLiteralModels
attribute [local instance] sourceIntegral sourceSmooth sourceProper constants

/-- The genuine integral-closure-chart model for the SPECIFIED generator f. -/
def singlePoleModel (f : (C ℚ).functionField) (ht : Transcendental ℚ f)
    [FiniteDimensional (IntermediateField.adjoin ℚ ({f} : Set (C ℚ).functionField)) (C ℚ).functionField] :
    CurveModel ℚ (C ℚ).functionField := by
  have hf : f≠0 := by intro h;rw [h] at ht;exact ht isAlgebraic_zero
  letI : Fact (f≠0) := ⟨hf⟩
  letI : FiniteDimensional (IntermediateField.adjoin ℚ ({f⁻¹} : Set (C ℚ).functionField)) (C ℚ).functionField := by
    rw [CurveModel.adjoin_simple_inv_eq]
    infer_instance
  exact CurveModel.ofGenerator ℚ f ht

/-- The specified actual model is isomorphic over Q to the ORIGINAL curve,
with actual generic pullback EXACTLY the given field identity. -/
theorem singlePole_model_comparison (f : (C ℚ).functionField)
    (ht : Transcendental ℚ f)
    [FiniteDimensional (IntermediateField.adjoin ℚ ({f} : Set (C ℚ).functionField)) (C ℚ).functionField] :
    let M := singlePoleModel f ht
    ∃ i : C ℚ ≅ M.C, i.hom ≫ M.toBase=cToBase ℚ ∧
      (C ℚ).fromSpecStalk (genericPoint (C ℚ)) ≫ i.hom=
        Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫
          M.C.fromSpecStalk (genericPoint M.C) := by
  let M := singlePoleModel f ht
  letI := M.isIntegral
  letI := M.isProper
  letI := M.smooth
  letI := M.functionFieldAlgebra
  let e : M.C.functionField ≃ₐ[ℚ] (C ℚ).functionField := M.ffAlgEquiv.symm
  obtain ⟨i,hi,hgeneric⟩ := SmoothCurveExtension.iso_of_functionField_algEquiv
    (cToBase ℚ) M.toBase e
  refine ⟨i,hi,?_⟩
  have he : e.toRingEquiv.toRingHom=M.ffEquiv.symm.toRingHom := by
    ext x
    rfl
  rw [he] at hgeneric
  exact hgeneric

#print axioms singlePoleModel
#print axioms singlePole_model_comparison
end FourCorner.ThetaRationalPicardInput
