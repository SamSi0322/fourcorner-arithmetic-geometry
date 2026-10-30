import ThetaCoverClassPortable.DOriginGeometry
import ThetaCoverClassPortable.geometry.SchemeModelFiniteExtension
import ThetaCoverClassPortable.SmoothCurveFieldIso

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicCurve
namespace FourCorner.DRationalInputs
open ThetaLiteralModels
local instance : IsIntegral curve := integral
local instance : SmoothOfRelativeDimension 1 toBase := smooth
local instance : IsProper toBase := proper
local instance : Algebra ℚ field := constants

/-- The genuine integral-closure-chart model for the SPECIFIED generator f. -/
def singlePoleModel (f : field) (ht : Transcendental ℚ f)
    [FiniteDimensional (IntermediateField.adjoin ℚ ({f} : Set field)) field] :
    CurveModel ℚ field := by
  have hf : f≠0 := by intro h;rw [h] at ht;exact ht isAlgebraic_zero
  letI : Fact (f≠0) := ⟨hf⟩
  letI : FiniteDimensional (IntermediateField.adjoin ℚ ({f⁻¹} : Set field)) field := by
    rw [CurveModel.adjoin_simple_inv_eq]
    infer_instance
  exact CurveModel.ofGenerator ℚ f ht

/-- The specified actual model is isomorphic over Q to the ORIGINAL curve,
with actual generic pullback EXACTLY the given field identity. -/
theorem singlePole_model_comparison (f : field)
    (ht : Transcendental ℚ f)
    [FiniteDimensional (IntermediateField.adjoin ℚ ({f} : Set field)) field] :
    let M := singlePoleModel f ht
    ∃ i : curve ≅ M.C, i.hom ≫ M.toBase=toBase ∧
      curve.fromSpecStalk (genericPoint curve) ≫ i.hom=
        Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫
          M.C.fromSpecStalk (genericPoint M.C) := by
  let M := singlePoleModel f ht
  letI := M.isIntegral
  letI := M.isProper
  letI := M.smooth
  letI := M.functionFieldAlgebra
  let e : M.C.functionField ≃ₐ[ℚ] field := M.ffAlgEquiv.symm
  obtain ⟨i,hi,hgeneric⟩ := SmoothCurveExtension.iso_of_functionField_algEquiv
    (toBase) M.toBase e
  refine ⟨i,hi,?_⟩
  have he : e.toRingEquiv.toRingHom=M.ffEquiv.symm.toRingHom := by
    ext x
    rfl
  rw [he] at hgeneric
  exact hgeneric

#print axioms singlePoleModel
#print axioms singlePole_model_comparison
end FourCorner.DRationalInputs
