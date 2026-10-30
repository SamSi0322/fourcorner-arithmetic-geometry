import ThetaCoverClassPortable.ThetaCoverNativeQuadraticField
import ThetaCoverClassPortable.ThetaCoverActualIntegralClosure

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.ThetaCoverNormalization
open ThetaLiteralModels ThetaCoverRationalData ThetaCoverNativeChartFields
open ThetaCoverNativeQuadraticField ThetaCoverActualIntegralClosure ThetaNativeFunctionFieldMap
local instance : IsIntegral (C ℚ) := ThetaSourceComparison.source_integral
local instance : IsIntegral (D ℚ) := ThetaDPlaneChartSections.original_integral
local instance : Surjective (ThetaProjection.projection (k:=ℚ)) := ThetaProjectionDegree.projection_surjective
local instance (U : (D ℚ).Opens) [Nonempty U] : Nonempty (pi ⁻¹ᵁ U) := preimage_nonempty U
local instance : Algebra targetField sourceField := (fieldMap (ThetaProjection.projection (k:=ℚ))).toAlgebra

/-- Actual normalization of the literal v²=h extension: exact original
primitive coordinate, native generic-Spec and relative-field diagrams,
AND true integral closure on EVERY nonempty affine target preimage.
No normalization property is supplied as an input or inserted as a label. -/
theorem actual_literal_normalization :
    IsFinite (ThetaProjection.projection (k:=ℚ)) ∧
    Etale (ThetaProjection.projection (k:=ℚ)) ∧
    actualV^2=algebraMap targetField sourceField rationalH ∧
    Algebra.adjoin targetField ({actualV}:Set sourceField)=⊤ ∧
    Nonempty (ThetaQuadraticKernel.Q rationalH ≃ₐ[targetField] sourceField) ∧
    original_quadratic_field_equiv.toRingHom.comp
        (algebraMap targetField (ThetaQuadraticKernel.Q rationalH))=
      fieldMap (ThetaProjection.projection (k:=ℚ)) ∧
    (Spec.map (CommRingCat.ofHom (fieldMap (ThetaProjection.projection (k:=ℚ)))) ≫
        (D ℚ).fromSpecStalk (genericPoint (D ℚ))=
      (C ℚ).fromSpecStalk (genericPoint (C ℚ)) ≫ ThetaProjection.projection) ∧
    (∀ (U : (D ℚ).Opens) (hU : IsAffineOpen U) [Nonempty U],
      letI := affineSectionsAlgebra U
      letI := affineFieldAlgebra U
      IsIntegralClosure Γ(C ℚ,pi ⁻¹ᵁ U) Γ(D ℚ,U) (C ℚ).functionField) :=
  ⟨ThetaProjectionFiniteEtale.projection_finite,ThetaProjectionFiniteEtale.projection_etale,
    actualV_square,actualV_generates,⟨original_quadratic_field_equiv⟩,
    original_relative_field_diagram,original_generic_Spec_diagram,actual_affine_integralClosure⟩

#print axioms actual_literal_normalization
end FourCorner.ThetaCoverNormalization
