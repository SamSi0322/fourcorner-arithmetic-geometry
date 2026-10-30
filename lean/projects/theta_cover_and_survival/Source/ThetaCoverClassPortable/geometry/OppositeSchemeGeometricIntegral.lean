import ThetaCoverClassPortable.geometry.OppositeSchemeModel
import ThetaCoverClassPortable.geometry.OppositeFieldGeometricIntegral
import ThetaCoverClassPortable.geometry.SchemeModelGeometricIntegral
import Mathlib.AlgebraicGeometry.Geometrically.Connected

noncomputable section
namespace FourCorner.OppositeSchemeModel
open AlgebraicGeometry OppositeCoordinateAlgebra
open scoped TensorProduct

universe u

/-- Tensor-domain preservation with the function-field algebra kept explicit. -/
def AllTensorDomains (K E : Type u) [Field K] [Field E] [Algebra K E] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L], IsDomain (L ⊗[K] E)

/-- The constant-field algebra used in the actual generic model construction. -/
abbrev modelFieldAlgebra {K : Type u} [Field K] [CharZero K] (mu nu : K) :
    Algebra K (functionField mu nu) := inferInstance

/-- The structural morphism of the same constructed model. Elaborating its
projection before specializing constants preserves the model's algebra instance. -/
abbrev modelToBase {K : Type u} [Field K] [CharZero K] (mu nu : K) :=
  (model mu nu).toBase

theorem model_geometricallyIntegral_of_tensor {K : Type u} [Field K] [CharZero K]
    (mu nu : K)
    (hgeom : AllTensorDomains K (functionField mu nu)) :
    GeometricallyIntegral (modelToBase mu nu) :=
  SchemeModelGeometricIntegral.model_geometricallyIntegral K (functionField mu nu) hgeom

/-- Rational algebra structures are unique, so the already proved tensor-domain
statement holds for the precise algebra carried by the model as well. -/
theorem rational_tensor_domain_for_algebra (L : Type) [Field L] [Algebra ℚ L]
    (mu nu : ℚ) (hnu : nu ≠ 0) (hpos : 0 < mu / nu) (hlt : mu / nu < 2)
    (a : Algebra ℚ (functionField mu nu)) :
    letI := a
    IsDomain (L ⊗[ℚ] functionField mu nu) := by
  have ha : a = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  subst a
  exact OppositeAffineModel.rational_functionField_all_extensions_domain L mu nu hnu hpos hlt

/-- Every field-valued scheme base change of the actual rational model is
integral. This is Mathlib geometric integrality, not a chosen alternate model. -/
theorem rational_model_geometricallyIntegral (mu nu : ℚ) (hnu : nu ≠ 0)
    (hpos : 0 < mu / nu) (hlt : mu / nu < 2) :
    GeometricallyIntegral (modelToBase mu nu) :=
  model_geometricallyIntegral_of_tensor mu nu
    (fun L _ _ => rational_tensor_domain_for_algebra L mu nu hnu hpos hlt
      (modelFieldAlgebra mu nu))

/-- Every field-valued base change of the same rational model is connected. -/
theorem rational_model_geometricallyConnected (mu nu : ℚ) (hnu : nu ≠ 0)
    (hpos : 0 < mu / nu) (hlt : mu / nu < 2) :
    GeometricallyConnected (modelToBase mu nu) := by
  have h := rational_model_geometricallyIntegral mu nu hnu hpos hlt
  refine ⟨fun {L} _ y {Z} fst snd hpb => ?_⟩
  have := h.geometrically_isIntegral y fst snd hpb
  infer_instance

#print axioms model_geometricallyIntegral_of_tensor
#print axioms rational_tensor_domain_for_algebra
#print axioms rational_model_geometricallyIntegral
#print axioms rational_model_geometricallyConnected
end FourCorner.OppositeSchemeModel
