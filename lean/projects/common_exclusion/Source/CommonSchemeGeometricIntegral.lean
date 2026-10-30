import CommonSchemeModel
import CommonGeometricField
import geometry.SchemeModelGeometricIntegral
import Mathlib.AlgebraicGeometry.Geometrically.Connected

noncomputable section
namespace FourCorner.CommonSchemeModel
open AlgebraicGeometry
open scoped TensorProduct
universe u

def AllTensorDomains (K E : Type u) [Field K] [Field E] [Algebra K E] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L], IsDomain (L ⊗[K] E)

abbrev modelToBase {K : Type u} [Field K] [CharZero K]
    (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :=
  (model t ht0 ht1 htm).toBase

theorem model_geometricallyIntegral_of_tensor {K : Type u} [Field K] [CharZero K]
    (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1)
    (hgeom : AllTensorDomains K (CommonLiteralField.field K t)) :
    GeometricallyIntegral (modelToBase t ht0 ht1 htm) := by
  letI : FiniteDimensional (RatFunc K) (CommonLiteralField.field K t) :=
    FiniteDimensional.of_finrank_pos (by
      rw [CommonLiteralField.finrank_field_eq_sixteen K ht0 ht1 htm]; norm_num)
  exact SchemeModelGeometricIntegral.model_geometricallyIntegral K
    (CommonLiteralField.field K t) hgeom

/-- The actual smooth proper model is geometrically integral under EVERY
field-valued scheme base change. -/
theorem model_geometricallyIntegral {K : Type u} [Field K] [CharZero K]
    (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    GeometricallyIntegral (modelToBase t ht0 ht1 htm) :=
  model_geometricallyIntegral_of_tensor t ht0 ht1 htm
    (fun L _ _ => CommonGeometricField.all_constants_domain K L ht0 ht1 htm)

theorem rational_model_geometricallyIntegral (t : ℚ)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    GeometricallyIntegral (modelToBase t ht0 ht1 htm) :=
  model_geometricallyIntegral t ht0 ht1 htm

/-- All base changes of that same rational proper model are connected. -/
theorem rational_model_geometricallyConnected (t : ℚ)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    GeometricallyConnected (modelToBase t ht0 ht1 htm) := by
  have h := rational_model_geometricallyIntegral t ht0 ht1 htm
  refine ⟨fun {L} _ y {Z} fst snd hpb => ?_⟩
  have := h.geometrically_isIntegral y fst snd hpb
  infer_instance

#print axioms model_geometricallyIntegral
#print axioms rational_model_geometricallyIntegral
#print axioms rational_model_geometricallyConnected
end FourCorner.CommonSchemeModel
