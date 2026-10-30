import ThetaCoverClassPortable.Slot03AdjacentBaseChange
import ThetaCoverClassPortable.Slot03AdjacentModel
import Mathlib.AlgebraicGeometry.Geometrically.Connected

noncomputable section
namespace FourCorner.Slot03Adjacent
open AlgebraicGeometry AlgebraicCurve
open scoped TensorProduct

def literalFieldRingEquiv {K : Type*} [Field K] [CharZero K] (c : K)
    (hc : c ≠ 0) (h : AdjacentPolynomials.Admissible c) :
    FractionRing (AdjacentCoordinateAlgebra.CoordinateRing c) ≃+* AdjacentGenus.field c :=
  (AdjacentCoordinateAlgebra.fractionFieldEquiv c hc h).toRingEquiv.trans
    (IntermediateField.equivOfEq (AdjacentCoordinateAlgebra.functionField_eq c hc)).toRingEquiv

theorem field_tensor_domain (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1)
    (L : Type*) [Field L] [Algebra ℚ L] :
    IsDomain (L ⊗[ℚ] AdjacentGenus.field c) := by
  have h := AdjacentPolynomials.rational_admissible (K := ℚ) c hc h1
  have hc0 : c ≠ 0 := ne_of_gt hc
  letI := AdjacentCoordinateAlgebra.coordinateRing_isDomain c h
  letI := tensor_domain c hc h1 L
  letI : IsDomain (L ⊗[ℚ] FractionRing (AdjacentCoordinateAlgebra.CoordinateRing c)) :=
    GeometricFractionField.isDomain_baseChange_fractionRing ℚ
      (AdjacentCoordinateAlgebra.CoordinateRing c)
      (FractionRing (AdjacentCoordinateAlgebra.CoordinateRing c)) L
  let e : FractionRing (AdjacentCoordinateAlgebra.CoordinateRing c) ≃ₐ[ℚ]
      AdjacentGenus.field c :=
    (literalFieldRingEquiv c hc0 h).toRatAlgEquiv
  let e' := Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[ℚ] L) e
  exact Function.Injective.isDomain e'.symm e'.symm.injective

universe u
abbrev modelFieldAlgebra {K : Type u} [Field K] [CharZero K] (c : K) :
    Algebra K (adjacentField c) := inferInstance
abbrev modelToBase {K : Type u} [Field K] [CharZero K] (c : K) := (model c).toBase

def AllTensorDomains (K E : Type u) [Field K] [Field E] [Algebra K E] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L], IsDomain (L ⊗[K] E)

theorem generic_model_geometricallyIntegral {K : Type u} [Field K] [CharZero K]
    (c : K) (hgeom : AllTensorDomains K (adjacentField c)) :
    GeometricallyIntegral (modelToBase c) :=
  SchemeModelGeometricIntegral.model_geometricallyIntegral K (adjacentField c) hgeom

theorem tensor_domain_for_algebra (L : Type) [Field L] [Algebra ℚ L]
    (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1) (a : Algebra ℚ (adjacentField c)) :
    letI := a
    IsDomain (L ⊗[ℚ] adjacentField c) := by
  have ha : a = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  subst a
  exact field_tensor_domain c hc h1 L

theorem model_geometricallyIntegral (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1) :
    GeometricallyIntegral (modelToBase c) :=
  generic_model_geometricallyIntegral c
    (fun L _ _ => tensor_domain_for_algebra L c hc h1 (modelFieldAlgebra c))

theorem model_geometricallyConnected (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1) :
    GeometricallyConnected (modelToBase c) := by
  have h := model_geometricallyIntegral c hc h1
  refine ⟨fun {L} _ y {Z} fst snd hpb => ?_⟩
  have := h.geometrically_isIntegral y fst snd hpb
  infer_instance

#print axioms field_tensor_domain
#print axioms model_geometricallyIntegral
#print axioms model_geometricallyConnected
end FourCorner.Slot03Adjacent
