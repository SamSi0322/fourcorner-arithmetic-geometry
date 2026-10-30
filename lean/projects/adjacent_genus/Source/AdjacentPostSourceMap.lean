import ProperCurveExtension
import AdjacentPostModelSource

noncomputable section
namespace FourCorner.AdjacentPostSourceMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open Slot03Adjacent Slot03HighAdjacentProjective AdjacentPostModelSource
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The function-field comparison preserves every actual literal regular function,
including all four ordered original coordinates. -/
theorem literalGenericFieldEquiv_coordinate (c : K) (h : AdjacentPolynomials.Admissible c)
    (a : literalR c) :
    letI := AdjacentCoordinateAlgebra.coordinateRing_isDomain c h
    letI : Algebra (literalR c) (Spec (.of (literalR c))).functionField :=
      instAlgebraCarrierFunctionFieldSpec (.of (literalR c))
    literalGenericFieldEquiv c h
      (algebraMap (literalR c) (Spec (.of (literalR c))).functionField a) =
      canonicalFieldEquiv c
        (IntermediateField.equivOfEq (AdjacentCoordinateAlgebra.functionField_eq c h.c_ne_zero)
          (AdjacentCoordinateAlgebra.embedding c h.c_ne_zero a)) := by
  letI := AdjacentCoordinateAlgebra.coordinateRing_isDomain c h
  letI : Algebra (literalR c) (Spec (.of (literalR c))).functionField :=
    instAlgebraCarrierFunctionFieldSpec (.of (literalR c))
  haveI : IsFractionRing (literalR c) (Spec (.of (literalR c))).functionField :=
    functionField_isFractionRing_of_affine (.of (literalR c))
  change canonicalFieldEquiv c
    (literalFieldRingEquiv c h.c_ne_zero h
      ((FractionRing.algEquiv (literalR c) (Spec (.of (literalR c))).functionField).symm
        (algebraMap (literalR c) (Spec (.of (literalR c))).functionField a))) = _
  rw [AlgEquiv.commutes]
  unfold literalFieldRingEquiv
  simp only [RingEquiv.trans_apply, RingEquiv.coe_toRingHom, AlgEquiv.toRingEquiv_eq_coe,
    AlgEquiv.coe_ringEquiv]
  rw [AdjacentCoordinateAlgebra.fractionFieldEquiv_algebraMap]

theorem canonicalSeparated (c : ℚ) : (canonicalScheme c).IsSeparated := by
  haveI : IsProper (modelToBase c) := inferInstance
  constructor
  rw [← terminal.comp_from (modelToBase c)]
  infer_instance

/-- The actual whole literal affine source maps to the canonical integral-closure-chart model.
This is extended by properness from its constructed, equation-preserving generic map. -/
def sourceToModel (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1) :
    Spec (.of (literalR c)) ⟶ canonicalScheme c := by
  let h := AdjacentPolynomials.rational_admissible_self c hc h1
  letI := AdjacentCoordinateAlgebra.coordinateRing_isDomain c h
  letI := literal_smooth c h
  letI := canonicalSeparated c
  haveI : IsProper (modelToBase c) := inferInstance
  exact ProperCurveExtension.extension
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ (literalR c)))) (modelToBase c)
    (literalGenericMap c h) (by
      apply Spec.homEquiv.injective
      apply CommRingCat.hom_ext
      exact Subsingleton.elim _ _)

/-- The extension really restricts to the original function-field morphism. -/
theorem generic_sourceToModel (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1) :
    let h := AdjacentPolynomials.rational_admissible_self c hc h1
    letI := AdjacentCoordinateAlgebra.coordinateRing_isDomain c h
    (Spec (.of (literalR c))).fromSpecStalk (genericPoint (Spec (.of (literalR c)))) ≫
      sourceToModel c hc h1 = literalGenericMap c h := by
  let h := AdjacentPolynomials.rational_admissible_self c hc h1
  letI := AdjacentCoordinateAlgebra.coordinateRing_isDomain c h
  letI := literal_smooth c h
  letI := canonicalSeparated c
  haveI : IsProper (modelToBase c) := inferInstance
  exact ProperCurveExtension.generic_extension
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ (literalR c)))) (modelToBase c)
    (literalGenericMap c h) (by
      apply Spec.homEquiv.injective
      apply CommRingCat.hom_ext
      exact Subsingleton.elim _ _)

/-- The whole source map is over the original rational coefficient field. -/
theorem sourceToModel_over (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1) :
    sourceToModel c hc h1 ≫ modelToBase c =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (literalR c))) := by
  apply Spec.homEquiv.injective
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _

#print axioms literalGenericFieldEquiv_coordinate
#print axioms sourceToModel
#print axioms generic_sourceToModel
#print axioms sourceToModel_over
end FourCorner.AdjacentPostSourceMap
