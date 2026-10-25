import NormalizedModelCover
import AdjacentPostEndpoint

noncomputable section
namespace FourCorner.AdjacentNormalizationCover
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open Slot03Adjacent AdjacentPostModelSource
universe u
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev baseScheme (K : Type u) [Field K] [CharZero K] := (NormalizedModelCover.baseModel K).C
abbrev baseToBase (K : Type u) [Field K] [CharZero K] := (NormalizedModelCover.baseModel K).toBase
abbrev baseFieldEquiv (K : Type u) [Field K] [CharZero K] := (NormalizedModelCover.baseModel K).ffEquiv

section Generic
variable {K : Type u} [Field K] [CharZero K]

/-- The actual finite normalization morphism in the original adjacent conic function-field extension. -/
def genericCover (c : K) : canonicalScheme c ⟶ baseScheme K := by
  letI := modelFieldAlgebra c
  letI : Algebra (RatFunc K) (adjacentField c) := (adjacentField c).toSubalgebra.algebra
  haveI : IsScalarTower K (RatFunc K) (adjacentField c) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply K (RatFunc K) (AlgebraicClosure (RatFunc K)) a
  letI : FiniteDimensional (RatFunc K) (adjacentField c) :=
    Multiquadratic.Tower.finiteDimensional_second (RatFunc K)
      (AdjacentPlaceOrders.actualValue c 0) (AdjacentPlaceOrders.actualValue c 1)
  exact NormalizedModelCover.cover K (adjacentField c)

theorem genericCover_isFinite (c : K) : IsFinite (genericCover c) := by
  letI := modelFieldAlgebra c
  letI : Algebra (RatFunc K) (adjacentField c) := (adjacentField c).toSubalgebra.algebra
  haveI : IsScalarTower K (RatFunc K) (adjacentField c) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply K (RatFunc K) (AlgebraicClosure (RatFunc K)) a
  letI : FiniteDimensional (RatFunc K) (adjacentField c) :=
    Multiquadratic.Tower.finiteDimensional_second (RatFunc K)
      (AdjacentPlaceOrders.actualValue c 0) (AdjacentPlaceOrders.actualValue c 1)
  exact NormalizedModelCover.cover_isFinite K (adjacentField c)

/-- Coordinate-preserving identification with the actual function field of the base conic model. -/
def genericConicFunctionFieldEquiv (c : K) (hc : c ≠ 0) (hA : c^2-1 ≠ 0) :
    FractionRing (AdjacentConicLiteralModel.CoordinateRing c) ≃+* (baseScheme K).functionField :=
  (AdjacentConicLiteralModel.functionFieldEquiv c hc hA).toRingEquiv.trans (baseFieldEquiv K)

end Generic

abbrev cover (c : ℚ) : canonicalScheme c ⟶ baseScheme ℚ := genericCover c
theorem cover_isFinite (c : ℚ) : IsFinite (cover c) := genericCover_isFinite c

def conicFunctionFieldEquiv (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1) :
    FractionRing (AdjacentConicLiteralModel.CoordinateRing c) ≃+* (baseScheme ℚ).functionField :=
  genericConicFunctionFieldEquiv c (ne_of_gt hc)
    (AdjacentPolynomials.rational_admissible_self c hc h1).conic_ne_zero

theorem conicFunctionFieldEquiv_U (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1) :
    conicFunctionFieldEquiv c hc h1
      (algebraMap (AdjacentConicLiteralModel.CoordinateRing c)
        (FractionRing (AdjacentConicLiteralModel.CoordinateRing c))
        (AdjacentConicLiteralModel.coordinateU c)) = baseFieldEquiv ℚ (AdjacentConic.u c) := by
  change baseFieldEquiv ℚ (AdjacentConicLiteralModel.functionFieldEquiv c _ _ _) = _
  rw [AdjacentConicLiteralModel.functionFieldEquiv_U]

theorem conicFunctionFieldEquiv_V (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1) :
    conicFunctionFieldEquiv c hc h1
      (algebraMap (AdjacentConicLiteralModel.CoordinateRing c)
        (FractionRing (AdjacentConicLiteralModel.CoordinateRing c))
        (AdjacentConicLiteralModel.coordinateV c)) = baseFieldEquiv ℚ (AdjacentConic.v c) := by
  change baseFieldEquiv ℚ (AdjacentConicLiteralModel.functionFieldEquiv c _ _ _) = _
  rw [AdjacentConicLiteralModel.functionFieldEquiv_V]

theorem conicFunctionFieldEquiv_slope (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1) :
    conicFunctionFieldEquiv c hc h1
      (AdjacentConicLiteralModel.slope c (ne_of_gt hc)
        (AdjacentPolynomials.rational_admissible_self c hc h1).conic_ne_zero) =
      baseFieldEquiv ℚ RatFunc.X := by
  change baseFieldEquiv ℚ (AdjacentConicLiteralModel.functionFieldEquiv c _ _ _) = _
  rw [AdjacentConicLiteralModel.functionFieldEquiv_slope]

/-- The actual normalization cover respects the original rational structural maps. -/
theorem cover_over (c : ℚ) : cover c ≫ baseToBase ℚ = modelToBase c := by
  haveI : IsIntegral (canonicalScheme c) := model_integral c
  haveI : IsDominant ((canonicalScheme c).fromSpecStalk (genericPoint (canonicalScheme c))) := ⟨by
    rw [DenseRange,Scheme.range_fromSpecStalk]
    refine Dense.mono (Set.singleton_subset_iff.mpr (specializes_refl (genericPoint (canonicalScheme c)))) ?_
    exact dense_iff_closure_eq.mpr (genericPoint_spec (canonicalScheme c))⟩
  apply ext_of_isDominant ((canonicalScheme c).fromSpecStalk (genericPoint (canonicalScheme c)))
  apply Spec.homEquiv.injective
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _

/-- Exact parameter hypotheses, genuine finite normalization cover, and both requested
geometric conclusions on its actual source and actual Qbar base change. -/
theorem adjacent_normalized_cover_connected_genus_five (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1) :
    IsFinite (cover c) ∧ GeometricallyConnected (modelToBase c) ∧
    (letI := Slot03HighAdjacent.geometricIntegral c hc h1
     letI := (baseToFunctionField (Slot03HighAdjacent.geometricToBase c)).toAlgebra
     genusFF (AlgebraicClosure ℚ) (Slot03HighAdjacent.geometricScheme c).functionField = 5) ∧
    (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
       (Slot03HighAdjacent.geometricToBase c) (Slot03HighAdjacent.geometricToBase c).kaehler ⊤
     Module.Finite (AlgebraicClosure ℚ) Γ((Slot03HighAdjacent.geometricToBase c).kaehler, ⊤) ∧
       Module.finrank (AlgebraicClosure ℚ) Γ((Slot03HighAdjacent.geometricToBase c).kaehler, ⊤) = 5) :=
  ⟨cover_isFinite c,model_geometricallyConnected c hc h1,
    Slot03HighAdjacent.geometric_genus_five c hc h1,
    Slot03HighAdjacent.geometric_globalDifferentials_five c hc h1⟩

#print axioms cover
#print axioms cover_isFinite
#print axioms cover_over
#print axioms conicFunctionFieldEquiv_slope
#print axioms conicFunctionFieldEquiv_U
#print axioms conicFunctionFieldEquiv_V
#print axioms adjacent_normalized_cover_connected_genus_five
end FourCorner.AdjacentNormalizationCover
