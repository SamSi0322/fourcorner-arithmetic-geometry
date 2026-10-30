import NormalizationGenericPoint
import CommonPostFiniteP1

noncomputable section
namespace FourCorner.CommonPostGenericEll
open CategoryTheory AlgebraicGeometry AlgebraicCurve IntermediateField
open CommonPostGeometricGenus CommonPostFiniteP1
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

/-- The actual literal field point used in the ell square is the generic point
of the same canonical D_t, not a special or constant point. -/
theorem sourceFieldPoint_generic (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    sourceFieldPoint t h0 h1 hm (IsLocalRing.closedPoint (CommonLiteralField.field ℚ t)) =
      genericPoint (commonCurve t h0 h1 hm) := by
  letI := modelFieldAlgebra t
  letI : FiniteDimensional (RatFunc ℚ) (CommonLiteralField.field ℚ t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen ℚ h0 h1 hm]; norm_num)
  obtain ⟨hf,hi⟩ := CurveModel.finiteDimensional_adjoin_towerGenerator ℚ (L := CommonLiteralField.field ℚ t)
  letI := hf
  letI := hi
  letI : Fact (NormalizedModelCover.fieldInclusion ℚ (CommonLiteralField.field ℚ t) RatFunc.X ≠ 0) :=
    ⟨CurveModel.towerGenerator_ne_zero ℚ⟩
  letI : Fact (CurveModel.towerGenerator ℚ (L := CommonLiteralField.field ℚ t) ≠ 0) :=
    ⟨CurveModel.towerGenerator_ne_zero ℚ⟩
  have h := NormalizationGenericPoint.fieldPoint_generic ℚ (CommonLiteralField.field ℚ t)
    (CurveModel.towerGenerator ℚ)
  change (NormalizedModelCover.sourceIso ℚ (CommonLiteralField.field ℚ t)).inv
    (NormalizationCoverField.fieldPoint ℚ (CommonLiteralField.field ℚ t)
      (CurveModel.towerGenerator ℚ) (IsLocalRing.closedPoint (CommonLiteralField.field ℚ t))) = _
  rw [h]
  exact genericPoint_eq_of_isOpenImmersion (NormalizedModelCover.sourceIso ℚ (CommonLiteralField.field ℚ t)).inv

/-- The finite native ell map's source field point is dominant. -/
theorem sourceFieldPoint_dominant (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    IsDominant (sourceFieldPoint t h0 h1 hm) := by
  constructor
  intro x
  have hr : ({genericPoint (commonCurve t h0 h1 hm)} : Set (commonCurve t h0 h1 hm)) ⊆
      Set.range (sourceFieldPoint t h0 h1 hm) := by
    apply Set.singleton_subset_iff.mpr
    exact ⟨IsLocalRing.closedPoint (CommonLiteralField.field ℚ t),sourceFieldPoint_generic t h0 h1 hm⟩
  have hc := closure_mono hr
  rw [show closure ({genericPoint (commonCurve t h0 h1 hm)} : Set (commonCurve t h0 h1 hm)) = Set.univ from genericPoint_spec _] at hc
  exact hc trivial
end FourCorner.CommonPostGenericEll
#print axioms FourCorner.CommonPostGenericEll.sourceFieldPoint_generic
#print axioms FourCorner.CommonPostGenericEll.sourceFieldPoint_dominant
