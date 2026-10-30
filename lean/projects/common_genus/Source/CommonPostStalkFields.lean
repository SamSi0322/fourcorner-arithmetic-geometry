import GenericStalkField
import CommonPostGenericEll

noncomputable section
namespace FourCorner.CommonPostStalkFields
open CategoryTheory AlgebraicGeometry AlgebraicCurve IntermediateField
open CommonPostGeometricGenus CommonPostFiniteP1
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
local instance baseRatAlgebra : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
local instance p1Integral : IsIntegral (ProjectiveLineCharts.P1 ℚ) := ProjectiveLineCharts.integral ℚ

theorem source_stalk_bijective (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    Function.Bijective (Scheme.stalkClosedPointTo (sourceFieldPoint t h0 h1 hm)).hom := by
  letI := modelFieldAlgebra t
  letI : FiniteDimensional (RatFunc ℚ) (CommonLiteralField.field ℚ t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen ℚ h0 h1 hm]; norm_num)
  obtain ⟨hf,hi⟩ := CurveModel.finiteDimensional_adjoin_towerGenerator ℚ (L := CommonLiteralField.field ℚ t)
  letI := hf
  letI := hi
  let s := NormalizedModelCover.fieldInclusion ℚ (CommonLiteralField.field ℚ t) RatFunc.X
  letI : Fact (s ≠ 0) := ⟨CurveModel.towerGenerator_ne_zero ℚ⟩
  letI : FiniteDimensional ℚ⟮s⟯ (CommonLiteralField.field ℚ t) := hf
  letI : FiniteDimensional ℚ⟮s⁻¹⟯ (CommonLiteralField.field ℚ t) := hi
  have h := FractionGenericStalk.open_stalk_eval_bijective
    (CurveModel.chartRing ℚ ({s} : Set (CommonLiteralField.field ℚ t)))
    (CommonLiteralField.field ℚ t)
    (CurveModel.ι₀ ℚ s ≫ (NormalizedModelCover.sourceIso ℚ (CommonLiteralField.field ℚ t)).inv)
  have he : sourceFieldPoint t h0 h1 hm =
      FractionGenericStalk.fieldMap
        (CurveModel.chartRing ℚ ({s} : Set (CommonLiteralField.field ℚ t))) (CommonLiteralField.field ℚ t) ≫
          (CurveModel.ι₀ ℚ s ≫ (NormalizedModelCover.sourceIso ℚ (CommonLiteralField.field ℚ t)).inv) := by
    set_option backward.isDefEq.respectTransparency false in
      simp only [s,sourceFieldPoint,NormalizationCoverField.fieldPoint,FractionGenericStalk.fieldMap,Category.assoc]
  rw [he]
  exact h

private def baseChartOpen :
    Spec (.of (CurveModel.chartRing ℚ ({RatFunc.X} : Set (RatFunc ℚ)))) ⟶ ProjectiveLineCharts.P1 ℚ := by
  letI : Fact ((RatFunc.X : RatFunc ℚ) ≠ 0) := ⟨RatFunc.X_ne_zero⟩
  exact CurveModel.ι₀ ℚ (RatFunc.X : RatFunc ℚ) ≫
    (NormalizedModelCover.baseIso ℚ).inv ≫ NormalizedBaseP1.iso.hom

private instance baseChartOpen_isOpenImmersion : IsOpenImmersion baseChartOpen := by
  unfold baseChartOpen
  infer_instance

private theorem baseFieldPoint_eq : baseFieldPoint =
    FractionGenericStalk.fieldMap
      (CurveModel.chartRing ℚ ({RatFunc.X} : Set (RatFunc ℚ))) (RatFunc ℚ) ≫ baseChartOpen := by
  rfl

theorem base_stalk_bijective : Function.Bijective (Scheme.stalkClosedPointTo baseFieldPoint).hom := by
  letI : Fact ((RatFunc.X : RatFunc ℚ) ≠ 0) := ⟨RatFunc.X_ne_zero⟩
  have h := FractionGenericStalk.open_stalk_eval_bijective
    (CurveModel.chartRing ℚ ({RatFunc.X} : Set (RatFunc ℚ))) (RatFunc ℚ) baseChartOpen
  rwa [← baseFieldPoint_eq] at h

theorem baseFieldPoint_generic : baseFieldPoint (IsLocalRing.closedPoint (RatFunc ℚ)) =
    genericPoint (ProjectiveLineCharts.P1 ℚ) := by
  letI : Fact ((RatFunc.X : RatFunc ℚ) ≠ 0) := ⟨RatFunc.X_ne_zero⟩
  rw [baseFieldPoint_eq]
  exact FractionGenericStalk.open_fieldMap_generic _ _ baseChartOpen

/-- This field isomorphism is induced by the original source field-point
morphism on the actual generic stalk. -/
def sourceEquiv (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    (commonCurve t h0 h1 hm).functionField ≃+* CommonLiteralField.field ℚ t :=
  GenericStalkField.equiv (sourceFieldPoint t h0 h1 hm)
    (CommonPostGenericEll.sourceFieldPoint_generic t h0 h1 hm) (source_stalk_bijective t h0 h1 hm)

def baseEquiv : (ProjectiveLineCharts.P1 ℚ).functionField ≃+* RatFunc ℚ :=
  GenericStalkField.equiv baseFieldPoint baseFieldPoint_generic base_stalk_bijective

theorem source_factor (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    Spec.map (CommRingCat.ofHom (sourceEquiv t h0 h1 hm).toRingHom) ≫
      (commonCurve t h0 h1 hm).fromSpecStalk (genericPoint (commonCurve t h0 h1 hm)) =
        sourceFieldPoint t h0 h1 hm :=
  GenericStalkField.factor _ _ _

theorem base_factor : Spec.map (CommRingCat.ofHom baseEquiv.toRingHom) ≫
    (ProjectiveLineCharts.P1 ℚ).fromSpecStalk (genericPoint (ProjectiveLineCharts.P1 ℚ)) =
      baseFieldPoint := GenericStalkField.factor _ _ _
end FourCorner.CommonPostStalkFields
#print axioms FourCorner.CommonPostStalkFields.sourceEquiv
#print axioms FourCorner.CommonPostStalkFields.baseEquiv
#print axioms FourCorner.CommonPostStalkFields.source_factor
#print axioms FourCorner.CommonPostStalkFields.base_factor
