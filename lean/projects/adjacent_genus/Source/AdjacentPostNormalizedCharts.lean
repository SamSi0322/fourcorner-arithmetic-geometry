import AdjacentPostSourceMap

noncomputable section
namespace FourCorner.AdjacentPostNormalizedCharts
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open Slot03Adjacent AdjacentPostModelSource
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The normalizing parameter is the original conic parameter, embedded in the actual radical field. -/
abbrev parameter (c : K) : adjacentField c := CurveModel.towerGenerator K

theorem parameter_eq (c : K) : parameter c = algebraMap (RatFunc K) (adjacentField c) RatFunc.X := rfl

theorem parameter_ne_zero (c : K) : parameter c ≠ 0 := CurveModel.towerGenerator_ne_zero K

/-- The two chart rings are actual integral closures inside the original adjacent radical field. -/
theorem zero_chart_isIntegralClosure (c : K) :
    IsIntegralClosure (CurveModel.chartRing K ({parameter c} : Set (adjacentField c)))
      (Algebra.adjoin K ({parameter c} : Set (adjacentField c))) (adjacentField c) := inferInstance

theorem infinity_chart_isIntegralClosure (c : K) :
    IsIntegralClosure (CurveModel.chartRing K ({(parameter c)⁻¹} : Set (adjacentField c)))
      (Algebra.adjoin K ({(parameter c)⁻¹} : Set (adjacentField c))) (adjacentField c) := inferInstance

section GenericConstruction
variable (F E : Type u) [Field F] [CharZero F] [Field E]
  [Algebra F E] [Algebra (RatFunc F) E] [IsScalarTower F (RatFunc F) E]
  [FiniteDimensional (RatFunc F) E]

theorem generic_zero_chart_finite :
    Module.Finite (Algebra.adjoin F ({CurveModel.towerGenerator F (L := E)} : Set E))
      (CurveModel.chartRing F ({CurveModel.towerGenerator F (L := E)} : Set E)) := by
  obtain ⟨hf,_⟩ := CurveModel.finiteDimensional_adjoin_towerGenerator F (L := E)
  letI := hf
  exact CurveModel.finite_chartRing F (CurveModel.towerGenerator F)

theorem generic_infinity_chart_finite :
    Module.Finite (Algebra.adjoin F ({(CurveModel.towerGenerator F (L := E))⁻¹} : Set E))
      (CurveModel.chartRing F ({(CurveModel.towerGenerator F (L := E))⁻¹} : Set E)) := by
  obtain ⟨_,hf⟩ := CurveModel.finiteDimensional_adjoin_towerGenerator F (L := E)
  letI := hf
  exact CurveModel.finite_chartRing F ((CurveModel.towerGenerator F)⁻¹)

theorem generic_scheme_eq_normalized_gluing :
    letI : Fact (CurveModel.towerGenerator F (L := E) ≠ 0) := ⟨CurveModel.towerGenerator_ne_zero F⟩
    (SchemeModelFiniteExtension.model F E).C = CurveModel.glued F (CurveModel.towerGenerator F (L := E)) := by
  unfold SchemeModelFiniteExtension.model
  obtain ⟨hf,hi⟩ := CurveModel.finiteDimensional_adjoin_towerGenerator F (L := E)
  rfl

end GenericConstruction

private theorem and_cases_model_C {P Q : Prop} {F E : Type u} [Field F] [Field E] [Algebra F E]
    (h : P ∧ Q) (M : P → Q → CurveModel F E) (Y : Scheme.{u})
    (hY : ∀ p q, (M p q).C = Y) : (And.casesOn h M : CurveModel F E).C = Y := by
  obtain ⟨p,q⟩ := h
  exact hY p q

/-- The supplied model is the actual glued integral-closure-chart Scheme. -/
theorem canonical_eq_normalized_gluing (c : K) :
    letI : Fact (parameter c ≠ 0) := ⟨parameter_ne_zero c⟩
    canonicalScheme c = CurveModel.glued K (parameter c) :=
by
  unfold canonicalScheme Slot03Adjacent.model SchemeModelFiniteExtension.model
  apply and_cases_model_C
  intro p q
  rfl

/-- The actual overlap is localization at the parameter on the zero chart. -/
theorem zero_overlap_localization (c : K) :
    letI := (CurveModel.incl₀ K (parameter c)).toRingHom.toAlgebra
    IsLocalization.Away (CurveModel.tChart K (parameter c))
      (CurveModel.chartRing K ({parameter c,(parameter c)⁻¹} : Set (adjacentField c))) :=
  CurveModel.isLocalization_away_incl₀ K (parameter c) (parameter_ne_zero c)

/-- The actual overlap is localization at the inverse parameter on the infinity chart. -/
theorem infinity_overlap_localization (c : K) :
    letI := (CurveModel.inclInf K (parameter c)).toRingHom.toAlgebra
    IsLocalization.Away (CurveModel.tInvChart K (parameter c))
      (CurveModel.chartRing K ({parameter c,(parameter c)⁻¹} : Set (adjacentField c))) :=
  CurveModel.isLocalization_away_inclInf K (parameter c) (parameter_ne_zero c)

#print axioms parameter_eq
#print axioms zero_chart_isIntegralClosure
#print axioms infinity_chart_isIntegralClosure
#print axioms generic_zero_chart_finite
#print axioms generic_infinity_chart_finite
#print axioms canonical_eq_normalized_gluing
#print axioms zero_overlap_localization
#print axioms infinity_overlap_localization
end FourCorner.AdjacentPostNormalizedCharts
