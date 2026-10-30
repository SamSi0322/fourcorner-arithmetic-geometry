import ThetaCoverClassPortable.ThetaCoverQuadraticCoefficientData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits

namespace FourCorner.ThetaQuadraticCurve
open ThetaLiteralModels ThetaDGeometricModel

abbrev F := ThetaSqrtTwo
abbrev coefficientEmbedding := ThetaCoverQuadraticCoefficientData.coefficientEmbedding
abbrev baseMap := Scheme.TwoAffineOpenCover.specMap ℚ F
abbrev curve := pullback (dToBase ℚ) baseMap
abbrev toBase : curve ⟶ Spec (.of F) := pullback.snd (dToBase ℚ) baseMap
abbrev toRational : curve ⟶ D ℚ := pullback.fst (dToBase ℚ) baseMap
abbrev extensionMap : Spec (.of K) ⟶ Spec (.of F) :=
  Spec.map (CommRingCat.ofHom coefficientEmbedding.toRingHom)

theorem extensionMap_comp : extensionMap ≫ baseMap = qb :=
  ThetaSourceComparison.rational_base_unique _ _

abbrev geometricBaseChange := pullback toBase extensionMap

/-- The actual map from the original geometric curve to its quadratic model. -/
def geometricProjection : geometricD ⟶ curve :=
  pullback.lift (pullback.fst (dToBase ℚ) qb)
    (ThetaDGeometricModel.toBase ≫ extensionMap) (by
      rw [Category.assoc, extensionMap_comp, pullback.condition])

@[reassoc (attr := simp)] theorem geometricProjection_toRational :
    geometricProjection ≫ toRational = pullback.fst (dToBase ℚ) qb := by
  simp [geometricProjection, toRational]

@[reassoc (attr := simp)] theorem geometricProjection_toBase :
    geometricProjection ≫ toBase = ThetaDGeometricModel.toBase ≫ extensionMap := by
  simp [geometricProjection, toBase]

/-- Both directions retain the two actual pullback projections. -/
def geometricBaseChangeIso : geometricBaseChange ≅ geometricD where
  hom := pullback.lift (pullback.fst toBase extensionMap ≫ toRational)
    (pullback.snd toBase extensionMap) (by
      rw [Category.assoc, pullback.condition, ← extensionMap_comp]
      simp only [← Category.assoc, pullback.condition])
  inv := pullback.lift geometricProjection ThetaDGeometricModel.toBase
    geometricProjection_toBase
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [geometricProjection, toRational, Category.assoc]
      · simpa [geometricProjection, toBase, Category.assoc] using
          (pullback.condition (f := toBase) (g := extensionMap)).symm
    · simp
  inv_hom_id := by
    apply pullback.hom_ext <;> simp [geometricProjection, toRational, Category.assoc]

@[reassoc (attr := simp)] theorem geometricBaseChangeIso_fst :
    geometricBaseChangeIso.hom ≫ pullback.fst (dToBase ℚ) qb =
      pullback.fst toBase extensionMap ≫ toRational := by
  simp [geometricBaseChangeIso]

@[reassoc (attr := simp)] theorem geometricBaseChangeIso_snd :
    geometricBaseChangeIso.hom ≫ ThetaDGeometricModel.toBase =
      pullback.snd toBase extensionMap := by
  simp [geometricBaseChangeIso, ThetaDGeometricModel.toBase]

theorem extensionMap_surjective : Surjective extensionMap := by
  constructor
  intro q
  exact ⟨(⊥ : PrimeSpectrum K), Subsingleton.elim _ _⟩

theorem extensionMap_flat : Flat extensionMap := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  letI : Algebra F K := coefficientEmbedding.toRingHom.toAlgebra
  change (algebraMap F K).Flat
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

theorem curve_integral : IsIntegral curve := by
  letI := geometric_integral
  letI : IsIntegral geometricBaseChange := IsIntegral.of_isIso geometricBaseChangeIso.inv
  letI := extensionMap_surjective
  letI := extensionMap_flat
  exact ThetaFlatIntegralDescent.integral (pullback.fst toBase extensionMap)

theorem curve_proper : IsProper toBase := by
  letI := d_proper ℚ
  infer_instance

theorem curve_smooth : SmoothOfRelativeDimension 1 toBase := by
  letI := ThetaTargetSmooth.target_smooth (k := ℚ)
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance

theorem geometricProjection_surjective : Surjective geometricProjection := by
  have he : geometricProjection = geometricBaseChangeIso.inv ≫
      pullback.fst toBase extensionMap := by simp [geometricBaseChangeIso]
  rw [he]
  letI := extensionMap_surjective
  infer_instance

theorem baseMap_surjective : Surjective baseMap := by
  constructor
  intro q
  exact ⟨(⊥ : PrimeSpectrum F), Subsingleton.elim _ _⟩

theorem toRational_surjective : Surjective toRational := by
  letI := baseMap_surjective
  infer_instance

local instance : IsIntegral curve := curve_integral
abbrev functionField := curve.functionField
abbrev fieldAlgebra : Algebra F functionField := (baseToFunctionField toBase).toAlgebra

theorem field_isCurveOver : letI := fieldAlgebra; IsCurveOver F functionField := by
  letI := curve_smooth
  letI := fieldAlgebra
  exact isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one toBase
    (RingEquiv.refl _) (fun _ => rfl)

theorem field_essFiniteType : letI := fieldAlgebra; Algebra.EssFiniteType F functionField := by
  letI := curve_proper
  letI := curve_smooth
  letI := fieldAlgebra
  exact essFiniteType_functionField toBase

end FourCorner.ThetaQuadraticCurve
