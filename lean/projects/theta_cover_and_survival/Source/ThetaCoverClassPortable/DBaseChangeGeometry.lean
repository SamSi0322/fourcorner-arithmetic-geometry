import ThetaCoverClassPortable.DFieldCore
import ThetaCoverClassPortable.ThetaRationalPicardInput
import ThetaCoverClassPortable.ThetaFlatIntegralDescent
import ThetaCoverClassPortable.ThetaIsoFunctionField

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
namespace FourCorner.DRationalInputs
open ThetaLiteralModels

abbrev projection : C ℚ ⟶ curve := ThetaProjection.projection (k:=ℚ)
theorem projection_over : projection ≫ toBase = cToBase ℚ :=
  ThetaSourceComparison.rational_base_unique _ _

abbrev XAt {K : Type} [Field K] (y : Spec (.of K) ⟶ Spec (.of ℚ)) := pullback toBase y
abbrev cAt {K : Type} [Field K] (y : Spec (.of K) ⟶ Spec (.of ℚ)) := pullback.snd toBase y
abbrev coverSource {K : Type} [Field K] (y : Spec (.of K) ⟶ Spec (.of ℚ)) :=
  pullback projection (pullback.fst toBase y)
abbrev coverMap {K : Type} [Field K] (y : Spec (.of K) ⟶ Spec (.of ℚ)) : coverSource y ⟶ XAt y :=
  pullback.snd projection (pullback.fst toBase y)
abbrev sourceBase {K : Type} [Field K] (y : Spec (.of K) ⟶ Spec (.of ℚ)) : coverSource y ⟶ Spec (.of K) :=
  coverMap y ≫ cAt y

variable {K : Type} [Field K] (y : Spec (.of K) ⟶ Spec (.of ℚ))

def sourceMap : coverSource y ⟶ pullback (cToBase ℚ) y :=
  pullback.lift (pullback.fst projection (pullback.fst toBase y)) (sourceBase y) (by
    rw [← projection_over, ← Category.assoc, pullback.condition]
    simp only [sourceBase, coverMap, cAt, Category.assoc, pullback.condition])

def mapFromC : pullback (cToBase ℚ) y ⟶ XAt y :=
  pullback.lift (pullback.fst (cToBase ℚ) y ≫ projection) (pullback.snd (cToBase ℚ) y) (by
    rw [Category.assoc, projection_over, pullback.condition])

def sourceInv : pullback (cToBase ℚ) y ⟶ coverSource y :=
  pullback.lift (pullback.fst (cToBase ℚ) y) (mapFromC y) (by simp [mapFromC])

/-- Actual associativity comparison for the base change of the original pi. -/
def sourceIso : coverSource y ≅ pullback (cToBase ℚ) y where
  hom := sourceMap y
  inv := sourceInv y
  hom_inv_id := by
    apply pullback.hom_ext
    · simp [sourceMap, sourceInv, Category.assoc]
    · apply pullback.hom_ext
      · simpa [sourceMap, sourceInv, mapFromC, Category.assoc] using
          (pullback.condition (f:=projection) (g:=pullback.fst toBase y))
      · simp [sourceMap, sourceInv, mapFromC, sourceBase, coverMap, cAt, Category.assoc]
  inv_hom_id := by
    apply pullback.hom_ext <;>
      simp [sourceMap, sourceInv, mapFromC, sourceBase, coverMap, cAt, Category.assoc]

theorem sourceIso_over : (sourceIso y).hom ≫ pullback.snd (cToBase ℚ) y = sourceBase y := by
  simp [sourceIso, sourceMap]

theorem cover_finite : IsFinite (coverMap y) := by
  letI := ThetaProjectionFiniteEtale.projection_finite
  infer_instance

theorem cover_etale : Etale (coverMap y) := by
  letI := ThetaProjectionFiniteEtale.projection_etale
  infer_instance

theorem cover_flat : Flat (coverMap y) := by
  letI := ThetaProjectionFiniteEtale.projection_etale
  infer_instance

theorem cover_surjective : Surjective (coverMap y) := by
  letI := ThetaProjectionDegree.projection_surjective
  infer_instance

theorem cover_rank (z : XAt y) : (coverMap y).finrank z = 2 := by
  letI := ThetaProjectionFiniteEtale.projection_finite
  letI := ThetaProjectionFiniteEtale.projection_etale
  rw [Scheme.Hom.finrank_pullback_snd]
  exact ThetaProjectionDegree.projection_degree_two _

theorem source_integral_at : IsIntegral (coverSource y) := by
  letI := FourCorner.ThetaRationalPicardInput.source_geometricallyIntegral
  letI : IsIntegral (pullback (cToBase ℚ) y) :=
    GeometricallyIntegral.geometrically_isIntegral (f:=cToBase ℚ) y
      (pullback.fst _ _) (pullback.snd _ _) (.of_hasPullback _ _)
  exact IsIntegral.of_isIso (sourceIso y).inv

/-- Every actual field base change of the ORIGINAL D is integral, proved by
faithfully flat descent along the actual original finite etale pi. -/
theorem integral_at : IsIntegral (XAt y) := by
  letI := source_integral_at y
  letI := cover_flat y
  letI := cover_surjective y
  exact ThetaFlatIntegralDescent.integral (coverMap y)

theorem geometricallyIntegral : GeometricallyIntegral toBase := by
  constructor
  intro L _ t Z fst snd hpb
  letI := integral_at t
  exact IsIntegral.of_isIso hpb.isoPullback.inv

theorem proper_at : IsProper (cAt y) := by
  letI := proper
  infer_instance

theorem smooth_at : SmoothOfRelativeDimension 1 (cAt y) := by
  letI := smooth
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  exact MorphismProperty.pullback_snd (P:=@SmoothOfRelativeDimension 1) _ _ inferInstance

theorem source_proper_at : IsProper (sourceBase y) := by
  letI := proper_at y
  letI := cover_finite y
  infer_instance

theorem source_smooth_at : SmoothOfRelativeDimension 1 (sourceBase y) := by
  letI := smooth_at y
  letI := cover_etale y
  haveI : SmoothOfRelativeDimension 0 (coverMap y) := inferInstance
  change SmoothOfRelativeDimension (0+1) (coverMap y ≫ cAt y)
  infer_instance

end FourCorner.DRationalInputs
