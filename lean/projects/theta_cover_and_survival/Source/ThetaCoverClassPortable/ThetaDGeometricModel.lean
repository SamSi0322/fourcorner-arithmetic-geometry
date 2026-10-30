import ThetaCoverClassPortable.ThetaFlatIntegralDescent
import ThetaCoverClassPortable.ThetaProjectionDegree
import ThetaCoverClassPortable.ThetaSourceGenus
import ThetaCoverClassPortable.ThetaTargetSmooth

namespace FourCorner.ThetaDGeometricModel
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve ThetaLiteralModels
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

abbrev K := AlgebraicClosure ℚ
abbrev qb := Scheme.TwoAffineOpenCover.specMap ℚ K
abbrev geometricD := pullback (dToBase ℚ) qb
abbrev toBase : geometricD ⟶ Spec (.of K) := pullback.snd (dToBase ℚ) qb
abbrev projection := ThetaProjection.projection (k:=ℚ)
lemma projection_over : projection ≫ dToBase ℚ=cToBase ℚ :=
  ThetaSourceComparison.rational_base_unique _ _

/-- The standard base change of the ACTUAL finite etale covering map. -/
abbrev coverSource := pullback projection (pullback.fst (dToBase ℚ) qb)
abbrev coverMap : coverSource ⟶ geometricD := pullback.snd projection (pullback.fst (dToBase ℚ) qb)

def coverSourceIso : coverSource ≅ ThetaSourceGenus.geometricScheme := by
  simpa only [projection_over] using pullbackRightPullbackFstIso (dToBase ℚ) qb projection

theorem cover_integral : IsIntegral coverSource := by
  letI := ThetaSourceGenus.geometric_integral
  exact IsIntegral.of_isIso coverSourceIso.inv

theorem cover_flat : Flat coverMap := by
  letI := ThetaProjectionFiniteEtale.projection_etale
  infer_instance

theorem cover_surjective : Surjective coverMap := by
  letI := ThetaProjectionDegree.projection_surjective
  infer_instance

/-- Integrality of the ACTUAL Qbar pullback of the ORIGINAL plane quartic,
derived from the SAME geometrically integral cover and faithful-flat descent. -/
theorem geometric_integral : IsIntegral geometricD := by
  letI := cover_integral
  letI := cover_flat
  letI := cover_surjective
  exact ThetaFlatIntegralDescent.integral coverMap

theorem geometric_proper : IsProper toBase := by
  letI := d_proper ℚ
  infer_instance

theorem geometric_smooth : SmoothOfRelativeDimension 1 toBase := by
  letI := ThetaTargetSmooth.target_smooth (k:=ℚ)
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  exact MorphismProperty.pullback_snd (P:=@SmoothOfRelativeDimension 1) _ _ inferInstance

local instance integralD : IsIntegral geometricD := geometric_integral
abbrev field : Type := geometricD.functionField
abbrev fieldAlgebra : Algebra K field := (baseToFunctionField toBase).toAlgebra

/-- The true native function field of this same original geometric curve
is a curve function field; no genus or auxiliary field comparison is assumed. -/
theorem field_isCurveOver :
    letI := fieldAlgebra; IsCurveOver K field := by
  letI := geometric_integral
  letI := geometric_smooth
  letI := fieldAlgebra
  exact isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one toBase (RingEquiv.refl _) (fun _ => rfl)

theorem field_essFiniteType :
    letI := fieldAlgebra; Algebra.EssFiniteType K field := by
  letI := geometric_proper
  letI := geometric_integral
  letI := geometric_smooth
  letI := fieldAlgebra
  exact essFiniteType_functionField toBase

/-- A genuine CurveModel and actual over-K isomorphism for the NATIVE
function field of original D_Qbar, from the frozen generic construction. -/
theorem exists_model :
    letI := geometric_integral
    letI := fieldAlgebra
    ∃M : CurveModel K geometricD.functionField,∃i : geometricD ≅ M.C,i.hom ≫ M.toBase=toBase := by
  letI := geometric_integral
  letI := geometric_smooth
  letI := geometric_proper
  obtain ⟨M,i,hi,_⟩ := NativeCurveModelExistence.exists_model toBase
  exact ⟨M,i,hi⟩

#print axioms geometric_integral
#print axioms geometric_smooth
#print axioms field_isCurveOver
#print axioms field_essFiniteType
#print axioms exists_model
end
end FourCorner.ThetaDGeometricModel
