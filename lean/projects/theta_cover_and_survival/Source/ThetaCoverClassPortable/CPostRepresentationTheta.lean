import ThetaCoverClassPortable.CPostRepresentationProperties
import ThetaCoverClassPortable.ActualFibrePoincareTwistQQ
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_thetaBundle

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
namespace FourCorner.ActualPicardProperties

/-- The genuine determinant theta line bundle of the actual represented C_T,
using r=2g=10 and rank r+1-g=6, from actual C genus five. -/
theorem C_baseChange_theta_invertible
    (T : Type) [CommRing T] [Algebra ℚ T] [IsNoetherianRing T]
    (D : RelativePic0Designation T (SmoothProperCurve.baseChange ℚ (ThetaLiteralModels.cToBase ℚ) T))
    (h : RepresentsRelSubPic (SmoothProperCurve.baseChange ℚ (ThetaLiteralModels.cToBase ℚ) T)
      (SmoothProperCurve.sectionBaseChange T ThetaRationalPicardInput.OC)
      (algEquivZeroCut (SmoothProperCurve.baseChange ℚ (ThetaLiteralModels.cToBase ℚ) T)
        (SmoothProperCurve.sectionBaseChange T ThetaRationalPicardInput.OC)) D)
    [LocallyOfFiniteType D.toBase] :
    Scheme.Modules.IsInvertible (thetaBundle (SmoothProperCurve.baseChange ℚ (ThetaLiteralModels.cToBase ℚ) T)
      (SmoothProperCurve.sectionBaseChange T ThetaRationalPicardInput.OC) D.toBase h.poincare 10 6) := by
  let c := SmoothProperCurve.baseChange ℚ (ThetaLiteralModels.cToBase ℚ) T
  let ε := SmoothProperCurve.sectionBaseChange T ThetaRationalPicardInput.OC
  letI := ThetaRationalPicardInput.source_proper
  letI := ThetaRationalPicardInput.source_smooth
  letI := ThetaRationalPicardInput.source_geometricallyIntegral
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : IsProper c := inferInstance
  haveI : SmoothOfRelativeDimension 1 c := MorphismProperty.pullback_snd _ _ inferInstance
  haveI : GeometricallyIntegral c := inferInstance
  have hF : ∀ m0 : ℕ, ∃ F : SmoothProperCurve.FiniteMapData c ε, m0 ≤ F.m := by
    intro m0
    obtain ⟨F,hF⟩ := CActualRationalInputsCompletion.actual_hF m0
    exact ⟨F.baseChange T,hF⟩
  let F := (ThetaRationalPicardInput.actual_finiteMapData 0).baseChange T
  have hfib := P2MW.ActualFibrePoincareTwistQQ.solution T c ε (algebraMap ℚ T) F D h 5
    (C_baseChange_RR_genus T) 10 (by omega)
  exact AlgebraicGeometry.RelPicard.isInvertible_thetaBundle T c ε hF h.poincare 10 6 hfib

#print axioms C_baseChange_theta_invertible
end FourCorner.ActualPicardProperties
