import ThetaCoverClassPortable.DPostRepresentationProperties
import ThetaCoverClassPortable.ActualFibrePoincareTwistQQ
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_thetaBundle
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
namespace FourCorner.ActualPicardProperties

/-- The genuine determinant theta line bundle of the actual represented D_T,
using degree six and its proved rank four. -/
theorem D_baseChange_theta_invertible
    (T : Type) [CommRing T] [Algebra ℚ T] [IsNoetherianRing T]
    (D : RelativePic0Designation T (SmoothProperCurve.baseChange ℚ DRationalInputs.toBase T))
    (h : RepresentsRelSubPic (SmoothProperCurve.baseChange ℚ DRationalInputs.toBase T)
      (SmoothProperCurve.sectionBaseChange T DRationalInputs.OD)
      (algEquivZeroCut (SmoothProperCurve.baseChange ℚ DRationalInputs.toBase T)
        (SmoothProperCurve.sectionBaseChange T DRationalInputs.OD)) D)
    [LocallyOfFiniteType D.toBase] :
    Scheme.Modules.IsInvertible (thetaBundle (SmoothProperCurve.baseChange ℚ DRationalInputs.toBase T)
      (SmoothProperCurve.sectionBaseChange T DRationalInputs.OD) D.toBase h.poincare 6 4) := by
  let c := SmoothProperCurve.baseChange ℚ DRationalInputs.toBase T
  let ε := SmoothProperCurve.sectionBaseChange T DRationalInputs.OD
  letI := DRationalInputs.proper
  letI := DRationalInputs.smooth
  letI := DRationalInputs.geometricallyIntegral
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : IsProper c := inferInstance
  haveI : SmoothOfRelativeDimension 1 c := MorphismProperty.pullback_snd _ _ inferInstance
  haveI : GeometricallyIntegral c := inferInstance
  have hF : ∀ m0 : ℕ, ∃ F : SmoothProperCurve.FiniteMapData c ε, m0 ≤ F.m := by
    intro m0
    obtain ⟨F,hF,_⟩ := DRationalInputs.actual_unbounded_finiteMapData_baseChange T m0
    exact ⟨F,hF⟩
  let F := (DRationalInputs.actual_finiteMapData 0).baseChange T
  have hfib := P2MW.ActualFibrePoincareTwistQQ.solution T c ε (algebraMap ℚ T) F D h 3
    (D_baseChange_RR_genus T) 6 (by omega)
  exact AlgebraicGeometry.RelPicard.isInvertible_thetaBundle T c ε hF h.poincare 6 4 hfib

#print axioms D_baseChange_theta_invertible
end FourCorner.ActualPicardProperties
