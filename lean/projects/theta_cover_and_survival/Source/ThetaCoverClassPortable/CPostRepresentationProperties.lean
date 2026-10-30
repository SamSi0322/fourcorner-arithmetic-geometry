import ThetaCoverClassPortable.ActualPicardProperConnectedQ
import ThetaCoverClassPortable.CBaseChangeModelGenus
import ThetaCoverClassPortable.CActualRepresentedSplitBase
import ThetaCoverClassPortable.ActualRelativeOpenChartInputs
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_smooth_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 16000000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian
namespace FourCorner.ActualPicardProperties

/-- Conditional properties of the SAME actual C/QQ base change and SAME
native OC once its actual relative Picard representation is constructed.
Every curve/FMD/relative-affine/genus input is supplied internally. -/
theorem C_baseChange_postrep_properties
    (T : Type) [CommRing T] [Algebra ℚ T] [IsNoetherianRing T]
    (D : RelativePic0Designation T (SmoothProperCurve.baseChange ℚ (ThetaLiteralModels.cToBase ℚ) T))
    (h : RepresentsRelSubPic (SmoothProperCurve.baseChange ℚ (ThetaLiteralModels.cToBase ℚ) T)
      (SmoothProperCurve.sectionBaseChange T ThetaRationalPicardInput.OC)
      (algEquivZeroCut (SmoothProperCurve.baseChange ℚ (ThetaLiteralModels.cToBase ℚ) T)
        (SmoothProperCurve.sectionBaseChange T ThetaRationalPicardInput.OC)) D)
    [LocallyOfFiniteType D.toBase] :
    Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase ∧ IsSeparated D.toBase := by
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
  have hcov := ThetaRationalPicardInput.actual_curve_relative_affines T
  have hg := C_baseChange_RR_genus T
  have hsm := AlgebraicGeometry.RelPicard.smooth_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
    T c ε hF D h
  obtain ⟨hpr,hgc⟩ := proper_and_connected_of_represents_Q_and_curve_affines T (algebraMap ℚ T)
    c ε hF hcov 5 hg D h
  letI := hpr
  exact ⟨hsm,hpr,hgc,inferInstance⟩

#print axioms C_baseChange_postrep_properties
end FourCorner.ActualPicardProperties
