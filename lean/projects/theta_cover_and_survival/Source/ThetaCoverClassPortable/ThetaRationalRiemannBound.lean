import ThetaCoverClassPortable.ThetaOriginPlace
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
namespace FourCorner.ThetaRationalPicardInput
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaLiteralModels SmoothProperClosedPointPlaces

attribute [local instance] sourceIntegral sourceSmooth sourceProper constants

/-- The SAME native original function field is a function field over Q. -/
theorem source_isCurveOver : IsCurveOver ℚ (C ℚ).functionField :=
  isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one (cToBase ℚ)
    (RingEquiv.refl _) (fun _ => rfl)

theorem source_essFiniteType : Algebra.EssFiniteType ℚ (C ℚ).functionField :=
  essFiniteType_functionField (cToBase ℚ)

/-- The actual rational origin forces the constants to be Q itself. -/
theorem source_constantsAreBase : ConstantsAreBase ℚ (C ℚ).functionField := by
  letI := source_isCurveOver
  exact constantsAreBase_of_deg_eq_one originPlace originPlace_degree_one

/-- Genuine rational-base Riemann genus bound/reached data, obtained over Q
using perfection and the actual degree-one origin; no Qbar specialization. -/
theorem source_stichtenothGenusExists : StichtenothGenusExists ℚ (C ℚ).functionField := by
  letI := source_isCurveOver
  letI := source_essFiniteType
  exact stichtenothGenusExists_of_isCurveOver source_constantsAreBase

#print axioms source_isCurveOver
#print axioms source_essFiniteType
#print axioms source_constantsAreBase
#print axioms source_stichtenothGenusExists
end FourCorner.ThetaRationalPicardInput
