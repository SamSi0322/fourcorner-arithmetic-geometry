import ThetaCoverClassPortable.ActualZariskiPicardSheaf
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ThetaCoverClassPortable.ThetaIteratedUniversalGlobalSections

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
namespace FourCorner.ThetaRationalPicardInput
open ThetaLiteralModels AlgebraicGeometry.RelPicard

/-- The ACTUAL basechanged original C/OC has the ACTUAL Picard zero-cut
Zariski sheaf on the SAME base R, for every Q-algebra R. In particular this
applies to the very R' chosen by actual_reduced_base_family_inputs. There is
no new choice of a finite-etale base and no caller-provided Q-algebra on S. -/
theorem actual_basechanged_relSubPic_zariski_sheaf (R:Type)[CommRing R][Algebra ℚ R] :
 let cR:=SmoothProperCurve.baseChange ℚ (cToBase ℚ) R
 let εR:=SmoothProperCurve.sectionBaseChange R OC
 Presieve.IsSheaf (Scheme.zariskiTopology.over (Spec (.of R)))
  (relSubPicPresheaf cR εR (algEquivZeroCut cR εR)) := by
  apply AlgebraicGeometry.RelPicard.isSheaf_relSubPicPresheaf_algEquivZeroCut_zariski_of_bijective_sections
    R (SmoothProperCurve.baseChange ℚ (cToBase ℚ) R) (SmoothProperCurve.sectionBaseChange R OC)
  intro S _ _
  exact actual_iterated_universal_global_sections R S

#check @actual_basechanged_relSubPic_zariski_sheaf
#print axioms actual_basechanged_relSubPic_zariski_sheaf
end FourCorner.ThetaRationalPicardInput
