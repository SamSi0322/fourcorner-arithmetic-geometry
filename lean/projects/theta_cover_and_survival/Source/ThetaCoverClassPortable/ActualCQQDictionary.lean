import ThetaCoverClassPortable.ActualCQQRepresentation
import ThetaCoverClassPortable.ActualGroupAbelJacobiDictionaryFMD
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
namespace FourCorner.ActualCQQRepresentation
/-- The accepted genuine group/AJ/Pic0 dictionary instantiated on the actual
original C/QQ representer, with native OC and actual FiniteMapData supplied.
Only the geometric Pic0 part uses algebraically closed coefficient fields. -/
def actual_group_abelJacobi_pic0 :=
  letI := ThetaRationalPicardInput.source_proper
  letI := ThetaRationalPicardInput.source_smooth
  letI := ThetaRationalPicardInput.source_geometricallyIntegral
  P2MW.ActualGroupAbelJacobiDictionaryFMD.solution.{0,0}
    ℚ (ThetaLiteralModels.cToBase ℚ) ThetaRationalPicardInput.OC (ThetaRationalPicardInput.actual_finiteMapData 0)
    designation represents smooth proper geometricallyConnected
#print axioms actual_group_abelJacobi_pic0
end FourCorner.ActualCQQRepresentation
