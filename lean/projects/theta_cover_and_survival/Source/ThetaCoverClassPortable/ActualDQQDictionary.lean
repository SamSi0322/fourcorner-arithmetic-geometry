import ThetaCoverClassPortable.ActualDQQRepresentation
import ThetaCoverClassPortable.ActualGroupAbelJacobiDictionaryFMD
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
namespace FourCorner.ActualDQQRepresentation
/-- The accepted genuine group/AJ/Pic0 dictionary instantiated on the actual
original D/QQ representer, with original OD and actual FiniteMapData supplied.
Only the geometric Pic0 part uses algebraically closed coefficient fields. -/
def actual_group_abelJacobi_pic0 :=
  letI := DRationalInputs.proper
  letI := DRationalInputs.smooth
  letI := DRationalInputs.geometricallyIntegral
  P2MW.ActualGroupAbelJacobiDictionaryFMD.solution.{0,0}
    ℚ DRationalInputs.toBase DRationalInputs.OD (DRationalInputs.actual_finiteMapData 0)
    designation represents smooth proper geometricallyConnected
#print axioms actual_group_abelJacobi_pic0
end FourCorner.ActualDQQRepresentation
