import EllipticQuarticPoint
import IntegralTwoOpen

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
universe u
namespace FourCorner.EllipticQuarticModel
variable (K : Type u) [Field K]

theorem zero_chart_integral :
    IsIntegral (Proj.basicOpen (grading K) (projectiveCoordinate K 0)).toScheme := by
  haveI : Nonempty (Proj.basicOpen (grading K) (projectiveCoordinate K 0)).toScheme :=
    Nonempty.map (zeroNativeIso K).inv.base inferInstance
  exact isIntegral_of_isOpenImmersion (zeroNativeIso K).hom

theorem infinity_chart_integral :
    IsIntegral (Proj.basicOpen (grading K) (projectiveCoordinate K 2)).toScheme := by
  haveI : Nonempty (Proj.basicOpen (grading K) (projectiveCoordinate K 2)).toScheme :=
    Nonempty.map (infinityNativeIso K).inv.base inferInstance
  exact isIntegral_of_isOpenImmersion (infinityNativeIso K).hom

/-- Integrality of the independently defined projective target follows from
its two literal affine domains and an actual point in their intersection. -/
theorem integral : IsIntegral (curve K) := by
  change IsIntegral (Proj (grading K))
  haveI := zero_chart_integral K
  haveI := infinity_chart_integral K
  exact FourCorner.integral_two_open
    (Proj.basicOpen (grading K) (projectiveCoordinate K 0))
    (Proj.basicOpen (grading K) (projectiveCoordinate K 2))
    (two_opens_cover K) (chart_overlap_nonempty K)

end FourCorner.EllipticQuarticModel
#print axioms FourCorner.EllipticQuarticModel.integral
