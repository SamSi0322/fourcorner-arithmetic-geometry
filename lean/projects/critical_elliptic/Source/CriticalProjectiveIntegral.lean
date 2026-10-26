import CriticalSecondChart
import CriticalTwoChartCover
import IntegralTwoOpen

noncomputable section
namespace FourCorner.CriticalProjectiveIntegral
open AlgebraicGeometry CategoryTheory CriticalProj23 CriticalStandardCharts
variable {k : Type*} [Field k]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem projective_integral (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) : IsIntegral (criticalCurve i) := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  letI : IsDomain (affineRing i 0) :=
    Function.Injective.isDomain (zeroEquiv i).toRingHom (zeroEquiv i).injective
  letI := CriticalSecondChart.isDomain i hi h2
  let U:=(CriticalTwoChartCover.cover i).U0
  let V:=(CriticalTwoChartCover.cover i).U1
  haveI : IsIntegral U.toScheme := IsIntegral.of_isIso (chartIso i 0).inv
  haveI : IsIntegral V.toScheme := IsIntegral.of_isIso (chartIso i 1).inv
  exact integral_two_open U V (CriticalTwoChartCover.two_charts_cover i)
    (CriticalTwoChartCover.overlap_nonempty i)
end FourCorner.CriticalProjectiveIntegral
#print axioms FourCorner.CriticalProjectiveIntegral.projective_integral
