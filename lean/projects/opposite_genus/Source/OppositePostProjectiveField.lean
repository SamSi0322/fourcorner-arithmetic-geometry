import OppositePostGlobalIntegral
import OppositePostGlobalSmooth
import OppositePostProper
import Slot02HighGeometricDifferentials

noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
namespace FourCorner.OppositeProjective.PostField
open OppositePolynomials OppositeCoordinateAlgebra

abbrev affineT (mu nu : ℚ) : (curve mu nu).Opens :=
  Proj.basicOpen (quotientGrading mu nu) (PostIntegral.t mu nu)

theorem affineT_nonempty (mu nu : ℚ) (hn : nu ≠ 0) (hp : 0 < mu/nu) (hl : mu/nu < 2) :
    Nonempty (affineT mu nu) := by
  have hm : mu ≠ 0 := by intro h; simp [h] at hp
  letI := HighChart.chart_isDomain hm hn (rational_A_ne_zero mu nu hn)
    (rational_B_ne_zero mu nu hn hp hl) (rational_S_ne_zero mu nu hn)
  exact Nonempty.map (Proj.basicOpenIsoSpec (quotientGrading mu nu) (PostIntegral.t mu nu)
    (PostIntegral.ht mu nu) one_pos).inv.base inferInstance

/-- The actual function field of the literal projective intersection is the original degree-eight radical field. -/
def functionFieldEquiv (mu nu : ℚ) (hn : nu ≠ 0) (hp : 0 < mu/nu) (hl : mu/nu < 2) :
    letI := PostIntegral.rational_literal_projective_integral mu nu hn hp hl
    functionField mu nu ≃+* (curve mu nu).functionField := by
  letI := PostIntegral.rational_literal_projective_integral mu nu hn hp hl
  letI := OppositeAffineModel.rational_coordinateRing_isDomain mu nu hn hp hl
  letI := OppositeAffineModel.rational_coordinateRing_isFractionRing mu nu hn hp hl
  haveI := affineT_nonempty mu nu hn hp hl
  have ha : IsAffineOpen (affineT mu nu) :=
    Proj.isAffineOpen_basicOpen (quotientGrading mu nu) (PostIntegral.t mu nu)
      (PostIntegral.ht mu nu) one_pos
  haveI : IsFractionRing Γ(curve mu nu,affineT mu nu) (curve mu nu).functionField :=
    functionField_isFractionRing_of_isAffineOpen (curve mu nu) (affineT mu nu) ha
  let e0 : HighChart.chartRing mu nu ≃+* Γ(curve mu nu,affineT mu nu) :=
    (Proj.basicOpenIsoAway (quotientGrading mu nu) (PostIntegral.t mu nu)
      (PostIntegral.ht mu nu) one_pos).commRingCatIsoToRingEquiv
  let e : ring mu nu ≃+* Γ(curve mu nu,affineT mu nu) :=
    (HighChart.chartLiteralEquiv mu nu (rational_A_ne_zero mu nu hn)).symm.toRingEquiv.trans e0
  exact IsFractionRing.ringEquivOfRingEquiv e

end FourCorner.OppositeProjective.PostField
#print axioms FourCorner.OppositeProjective.PostField.functionFieldEquiv
