import HpUChartEquiv
import HpTwoChartCover
import IntegralTwoOpen

namespace FourCorner.HpLiteralIntegral
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open HpLiteralProjective HpTwoChartCover
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type*) [Field K] [CharZero K]
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

abbrev ZRing (p : K) := ThetaQuotientChart.chartRing (equation K p) (homogeneous K p) 0
abbrev URing (p : K) := ThetaQuotientChart.chartRing (equation K p) (homogeneous K p) 1
abbrev overlap (p : K) := Away (G K p) (coordinate K p 1*coordinate K p 0)
abbrev boundaryRatio (p : K) := Away.isLocalizationElem (degree K p 1) (degree K p 0)
def fromU (p : K) : URing K p →+* overlap K p := awayMap (G K p) (degree K p 0) rfl
def fromZ (p : K) : ZRing K p →+* overlap K p := awayMap (G K p) (degree K p 1) (mul_comm _ _)

 theorem boundaryRatio_image (p : K) :
    ThetaQuotientChart.chartEquiv (equation K p) (homogeneous K p) 1 (boundaryRatio K p)=HpUChartEquiv.x K p 0 := by
  change ThetaQuotientChart.chartDehom (equation K p) (homogeneous K p) 1
    (Away.mk (G K p) (degree K p 1) 1 (coordinate K p 0^1) _)=_
  simp only [pow_one]
  rw [ThetaQuotientChart.chartDehom_mk]
  change Ideal.Quotient.mk (ThetaQuotientChart.affineIdeal (equation K p) 1)
    (ThetaAmbientChart.dehom K 4 1 (X 0))=HpUChartEquiv.x K p 0
  simp [ThetaAmbientChart.dehom,HpLiteralSmooth.drop_table,HpUChartEquiv.x]

 theorem boundaryRatio_regular (p : K) (hp : p ≠ 0) : IsRegular (boundaryRatio K p) := by
  have hr := HpUChartEquiv.z_regular K p hp
  have he := boundaryRatio_image K p
  have hi : Function.Injective (fun a : URing K p=>boundaryRatio K p*a) := by
    intro a b hab
    apply (ThetaQuotientChart.chartEquiv (equation K p) (homogeneous K p) 1).injective
    apply hr.left
    change HpUChartEquiv.x K p 0*ThetaQuotientChart.chartEquiv (equation K p) (homogeneous K p) 1 a=
      HpUChartEquiv.x K p 0*ThetaQuotientChart.chartEquiv (equation K p) (homogeneous K p) 1 b
    rw [← he,← map_mul,← map_mul]
    exact congrArg (ThetaQuotientChart.chartEquiv (equation K p) (homogeneous K p) 1) hab
  refine ⟨hi,?_⟩
  intro a b hab
  apply hi
  calc
    boundaryRatio K p*a=a*boundaryRatio K p := mul_comm _ _
    _=b*boundaryRatio K p := hab
    _=boundaryRatio K p*b := mul_comm _ _

 theorem fromU_injective (p : K) (hp : p ≠ 0) : Function.Injective (fromU K p) := by
  letI := (fromU K p).toAlgebra
  haveI : IsLocalization.Away (boundaryRatio K p) (overlap K p) :=
    Away.isLocalization_mul (degree K p 1) (degree K p 0) rfl one_ne_zero
  change Function.Injective (algebraMap (URing K p) (overlap K p))
  apply IsLocalization.injectiveₛ (M:=Submonoid.powers (boundaryRatio K p))
  rintro _ ⟨n,rfl⟩
  exact IsRegular.pow n (boundaryRatio_regular K p hp)

 theorem overlap_nontrivial (p : K) (hp : p ≠ 0) : Nontrivial (overlap K p) := by
  haveI : Nontrivial (HpUChartTower.Tower K p) := inferInstance
  haveI : Nontrivial (HpUChartEquiv.B K p) := (HpUChartEquiv.ringEquiv K p hp).toEquiv.nontrivial
  haveI : Nontrivial (URing K p) :=
    (ThetaQuotientChart.chartEquiv (equation K p) (homogeneous K p) 1).toEquiv.nontrivial
  exact Function.Injective.nontrivial (fromU_injective K p hp)

 theorem ZRing_isDomain (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) : IsDomain (ZRing K p) := by
  letI := HpAffineEquiv.affine_isDomain K p hp ha hb
  let e := ThetaQuotientChart.chartEquiv (equation K p) (homogeneous K p) 0
  exact Function.Injective.isDomain e e.injective

 theorem overlap_isDomain (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) : IsDomain (overlap K p) := by
  letI := ZRing_isDomain K p hp ha hb
  letI := overlap_nontrivial K p hp
  letI := (fromZ K p).toAlgebra
  haveI : IsLocalization.Away (Away.isLocalizationElem (degree K p 0) (degree K p 1)) (overlap K p) :=
    Away.isLocalization_mul (degree K p 0) (degree K p 1) (mul_comm _ _) one_ne_zero
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (fromZ K p))) := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap (ZRing K p) (overlap K p))))
    exact IsOpenImmersion.of_isLocalization (Away.isLocalizationElem (degree K p 0) (degree K p 1))
  haveI : IsIntegral (Spec (.of (overlap K p))) := isIntegral_of_isOpenImmersion (Spec.map (CommRingCat.ofHom (fromZ K p)))
  exact (affine_isIntegral_iff (.of (overlap K p))).mp inferInstance

 theorem URing_isDomain (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) : IsDomain (URing K p) := by
  letI := overlap_isDomain K p hp ha hb
  exact Function.Injective.isDomain (fromU K p) (fromU_injective K p hp)

/-- The WHOLE literal projective three-quadric C_p is integral. Boundary
regularity and the actual homogeneous overlap exclude hidden components. -/
theorem integral (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) : IsIntegral (curve K p) := by
  let UZ : (curve K p).Opens := Proj.basicOpen (G K p) (coordinate K p 0)
  let UU : (curve K p).Opens := Proj.basicOpen (G K p) (coordinate K p 1)
  letI := ZRing_isDomain K p hp ha hb
  letI := URing_isDomain K p hp ha hb
  haveI : IsIntegral UZ.toScheme := IsIntegral.of_isIso (Proj.basicOpenIsoSpec (G K p) (coordinate K p 0) (degree K p 0) one_pos).inv
  haveI : IsIntegral UU.toScheme := IsIntegral.of_isIso (Proj.basicOpenIsoSpec (G K p) (coordinate K p 1) (degree K p 1) one_pos).inv
  have hne : ((UZ : Set (curve K p))∩(UU : Set (curve K p))).Nonempty := by
    letI := overlap_nontrivial K p hp
    let x : Spec (.of (overlap K p)) := Classical.choice inferInstance
    let y := Proj.awayι (G K p) (coordinate K p 1*coordinate K p 0)
      (SetLike.mul_mem_graded (degree K p 1) (degree K p 0)) (by decide : 0<1+1) x
    have hy : y∈Proj.basicOpen (G K p) (coordinate K p 1*coordinate K p 0) := by
      rw [← Proj.opensRange_awayι (G K p) (coordinate K p 1*coordinate K p 0)
        (SetLike.mul_mem_graded (degree K p 1) (degree K p 0)) (by decide : 0<1+1)]
      exact ⟨x,rfl⟩
    rw [Proj.basicOpen_mul] at hy
    exact ⟨y,hy.2,hy.1⟩
  exact integral_two_open UZ UU (two_charts_cover K p hp) hne

#print axioms fromU_injective
#print axioms overlap_isDomain
#print axioms integral
end
end FourCorner.HpLiteralIntegral
