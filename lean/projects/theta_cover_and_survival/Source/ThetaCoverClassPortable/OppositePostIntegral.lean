import ThetaCoverClassPortable.OppositePostPTowerEquiv
import ThetaCoverClassPortable.OppositePostTwoChartCover

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace FourCorner.OppositeProjective.PostIntegral
open OppositePolynomials
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

abbrev p (mu nu : K) := Ideal.Quotient.mk (OppositeHomogeneousQuadrics.ideal mu nu) (X (0 : Fin 5))
abbrev t (mu nu : K) := Ideal.Quotient.mk (OppositeHomogeneousQuadrics.ideal mu nu) (X (4 : Fin 5))
abbrev hp (mu nu : K) : p mu nu ∈ quotientGrading mu nu 1 :=
  (HighChart.quotientMap mu nu).map_mem (Slot02HighProjSpace.X_mem_one K 4 0)
abbrev ht (mu nu : K) : t mu nu ∈ quotientGrading mu nu 1 :=
  (HighChart.quotientMap mu nu).map_mem (Slot02HighProjSpace.X_mem_one K 4 4)
abbrev overlapRing (mu nu : K) := Away (quotientGrading mu nu) (p mu nu*t mu nu)
abbrev boundaryRatio (mu nu : K) := Away.isLocalizationElem (hp mu nu) (ht mu nu)
def fromP (mu nu : K) : PostPChart.chartRing mu nu →+* overlapRing mu nu :=
  awayMap (quotientGrading mu nu) (ht mu nu) rfl
def fromT (mu nu : K) : HighChart.chartRing mu nu →+* overlapRing mu nu :=
  awayMap (quotientGrading mu nu) (hp mu nu) (mul_comm _ _)

lemma boundaryRatio_image (mu nu : K) :
    PostPChart.chartEquiv mu nu (boundaryRatio mu nu) = PostPTower.ax mu nu 0 := by
  change PostPChart.chartDehom mu nu
    (Away.mk (quotientGrading mu nu) (hp mu nu) 1 (t mu nu ^ 1) _) = _
  simp only [pow_one]
  rw [PostPChart.chartDehom_mk]
  change PostPChart.dehomQuotient mu nu
    (Ideal.Quotient.mk (OppositeHomogeneousQuadrics.ideal mu nu) (X (4 : Fin 5))) = _
  unfold PostPChart.dehomQuotient
  rw [Ideal.quotientMap_mk]
  simp [PostPChart.dehomP,PostPTower.ax,PostPSmooth.ax]

lemma boundaryRatio_regular (mu nu : K) : IsRegular (boundaryRatio mu nu) := by
  have hr := PostPTower.affine_t_regular mu nu
  have he := boundaryRatio_image mu nu
  have hinj : Function.Injective (fun x : PostPChart.chartRing mu nu => boundaryRatio mu nu*x) := by
    intro x y hxy
    apply (PostPChart.chartEquiv mu nu).injective
    apply hr.left
    change PostPTower.ax mu nu 0 * PostPChart.chartEquiv mu nu x =
      PostPTower.ax mu nu 0 * PostPChart.chartEquiv mu nu y
    rw [← he, ← map_mul, ← map_mul]
    exact congrArg (PostPChart.chartEquiv mu nu) hxy
  exact ⟨hinj,fun x y hxy => hinj (by simpa only [mul_comm] using hxy)⟩

lemma fromP_injective (mu nu : K) : Function.Injective (fromP mu nu) := by
  letI := (fromP mu nu).toAlgebra
  haveI : IsLocalization.Away (boundaryRatio mu nu) (overlapRing mu nu) :=
    Away.isLocalization_mul (hp mu nu) (ht mu nu) rfl one_ne_zero
  change Function.Injective (algebraMap (PostPChart.chartRing mu nu) (overlapRing mu nu))
  apply IsLocalization.injectiveₛ (M := Submonoid.powers (boundaryRatio mu nu))
  rintro _ ⟨n,rfl⟩
  exact IsRegular.pow n (boundaryRatio_regular mu nu)

lemma overlap_nontrivial (mu nu : K) : Nontrivial (overlapRing mu nu) := by
  haveI : Nontrivial (PostPTower.Tower mu nu) := inferInstance
  haveI : Nontrivial (PostPChart.affineRing mu nu) :=
    (PostPTower.affineEquiv mu nu).toEquiv.nontrivial
  haveI : Nontrivial (PostPChart.chartRing mu nu) :=
    (PostPChart.chartEquiv mu nu).toEquiv.nontrivial
  exact Function.Injective.nontrivial (fromP_injective mu nu)

/-- The actual intersection embeds as an open subscheme of the already integral T chart. -/
lemma overlap_isDomain {mu nu : K} (hm : mu ≠ 0) (hn : nu ≠ 0)
    (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    IsDomain (overlapRing mu nu) := by
  letI := HighChart.chart_isDomain hm hn hA hB hS
  letI := overlap_nontrivial mu nu
  letI := (fromT mu nu).toAlgebra
  haveI : IsLocalization.Away (Away.isLocalizationElem (ht mu nu) (hp mu nu)) (overlapRing mu nu) :=
    Away.isLocalization_mul (ht mu nu) (hp mu nu) (mul_comm _ _) one_ne_zero
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (fromT mu nu))) := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (HighChart.chartRing mu nu) (overlapRing mu nu))))
    exact IsOpenImmersion.of_isLocalization (Away.isLocalizationElem (ht mu nu) (hp mu nu))
  haveI : IsIntegral (Spec (.of (overlapRing mu nu))) :=
    isIntegral_of_isOpenImmersion (Spec.map (CommRingCat.ofHom (fromT mu nu)))
  exact (affine_isIntegral_iff (.of (overlapRing mu nu))).mp inferInstance

/-- No hidden component at infinity: the whole genuine P-chart ring is a domain. -/
theorem pChart_isDomain {mu nu : K} (hm : mu ≠ 0) (hn : nu ≠ 0)
    (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    IsDomain (PostPChart.chartRing mu nu) := by
  letI := overlap_isDomain hm hn hA hB hS
  exact Function.Injective.isDomain (fromP mu nu) (fromP_injective mu nu)

end FourCorner.OppositeProjective.PostIntegral
#print axioms FourCorner.OppositeProjective.PostIntegral.pChart_isDomain
