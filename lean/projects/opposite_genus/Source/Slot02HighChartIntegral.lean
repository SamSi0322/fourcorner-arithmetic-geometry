import Slot02HighAffinePresentation

noncomputable section
open AlgebraicGeometry AlgebraicCurve MvPolynomial HomogeneousLocalization
namespace FourCorner.OppositeProjective.HighChart
open OppositeCoordinateAlgebra OppositePolynomials HighAffine
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The degree-zero constant map to the actual homogeneous-quotient chart. -/
def chartConstants (mu nu : K) : K →+* chartRing mu nu :=
  (fromZeroRingHom (quotientGrading mu nu) _).comp
    { toFun := fun a => ⟨(quotientMap mu nu) (C a),
        (quotientMap mu nu).map_mem (OppositeProjective.constants a).property⟩
      map_zero' := Subtype.ext (by simp)
      map_one' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
instance chartAlgebra (mu nu : K) : Algebra K (chartRing mu nu) := (chartConstants mu nu).toAlgebra

lemma chartDehom_constants (mu nu a : K) :
    chartDehom mu nu (chartConstants mu nu a) = algebraMap K (affineRing mu nu) a := by
  change chartDehom mu nu (Away.mk (quotientGrading mu nu)
    ((quotientMap mu nu).map_mem (Slot02HighProjSpace.X_mem_one K 4 4)) 0
    ((quotientMap mu nu) (C a)) _) = _
  rw [chartDehom_mk]
  change OppositeProjective.dehomQuotient mu nu
    (Ideal.Quotient.mk (OppositeHomogeneousQuadrics.ideal mu nu) (C a)) = _
  unfold OppositeProjective.dehomQuotient
  rw [Ideal.quotientMap_mk]
  simp [OppositeHomogeneousQuadrics.dehomT]
  rfl

/-- Genuine standard projective chart, with its original scalar map, equals the literal monic coordinate ring. -/
def chartLiteralEquiv (mu nu : K) (hA : A mu nu ≠ 0) : chartRing mu nu ≃ₐ[K] ring mu nu :=
  { (chartEquiv mu nu).trans (HighAffine.affineEquiv mu nu hA) with
    commutes' := fun a => by
      change affineToTower mu nu hA (chartDehom mu nu (chartConstants mu nu a)) = _
      rw [chartDehom_constants, affineToTower_constant] }

/-- The degree-zero-localization ring of the actual T chart is a domain. -/
theorem chart_isDomain {mu nu : K} (hm : mu ≠ 0) (hn : nu ≠ 0)
    (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    IsDomain (chartRing mu nu) := by
  letI := coordinateRing_isDomain hm hn hA hB hS
  exact Function.Injective.isDomain (chartLiteralEquiv mu nu hA).toRingHom
    (chartLiteralEquiv mu nu hA).injective

/-- Integrality of the actual T basic-open subscheme, not a replacement affine scheme. -/
theorem chartScheme_isIntegral {mu nu : K} (hm : mu ≠ 0) (hn : nu ≠ 0)
    (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    IsIntegral ((Proj.basicOpen (quotientGrading mu nu)
      (Ideal.Quotient.mk (OppositeHomogeneousQuadrics.ideal mu nu) (X (4 : Fin 5)))).toScheme) := by
  letI := coordinateRing_isDomain hm hn hA hB hS
  haveI : IsDomain (affineRing mu nu) :=
    Function.Injective.isDomain (HighAffine.affineEquiv mu nu hA).toRingHom
      (HighAffine.affineEquiv mu nu hA).injective
  haveI : IsIntegral (Spec (.of (affineRing mu nu))) := inferInstance
  haveI : Nonempty ((Proj.basicOpen (quotientGrading mu nu)
      (Ideal.Quotient.mk (OppositeHomogeneousQuadrics.ideal mu nu) (X (4 : Fin 5)))).toScheme) :=
    ⟨(chartSchemeIso mu nu).inv.base (Classical.choice (inferInstance : Nonempty (Spec (.of (affineRing mu nu)))))⟩
  exact isIntegral_of_isOpenImmersion (chartSchemeIso mu nu).hom

end FourCorner.OppositeProjective.HighChart
#print axioms FourCorner.OppositeProjective.HighChart.chartLiteralEquiv
#print axioms FourCorner.OppositeProjective.HighChart.chartScheme_isIntegral
