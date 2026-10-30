import CriticalProjectiveIntegral
import CriticalChartBase
import CriticalAffineBaseChange
import AffineChartSections
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isIntegral_pullback_and_nonempty_of_isDomain_tensorProduct
import Mathlib.AlgebraicGeometry.Geometrically.Integral

noncomputable section
namespace FourCorner.CriticalGeometricIntegral
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CriticalProj23 CriticalStandardCharts
open scoped TensorProduct
universe u
variable {k : Type u} [Field k]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

theorem tensor_zero_isDomain (i : k) (hi : i^2= -1) (h2 : (2:k)≠0)
    (L : Type u) [Field L] [Algebra k L] : IsDomain (L ⊗[k] affineRing i 0) := by
  letI := CriticalAffineBaseChange.isDomain_tensor i L hi h2
  let e : affineRing i 0 ≃ₐ[k] CriticalAffineGeometry.ring i := Ideal.quotientEquivAlgOfEq k (zero_ideal i)
  let t:=Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[k] L) e
  exact Function.Injective.isDomain t.toRingHom t.injective

theorem tensor_one_isDomain (i : k) (hi : i^2= -1) (h2 : (2:k)≠0)
    (L : Type u) [Field L] [Algebra k L] : IsDomain (L ⊗[k] affineRing i 1) := by
  letI := CriticalAffineBaseChange.isDomain_tensor (-i) L (by simpa only [neg_sq] using hi) h2
  let t:=Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[k] L) (CriticalSecondChart.equiv i)
  exact Function.Injective.isDomain t.toRingHom t.injective

/-- Every actual field pullback of the ORIGINAL projective intersection is
integral, by its actual scalar-extended two-affine cover. -/
theorem pullback_integral (i : k) (hi : i^2= -1) (h2 : (2:k)≠0)
    (L : Type u) [Field L] [Algebra k L] :
    IsIntegral (pullback (criticalToSpec i) (Scheme.TwoAffineOpenCover.specMap k L)) := by
  let V:=CriticalTwoChartCover.cover i
  letI := CriticalProjectiveIntegral.projective_integral i hi h2
  have hn:=CriticalTwoChartCover.overlap_nonempty i
  haveI : Nonempty (V.U0 ⊓ V.U1 : (criticalCurve i).Opens) := ⟨⟨hn.choose,hn.choose_spec⟩⟩
  letI := tensor_zero_isDomain i hi h2 L
  letI := tensor_one_isDomain i hi h2 L
  haveI : IsDomain (L ⊗[k] (V.cover (criticalToSpec i)).A0) :=
    AffineChartSections.isDomain_tensor_sections (criticalToSpec i) V.U0
      (chartIso i 0) (CriticalChartBase.chart_over_base i 0) L
  haveI : IsDomain (L ⊗[k] (V.cover (criticalToSpec i)).A1) :=
    AffineChartSections.isDomain_tensor_sections (criticalToSpec i) V.U1
      (chartIso i 1) (CriticalChartBase.chart_over_base i 1) L
  haveI : IsDomain (V.cover (criticalToSpec i)).A01 := by
    change IsDomain Γ(criticalCurve i,V.U0 ⊓ V.U1)
    infer_instance
  haveI : Nontrivial (L ⊗[k] (V.cover (criticalToSpec i)).A01) := inferInstance
  exact (V.isIntegral_pullback_and_nonempty_of_isDomain_tensorProduct (criticalToSpec i) L).1

/-- Native geometrical integrality of exactly C_i -> Spec k, without any
perfectness/CharZero assumption or assumed elliptic isomorphism. -/
theorem geometricallyIntegral (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) :
    GeometricallyIntegral (criticalToSpec i) := by
  refine ⟨geometrically_iff_of_commRing.mpr ?_⟩
  intro L _ _ Y fst snd hpb
  haveI := pullback_integral i hi h2 L
  haveI : Nonempty Y := Nonempty.map hpb.isoPullback.inv.base inferInstance
  exact isIntegral_of_isOpenImmersion hpb.isoPullback.hom
end FourCorner.CriticalGeometricIntegral
#print axioms FourCorner.CriticalGeometricIntegral.pullback_integral
#print axioms FourCorner.CriticalGeometricIntegral.geometricallyIntegral
