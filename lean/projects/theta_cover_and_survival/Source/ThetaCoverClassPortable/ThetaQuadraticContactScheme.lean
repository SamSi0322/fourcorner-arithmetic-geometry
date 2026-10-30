import ThetaCoverClassPortable.ThetaQuadraticContactAlgebra
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits MvPolynomial

namespace FourCorner.ThetaQuadraticContactScheme
open ThetaQuadraticCurve ThetaQuadraticContactAlgebra

/-- Both algebraic coordinates generate the entire degree-four QQ-field;
over F the contact field has degree two. -/
theorem chartEvaluation_surjective (plus : Bool) :
    Function.Surjective (chartEvaluation plus) := by
  rintro ⟨⟨a,b⟩,⟨c,d⟩⟩
  cases plus
  · refine ⟨Ideal.Quotient.mk _ (C a+C b*X 0+C c*X 1+C d*X 0*X 1),?_⟩
    apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
      simp [chartEvaluation,values,abscissa,radical,ordinate,QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul]
  · refine ⟨Ideal.Quotient.mk _ (C a-C b*X 0+C c*X 1-C d*X 0*X 1),?_⟩
    apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
      simp [chartEvaluation,values,abscissa,radical,ordinate,QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul]

theorem pointToBase_finite : IsFinite pointToBase := by
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

theorem contactMap_proper (plus : Bool) : IsProper (contactMap plus) := by
  letI := curve_proper
  letI := pointToBase_finite
  haveI : IsProper (contactMap plus ≫ toBase) := by
    simpa only [contactMap_toBase] using (inferInstance : IsProper pointToBase)
  exact IsProper.of_comp (contactMap plus) toBase

theorem contactMap_immersion (plus : Bool) : IsImmersion (contactMap plus) := by
  letI : IsOpenImmersion (ThetaDPlaneChartSections.chartMap 2) := by
    unfold ThetaDPlaneChartSections.chartMap
    infer_instance
  letI := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (chartEvaluation plus).toRingHom) (chartEvaluation_surjective plus)
  haveI : IsImmersion (rationalChartPoint plus) := by
    unfold rationalChartPoint
    infer_instance
  haveI : IsImmersion (contactMap plus ≫ toRational) := by
    simpa only [contactMap_toRational] using (inferInstance : IsImmersion (rationalChartPoint plus))
  exact IsImmersion.of_comp (contactMap plus) toRational

/-- An actual closed immersion Spec(contactField) -> D_F, rather than
a fixed geometric point label or a presumed pair of F-rational points. -/
theorem contactMap_closedImmersion (plus : Bool) : IsClosedImmersion (contactMap plus) := by
  letI := contactMap_proper plus
  letI := contactMap_immersion plus
  exact (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance,inferInstance⟩

def closedContact (plus : Bool) : closedPoints curve :=
  ⟨contactMap plus (IsLocalRing.closedPoint contactField),by
    letI := contactMap_closedImmersion plus
    have h := (contactMap plus).isClosedEmbedding.isClosedMap _
      (isClosed_singleton : IsClosed ({IsLocalRing.closedPoint contactField} : Set (Spec (.of contactField))))
    simpa using h⟩

end FourCorner.ThetaQuadraticContactScheme
