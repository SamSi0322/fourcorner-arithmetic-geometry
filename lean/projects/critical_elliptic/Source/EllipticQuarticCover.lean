import EllipticQuarticModel
import CriticalCharts23

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial AlgebraicGeometry HomogeneousIdealQuotientGrading
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
namespace FourCorner.EllipticQuarticModel
variable (K : Type u) [Field K]
abbrev grading := CriticalQuotientChart.G (equation K) (homogeneous K)
abbrev homogeneousRing := ambient K ⧸ (ideal K).toIdeal
def projectiveCoordinate (j : Fin 4) : homogeneousRing K :=
  Ideal.Quotient.mk _ (X j)

theorem projective_conic : projectiveCoordinate K 0 * projectiveCoordinate K 2 =
    projectiveCoordinate K 1 ^ 2 := by
  have h : Ideal.Quotient.mk (ideal K).toIdeal (equation K 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨0,rfl⟩)
  change Ideal.Quotient.mk (ideal K).toIdeal (X 0 * X 2 - X 1 ^ 2) = 0 at h
  rw [map_sub,map_mul,map_pow] at h
  exact sub_eq_zero.mp h

theorem projective_cubic : projectiveCoordinate K 3 ^ 2 =
    projectiveCoordinate K 1 * projectiveCoordinate K 2 -
      projectiveCoordinate K 0 * projectiveCoordinate K 1 := by
  have h : Ideal.Quotient.mk (ideal K).toIdeal (equation K 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨1,rfl⟩)
  change Ideal.Quotient.mk (ideal K).toIdeal
    (X 3 ^ 2 - X 1 * X 2 + X 0 * X 1) = 0 at h
  rw [map_add,map_sub,map_mul,map_mul,map_pow] at h
  change projectiveCoordinate K 3 ^ 2 - projectiveCoordinate K 1 * projectiveCoordinate K 2 +
    projectiveCoordinate K 0 * projectiveCoordinate K 1 = 0 at h
  linear_combination h

theorem irrelevant_le_coordinates :
    (HomogeneousIdeal.irrelevant (grading K)).toIdeal ≤
      Ideal.span (Set.range (projectiveCoordinate K)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro d hd q hq
  obtain ⟨p,hp,rfl⟩ := (mem_quotGrading_iff
    (homogeneousSubmodule (Fin 4) K) (ideal K).toIdeal).mp hq
  have hpx := CriticalProj23.positive_homogeneous_mem_span_X hd p hp
  have hm := Ideal.mem_map_of_mem (Ideal.Quotient.mk (ideal K).toIdeal) hpx
  change Ideal.Quotient.mk (ideal K).toIdeal p ∈
    Ideal.span (Set.range fun j : Fin 4 => Ideal.Quotient.mk (ideal K).toIdeal (X j))
  simpa only [Ideal.map_span,← Set.range_comp'] using hm

/-- The two genuine affine opens cover every prime of the original Proj,
including its scheme-theoretic boundary, not just its rational points. -/
theorem two_opens_cover :
    Proj.basicOpen (grading K) (projectiveCoordinate K 0) ⊔
      Proj.basicOpen (grading K) (projectiveCoordinate K 2) = ⊤ := by
  classical
  refine top_le_iff.mp fun x _ => ?_
  change projectiveCoordinate K 0 ∉ x.asHomogeneousIdeal ∨
    projectiveCoordinate K 2 ∉ x.asHomogeneousIdeal
  by_contra h
  have h0 : projectiveCoordinate K 0 ∈ x.asHomogeneousIdeal.toIdeal := by
    simpa using (not_or.mp h).1
  have h2 : projectiveCoordinate K 2 ∈ x.asHomogeneousIdeal.toIdeal := by
    simpa using (not_or.mp h).2
  have h1sq : projectiveCoordinate K 1 ^ 2 ∈ x.asHomogeneousIdeal.toIdeal := by
    rw [←projective_conic]
    exact x.asHomogeneousIdeal.toIdeal.mul_mem_right _ h0
  have h1 : projectiveCoordinate K 1 ∈ x.asHomogeneousIdeal.toIdeal :=
    (x.isPrime.pow_mem_iff_mem 2 (by decide)).mp h1sq
  have h3sq : projectiveCoordinate K 3 ^ 2 ∈ x.asHomogeneousIdeal.toIdeal := by
    rw [projective_cubic]
    exact x.asHomogeneousIdeal.toIdeal.sub_mem
      (x.asHomogeneousIdeal.toIdeal.mul_mem_right _ h1)
      (x.asHomogeneousIdeal.toIdeal.mul_mem_right _ h0)
  have h3 : projectiveCoordinate K 3 ∈ x.asHomogeneousIdeal.toIdeal :=
    (x.isPrime.pow_mem_iff_mem 2 (by decide)).mp h3sq
  apply x.not_irrelevant_le
  apply (irrelevant_le_coordinates K).trans
  apply Ideal.span_le.mpr
  rintro _ ⟨j,rfl⟩
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3

end FourCorner.EllipticQuarticModel
#print axioms FourCorner.EllipticQuarticModel.two_opens_cover
