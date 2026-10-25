import Slot02HighChartIntegral
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

noncomputable section
open AlgebraicGeometry MvPolynomial HomogeneousIdealQuotientGrading
namespace FourCorner.OppositeProjective.PostChart
open HighChart
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev coord (mu nu : K) (i : Fin 5) := (quotientMap mu nu) (X i)

/-- If P=T=0 in a prime of the homogeneous coordinate ring, all coordinates vanish. -/
lemma all_coordinates_mem_of_PT (mu nu : K) (I : Ideal (coordinateRing mu nu)) [I.IsPrime]
    (hP : coord mu nu 0 ∈ I) (hT : coord mu nu 4 ∈ I) :
    ∀ i : Fin 5, coord mu nu i ∈ I := by
  let f : OppositeHomogeneousQuadrics.Ambient K →+* coordinateRing mu nu ⧸ I :=
    (Ideal.Quotient.mk I).comp (quotientMap mu nu).toRingHom
  have hp : f (X 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hP
  have ht : f (X 4) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hT
  have h (i : Fin 3) : f (OppositeHomogeneousQuadrics.quadric mu nu i) = 0 := by
    change Ideal.Quotient.mk I ((quotientMap mu nu) (OppositeHomogeneousQuadrics.quadric mu nu i)) = 0
    erw [show (quotientMap mu nu) (OppositeHomogeneousQuadrics.quadric mu nu i) = 0 from equation_vanishes mu nu i, map_zero]
  have hZ : coord mu nu 3 ∈ I := by
    have h0 := h 0
    simp only [OppositeHomogeneousQuadrics.quadric, OppositeHomogeneousQuadrics.F0,
      map_add, map_sub, map_mul, map_pow, hp, ht, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, add_zero] at h0
    have hz2 : f (X 3)^2 = 0 := by linear_combination h0
    apply (inferInstance : I.IsPrime).mem_of_pow_mem 2
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_pow]
    exact hz2
  have hQ : coord mu nu 1 ∈ I := by
    have h1 := h 1
    simp only [OppositeHomogeneousQuadrics.quadric, OppositeHomogeneousQuadrics.F1,
      map_sub, map_mul, map_pow, hp, ht, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] at h1
    have hq2 : f (X 1)^2 = 0 := by linear_combination h1
    apply (inferInstance : I.IsPrime).mem_of_pow_mem 2
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_pow]
    exact hq2
  have hR : coord mu nu 2 ∈ I := by
    have h2 := h 2
    simp only [OppositeHomogeneousQuadrics.quadric, OppositeHomogeneousQuadrics.F2,
      map_add, map_sub, map_mul, map_pow, hp, ht, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, add_zero] at h2
    have hr2 : f (X 2)^2 = 0 := by linear_combination h2
    apply (inferInstance : I.IsPrime).mem_of_pow_mem 2
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_pow]
    exact hr2
  intro i
  fin_cases i <;> assumption

/-- The true two standard charts T≠0 and P≠0 already cover the full opposite Proj, including infinity. -/
theorem two_charts_cover (mu nu : K) :
    Proj.basicOpen (quotientGrading mu nu) (coord mu nu 4) ⊔
      Proj.basicOpen (quotientGrading mu nu) (coord mu nu 0) = ⊤ := by
  apply top_le_iff.mp
  intro x _
  change coord mu nu 4 ∉ x.asHomogeneousIdeal ∨ coord mu nu 0 ∉ x.asHomogeneousIdeal
  by_contra h
  push_neg at h
  haveI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have hall := all_coordinates_mem_of_PT mu nu x.asHomogeneousIdeal.toIdeal h.2 h.1
  apply x.not_irrelevant_le
  have hirr := ProjectiveQuotientCharts.irrelevant_le_span_coordinates K 4
    (OppositeHomogeneousQuadrics.homogeneousIdeal mu nu)
  have hle : Ideal.span (Set.range (coord mu nu)) ≤ x.asHomogeneousIdeal.toIdeal := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hall i
  exact hirr.trans hle


/-- Genuine two-affine cover of the full projective scheme, with affine overlap. -/
def twoAffineOpenCover (mu nu : K) : (curve mu nu).TwoAffineOpenCover where
  U0 := Proj.basicOpen (quotientGrading mu nu) (coord mu nu 4)
  U1 := Proj.basicOpen (quotientGrading mu nu) (coord mu nu 0)
  isAffineOpen_U0 := Proj.isAffineOpen_basicOpen (quotientGrading mu nu) _
    ((quotientMap mu nu).map_mem (Slot02HighProjSpace.X_mem_one K 4 4)) one_pos
  isAffineOpen_U1 := Proj.isAffineOpen_basicOpen (quotientGrading mu nu) _
    ((quotientMap mu nu).map_mem (Slot02HighProjSpace.X_mem_one K 4 0)) one_pos
  sup_eq_top := two_charts_cover mu nu
  isAffineOpen_inf := by
    rw [← Proj.basicOpen_mul]
    exact Proj.isAffineOpen_basicOpen (quotientGrading mu nu) _
      (SetLike.mul_mem_graded
        ((quotientMap mu nu).map_mem (Slot02HighProjSpace.X_mem_one K 4 4))
        ((quotientMap mu nu).map_mem (Slot02HighProjSpace.X_mem_one K 4 0))) (by decide : 0 < 1+1)

end FourCorner.OppositeProjective.PostChart
#print axioms FourCorner.OppositeProjective.PostChart.two_charts_cover

#print axioms FourCorner.OppositeProjective.PostChart.twoAffineOpenCover
