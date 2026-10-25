import Slot03HighAdjacentAffineComparison

noncomputable section
open AlgebraicGeometry MvPolynomial HomogeneousIdealQuotientGrading
attribute [local instance] MvPolynomial.gradedAlgebra
namespace FourCorner.AdjacentPost
open Slot03HighAdjacentProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance (c : K) : GradedRing (quotientGrading c) :=
  quotGradingGradedRingOfHomogeneous (grading K) (homogeneousIdeal c)

abbrev quotientMap (c : K) := quotientGradedMap (grading K) (homogeneousIdeal c)
abbrev coord (c : K) (i : Fin 5) := (quotientMap c) (X i)

lemma equation_vanishes (c : K) (i : Fin 3) : (quotientMap c) (quadric c i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)

/-- No point of the literal projective source can have both U and T zero. -/
lemma all_coordinates_mem_of_UT (c : K) (hc : c ≠ 0)
    (I : Ideal (coordinateRing c)) [I.IsPrime]
    (hU : coord c 0 ∈ I) (hT : coord c 4 ∈ I) :
    ∀ i : Fin 5, coord c i ∈ I := by
  letI : IsDomain (coordinateRing c ⧸ I) := Ideal.Quotient.isDomain I
  let f : Ambient K →+* coordinateRing c ⧸ I := (Ideal.Quotient.mk I).comp (quotientMap c).toRingHom
  have hu : f (X 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hU
  have ht : f (X 4) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hT
  have h (i : Fin 3) : f (quadric c i) = 0 := by
    change Ideal.Quotient.mk I ((quotientMap c) (quadric c i)) = 0
    rw [equation_vanishes, map_zero]
  have hc2 : f (C (c^2)) ≠ 0 :=
    (map_ne_zero (f.comp C)).mpr (pow_ne_zero 2 hc)
  have hv : f (X 1) = 0 := by
    have h0 : f (C (c^2)) * f (X 1)^2 = 0 := by
      have h0 := h 0
      simp only [quadric, map_add, map_sub, map_mul, map_pow, hu, ht] at h0
      simp only [map_pow]
      linear_combination h0
    have hz2 : f (X 1)^2 = 0 := by
      exact ((mul_eq_zero (a := f (C (c^2))) (b := f (X 1)^2)).mp h0).resolve_left hc2
    exact (sq_eq_zero_iff (a := f (X 1))).mp hz2
  have hp : f (X 2) = 0 := by
    have h1 : f (X 2)^2 = 0 := by
      have h1 := h 1
      simp only [quadric, map_add, map_sub, map_mul, map_pow, hu, ht, hv] at h1
      linear_combination h1
    exact (sq_eq_zero_iff (a := f (X 2))).mp h1
  have hq : f (X 3) = 0 := by
    have h2 : f (X 3)^2 = 0 := by
      have h2 := h 2
      simp only [quadric, map_add, map_sub, map_mul, map_pow, hu, ht, hv] at h2
      linear_combination h2
    exact (sq_eq_zero_iff (a := f (X 3))).mp h2
  intro i
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change f (X i) = 0
  fin_cases i <;> assumption

/-- These two genuine basic opens cover the entire literal projective Scheme, including infinity. -/
theorem two_charts_cover (c : K) (hc : c ≠ 0) :
    Proj.basicOpen (quotientGrading c) (coord c 4) ⊔
      Proj.basicOpen (quotientGrading c) (coord c 0) = ⊤ := by
  apply top_le_iff.mp
  intro x _
  change coord c 4 ∉ x.asHomogeneousIdeal ∨ coord c 0 ∉ x.asHomogeneousIdeal
  by_contra h
  push_neg at h
  haveI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have hall := all_coordinates_mem_of_UT c hc x.asHomogeneousIdeal.toIdeal h.2 h.1
  apply x.not_irrelevant_le
  have hirr := ProjectiveQuotientCharts.irrelevant_le_span_coordinates K 4 (homogeneousIdeal c)
  have hle : Ideal.span (Set.range (coord c)) ≤ x.asHomogeneousIdeal.toIdeal := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hall i
  exact hirr.trans hle

/-- A two-affine cover with affine overlap of the actual adjacent three-quadric Proj. -/
def twoAffineOpenCover (c : K) (hc : c ≠ 0) : (curve c).TwoAffineOpenCover where
  U0 := Proj.basicOpen (quotientGrading c) (coord c 4)
  U1 := Proj.basicOpen (quotientGrading c) (coord c 0)
  isAffineOpen_U0 := Proj.isAffineOpen_basicOpen (quotientGrading c) _
    ((quotientMap c).map_mem (Slot02HighProjSpace.X_mem_one K 4 4)) one_pos
  isAffineOpen_U1 := Proj.isAffineOpen_basicOpen (quotientGrading c) _
    ((quotientMap c).map_mem (Slot02HighProjSpace.X_mem_one K 4 0)) one_pos
  sup_eq_top := two_charts_cover c hc
  isAffineOpen_inf := by
    rw [← Proj.basicOpen_mul]
    exact Proj.isAffineOpen_basicOpen (quotientGrading c) _
      (SetLike.mul_mem_graded
        ((quotientMap c).map_mem (Slot02HighProjSpace.X_mem_one K 4 4))
        ((quotientMap c).map_mem (Slot02HighProjSpace.X_mem_one K 4 0))) (by decide : 0 < 1+1)

/-- The genuine T chart is integral, by its constructed literal-source Scheme isomorphism. -/
theorem tChart_isIntegral (c : K) (h : AdjacentPolynomials.Admissible c) :
    letI : GradedRing (quotientGrading c) :=
      quotGradingGradedRingOfHomogeneous (grading K) (homogeneousIdeal c)
    IsIntegral ((Proj.basicOpen (quotientGrading c) (coord c 4)).toScheme) := by
  letI := AdjacentCoordinateAlgebra.coordinateRing_isDomain c h
  letI : GradedRing (quotientGrading c) :=
    quotGradingGradedRingOfHomogeneous (grading K) (homogeneousIdeal c)
  haveI : Nonempty ((Proj.basicOpen (quotientGrading c) (coord c 4)).toScheme) :=
    Nonempty.map (literalChartSchemeIso c).inv.base inferInstance
  exact isIntegral_of_isOpenImmersion (literalChartSchemeIso c).hom

#print axioms all_coordinates_mem_of_UT
#print axioms two_charts_cover
#print axioms twoAffineOpenCover
#print axioms tChart_isIntegral
end FourCorner.AdjacentPost
