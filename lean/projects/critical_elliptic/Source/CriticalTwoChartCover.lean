import CriticalStandardCharts
import CriticalSchemePoints23
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

noncomputable section
namespace FourCorner.CriticalTwoChartCover
open AlgebraicGeometry MvPolynomial CriticalProj23 CriticalElliptic23
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type*} [Field k]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

lemma equation_zero (i : k) (a : Fin 2) :
    Ideal.Quotient.mk (homogeneousIdeal i).toIdeal (equation i a)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨a,rfl⟩)

lemma all_coordinates_mem (i : k) (I : Ideal (Ambient k ⧸ (homogeneousIdeal i).toIdeal)) [I.IsPrime]
    (h0 : coordinate i 0∈I) (h1 : coordinate i 1∈I) : ∀ j,coordinate i j∈I := by
  let f : Ambient k →+* (Ambient k ⧸ (homogeneousIdeal i).toIdeal) ⧸ I :=
    (Ideal.Quotient.mk I).comp (Ideal.Quotient.mk (homogeneousIdeal i).toIdeal)
  have hx0 : f (X 0)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr h0
  have hx1 : f (X 1)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr h1
  have he (a : Fin 2) : f (equation i a)=0 := by
    change Ideal.Quotient.mk I (Ideal.Quotient.mk (homogeneousIdeal i).toIdeal (equation i a))=0
    rw [equation_zero,map_zero]
  have hx2 : f (X 2)^2=0 := by
    have h:=he 0
    simp only [equation,F0,map_sub,map_mul,map_pow,hx0,hx1] at h
    linear_combination h
  have hx3 : f (X 3)^2=0 := by
    have h:=he 1
    simp only [equation,F1,map_sub,map_mul,map_pow,hx0,hx1] at h
    linear_combination h
  have hcoord (j : Fin 4) (h : f (X j)^2=0) : coordinate i j∈I := by
    apply (inferInstance : I.IsPrime).mem_of_pow_mem 2
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_pow]
    change f (X j)^2=0
    exact h
  intro j
  fin_cases j
  · exact h0
  · exact h1
  · exact hcoord 2 hx2
  · exact hcoord 3 hx3

/-- The actual V0 and V1 opens cover the WHOLE original projective curve. -/
theorem two_charts_cover (i : k) :
    Proj.basicOpen (criticalGrading i) (coordinate i 0) ⊔
      Proj.basicOpen (criticalGrading i) (coordinate i 1)=⊤ := by
  apply top_le_iff.mp
  intro x _
  change coordinate i 0∉x.asHomogeneousIdeal ∨ coordinate i 1∉x.asHomogeneousIdeal
  by_contra h
  push_neg at h
  haveI : x.asHomogeneousIdeal.toIdeal.IsPrime:=x.isPrime
  have hall:=all_coordinates_mem i x.asHomogeneousIdeal.toIdeal h.1 h.2
  apply x.not_irrelevant_le
  exact (critical_irrelevant_le_span i).trans (Ideal.span_le.mpr (by
    rintro _ ⟨j,rfl⟩; exact hall j))

def cover (i : k) : (criticalCurve i).TwoAffineOpenCover where
  U0:=Proj.basicOpen (criticalGrading i) (coordinate i 0)
  U1:=Proj.basicOpen (criticalGrading i) (coordinate i 1)
  isAffineOpen_U0:=Proj.isAffineOpen_basicOpen _ _ (coordinate_degree_one i 0) one_pos
  isAffineOpen_U1:=Proj.isAffineOpen_basicOpen _ _ (coordinate_degree_one i 1) one_pos
  sup_eq_top:=two_charts_cover i
  isAffineOpen_inf:=by
    rw [←Proj.basicOpen_mul]
    exact Proj.isAffineOpen_basicOpen _ _
      (SetLike.mul_mem_graded (coordinate_degree_one i 0) (coordinate_degree_one i 1)) (by decide : 0<1+1)

/-- A concrete actual Scheme point [1:1:1:1] lies in BOTH opens. -/
theorem overlap_nonempty (i : k) :
    (((cover i).U0 : Set (criticalCurve i)) ∩ (cover i).U1).Nonempty := by
  let e : Fin 3 → Bool:=fun _=>false
  let p:=signedSchemePoint i e
  let x : Spec (.of k):=Classical.choice inferInstance
  refine ⟨p x,?_,?_⟩
  all_goals change x∈pointOfCoordinates i (signedVector e) _ _ ⁻¹ᵁ Proj.basicOpen (criticalGrading i) (coordinate i _)
  all_goals rw [pointOfCoordinates_preimage_chart]
  all_goals simp [signedVector,e,sign]
end FourCorner.CriticalTwoChartCover
#print axioms FourCorner.CriticalTwoChartCover.two_charts_cover
#print axioms FourCorner.CriticalTwoChartCover.cover
#print axioms FourCorner.CriticalTwoChartCover.overlap_nonempty
