import HpUChartTower
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

namespace FourCorner.HpTwoChartCover
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open HpLiteralProjective
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type*) [Field K] [CharZero K]
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

abbrev Q (p : K) := ThetaQuotientChart.Q (equation K p) (homogeneous K p)
abbrev G (p : K) := ThetaQuotientChart.G (equation K p) (homogeneous K p)
abbrev coordinate (p : K) (i : Fin 5) := ThetaProjectiveModel.coordinate (equation K p) (homogeneous K p) i
abbrev degree (p : K) (i : Fin 5) := ThetaProjectiveModel.coordinate_degree (equation K p) (homogeneous K p) i

/-- At any prime of the ACTUAL homogeneous quotient, simultaneous Z=U=0
forces every coordinate into that prime; no boundary component is discarded. -/
theorem all_coordinates_mem (p : K) (hp : p ≠ 0) (I : Ideal (Q K p)) [I.IsPrime]
    (hz : coordinate K p 0∈I) (hu : coordinate K p 1∈I) : ∀i,coordinate K p i∈I := by
  let g := (ThetaQuotientChart.quotientMap (equation K p) (homogeneous K p)).toRingHom
  have he (i : Fin 3) : g (equation K p i)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  have h0:=he 0
  have h1:=he 1
  have h2:=he 2
  simp only [equation,map_mul,map_pow,map_sub,map_add] at h0 h1 h2
  have hz2 : (coordinate K p 0)^2∈I := by simpa only [pow_two] using I.mul_mem_left (coordinate K p 0) hz
  have hu2 : (coordinate K p 1)^2∈I := by simpa only [pow_two] using I.mul_mem_left (coordinate K p 1) hu
  have cancel (y : Q K p) (hy : g (C p)*y∈I) : y∈I := by
    have hh := I.mul_mem_left (g (C p⁻¹)) hy
    have hi : g (C p⁻¹)*g (C p)=1 := by
      rw [← map_mul,← MvPolynomial.C_mul,inv_mul_cancel₀ hp,map_one]
      exact map_one g
    rw [← mul_assoc,hi,one_mul] at hh
    exact hh
  have hv : coordinate K p 2∈I := by
    apply (inferInstance : I.IsPrime).mem_of_pow_mem 2
    apply cancel
    have hh : g (C p)*(coordinate K p 2)^2=(g (C 2)*(g (C p)-g (C 1)))*
        ((coordinate K p 1)^2-g (C p)*(coordinate K p 0)^2) := sub_eq_zero.mp h0
    rw [hh]
    exact I.mul_mem_left _ (I.sub_mem hu2 (I.mul_mem_left _ hz2))
  have hw : coordinate K p 3∈I := by
    apply (inferInstance : I.IsPrime).mem_of_pow_mem 2
    apply cancel
    have hh : g (C p)*(coordinate K p 3)^2=(g (C 2)*(g (C p)+g (C 1)))*
        ((coordinate K p 1)^2+g (C p)*(coordinate K p 0)^2) := sub_eq_zero.mp h1
    rw [hh]
    exact I.mul_mem_left _ (I.add_mem hu2 (I.mul_mem_left _ hz2))
  have ht : coordinate K p 4∈I := by
    apply (inferInstance : I.IsPrime).mem_of_pow_mem 2
    apply cancel
    have hh : g (C p)*(coordinate K p 4)^2=(g (C p)-g (C 1))*(coordinate K p 1)^2+
        (g (C p)*(g (C p)+g (C 1)))*(coordinate K p 0)^2 := by linear_combination h2
    rw [hh]
    exact I.add_mem (I.mul_mem_left _ hu2) (I.mul_mem_left _ hz2)
  intro i
  fin_cases i <;> assumption

/-- The TWO genuine standard opens Z≠0 and U≠0 cover the literal C_p. -/
theorem two_charts_cover (p : K) (hp : p ≠ 0) :
    Proj.basicOpen (G K p) (coordinate K p 0) ⊔ Proj.basicOpen (G K p) (coordinate K p 1)=⊤ := by
  apply top_le_iff.mp
  intro x _
  change coordinate K p 0∉x.asHomogeneousIdeal ∨ coordinate K p 1∉x.asHomogeneousIdeal
  by_contra h
  push_neg at h
  haveI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have hall := all_coordinates_mem K p hp x.asHomogeneousIdeal.toIdeal h.1 h.2
  apply x.not_irrelevant_le
  apply (ThetaProjectiveModel.irrelevant_span (equation K p) (homogeneous K p)).trans
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact hall i

 def cover (p : K) (hp : p ≠ 0) : (curve K p).TwoAffineOpenCover where
  U0 := Proj.basicOpen (G K p) (coordinate K p 0)
  U1 := Proj.basicOpen (G K p) (coordinate K p 1)
  isAffineOpen_U0 := Proj.isAffineOpen_basicOpen (G K p) _ (degree K p 0) one_pos
  isAffineOpen_U1 := Proj.isAffineOpen_basicOpen (G K p) _ (degree K p 1) one_pos
  sup_eq_top := two_charts_cover K p hp
  isAffineOpen_inf := by
    rw [← Proj.basicOpen_mul]
    exact Proj.isAffineOpen_basicOpen (G K p) _ (SetLike.mul_mem_graded (degree K p 0) (degree K p 1)) (by decide : 0<1+1)

#print axioms all_coordinates_mem
#print axioms two_charts_cover
#print axioms cover
end
end FourCorner.HpTwoChartCover
