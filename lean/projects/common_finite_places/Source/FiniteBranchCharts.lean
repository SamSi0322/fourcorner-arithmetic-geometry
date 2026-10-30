import FiniteRootData

noncomputable section
namespace FourCorner.FiniteBranchCharts
open AlgebraicCurve RadicalLinearization ResiduePlaceEvaluation LinearizedFactors
variable {k : Type*} [Field k] [NeZero (2:k)] {t κ : k}
local notation "E" => CommonGenus17Field.field k t κ
attribute [local instance] Classical.propDecidable

theorem branch_injective (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) :
    Function.Injective (branch t) := by
  have htwo : (2:k)≠0 := NeZero.ne _
  intro i j h
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk,branch] at h ⊢
  all_goals first | rfl | skip
  all_goals exfalso
  all_goals first
    | exact htwo (by first | linear_combination h | linear_combination -h)
    | exact h0 (by first | linear_combination h | linear_combination -h)
    | exact h1 (by first | linear_combination h | linear_combination -h)
    | exact hm (by first | linear_combination h | linear_combination -h)
    | exact h0 ((mul_eq_zero.mp (show (2:k)*t=0 by
        first | linear_combination h | linear_combination -h)).resolve_left htwo)
    | exact h1 (sub_eq_zero.mp ((mul_eq_zero.mp (show (2:k)*(t-1)=0 by
        first | linear_combination h | linear_combination -h)).resolve_left htwo))
    | have hz : t+1=0 := (mul_eq_zero.mp (show (2:k)*(t+1)=0 by
        first | linear_combination h | linear_combination -h)).resolve_left htwo
      apply hm
      linear_combination hz

theorem branch_chart (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∈ w.toValuationSubring) (j : Fin 5)
    (hj : evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩=branch t j) :
    (∀ i, w.ord (roots k t κ i)=if i=j then 1 else 0) ∧
    evaluate w hw (FiniteResidueChart.rootSection t κ hκ w hl j)=0 ∧
    (∀ i, i≠j → evaluate w hw (FiniteResidueChart.rootSection t κ hκ w hl i)≠0 ∧
      IsUnit (FiniteResidueChart.rootSection t κ hκ w hl i)) ∧
    (∀ i, evaluate w hw (FiniteResidueChart.rootSection t κ hκ w hl i)^2=
      values t κ⁻¹ (branch t j) i) := by
  have hinj := branch_injective h0 h1 hm
  constructor
  · intro i
    rw [FiniteRootData.root_order h0 h1 hm hκ w hw hl i,hj]
    simp only [hinj.eq_iff,eq_comm]
  constructor
  · exact (FiniteRootData.residue_zero_iff h1 hm hκ w hw hl j).mpr hj
  constructor
  · intro i hi
    have hn : evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩≠branch t i := by
      rw [hj]
      exact fun h => hi (hinj h).symm
    have hu := (FiniteRootData.unit_iff h1 hm hκ w hw hl i).mpr hn
    exact ⟨(ResidueValuationFacts.evaluate_nonzero_iff_unit _ _ _).mpr hu,hu⟩
  · intro i
    rw [FiniteResidueChart.residue_equations,hj]

theorem ordinary_chart (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∈ w.toValuationSubring)
    (hoff : ∀ i, evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩≠branch t i) :
    ∀ i, w.ord (roots k t κ i)=0 ∧
      evaluate w hw (FiniteResidueChart.rootSection t κ hκ w hl i)≠0 ∧
      IsUnit (FiniteResidueChart.rootSection t κ hκ w hl i) := by
  intro i
  have hu := (FiniteRootData.unit_iff h1 hm hκ w hw hl i).mpr (hoff i)
  refine ⟨?_,(ResidueValuationFacts.evaluate_nonzero_iff_unit _ _ _).mpr hu,hu⟩
  rw [FiniteRootData.root_order h0 h1 hm hκ w hw hl i,if_neg (hoff i)]
end FourCorner.FiniteBranchCharts
#print axioms FourCorner.FiniteBranchCharts.branch_chart
#print axioms FourCorner.FiniteBranchCharts.ordinary_chart
