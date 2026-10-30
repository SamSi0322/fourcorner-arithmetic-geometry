import OriginalFiniteUnits

noncomputable section
namespace FourCorner.ZeroResidueChart
open AlgebraicCurve RadicalLinearization ResiduePlaceEvaluation
variable {k : Type*} [Field k] [NeZero (2:k)] {t κ : k}
local notation "E" => CommonGenus17Field.field k t κ

/-- The zero chart uses Z, P, C, MZ, BZ from the SAME chosen rational place;
M and B themselves are poles of order one. -/
theorem zero_chart (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∈ w.toValuationSubring)
    (ha : evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩=0) :
    w.ord (Genus17Geometry.fiveRoot t κ 4)=1 ∧
    evaluate w hw (FiniteResidueChart.rootSection t κ hκ w hl 4)=0 ∧
    (∀ i : Fin 4, IsUnit (FiniteResidueChart.rootSection t κ hκ w hl i.castSucc) ∧
      evaluate w hw (FiniteResidueChart.rootSection t κ hκ w hl i.castSucc)≠0) ∧
    evaluate w hw (FiniteResidueChart.rootSection t κ hκ w hl 0)^2=t+1 ∧
    evaluate w hw (FiniteResidueChart.rootSection t κ hκ w hl 1)^2= -(t-1) ∧
    evaluate w hw (FiniteResidueChart.rootSection t κ hκ w hl 2)^2=(t-1)*(t+1)*κ⁻¹ ∧
    evaluate w hw (FiniteResidueChart.rootSection t κ hκ w hl 3)^2=(t+1)*(t-1)*κ⁻¹ ∧
    w.ord (Genus17Geometry.fiveRoot t κ 2)= -1 ∧
    w.ord (Genus17Geometry.fiveRoot t κ 3)= -1 := by
  have hb := FiniteBranchCharts.branch_chart h0 h1 hm hκ w hw hl 4 ha
  refine ⟨?_,hb.2.1,?_,?_,?_,?_,?_,OriginalFiniteOrders.zero_poles h0 h1 hm hκ w hw hl ha⟩
  · exact hb.1 4
  · intro i
    have hi : i.castSucc≠(4:Fin 5) := by
      intro heq
      have hval := congrArg Fin.val heq
      change i.val=4 at hval
      omega
    exact ⟨(hb.2.2.1 i.castSucc hi).2,(hb.2.2.1 i.castSucc hi).1⟩
  all_goals have he := FiniteResidueChart.residue_equations t κ hκ w hw hl
  · simpa [ha,values] using he 0
  · simpa [ha,values] using he 1
  · simpa [ha,values] using he 2
  · simpa [ha,values] using he 3
end FourCorner.ZeroResidueChart
#print axioms FourCorner.ZeroResidueChart.zero_chart
