import InfinityChartEquations

noncomputable section
namespace FourCorner.InfinityResidueChart
open AlgebraicCurve ResiduePlaceEvaluation InfinityRootOrders
variable {k : Type*} [Field k] [NeZero (2:k)] {t κ : k}
local notation "E" => CommonGenus17Field.field k t κ

def parameterSection (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hl : RadicalLinearization.ell k t κ ∉ w.toValuationSubring) :
    w.toValuationSubring :=
  ⟨parameter t κ,w.mem_of_ord_nonneg (parameter_ne_zero h1 hm hκ)
    (by rw [parameter_order h0 h1 hm hκ w hl]; norm_num)⟩

def rootSection (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hl : RadicalLinearization.ell k t κ ∉ w.toValuationSubring) (i : Fin 4) :
    w.toValuationSubring :=
  ⟨normalized t κ i,w.mem_of_ord_nonneg (normalized_ne_zero h1 hm hκ i)
    (by rw [normalized_order h0 h1 hm hκ w hl i])⟩

def residueValues (t κ : k) : Fin 4 → k
  | 0 => κ
  | 1 => κ
  | 2 => -(t-1)
  | 3 => t+1

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

theorem parameter_residue (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∉ w.toValuationSubring) :
    evaluate w hw (parameterSection h0 h1 hm hκ w hl)=0 := by
  apply (ResidueValuationFacts.evaluate_zero_iff_ord_pos _ _ _ (parameter_ne_zero h1 hm hκ)).mpr
  change 0<w.ord (parameter t κ)
  rw [parameter_order h0 h1 hm hκ w hl]
  norm_num

theorem root_unit (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hl : RadicalLinearization.ell k t κ ∉ w.toValuationSubring) (i : Fin 4) :
    IsUnit (rootSection h0 h1 hm hκ w hl i) :=
  ResidueValuationFacts.unit_of_ord_zero w _ (normalized_ne_zero h1 hm hκ i)
    (normalized_order h0 h1 hm hκ w hl i)

theorem residue_equations (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∉ w.toValuationSubring) (i : Fin 4) :
    evaluate w hw (rootSection h0 h1 hm hκ w hl i)^2=residueValues t κ i := by
  have hs : rootSection h0 h1 hm hκ w hl i ^2 =
      InfinityChartEquations.values (algebraMap k w.toValuationSubring t)
        (algebraMap k w.toValuationSubring κ) (algebraMap k w.toValuationSubring κ⁻¹)
        (parameterSection h0 h1 hm hκ w hl) i := by
    apply Subtype.ext
    change normalized t κ i ^2 = _
    rw [InfinityChartEquations.normalized_sq h1 hm hκ i]
    exact (InfinityChartEquations.map_values w.toValuationSubring.subtype
      (algebraMap k w.toValuationSubring t) (algebraMap k w.toValuationSubring κ)
      (algebraMap k w.toValuationSubring κ⁻¹) (parameterSection h0 h1 hm hκ w hl) i).symm
  have he := congrArg (evaluate w hw) hs
  rw [map_pow] at he
  have hemap := InfinityChartEquations.map_values (evaluate w hw).toRingHom
    (algebraMap k w.toValuationSubring t) (algebraMap k w.toValuationSubring κ)
    (algebraMap k w.toValuationSubring κ⁻¹) (parameterSection h0 h1 hm hκ w hl) i
  change (evaluate w hw) _ = InfinityChartEquations.values
    ((evaluate w hw) (algebraMap k w.toValuationSubring t))
    ((evaluate w hw) (algebraMap k w.toValuationSubring κ))
    ((evaluate w hw) (algebraMap k w.toValuationSubring κ⁻¹))
    ((evaluate w hw) (parameterSection h0 h1 hm hκ w hl)) i at hemap
  rw [evaluate_constant,evaluate_constant,evaluate_constant,parameter_residue] at hemap
  rw [hemap] at he
  exact he.trans (by fin_cases i <;> simp [InfinityChartEquations.values,residueValues])

/-- Complete ordered infinity residue data, all from the original chosen place.
The four units are P/Z,C/Z,M,B and the parameter is exactly 1/Z. -/
theorem infinity_chart (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∉ w.toValuationSubring) :
    w.ord (parameter t κ)=1 ∧ evaluate w hw (parameterSection h0 h1 hm hκ w hl)=0 ∧
    ∀ i, w.ord (normalized t κ i)=0 ∧ IsUnit (rootSection h0 h1 hm hκ w hl i) ∧
      evaluate w hw (rootSection h0 h1 hm hκ w hl i)≠0 ∧
      evaluate w hw (rootSection h0 h1 hm hκ w hl i)^2=residueValues t κ i := by
  refine ⟨parameter_order h0 h1 hm hκ w hl,parameter_residue h0 h1 hm hκ w hw hl,?_⟩
  intro i
  have hu := root_unit h0 h1 hm hκ w hl i
  exact ⟨normalized_order h0 h1 hm hκ w hl i,hu,
    (ResidueValuationFacts.evaluate_nonzero_iff_unit _ _ _).mpr hu,
    residue_equations h0 h1 hm hκ w hw hl i⟩
end FourCorner.InfinityResidueChart
#print axioms FourCorner.InfinityResidueChart.infinity_chart
#print axioms FourCorner.InfinityResidueChart.residue_equations
