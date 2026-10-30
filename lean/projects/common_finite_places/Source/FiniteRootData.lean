import ResiduePlaceImage
import FiniteResidueChart

noncomputable section
namespace FourCorner.FiniteRootData
open AlgebraicCurve AlgebraicCurve.RationalFunctionField RadicalLinearization ResiduePlaceEvaluation
open LinearizedFactors
variable {k : Type*} [Field k] [NeZero (2:k)] {t κ : k}
local notation "E" => CommonGenus17Field.field k t κ
local instance finiteLine : FiniteDimensional (RatFunc k) E := ResidueRadicalField.finite_over_line k t κ
local instance : DecidableEq (RatFunc k) := Classical.decEq _
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false

theorem residue_zero_iff (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∈ w.toValuationSubring) (i : Fin 5) :
    evaluate w hw (FiniteResidueChart.rootSection t κ hκ w hl i)=0 ↔
      evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩=branch t i := by
  have he := FiniteResidueChart.residue_equations t κ hκ w hw hl i
  rw [←values_zero_iff h1 hm hκ,←he]
  exact (sq_eq_zero_iff).symm

theorem unit_iff (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∈ w.toValuationSubring) (i : Fin 5) :
    IsUnit (FiniteResidueChart.rootSection t κ hκ w hl i) ↔
      evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩≠branch t i := by
  rw [←ResidueValuationFacts.evaluate_nonzero_iff_unit,ne_eq,residue_zero_iff h1 hm hκ]

theorem branch_support (t : k) (i : Fin 5) :
    placeOfPoint k (branch t i) ∈ OddFourPlaces.support t := by
  fin_cases i
  all_goals try (simp only [branch]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  all_goals apply Finset.mem_insert_of_mem
  all_goals apply Finset.mem_insert_of_mem
  all_goals apply (OddFourPlaces.mem_privatePlaces _ _).mpr
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩

theorem root_order_equation (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∈ w.toValuationSubring) (i : Fin 5) :
    2*w.ord (roots k t κ i) = (w.ramificationIndex (RatFunc k):ℤ)*
      (if evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩=branch t i then 1 else 0) := by
  have he := congrArg w.ord (roots_sq_factor t κ hκ i)
  have hc : algebraMap k E (coefficient t κ i)≠0 :=
    (map_ne_zero _).mpr (coefficient_ne_zero h1 hm hκ i)
  have hf : algebraMap (RatFunc k) E (OddFourPlaces.linear (branch t i))≠0 :=
    (map_ne_zero _).mpr (OddFourPlaces.linear_ne_zero _)
  rw [show roots k t κ i ^2 = roots k t κ i ^(2:ℤ) from (zpow_ofNat _ _).symm,w.ord_zpow,
    w.ord_mul hc hf,w.ord_algebraMap,zero_add,w.ord_restrict,
    ResiduePlaceImage.finite_image t κ w hw hl,OddFourPlaces.ord_linear_finite] at he
  exact he

theorem root_order (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∈ w.toValuationSubring) (i : Fin 5) :
    w.ord (roots k t κ i) =
      if evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩=branch t i then 1 else 0 := by
  have he := root_order_equation h1 hm hκ w hw hl i
  split_ifs with hi
  · have heidx : w.ramificationIndex (RatFunc k)=2 := by
      rw [OddFiveRamification.index_formula h0 h1 hm hκ,
        ResiduePlaceImage.finite_image t κ w hw hl,hi,
        if_pos (branch_support t i)]
    rw [heidx,if_pos hi] at he
    norm_num at he
    omega
  · rw [if_neg hi,mul_zero] at he
    omega
end FourCorner.FiniteRootData
#print axioms FourCorner.FiniteRootData.residue_zero_iff
#print axioms FourCorner.FiniteRootData.unit_iff
#print axioms FourCorner.FiniteRootData.root_order
