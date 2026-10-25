import CommonActualDegree
import CommonFourRamification
import CommonFourPlaceOrders
import CommonRamificationSum
import geometry.RatFuncFiniteExtension

noncomputable section
set_option maxHeartbeats 800000
namespace FourCorner.CommonLiteralField
open AlgebraicCurve
variable {K : Type*} [Field K] [CharZero K]
local instance : DecidableEq (Place K (RatFunc K)) := Classical.decEq _

theorem root_generates (t : K) : Algebra.adjoin (RatFunc K)
    {root K t 0,root K t 1,root K t 2,root K t 3} = ⊤ := by
  have hrange : Set.range (root K t) =
      {root K t 0,root K t 1,root K t 2,root K t 3} := by
    ext x
    simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> tauto
    · intro hx
      rcases hx with hx | hx | hx | hx
      · exact ⟨0,hx.symm⟩
      · exact ⟨1,hx.symm⟩
      · exact ⟨2,hx.symm⟩
      · exact ⟨3,hx.symm⟩
  apply (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic
    (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)).mp
  rw [← hrange]
  exact root_adjoin_eq_top K t

theorem radicand_ne_zero {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (htm : t ≠ -1) (i : Fin 4) : radicand K t i ≠ 0 := by
  have hn := CommonFiveIndependence.four_product_nonsquare ht0 ht1 htm {i} (by simp)
  simp only [Finset.prod_singleton] at hn
  intro hz
  apply hn
  simp [hz]

theorem ramificationIndex_formula [IsAlgClosed K] {t : K}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1)
    (w : Place K (field K t)) :
    w.ramificationIndex (RatFunc K) =
      if w.restrict (RatFunc K) ∈ CommonFourPlaceOrders.support t then 2 else 1 := by
  classical
  letI : FiniteDimensional (RatFunc K) (field K t) :=
    FiniteDimensional.of_finrank_pos (by rw [finrank_field_eq_sixteen K ht0 ht1 htm]; norm_num)
  rw [CommonFourRamification.index_formula w
    (radicand K t 0) (radicand K t 1) (radicand K t 2) (radicand K t 3)
    (root K t 0) (root K t 1) (root K t 2) (root K t 3)
    (root_sq K t 0) (root_sq K t 1) (root_sq K t 2) (root_sq K t 3)
    (radicand_ne_zero ht0 ht1 htm 0) (radicand_ne_zero ht0 ht1 htm 1)
    (radicand_ne_zero ht0 ht1 htm 2) (radicand_ne_zero ht0 ht1 htm 3) (root_generates t)]
  have hall : (∀ i : Fin 4, Even ((w.restrict (RatFunc K)).ord (radicand K t i))) ↔
      (Even ((w.restrict (RatFunc K)).ord (radicand K t 0)) ∧
       Even ((w.restrict (RatFunc K)).ord (radicand K t 1)) ∧
       Even ((w.restrict (RatFunc K)).ord (radicand K t 2)) ∧
       Even ((w.restrict (RatFunc K)).ord (radicand K t 3))) := by
    simp [Fin.forall_fin_succ]
  have hs := CommonFourPlaceOrders.exists_odd_iff_mem_support t ht0 ht1 htm
    (w.restrict (RatFunc K))
  by_cases hm : w.restrict (RatFunc K) ∈ CommonFourPlaceOrders.support t
  · rw [if_pos hm,if_neg]
    intro hh
    obtain ⟨i,hi⟩ := hs.mpr hm
    exact (Int.not_even_iff_odd.mpr hi) ((hall.mpr hh) i)
  · rw [if_neg hm,if_pos]
    apply hall.mp
    intro i
    by_contra hh
    exact hm (hs.mp ⟨i,Int.not_even_iff_odd.mp hh⟩)

theorem genusFF_eq_nine [IsAlgClosed K] {t : K}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    genusFF K (field K t) = 9 := by
  classical
  letI : FiniteDimensional (RatFunc K) (field K t) :=
    FiniteDimensional.of_finrank_pos (by rw [finrank_field_eq_sixteen K ht0 ht1 htm]; norm_num)
  letI : IsCurveOver K (RatFunc K) := RatFuncFiniteExtension.isCurveOver_of_charZero K (RatFunc K)
  letI : IsCurveOver K (field K t) := RatFuncFiniteExtension.isCurveOver_of_charZero K (field K t)
  apply CommonRamificationSum.genusFF_eq_nine_of_degree_sixteen_and_six_branch_places
    (RatFuncFiniteExtension.base_oneVariable K) (RatFuncFiniteExtension.genus_base_eq_zero K)
    (CommonFourPlaceOrders.support t) (CommonFourPlaceOrders.support_card t ht0 ht1 htm)
    (finrank_field_eq_sixteen K ht0 ht1 htm)
  exact ramificationIndex_formula ht0 ht1 htm

#print axioms root_generates
#print axioms ramificationIndex_formula
#print axioms genusFF_eq_nine
end FourCorner.CommonLiteralField
