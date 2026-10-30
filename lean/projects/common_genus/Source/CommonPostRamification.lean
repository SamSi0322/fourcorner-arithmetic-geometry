import CommonActualGenus
import Theorems.Thm_AlgebraicCurve_Place_exists_restrict_eq

noncomputable section
namespace FourCorner.CommonPostRamification
open AlgebraicCurve CommonLiteralField
variable {K : Type*} [Field K] [CharZero K]
attribute [local instance] Classical.propDecidable
theorem ramificationIndex_formula {t : K}
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

/-- Actual ramification of the literal four-root extension over any characteristic-zero constants. -/
theorem ramifies_iff {t : K} (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1)
    (w : Place K (field K t)) :
    1 < w.ramificationIndex (RatFunc K) ↔ w.restrict (RatFunc K) ∈ CommonFourPlaceOrders.support t := by
  rw [ramificationIndex_formula h0 h1 hm]
  split_ifs <;> simp_all

end FourCorner.CommonPostRamification
#print axioms FourCorner.CommonPostRamification.ramificationIndex_formula
#print axioms FourCorner.CommonPostRamification.ramifies_iff
