import ActualSourceDepth

noncomputable section
namespace FourCorner.CommonSource

/-- The two remaining torsion-coordinate orders in the n=1 case, stated over
Q so the identical source can subsequently be reduced at every odd prime. -/
theorem rational_orders_one_survive {n a c x w : ℚ}
    (hn : (n:ℚ_[2]) ≠ 0) (hvn : (n:ℚ_[2]).valuation=0)
    (hxv : (x:ℚ_[2]).valuation < 0) (hwv : (w:ℚ_[2]).valuation < 0)
    (hxe : Even (x:ℚ_[2]).valuation)
    (ho : commonSourceDyadicOrdersOne (n:ℚ_[2]) x w a c)
    (hf : Even (commonSourceReturn (n:ℚ_[2]) a c).valuation) :
    (a=commonSourceTranslateMinus n x ∧ c=commonSourceTranslatePlus n w) ∨
    (a=commonSourceTranslatePlus n x ∧ c=commonSourceTranslateMinus n w) := by
  rcases ho with h | h | h | h
  · exact False.elim (commonSource_dyadic_not_even_zero_orders hn hvn hxv hwv hxe (Or.inl h) hf)
  · exact False.elim (commonSource_dyadic_not_even_zero_orders hn hvn hxv hwv hxe (Or.inr h) hf)
  · left
    rcases h with ⟨ha,hc⟩
    constructor
    · dsimp [commonSourceTranslateMinus] at ha ⊢
      exact_mod_cast ha
    · dsimp [commonSourceTranslatePlus] at hc ⊢
      exact_mod_cast hc
  · right
    rcases h with ⟨ha,hc⟩
    constructor
    · dsimp [commonSourceTranslatePlus] at ha ⊢
      exact_mod_cast ha
    · dsimp [commonSourceTranslateMinus] at hc ⊢
      exact_mod_cast hc

/-- The two remaining torsion-coordinate orders in the n=7 case, over Q. -/
theorem rational_orders_seven_survive {n a c x w : ℚ}
    (hn : (n:ℚ_[2]) ≠ 0) (hvn : (n:ℚ_[2]).valuation=0)
    (hxv : (x:ℚ_[2]).valuation < 0) (hwv : (w:ℚ_[2]).valuation < 0)
    (hwe : Even (w:ℚ_[2]).valuation)
    (ho : commonSourceDyadicOrdersSeven (n:ℚ_[2]) x w a c)
    (hf : Even (commonSourceReturn (n:ℚ_[2]) a c).valuation) :
    (a=x ∧ c=w) ∨
    (a=commonSourceTranslateZero n x ∧ c=commonSourceTranslateZero n w) := by
  rcases ho with ⟨ha,hc⟩ | ⟨ha,hc⟩ | h | h
  · rw [ha,hc] at hf
    exact False.elim (commonSource_dyadic_plus_plus_not_even hn hvn hxv hwv hf)
  · rw [ha,hc] at hf
    exact False.elim (commonSource_dyadic_minus_minus_not_even hn hvn hxv hwv hwe hf)
  · left
    exact ⟨by exact_mod_cast h.1,by exact_mod_cast h.2⟩
  · right
    rcases h with ⟨ha,hc⟩
    constructor
    · dsimp [commonSourceTranslateZero] at ha ⊢
      exact_mod_cast ha
    · dsimp [commonSourceTranslateZero] at hc ⊢
      exact_mod_cast hc

/-- A complete actual ordered source with even dyadic return has precisely one
of the four surviving rational coordinate orders. All selected labels come
from the same source decomposition; there is no per-prime choice. -/
theorem actual_source_surviving_orders {n : ℤ} (hn : n ≠ 0)
    (hn8 : n%8=1 ∨ n%8=7) {a b c e u v x y w z : ℚ}
    (hQ : CongruentEquation (n:ℚ) a b) (hR : CongruentEquation (n:ℚ) c e)
    (hU : CongruentEquation (n:ℚ) x y) (hV : CongruentEquation (n:ℚ) w z)
    (ha : a ≠ 0) (hc : c ≠ 0) (ham : a-n ≠ 0) (hcm : c-n ≠ 0)
    (hap : a+n ≠ 0) (hcp : c+n ≠ 0)
    (hu : u^2= -(a*c)/n) (hv : v^2= -((a-n)*(c-n))/n)
    (hUH : finitePoint (by exact_mod_cast hn) hU ∈ H n hn)
    (hVH : finitePoint (by exact_mod_cast hn) hV ∈ H n hn)
    (τQ τR : Point (n:ℚ)) (htQ : 2 • τQ=0) (htR : 2 • τR=0)
    (hQU : finitePoint (by exact_mod_cast hn) hQ=finitePoint (by exact_mod_cast hn) hU+τQ)
    (hRV : finitePoint (by exact_mod_cast hn) hR=finitePoint (by exact_mod_cast hn) hV+τR)
    (hf : Even (commonSourceReturn (n:ℚ_[2]) a c).valuation) :
    (n%8=1 ∧ ((a=commonSourceTranslateMinus (n:ℚ) x ∧ c=commonSourceTranslatePlus (n:ℚ) w) ∨
      (a=commonSourceTranslatePlus (n:ℚ) x ∧ c=commonSourceTranslateMinus (n:ℚ) w))) ∨
    (n%8=7 ∧ ((a=x ∧ c=w) ∨
      (a=commonSourceTranslateZero (n:ℚ) x ∧ c=commonSourceTranslateZero (n:ℚ) w))) := by
  obtain ⟨hx,hxm,hxp,hxv,hxe⟩ := actual_H_coordinate_data hn hU hUH
  obtain ⟨hw,hwm,hwp,hwv,hwe⟩ := actual_H_coordinate_data hn hV hVH
  have hodd : Odd n := by
    rcases hn8 with h | h
    · exact Int.odd_iff.mpr (by omega)
    · exact Int.odd_iff.mpr (by omega)
  obtain ⟨hn2,hvn⟩ := commonSource_dyadic_odd_int_unit hodd
  have hs := source_kummer_sum (by exact_mod_cast hn) hQ hR ha hc ham hcm hap hcp hu hv
  rcases hn8 with h | h
  · left;refine ⟨h,?_⟩
    have ht := source_torsion_sum_one n hn h _ _ _ _ τQ τR hUH hVH hQU hRV htQ htR hs
    have ho := actual_coordinate_orders_one (by exact_mod_cast hn) hQ hR hU hV
      hx hxm hxp hw hwm hwp τQ τR htQ ht hQU hRV
    exact rational_orders_one_survive hn2 hvn hxv hwv hxe ho hf
  · right;refine ⟨h,?_⟩
    have ht := source_torsion_sum_seven n hn h _ _ _ _ τQ τR hUH hVH hQU hRV htQ htR hs
    have ho := actual_coordinate_orders_seven (by exact_mod_cast hn) hQ hR hU hV
      hx hxm hxp hw hwm hwp τQ τR htQ ht hQU hRV
    exact rational_orders_seven_survive hn2 hvn hxv hwv hwe ho hf

#print axioms actual_source_surviving_orders
end FourCorner.CommonSource
