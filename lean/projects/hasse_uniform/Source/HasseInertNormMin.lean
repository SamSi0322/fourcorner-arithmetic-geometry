import HasseOddSymbol

namespace FourCorner.HasseInertNormMin

variable {q : ℕ} [Fact q.Prime]

/-- Exact valuation of the actual unramified quadratic norm, at every
positive or negative depth, with no cancellation when 2 is nonsquare. -/
theorem norm_form_val_min (hq : q ≠ 2) (h2 : ¬ IsSquare (2 : ℚ_[q]))
    (x y : ℚ_[q]) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x^2-2*y^2).valuation=2*min x.valuation y.valuation := by
  by_cases he : x.valuation=y.valuation
  · rw [HasseInertNorm.norm_form_val_equal hq h2 hx hy he]
    rw [he,min_self]
  · have ht : (2*y^2).valuation=2*y.valuation := by
      rw [Padic.valuation_mul (by norm_num) (pow_ne_zero _ hy),commonRoot_val_two hq,
        Padic.valuation_pow]
      simp
    have hh := commonRoot_val_sub_of_ne (pow_ne_zero 2 hx)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))
      (show (x^2).valuation ≠ (2*y^2).valuation by rw [Padic.valuation_pow,ht]; omega)
    rw [hh,Padic.valuation_pow,ht]
    rcases le_total x.valuation y.valuation with h | h
    · rw [min_eq_left h,min_eq_left (by omega)]
      norm_num
    · rw [min_eq_right h,min_eq_right (by omega)]

#print axioms norm_form_val_min

end FourCorner.HasseInertNormMin
