import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic

set_option autoImplicit false

namespace FourCorner

private instance primeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- A dyadic power used to clear denominators is nonzero. -/
theorem commonRoot_dyadic_power_ne_zero (h : ℕ) : (2 : ℚ_[2]) ^ h ≠ 0 := by
  exact pow_ne_zero _ (by norm_num)

/-- The actual dyadic norm of the denominator-clearing power. -/
theorem commonRoot_dyadic_power_norm (h : ℕ) :
    ‖(2 : ℚ_[2]) ^ h‖ = (1 / 2 : ℝ) ^ h := by
  rw [norm_pow]
  have h2 : ‖(2 : ℚ_[2])‖ = (1 / 2 : ℝ) := by
    simpa using (Padic.norm_p (p := 2))
  rw [h2]

/-- The denominator-clearing power is integral. -/
theorem commonRoot_dyadic_power_norm_le_one (h : ℕ) :
    ‖(2 : ℚ_[2]) ^ h‖ ≤ 1 := by
  rw [commonRoot_dyadic_power_norm]
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- Multiplying a nonintegral dyadic number by the suitable nonnegative power
of two makes its norm exactly one. -/
theorem commonRoot_dyadic_scale_to_unit (z : ℚ_[2]) (hz : 1 < ‖z‖) :
    ∃ h : ℕ, ‖(2 : ℚ_[2]) ^ h * z‖ = 1 := by
  have hz0 : z ≠ 0 := by
    intro he
    simp only [he, norm_zero] at hz
    norm_num at hz
  have hv : z.valuation < 0 := by
    have hn : ¬ (0 ≤ z.valuation) := by
      intro h
      exact (not_le_of_gt hz) ((Padic.norm_le_one_iff_val_nonneg z).2 h)
    omega
  let h : ℕ := (-z.valuation).toNat
  have hh : (h : ℤ) = -z.valuation := Int.toNat_of_nonneg (by omega)
  refine ⟨h, ?_⟩
  rw [Padic.norm_eq_zpow_neg_valuation
    (mul_ne_zero (commonRoot_dyadic_power_ne_zero h) hz0)]
  have hv2 : (2 : ℚ_[2]).valuation = 1 := Padic.valuation_p
  rw [Padic.valuation_mul (commonRoot_dyadic_power_ne_zero h) hz0,
    Padic.valuation_pow, hv2, mul_one, hh]
  simp

/-- Every pair of dyadic coordinates has one common nonnegative dyadic
scaling for which all three homogeneous coordinates are integral and at
least one is a unit. Zero coordinates are allowed. -/
theorem commonRoot_dyadic_primitive_scale (x y : ℚ_[2]) :
    ∃ h : ℕ, let N := (2 : ℚ_[2]) ^ h
      N ≠ 0 ∧ ‖N‖ ≤ 1 ∧ ‖N * x‖ ≤ 1 ∧ ‖N * y‖ ≤ 1 ∧
      (‖N‖ = 1 ∨ ‖N * x‖ = 1 ∨ ‖N * y‖ = 1) := by
  by_cases hx : ‖x‖ ≤ 1
  · by_cases hy : ‖y‖ ≤ 1
    · refine ⟨0, ?_⟩
      simp only [pow_zero, ne_eq, one_ne_zero, not_false_eq_true, norm_one,
        one_mul, le_refl, true_or, and_true, true_and]
      exact ⟨hx, hy⟩
    · obtain ⟨h, hh⟩ := commonRoot_dyadic_scale_to_unit y (lt_of_not_ge hy)
      refine ⟨h, commonRoot_dyadic_power_ne_zero h,
        commonRoot_dyadic_power_norm_le_one h, ?_, hh.le, Or.inr (Or.inr hh)⟩
      rw [norm_mul]
      calc
        ‖(2 : ℚ_[2]) ^ h‖ * ‖x‖ ≤ ‖(2 : ℚ_[2]) ^ h‖ * 1 :=
          mul_le_mul_of_nonneg_left hx (norm_nonneg _)
        _ ≤ 1 := by simpa using commonRoot_dyadic_power_norm_le_one h
  · by_cases hxy : ‖x‖ ≤ ‖y‖
    · have hy : 1 < ‖y‖ := lt_of_lt_of_le (lt_of_not_ge hx) hxy
      obtain ⟨h, hh⟩ := commonRoot_dyadic_scale_to_unit y hy
      refine ⟨h, commonRoot_dyadic_power_ne_zero h,
        commonRoot_dyadic_power_norm_le_one h, ?_, hh.le, Or.inr (Or.inr hh)⟩
      calc
        ‖(2 : ℚ_[2]) ^ h * x‖ ≤ ‖(2 : ℚ_[2]) ^ h * y‖ := by
          simp only [norm_mul]
          exact mul_le_mul_of_nonneg_left hxy (norm_nonneg _)
        _ = 1 := hh
    · obtain ⟨h, hh⟩ := commonRoot_dyadic_scale_to_unit x (lt_of_not_ge hx)
      refine ⟨h, commonRoot_dyadic_power_ne_zero h,
        commonRoot_dyadic_power_norm_le_one h, hh.le, ?_, Or.inr (Or.inl hh)⟩
      calc
        ‖(2 : ℚ_[2]) ^ h * y‖ ≤ ‖(2 : ℚ_[2]) ^ h * x‖ := by
          simp only [norm_mul]
          exact mul_le_mul_of_nonneg_left (le_of_not_ge hxy) (norm_nonneg _)
        _ = 1 := hh

#print axioms commonRoot_dyadic_power_ne_zero
#print axioms commonRoot_dyadic_power_norm
#print axioms commonRoot_dyadic_power_norm_le_one
#print axioms commonRoot_dyadic_scale_to_unit
#print axioms commonRoot_dyadic_primitive_scale

end FourCorner
