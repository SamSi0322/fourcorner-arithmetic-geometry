import FourCorner.CommonRootSource
import FourCorner.CommonRootPadicVal
import FourCorner.CommonRootSymmetries
import FourCorner.CommonRootSupportNegative

namespace FourCorner.CommonRootSource

/-- If `t+1` is a unit, odd valuation of the common coordinate forces it to
have exactly the positive valuation of `t-1`. -/
theorem support_val_s_eq_ell_of_T_unit {p : ℕ} [Fact p.Prime] {t : ℚ_[p]}
    (S : CommonRootSource ℚ_[p] t) (hT : (t + 1).valuation = 0)
    (hodd : Odd S.ell.valuation) :
    (t - 1).valuation = S.ell.valuation ∧ 0 < (t - 1).valuation := by
  have hP : 2 * S.P.valuation = (S.ell + (t + 1)).valuation := by
    simpa only [Padic.valuation_pow, Nat.cast_ofNat] using congrArg Padic.valuation S.sqP
  have hC : 2 * S.C.valuation = (S.ell - (t - 1)).valuation := by
    simpa only [Padic.valuation_pow, Nat.cast_ofNat] using congrArg Padic.valuation S.sqC
  have hM : 2 * S.M.valuation =
      (t - 1).valuation + (t + 1 - S.ell).valuation - S.ell.valuation := by
    have h := congrArg Padic.valuation S.sqM
    rw [Padic.valuation_pow,
      commonRoot_val_div (mul_ne_zero S.s_ne_zero S.T_sub_ell_ne_zero) S.ell_ne_zero,
      Padic.valuation_mul S.s_ne_zero S.T_sub_ell_ne_zero] at h
    exact h
  obtain ⟨k, hk⟩ := hodd
  have hn : 0 < S.ell.valuation := by
    by_contra hn
    have hnlt : S.ell.valuation < 0 := by omega
    have h := commonRoot_val_add_of_ne S.ell_ne_zero S.T_ne_zero
      (show S.ell.valuation ≠ (t + 1).valuation by omega)
    rw [hT, min_eq_left (le_of_lt hnlt)] at h
    rw [h] at hP
    omega
  have hTM := commonRoot_val_sub_of_ne S.T_ne_zero S.ell_ne_zero
    (show (t + 1).valuation ≠ S.ell.valuation by omega)
  rw [hT, min_eq_left (le_of_lt hn)] at hTM
  rw [hTM] at hM
  have heq : (t - 1).valuation = S.ell.valuation := by
    by_contra heq
    have h := commonRoot_val_sub_of_ne S.ell_ne_zero S.s_ne_zero (Ne.symm heq)
    rw [h] at hC
    omega
  exact ⟨heq, by omega⟩

/-- For an integral parameter, at least one of its two neighbors is a unit
at an odd prime. -/
theorem support_s_or_T_unit_of_t_val_nonneg {p : ℕ} [Fact p.Prime] {t : ℚ_[p]}
    (S : CommonRootSource ℚ_[p] t) (hp : p ≠ 2) (ht : 0 ≤ t.valuation) :
    (t - 1).valuation = 0 ∨ (t + 1).valuation = 0 := by
  have hs : 0 ≤ (t - 1).valuation := by
    have h := Padic.le_valuation_add (show t + -(1 : ℚ_[p]) ≠ 0 by
      simpa only [sub_eq_add_neg] using S.s_ne_zero)
    rw [commonRoot_val_neg, Padic.valuation_one, min_eq_right ht] at h
    simpa only [sub_eq_add_neg] using h
  have hT : 0 ≤ (t + 1).valuation := by
    have h := Padic.le_valuation_add S.T_ne_zero
    rwa [Padic.valuation_one, min_eq_right ht] at h
  have he : (t + 1) + -(t - 1) = (2 : ℚ_[p]) := by ring
  have htwo : (2 : ℚ_[p]) ≠ 0 := by exact_mod_cast (show (2 : ℚ) ≠ 0 by decide)
  have h := Padic.le_valuation_add (show (t + 1) + -(t - 1) ≠ 0 by rwa [he])
  rw [commonRoot_val_neg, he, commonRoot_val_two hp] at h
  omega

/-- The nonnegative-parameter-valuation case of common-coordinate support. -/
theorem support_val_d_pos_odd_of_ell_odd_of_nonneg {p : ℕ} [Fact p.Prime] {t : ℚ_[p]}
    (S : CommonRootSource ℚ_[p] t) (hp : p ≠ 2) (ht : 0 ≤ t.valuation)
    (hodd : Odd S.ell.valuation) :
    0 < (t ^ 2 - 1).valuation ∧ Odd (t ^ 2 - 1).valuation := by
  have hd : (t ^ 2 - 1).valuation = (t - 1).valuation + (t + 1).valuation := by
    rw [show t ^ 2 - 1 = (t - 1) * (t + 1) by ring,
      Padic.valuation_mul S.s_ne_zero S.T_ne_zero]
  rcases S.support_s_or_T_unit_of_t_val_nonneg hp ht with hs | hT
  · have hT' : ((-t) + 1).valuation = 0 := by
      rw [show -t + 1 = -(t - 1) by ring, commonRoot_val_neg, hs]
    have hodd' : Odd S.signChange.ell.valuation := hodd
    obtain ⟨he, hpos⟩ := S.signChange.support_val_s_eq_ell_of_T_unit hT' hodd'
    have hs' : ((-t) - 1).valuation = (t + 1).valuation := by
      rw [show -t - 1 = -(t + 1) by ring, commonRoot_val_neg]
    rw [hs'] at he hpos
    rw [hd, hs, zero_add]
    exact ⟨hpos, he ▸ hodd'⟩
  · obtain ⟨he, hpos⟩ := S.support_val_s_eq_ell_of_T_unit hT hodd
    rw [hd, hT, add_zero]
    exact ⟨hpos, he ▸ hodd⟩


/-- At every odd prime, odd valuation of the actual common coordinate can
occur only at a positive odd valuation of the parameter discriminant. -/
theorem support_val_d_pos_odd_of_ell_odd {p : ℕ} [Fact p.Prime] {t : ℚ_[p]}
    (S : CommonRootSource ℚ_[p] t) (hp : p ≠ 2)
    (hodd : Odd S.ell.valuation) :
    0 < (t ^ 2 - 1).valuation ∧ Odd (t ^ 2 - 1).valuation := by
  by_cases ht : t.valuation < 0
  · obtain ⟨a, ha⟩ := S.support_ell_even_of_t_val_neg hp ht
    obtain ⟨b, hb⟩ := hodd
    omega
  · exact S.support_val_d_pos_odd_of_ell_odd_of_nonneg hp (by omega) hodd

end FourCorner.CommonRootSource

#print axioms FourCorner.CommonRootSource.support_val_d_pos_odd_of_ell_odd
