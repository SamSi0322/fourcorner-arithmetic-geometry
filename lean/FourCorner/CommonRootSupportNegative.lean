import FourCorner.CommonRootSource
import FourCorner.CommonRootPadicVal

namespace FourCorner.CommonRootSource

variable {p : ℕ} [Fact p.Prime] {t : ℚ_[p]}

theorem support_s_val_of_t_val_neg (S : CommonRootSource ℚ_[p] t)
    (ht : t.valuation < 0) : (t - 1).valuation = t.valuation := by
  have h := commonRoot_val_sub_of_ne S.t_ne_zero (one_ne_zero : (1 : ℚ_[p]) ≠ 0)
    (show t.valuation ≠ (1 : ℚ_[p]).valuation by simpa using ne_of_lt ht)
  simpa only [Padic.valuation_one, min_eq_left ht.le] using h

theorem support_T_val_of_t_val_neg (S : CommonRootSource ℚ_[p] t)
    (ht : t.valuation < 0) : (t + 1).valuation = t.valuation := by
  have h := commonRoot_val_add_of_ne S.t_ne_zero (one_ne_zero : (1 : ℚ_[p]) ≠ 0)
    (show t.valuation ≠ (1 : ℚ_[p]).valuation by simpa using ne_of_lt ht)
  simpa only [Padic.valuation_one, min_eq_left ht.le] using h

theorem support_ell_even_of_val_lt_t_val (S : CommonRootSource ℚ_[p] t)
    (ht : t.valuation < 0) (hlt : S.ell.valuation < t.valuation) :
    Even S.ell.valuation := by
  have hT := S.support_T_val_of_t_val_neg ht
  have hv := commonRoot_val_add_of_ne S.ell_ne_zero S.T_ne_zero
    (show S.ell.valuation ≠ (t+1).valuation by rw [hT]; exact ne_of_lt hlt)
  rw [hT, min_eq_left hlt.le, ← S.sqP, Padic.valuation_pow] at hv
  exact ⟨S.P.valuation, by omega⟩

theorem support_ell_even_of_t_val_lt_val (S : CommonRootSource ℚ_[p] t)
    (ht : t.valuation < 0) (hlt : t.valuation < S.ell.valuation) :
    Even S.ell.valuation := by
  have hs := S.support_s_val_of_t_val_neg ht
  have hT := S.support_T_val_of_t_val_neg ht
  have hvP := commonRoot_val_add_of_ne S.ell_ne_zero S.T_ne_zero
    (show S.ell.valuation ≠ (t+1).valuation by rw [hT]; exact ne_of_gt hlt)
  rw [hT, min_eq_right hlt.le, ← S.sqP, Padic.valuation_pow] at hvP
  have hvDiff := commonRoot_val_sub_of_ne S.T_ne_zero S.ell_ne_zero
    (show (t+1).valuation ≠ S.ell.valuation by rw [hT]; exact ne_of_lt hlt)
  rw [hT, min_eq_left hlt.le] at hvDiff
  have hvM := congrArg Padic.valuation S.sqM
  rw [Padic.valuation_pow, commonRoot_val_div
      (mul_ne_zero S.s_ne_zero S.T_sub_ell_ne_zero) S.ell_ne_zero,
    Padic.valuation_mul S.s_ne_zero S.T_sub_ell_ne_zero, hs, hvDiff] at hvM
  exact ⟨2 * S.P.valuation - S.M.valuation, by omega⟩

theorem support_ell_even_of_val_eq_t_val (S : CommonRootSource ℚ_[p] t)
    (hp : p ≠ 2) (ht : t.valuation < 0) (hn : S.ell.valuation = t.valuation) :
    Even S.ell.valuation := by
  have hT := S.support_T_val_of_t_val_neg ht
  have hs := S.support_s_val_of_t_val_neg ht
  have hP := Padic.le_valuation_add S.ell_add_T_ne_zero
  rw [hn, hT, min_self, ← S.sqP, Padic.valuation_pow] at hP
  have hC := Padic.le_valuation_add
    (show S.ell + -(t - 1) ≠ 0 by simpa only [← sub_eq_add_neg] using S.ell_sub_s_ne_zero)
  rw [commonRoot_val_neg, hn, hs, min_self, ← sub_eq_add_neg, ← S.sqC,
    Padic.valuation_pow] at hC
  have htwo : (2 : ℚ_[p]) ≠ 0 := by norm_num
  have hdiff : S.P ^ 2 + -(S.C ^ 2) = 2 * t := by rw [S.sqP, S.sqC]; ring
  have hPC := Padic.le_valuation_add
    (show S.P ^ 2 + -(S.C ^ 2) ≠ 0 by rw [hdiff]; exact mul_ne_zero htwo S.t_ne_zero)
  rw [commonRoot_val_neg, hdiff, Padic.valuation_mul htwo S.t_ne_zero,
    commonRoot_val_two hp, zero_add, Padic.valuation_pow, Padic.valuation_pow] at hPC
  rcases le_total (2 * S.P.valuation) (2 * S.C.valuation) with h | h
  · refine ⟨S.P.valuation, ?_⟩
    simp only [Nat.cast_ofNat, min_eq_left h] at hPC
    omega
  · refine ⟨S.C.valuation, ?_⟩
    simp only [Nat.cast_ofNat, min_eq_right h] at hPC
    omega

/-- At an odd prime, a common four-root point with negative parameter valuation
has even valuation of the common support coordinate. -/
theorem support_ell_even_of_t_val_neg (S : CommonRootSource ℚ_[p] t)
    (hp : p ≠ 2) (ht : t.valuation < 0) : Even S.ell.valuation := by
  rcases lt_trichotomy S.ell.valuation t.valuation with hlt | heq | hgt
  · exact S.support_ell_even_of_val_lt_t_val ht hlt
  · exact S.support_ell_even_of_val_eq_t_val hp ht heq
  · exact S.support_ell_even_of_t_val_lt_val ht hgt

end FourCorner.CommonRootSource
