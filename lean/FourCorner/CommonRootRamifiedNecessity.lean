import FourCorner.ThetaLocalHensel
import FourCorner.CommonRootSource
import FourCorner.CommonRootPadicVal

namespace FourCorner

/-- At an odd prime a sufficiently small relative perturbation has square ratio. -/
theorem padic_odd_isSquare_ratio_of_norm_sub_lt {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {x y : ℚ_[p]} (hx : x ≠ 0) (hxy : ‖y - x‖ < ‖x‖) :
    IsSquare (y / x) := by
  have ht : ‖(y - x) / x‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hx)]
    exact hxy
  have hs := padic_odd_isSquare_one_add hp ((y - x) / x) ht
  have he : 1 + (y - x) / x = y / x := by field_simp; ring
  rwa [he] at hs

/-- Squarehood is unchanged by a sufficiently small relative perturbation. -/
theorem padic_odd_isSquare_iff_of_norm_sub_lt {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {x y : ℚ_[p]} (hx : x ≠ 0) (hxy : ‖y - x‖ < ‖x‖) :
    IsSquare x ↔ IsSquare y := by
  have hs := padic_odd_isSquare_ratio_of_norm_sub_lt hp hx hxy
  have hy : y ≠ 0 := by
    intro he
    rw [he, zero_sub, norm_neg] at hxy
    exact lt_irrefl _ hxy
  constructor
  · intro h
    have he : x * (y / x) = y := by field_simp
    simpa only [he] using h.mul hs
  · intro h
    have he : y / (y / x) = x := by field_simp
    simpa only [he] using h.div hs

/-- Transport a square along a small relative perturbation at an odd prime. -/
theorem padic_odd_isSquare_of_norm_sub_lt {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {x y : ℚ_[p]} (hx : x ≠ 0) (hs : IsSquare x)
    (hxy : ‖y - x‖ < ‖x‖) : IsSquare y :=
  (padic_odd_isSquare_iff_of_norm_sub_lt hp hx hxy).mp hs

end FourCorner

namespace FourCorner.CommonRootSource

/-- An odd positive valuation of `t-1` leaves exactly two possible valuations
for the actual source coordinate. -/
theorem ramified_ell_valuation_cases {p : ℕ} [Fact p.Prime] {t : ℚ_[p]}
    (S : CommonRootSource ℚ_[p] t) (hp : p ≠ 2)
    (hpos : 0 < (t - 1).valuation) (hodd : Odd (t - 1).valuation) :
    S.ell.valuation = 0 ∨ S.ell.valuation = (t - 1).valuation := by
  have hT := commonRoot_val_add_one_of_sub_one_pos hp hpos
  have hM : 2 * S.M.valuation =
      (t - 1).valuation + (t + 1 - S.ell).valuation - S.ell.valuation := by
    have h := congrArg Padic.valuation S.sqM
    rw [Padic.valuation_pow,
      commonRoot_val_div (mul_ne_zero S.s_ne_zero S.T_sub_ell_ne_zero) S.ell_ne_zero,
      Padic.valuation_mul S.s_ne_zero S.T_sub_ell_ne_zero] at h
    exact h
  have hC : 2 * S.C.valuation = (S.ell - (t - 1)).valuation := by
    simpa only [Padic.valuation_pow, Nat.cast_ofNat] using congrArg Padic.valuation S.sqC
  obtain ⟨k, hk⟩ := hodd
  rcases lt_trichotomy S.ell.valuation 0 with hn | hn | hn
  · have hd := commonRoot_val_sub_of_ne S.T_ne_zero S.ell_ne_zero
      (show (t + 1).valuation ≠ S.ell.valuation by omega)
    rw [hT, min_eq_right (le_of_lt hn)] at hd
    rw [hd] at hM
    omega
  · exact Or.inl hn
  · have hd := commonRoot_val_sub_of_ne S.T_ne_zero S.ell_ne_zero
      (show (t + 1).valuation ≠ S.ell.valuation by omega)
    rw [hT, min_eq_left (le_of_lt hn)] at hd
    rw [hd] at hM
    rcases lt_trichotomy S.ell.valuation (t - 1).valuation with hne | hne | hne
    · have hc := commonRoot_val_sub_of_ne S.ell_ne_zero S.s_ne_zero (ne_of_lt hne)
      rw [min_eq_left (le_of_lt hne)] at hc
      rw [hc] at hC
      omega
    · exact Or.inr hne
    · have hc := commonRoot_val_sub_of_ne S.ell_ne_zero S.s_ne_zero (ne_of_gt hne)
      rw [min_eq_right (le_of_lt hne)] at hc
      rw [hc] at hC
      omega

end FourCorner.CommonRootSource

#print axioms FourCorner.CommonRootSource.ramified_ell_valuation_cases

namespace FourCorner

/-- In the unit-coordinate branch, the source forces both two and the coordinate to be squares. -/
theorem commonRoot_ramified_zero_squares {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {t : ℚ_[p]} (S : CommonRootSource ℚ_[p] t)
    (hpos : 0 < (t - 1).valuation) (hodd : Odd (t - 1).valuation)
    (hn : S.ell.valuation = 0) : IsSquare (2 : ℚ_[p]) ∧ IsSquare S.ell := by
  have hT := commonRoot_val_add_one_of_sub_one_pos hp hpos
  have hvM := congrArg Padic.valuation S.sqM
  rw [Padic.valuation_pow,
    commonRoot_val_div (mul_ne_zero S.s_ne_zero S.T_sub_ell_ne_zero) S.ell_ne_zero,
    Padic.valuation_mul S.s_ne_zero S.T_sub_ell_ne_zero, hn, sub_zero] at hvM
  have hdnonneg : 0 ≤ (t + 1 - S.ell).valuation := by
    have hh := Padic.le_valuation_add
      (show (t + 1) + -S.ell ≠ 0 by simpa only [sub_eq_add_neg] using S.T_sub_ell_ne_zero)
    simpa only [← sub_eq_add_neg, commonRoot_val_neg, hn, hT, min_self] using hh
  have hdpos : 0 < (t + 1 - S.ell).valuation := by
    obtain ⟨k, hk⟩ := hodd
    norm_num only [Nat.cast_ofNat] at hvM
    omega
  have hs : ‖t - 1‖ < 1 := (commonRoot_norm_lt_one_iff S.s_ne_zero).mpr hpos
  have hd : ‖t + 1 - S.ell‖ < 1 :=
    (commonRoot_norm_lt_one_iff S.T_sub_ell_ne_zero).mpr hdpos
  have hellnorm : ‖S.ell‖ = 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation S.ell_ne_zero, hn, neg_zero, zpow_zero]
  have hnearC : ‖(S.ell - (t - 1)) - S.ell‖ < ‖S.ell‖ := by
    rw [show (S.ell - (t - 1)) - S.ell = -(t - 1) by ring, norm_neg, hellnorm]
    exact hs
  have hellsquare : IsSquare S.ell :=
    (padic_odd_isSquare_iff_of_norm_sub_lt hp S.ell_ne_zero hnearC).mpr
      (by rw [← S.sqC]; exact IsSquare.sq S.C)
  have hnearTwo : ‖S.ell - 2‖ < 1 := by
    rw [show S.ell - 2 = -(t + 1 - S.ell) + (t - 1) by ring]
    exact lt_of_le_of_lt (Padic.nonarchimedean _ _)
      (max_lt (by simpa only [norm_neg] using hd) hs)
  have htwo : (2 : ℚ_[p]) ≠ 0 := by norm_num
  have htwonorm : ‖(2 : ℚ_[p])‖ = 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation htwo, commonRoot_val_two hp, neg_zero, zpow_zero]
  refine ⟨?_, hellsquare⟩
  exact (padic_odd_isSquare_iff_of_norm_sub_lt hp htwo
    (by simpa only [htwonorm] using hnearTwo)).mpr hellsquare


/-- In the equal-positive-valuation branch, the opposite coordinate and two are squares. -/
theorem commonRoot_ramified_equal_positive_squares {p : ℕ} [Fact p.Prime]
    (hodd : p ≠ 2) {t : ℚ_[p]} (S : CommonRootSource ℚ_[p] t)
    (hpos : 0 < (t - 1).valuation) (hnpos : 0 < S.ell.valuation)
    (heq : S.ell.valuation = (t - 1).valuation) :
    IsSquare (2 : ℚ_[p]) ∧ IsSquare ((t^2 - 1) / S.ell) := by
  have hT : (t+1).valuation = 0 := commonRoot_val_add_one_of_sub_one_pos hodd hpos
  have hsnorm : ‖t-1‖ < 1 := (commonRoot_norm_lt_one_iff S.s_ne_zero).mpr hpos
  have hlnorm : ‖S.ell‖ < 1 := (commonRoot_norm_lt_one_iff S.ell_ne_zero).mpr hnpos
  have hn2 : ‖(2 : ℚ_[p])‖ = 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation (by norm_num : (2 : ℚ_[p]) ≠ 0),
      commonRoot_val_two hodd]
    simp
  have hPnear : ‖S.P^2 - (2 : ℚ_[p])‖ < 1 := by
    rw [S.sqP, show S.ell+(t+1)-2=S.ell+(t-1) by ring]
    exact lt_of_le_of_lt (Padic.nonarchimedean _ _) (max_lt hlnorm hsnorm)
  have htwo : IsSquare (2 : ℚ_[p]) := by
    apply (padic_odd_isSquare_iff_of_norm_sub_lt hodd
      (y := S.P^2) (by norm_num : (2 : ℚ_[p]) ≠ 0)
      (by simpa [hn2] using hPnear)).mpr
    exact ⟨S.P, by ring⟩
  have hdval : (t^2-1).valuation = (t-1).valuation := by
    rw [show t^2-1=(t-1)*(t+1) by ring,
      Padic.valuation_mul S.s_ne_zero S.T_ne_zero, hT, add_zero]
  have hqval : ((t^2-1)/S.ell).valuation = 0 := by
    rw [commonRoot_val_div S.d_ne_zero S.ell_ne_zero, hdval, heq, sub_self]
  have hqnorm : ‖(t^2-1)/S.ell‖ = 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation (div_ne_zero S.d_ne_zero S.ell_ne_zero), hqval]
    simp
  have hM : S.M^2 = (t^2-1)/S.ell-(t-1) := by
    rw [S.sqM]
    field_simp [S.ell_ne_zero]
    ring
  have hMnear : ‖S.M^2 - (t^2-1)/S.ell‖ < ‖(t^2-1)/S.ell‖ := by
    rw [hM, sub_sub_cancel_left, norm_neg, hqnorm]
    exact hsnorm
  exact ⟨htwo, (padic_odd_isSquare_iff_of_norm_sub_lt hodd
    (div_ne_zero S.d_ne_zero S.ell_ne_zero) hMnear).mpr ⟨S.M, by ring⟩⟩


end FourCorner

namespace FourCorner.CommonRootSource

/-- Necessity of the two common-root local square conditions at an odd prime
where the actual parameter is an odd-depth perturbation of one. -/
theorem ramified_local_necessity {p : ℕ} [Fact p.Prime] {t : ℚ_[p]}
    (S : CommonRootSource ℚ_[p] t) (hp : p ≠ 2)
    (hpos : 0 < (t - 1).valuation) (hodd : Odd (t - 1).valuation) :
    IsSquare (2 : ℚ_[p]) ∧
      (IsSquare S.ell ∨ IsSquare ((t^2 - 1) / S.ell)) := by
  rcases S.ramified_ell_valuation_cases hp hpos hodd with hn | hn
  · obtain ⟨h2, hell⟩ := commonRoot_ramified_zero_squares hp S hpos hodd hn
    exact ⟨h2, Or.inl hell⟩
  · obtain ⟨h2, hell⟩ := commonRoot_ramified_equal_positive_squares hp S hpos
      (by omega) hn
    exact ⟨h2, Or.inr hell⟩

end FourCorner.CommonRootSource

#print axioms FourCorner.CommonRootSource.ramified_local_necessity
