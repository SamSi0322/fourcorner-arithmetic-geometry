import FourCorner.CommonRootPadicResidue
import FourCorner.ThetaLocalHensel
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

set_option autoImplicit false
namespace FourCorner

variable {p : ℕ} [Fact p.Prime]

/-- The rational return expression, evaluated in the completed field. -/
noncomputable def csOddReturn (n a c : ℚ_[p]) : ℚ_[p] := (a + c) / (2 * (c + n))

/-- The supplement to quadratic reciprocity obstructs `2` in the actual field. -/
theorem csOdd_not_isSquare_two (hp : p % 8 = 5) : ¬ IsSquare (2 : ℚ_[p]) := by
  intro hs
  have hres := padicInt_isSquare_toZMod_of_isSquare_coe (2 : ℤ_[p]) hs
  have hsq : IsSquare (2 : ZMod p) := by simpa only [map_ofNat] using hres
  have h := (ZMod.exists_sq_eq_two_iff (show p ≠ 2 by omega)).mp hsq
  omega

/-- At the same primes, `-1` is a square in the actual completed field. -/
theorem csOdd_isSquare_neg_one (hp : p % 8 = 5) : IsSquare (-1 : ℚ_[p]) := by
  apply (padicInt_isSquare_coe_iff_residue_unit (show p ≠ 2 by omega) (-1 : ℤ_[p])
    (by simp)).mpr
  simpa using (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega)

/-- A square root of minus one is a nonsquare at primes congruent to five mod eight. -/
theorem csOdd_i_nonsquare (hp : p % 8 = 5) {i : ZMod p}
    (hi : i ^ 2 = -1) : ¬ IsSquare i := by
  rintro ⟨r, hr⟩
  have hr4 : r ^ 4 = -1 := by
    calc
      r ^ 4 = (r * r) ^ 2 := by ring
      _ = -1 := by rw [← hr, hi]
  have hr0 : r ≠ 0 := by
    intro hz
    rw [hz] at hr4
    simp at hr4
  have hr8 : r ^ 8 = 1 := by
    calc
      r ^ 8 = (r ^ 4) ^ 2 := by ring
      _ = 1 := by rw [hr4]; norm_num
  have hfermat := ZMod.pow_card_sub_one_eq_one hr0
  have he : p - 1 = 8 * (p / 8) + 4 := by omega
  rw [he, pow_add, pow_mul, hr8, one_pow, one_mul, hr4] at hfermat
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hns : ¬ IsSquare (2 : ZMod p) := by
      rw [ZMod.exists_sq_eq_two_iff (show p ≠ 2 by omega)]
      omega
    apply hns
    rw [hz]
    exact IsSquare.zero
  apply h2
  linear_combination -hfermat

/-- Multiplication by the square unit `n` preserves the cyclic odd-label obstruction. -/
theorem csOdd_ni_nonsquare (hp : p % 8 = 5) {n i : ZMod p}
    (hn : n ≠ 0) (hns : IsSquare n) (hi : i ^ 2 = -1) : ¬ IsSquare (n * i) := by
  intro hs
  have h := hs.div hns
  have he : n * i / n = i := by field_simp
  rw [he] at h
  exact csOdd_i_nonsquare hp hi h

/-- An actual integral point whose abscissa reduces to the odd cyclic label
cannot have square first Kummer coordinate. -/
theorem csOdd_abscissa_odd_label_nonsquare (hp : p % 8 = 5)
    (x : ℤ_[p]) {n i : ZMod p} (hn : n ≠ 0) (hns : IsSquare n)
    (hi : i ^ 2 = -1) (hx : PadicInt.toZMod x = n * i) :
    ¬ IsSquare (x : ℚ_[p]) := by
  apply padicInt_not_isSquare_coe_of_residue x
  rw [hx]
  exact csOdd_ni_nonsquare hp hn hns hi

/-- Any perturbation smaller than a nonzero square retains its square class. -/
theorem csOdd_isSquare_add_of_small {x t : ℚ_[p]} (hp : p ≠ 2)
    (hx : IsSquare x) (hsmall : ‖t‖ < ‖x‖) : IsSquare (x + t) := by
  have hx0 : x ≠ 0 := by intro hz; simp [hz] at hsmall; exact (not_lt_of_ge (norm_nonneg t)) hsmall
  have ht : ‖t / x‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hx0)]
    exact hsmall
  have hs := hx.mul (padic_odd_isSquare_one_add hp (t / x) ht)
  have he : x + t = x * (1 + t / x) := by field_simp
  rw [he]
  exact hs

/-- Near infinity the cubic itself forces its abscissa to be a square.
The open norm inequality covers every negative valuation, with no bound on depth. -/
theorem csOdd_isSquare_x_near_infinity (hp : p ≠ 2) {n x y : ℚ_[p]}
    (hn : ‖n‖ = 1) (hx : 1 < ‖x‖) (hcurve : y ^ 2 = x * (x - n) * (x + n)) :
    IsSquare x := by
  have hx0 : x ≠ 0 := by intro hz; norm_num [hz] at hx
  have hsmall : ‖-((n / x) ^ 2)‖ < 1 := by
    rw [norm_neg, norm_pow, norm_div, hn]
    have hi : 0 ≤ 1 / ‖x‖ := by positivity
    have hi1 : 1 / ‖x‖ < 1 := (div_lt_one (by linarith)).mpr hx
    nlinarith
  have hcor := padic_odd_isSquare_one_add hp (-((n / x) ^ 2)) hsmall
  have heq : x * (1 + -((n / x) ^ 2)) = (y / x) ^ 2 := by
    field_simp
    linear_combination -hcurve
  have hcor0 : 1 + -((n / x) ^ 2) ≠ 0 := by
    intro hz
    have he : -((n / x) ^ 2) = -1 := by linear_combination hz
    rw [he] at hsmall
    norm_num at hsmall
  have h := (IsSquare.sq (y / x)).div hcor
  rw [← heq, mul_div_cancel_right₀ _ hcor0] at h
  exact h

/-- Near `T₀` the same equation gives square class `-1`; when `-1` is a square,
so is the abscissa. This includes the exact point `T₀`. -/
theorem csOdd_isSquare_x_near_zero (hp : p ≠ 2) {n x y : ℚ_[p]}
    (hn : ‖n‖ = 1) (hx : ‖x‖ < 1) (hm : IsSquare (-1 : ℚ_[p]))
    (hcurve : y ^ 2 = x * (x - n) * (x + n)) : IsSquare x := by
  have hn0 : n ≠ 0 := by intro hz; simp [hz] at hn
  have hsmall : ‖-((x / n) ^ 2)‖ < 1 := by
    rw [norm_neg, norm_pow, norm_div, hn, div_one]
    nlinarith [norm_nonneg x]
  have hcor := padic_odd_isSquare_one_add hp (-((x / n) ^ 2)) hsmall
  have heq : x * (1 + -((x / n) ^ 2)) = -1 * (y / n) ^ 2 := by
    field_simp
    linear_combination hcurve
  have hcor0 : 1 + -((x / n) ^ 2) ≠ 0 := by
    intro hz
    have he : -((x / n) ^ 2) = -1 := by linear_combination hz
    rw [he] at hsmall
    norm_num at hsmall
  have h := (hm.mul (IsSquare.sq (y / n))).div hcor
  rw [← heq, mul_div_cancel_right₀ _ hcor0] at h
  exact h

private theorem csOdd_add_ne_zero_of_norm_lt {x y : ℚ_[p]}
    (h : ‖y‖ < ‖x‖) : x + y ≠ 0 := by
  intro hz
  have he : x = -y := eq_neg_of_add_eq_zero_left hz
  rw [he, norm_neg] at h
  exact lt_irrefl _ h

private theorem csOdd_not_square_of_double {x : ℚ_[p]} (hx : x ≠ 0)
    (hdouble : IsSquare (2 * x)) (htwo : ¬ IsSquare (2 : ℚ_[p])) : ¬ IsSquare x := by
  intro hs
  have h := hdouble.div hs
  rw [mul_div_cancel_right₀ _ hx] at h
  exact htwo h

/-- For opposite reductions `O,T₀`, the return has the nonsquare class `2`.
Only the actual cubic, norm neighborhoods, and the local square class of `n` enter. -/
theorem csOdd_not_isSquare_return_infinity_zero (hp : p % 8 = 5)
    {n a b c : ℚ_[p]} (hn : ‖n‖ = 1) (hns : IsSquare n)
    (ha : 1 < ‖a‖) (hc : ‖c‖ < 1)
    (hcurve : b ^ 2 = a * (a - n) * (a + n)) :
    ¬ IsSquare (csOddReturn n a c) := by
  have hodd : p ≠ 2 := by omega
  have hac := csOdd_isSquare_add_of_small hodd
    (csOdd_isSquare_x_near_infinity hodd hn ha hcurve) (lt_trans hc ha)
  have hcn : IsSquare (c + n) := by
    simpa [add_comm] using csOdd_isSquare_add_of_small hodd hns (by simpa [hn] using hc)
  have hac0 := csOdd_add_ne_zero_of_norm_lt (lt_trans hc ha)
  have hcn0 : c + n ≠ 0 := by
    simpa [add_comm] using csOdd_add_ne_zero_of_norm_lt (show ‖c‖ < ‖n‖ by simpa [hn] using hc)
  have hf0 : csOddReturn n a c ≠ 0 := div_ne_zero hac0 (mul_ne_zero (by norm_num) hcn0)
  apply csOdd_not_square_of_double hf0 _ (csOdd_not_isSquare_two hp)
  have h := hac.div hcn
  have he : 2 * csOddReturn n a c = (a + c) / (c + n) := by
    dsimp [csOddReturn]
    field_simp
  rw [he]
  exact h

/-- The reversed order `T₀,O` has the same obstruction, at every depth. -/
theorem csOdd_not_isSquare_return_zero_infinity (hp : p % 8 = 5)
    {n a c e : ℚ_[p]} (hn : ‖n‖ = 1)
    (ha : ‖a‖ < 1) (hc : 1 < ‖c‖)
    (hcurve : e ^ 2 = c * (c - n) * (c + n)) :
    ¬ IsSquare (csOddReturn n a c) := by
  have hodd : p ≠ 2 := by omega
  have hcs := csOdd_isSquare_x_near_infinity hodd hn hc hcurve
  have hac : IsSquare (a + c) := by
    simpa [add_comm] using csOdd_isSquare_add_of_small hodd hcs (lt_trans ha hc)
  have hcn := csOdd_isSquare_add_of_small hodd hcs (show ‖n‖ < ‖c‖ by simpa [hn] using hc)
  have hac0 : a + c ≠ 0 := by
    simpa [add_comm] using csOdd_add_ne_zero_of_norm_lt (lt_trans ha hc)
  have hcn0 := csOdd_add_ne_zero_of_norm_lt (show ‖n‖ < ‖c‖ by simpa [hn] using hc)
  have hf0 : csOddReturn n a c ≠ 0 := div_ne_zero hac0 (mul_ne_zero (by norm_num) hcn0)
  apply csOdd_not_square_of_double hf0 _ (csOdd_not_isSquare_two hp)
  have h := hac.div hcn
  have he : 2 * csOddReturn n a c = (a + c) / (c + n) := by
    dsimp [csOddReturn]
    field_simp
  rw [he]
  exact h

end FourCorner

#print axioms FourCorner.csOdd_not_isSquare_return_infinity_zero
#print axioms FourCorner.csOdd_not_isSquare_return_zero_infinity
