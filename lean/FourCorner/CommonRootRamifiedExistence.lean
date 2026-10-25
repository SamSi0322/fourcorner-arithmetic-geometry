import FourCorner.CommonRootSource
import FourCorner.CommonRootPadicVal
import FourCorner.ThetaLocalHensel

set_option autoImplicit false

namespace FourCorner

/-- A small perturbation of a square unit remains a nonzero square, by the
actual `p`-adic Hensel theorem. -/
theorem commonRoot_square_unit_add_small {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (a b : ℚ_[p]) (ha : ‖a‖ = 1) (hasq : IsSquare a) (hb : ‖b‖ < 1) :
    IsSquare (a + b) ∧ a + b ≠ 0 := by
  have ha0 : a ≠ 0 := by intro hz; simp [hz] at ha
  have hsmall : ‖b / a‖ < 1 := by simpa only [norm_div, ha, div_one] using hb
  have hsq := hasq.mul (padic_odd_isSquare_one_add hp (b / a) hsmall)
  have hprod : a * (1 + b / a) = a + b := by field_simp
  rw [hprod] at hsq
  refine ⟨hsq, ?_⟩
  have hn : ‖a + b‖ = ‖a‖ := Padic.norm_eq_of_norm_sub_lt_right (by
    simpa only [add_sub_cancel_left, ha] using hb)
  intro hz
  rw [hz, norm_zero, ha] at hn
  norm_num at hn

/-- When `t` is close to one and two is a square, the constant choice `ell = 2`
gives an actual four-root source. The two remaining roots are Hensel lifts;
the other roots are explicitly `(t-1)/sqrt(2)` and `(t+1)/sqrt(2)`. -/
theorem commonRoot_ramified_exists_square_ell_of_norm {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (t : ℚ_[p]) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (htm1 : t ≠ -1) (ht : ‖t - 1‖ < 1) (h2 : IsSquare (2 : ℚ_[p])) :
    ∃ S : CommonRootSource ℚ_[p] t, S.ell = 2 ∧ IsSquare S.ell := by
  have htwo : ‖(2 : ℚ_[p])‖ = 1 := by
    apply Padic.norm_natCast_eq_one_iff.mpr
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by
      intro h
      exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h))
  have hfour : ‖(4 : ℚ_[p])‖ = 1 := by
    calc
      ‖(4 : ℚ_[p])‖ = ‖(2 : ℚ_[p]) ^ 2‖ := by norm_num
      _ = 1 := by rw [norm_pow, htwo]; norm_num
  have hfour_sq : IsSquare (4 : ℚ_[p]) := ⟨2, by norm_num⟩
  obtain ⟨hPsq, hPn⟩ := commonRoot_square_unit_add_small hp 4 (t - 1) hfour hfour_sq ht
  obtain ⟨hCsq, hCn⟩ := commonRoot_square_unit_add_small hp 2 (-(t - 1)) htwo h2
    (by simpa only [norm_neg] using ht)
  obtain ⟨a, ha⟩ := h2.exists_sq
  obtain ⟨P, hP⟩ := hPsq.exists_sq
  obtain ⟨C, hC⟩ := hCsq.exists_sq
  have ha0 : a ≠ 0 := by intro hz; rw [hz] at ha; norm_num at ha
  have hP0 : P ≠ 0 := by intro hz; apply hPn; rw [hP, hz]; norm_num
  have hC0 : C ≠ 0 := by intro hz; apply hCn; rw [hC, hz]; norm_num
  have hs0 : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have hT0 : t + 1 ≠ 0 := by
    intro hz
    exact htm1 (eq_neg_of_add_eq_zero_left hz)
  let S : CommonRootSource ℚ_[p] t := {
    ell := 2
    P := P
    C := C
    M := (t - 1) / a
    B := (t + 1) / a
    t_ne_zero := ht0
    t_ne_one := ht1
    t_ne_neg_one := htm1
    ell_ne_zero := by norm_num
    P_ne_zero := hP0
    C_ne_zero := hC0
    M_ne_zero := div_ne_zero hs0 ha0
    B_ne_zero := div_ne_zero hT0 ha0
    sqP := by rw [← hP]; ring
    sqC := by rw [← hC]; ring
    sqM := by rw [div_pow, ← ha]; ring
    sqB := by rw [div_pow, ← ha]; ring
  }
  exact ⟨S, rfl, h2⟩

/-- Positive ramification depth at `t-1` gives the same genuine local source.
The stronger odd-depth assumption is unnecessary for this existence direction. -/
theorem commonRoot_ramified_exists_square_ell {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (t : ℚ_[p]) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (htm1 : t ≠ -1) (ht : 0 < (t - 1).valuation) (h2 : IsSquare (2 : ℚ_[p])) :
    ∃ S : CommonRootSource ℚ_[p] t, S.ell = 2 ∧ IsSquare S.ell := by
  apply commonRoot_ramified_exists_square_ell_of_norm hp t ht0 ht1 htm1
  · exact (commonRoot_norm_lt_one_iff (sub_ne_zero.mpr ht1)).mpr ht
  · exact h2

end FourCorner

#print axioms FourCorner.commonRoot_ramified_exists_square_ell
