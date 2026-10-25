import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

namespace FourCorner

private theorem nine_rat_sum_dominant {p : ℕ} [Fact p.Prime] {q r : ℚ}
    (hq : q ≠ 0) (hval : r = 0 ∨ padicValRat p q < padicValRat p r) :
    q + r ≠ 0 ∧ padicValRat p (q + r) = padicValRat p q := by
  rcases hval with rfl | hlt
  · simp [hq]
  by_cases hr : r = 0
  · simp [hr, hq]
  have hs : q + r ≠ 0 := by
    intro he
    have heq : q = -r := eq_neg_of_add_eq_zero_left he
    have hv := congrArg (padicValRat p) heq
    rw [padicValRat.neg] at hv
    omega
  exact ⟨hs, padicValRat.add_eq_of_lt hs hq hr hlt⟩

/-- Away from the constant coefficient, every nonzero rational abscissa on an integral
Weierstrass cubic has even valuation. This also includes points with zero ordinate. -/
theorem cubic_even_valuation_of_not_dvd {a b : ℤ} {x y : ℚ} {p : ℕ}
    (hp : p.Prime) (hx : x ≠ 0) (hb : ¬(p : ℤ) ∣ b)
    (h : y ^ 2 = x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x) :
    Even (padicValRat p x) := by
  let : Fact p.Prime := ⟨hp⟩
  have hb0 : b ≠ 0 := by intro he; exact hb (he ▸ dvd_zero _)
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
  have vb : padicValRat p (b : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hb, Nat.cast_zero]
  have va : 0 ≤ padicValRat p (a : ℚ) := by
    rw [padicValRat.of_int]; positivity
  have hf : y ^ 2 = x * (x ^ 2 + (a : ℚ) * x + (b : ℚ)) := by
    rw [h]; ring
  rcases lt_trichotomy (padicValRat p x) 0 with hneg | hzero | hpos
  · have hax : (a : ℚ) * x = 0 ∨
        padicValRat p (x ^ 2) < padicValRat p ((a : ℚ) * x) := by
      by_cases ha : a = 0
      · left; simp [ha]
      · right
        have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha
        rw [padicValRat.pow, padicValRat.mul haq hx]
        norm_num
        omega
    obtain ⟨hs0, hvs⟩ := nine_rat_sum_dominant (pow_ne_zero 2 hx) hax
    have hvs' : padicValRat p (x ^ 2 + (a : ℚ) * x) = 2 * padicValRat p x := by
      simpa using hvs
    obtain ⟨ht0, hvt⟩ := nine_rat_sum_dominant hs0 (Or.inr
      (show padicValRat p (x ^ 2 + (a : ℚ) * x) < padicValRat p (b : ℚ) by
        rw [hvs', vb]; omega))
    have hv := congrArg (padicValRat p) hf
    rw [padicValRat.pow, padicValRat.mul hx ht0, hvt, hvs'] at hv
    norm_num at hv
    refine ⟨padicValRat p y - padicValRat p x, ?_⟩
    omega
  · rw [hzero]; exact ⟨0, by ring⟩
  · have hax : (a : ℚ) * x = 0 ∨
        padicValRat p (b : ℚ) < padicValRat p ((a : ℚ) * x) := by
      by_cases ha : a = 0
      · left; simp [ha]
      · right
        have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha
        rw [padicValRat.mul haq hx, vb]
        omega
    obtain ⟨hs0, hvs⟩ := nine_rat_sum_dominant hbq hax
    have hvs' : padicValRat p ((b : ℚ) + (a : ℚ) * x) = 0 := hvs.trans vb
    obtain ⟨ht0, hvt⟩ := nine_rat_sum_dominant hs0 (Or.inr
      (show padicValRat p ((b : ℚ) + (a : ℚ) * x) < padicValRat p (x ^ 2) by
        rw [hvs', padicValRat.pow]; norm_num; omega))
    have hr : x ^ 2 + (a : ℚ) * x + (b : ℚ) = (b : ℚ) + (a : ℚ) * x + x ^ 2 := by ring
    rw [hr] at hf
    have hv := congrArg (padicValRat p) hf
    rw [padicValRat.pow, padicValRat.mul hx ht0, hvt, hvs'] at hv
    norm_num at hv
    refine ⟨padicValRat p y, ?_⟩
    omega

/-- Odd valuation of the abscissa of an integral Weierstrass cubic can occur only
at a prime dividing the linear coefficient. No nonzero-ordinate hypothesis is needed. -/
theorem cubic_odd_valuation_support {a b : ℤ} {x y : ℚ} {p : ℕ}
    (hp : p.Prime) (hx : x ≠ 0) (_hb : b ≠ 0)
    (h : y ^ 2 = x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x)
    (hv : Odd (padicValRat p x)) : (p : ℤ) ∣ b := by
  by_contra hb
  have he := cubic_even_valuation_of_not_dvd hp hx hb h
  exact (Int.not_even_iff_odd.mpr hv) he

end FourCorner

#print axioms FourCorner.cubic_odd_valuation_support
#print axioms FourCorner.cubic_even_valuation_of_not_dvd
