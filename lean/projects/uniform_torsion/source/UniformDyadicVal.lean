import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-! Exact dyadic valuations of rational coordinates and the rational duplication
abscissa on `y² = x³ + a*x² + b²*x`. All zero cases are handled explicitly. -/

namespace FourCorner.UniformTorsion

/-- Distinct finite rational valuations prevent cancellation. -/
theorem dyadic_add_ne_zero_of_val_ne {q r : ℚ}
    (hval : padicValRat 2 q ≠ padicValRat 2 r) : q + r ≠ 0 := by
  intro h
  have hq : q = -r := eq_neg_of_add_eq_zero_left h
  apply hval
  rw [hq, padicValRat.neg]

/-- A uniquely least-valued nonzero summand determines a three-term sum. -/
theorem dyadic_unique_min_three {q r s : ℚ} (hq : q ≠ 0) (_hr : r ≠ 0)
    (_hs : s ≠ 0) (hqr : padicValRat 2 q < padicValRat 2 r)
    (hqs : padicValRat 2 q < padicValRat 2 s) :
    q + r + s ≠ 0 ∧ padicValRat 2 (q + r + s) = padicValRat 2 q := by
  by_cases hrs : r + s = 0
  · simpa [add_assoc, hrs] using hq
  · have hv : padicValRat 2 q < padicValRat 2 (r + s) :=
      lt_of_lt_of_le (lt_min hqr hqs) (padicValRat.min_le_padicValRat_add hrs)
    have hn := dyadic_add_ne_zero_of_val_ne (ne_of_lt hv)
    rw [add_assoc]
    exact ⟨hn, padicValRat.add_eq_of_lt hn hq hrs hv⟩

/-- Positive x-valuation: the linear term has uniquely least valuation. -/
theorem dyadic_curve_positive {a b x y : ℚ} (ha : 1 ≤ padicValRat 2 a)
    (hb : b ≠ 0) (hvb : padicValRat 2 b = 0) (hx : x ≠ 0)
    (heq : y ^ 2 = x ^ 3 + a * x ^ 2 + b ^ 2 * x)
    (hvx : 0 < padicValRat 2 x) :
    y ≠ 0 ∧ 2 * padicValRat 2 y = padicValRat 2 x := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have h3 : padicValRat 2 (x ^ 3) = 3 * padicValRat 2 x := by simp
  have h2 : padicValRat 2 (a * x ^ 2) = padicValRat 2 a + 2 * padicValRat 2 x := by
    rw [padicValRat.mul ha0 (pow_ne_zero _ hx)]; simp
  have h1 : padicValRat 2 (b ^ 2 * x) = padicValRat 2 x := by
    rw [padicValRat.mul (pow_ne_zero _ hb) hx]; simp [hvb]
  have hmin := dyadic_unique_min_three (mul_ne_zero (pow_ne_zero 2 hb) hx)
    (pow_ne_zero 3 hx) (mul_ne_zero ha0 (pow_ne_zero 2 hx))
    (show padicValRat 2 (b ^ 2 * x) < padicValRat 2 (x ^ 3) by omega)
    (show padicValRat 2 (b ^ 2 * x) < padicValRat 2 (a * x ^ 2) by omega)
  have heq' : y ^ 2 = b ^ 2 * x + x ^ 3 + a * x ^ 2 := by rw [heq]; ring
  have hy : y ≠ 0 := by intro h; apply hmin.1; rw [← heq', h]; norm_num
  refine ⟨hy, ?_⟩
  have hval := congrArg (padicValRat 2) heq'
  rw [hmin.2, h1, padicValRat.pow] at hval
  exact hval

/-- Negative x-valuation: the cubic term has uniquely least valuation. -/
theorem dyadic_curve_negative {a b x y : ℚ} (ha : 1 ≤ padicValRat 2 a)
    (hb : b ≠ 0) (hvb : padicValRat 2 b = 0) (hx : x ≠ 0)
    (heq : y ^ 2 = x ^ 3 + a * x ^ 2 + b ^ 2 * x)
    (hvx : padicValRat 2 x < 0) :
    y ≠ 0 ∧ 2 * padicValRat 2 y = 3 * padicValRat 2 x := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have h3 : padicValRat 2 (x ^ 3) = 3 * padicValRat 2 x := by simp
  have h2 : padicValRat 2 (a * x ^ 2) = padicValRat 2 a + 2 * padicValRat 2 x := by
    rw [padicValRat.mul ha0 (pow_ne_zero _ hx)]; simp
  have h1 : padicValRat 2 (b ^ 2 * x) = padicValRat 2 x := by
    rw [padicValRat.mul (pow_ne_zero _ hb) hx]; simp [hvb]
  have hmin := dyadic_unique_min_three (pow_ne_zero 3 hx)
    (mul_ne_zero ha0 (pow_ne_zero 2 hx)) (mul_ne_zero (pow_ne_zero 2 hb) hx)
    (show padicValRat 2 (x ^ 3) < padicValRat 2 (a * x ^ 2) by omega)
    (show padicValRat 2 (x ^ 3) < padicValRat 2 (b ^ 2 * x) by omega)
  have hy : y ≠ 0 := by intro h; apply hmin.1; rw [← heq, h]; norm_num
  refine ⟨hy, ?_⟩
  have hval := congrArg (padicValRat 2) heq
  rw [hmin.2, h3, padicValRat.pow] at hval
  exact hval

/-- The duplication numerator is a unit when x has positive valuation. -/
theorem dyadic_dup_numerator_positive {b x : ℚ} (hb : b ≠ 0)
    (hvb : padicValRat 2 b = 0) (hx : x ≠ 0) (hvx : 0 < padicValRat 2 x) :
    x ^ 2 - b ^ 2 ≠ 0 ∧ padicValRat 2 (x ^ 2 - b ^ 2) = 0 := by
  have hlt : padicValRat 2 (-(b ^ 2)) < padicValRat 2 (x ^ 2) := by
    simp only [padicValRat.neg, padicValRat.pow, hvb, mul_zero, Nat.cast_ofNat]
    omega
  have hn := dyadic_add_ne_zero_of_val_ne (ne_of_lt hlt)
  have hv := padicValRat.add_eq_of_lt hn (neg_ne_zero.mpr (pow_ne_zero 2 hb))
    (pow_ne_zero 2 hx) hlt
  have he : -(b ^ 2) + x ^ 2 = x ^ 2 - b ^ 2 := by ring
  rw [he] at hn hv
  exact ⟨hn, by simpa [hvb] using hv⟩

/-- For negative x-valuation the squared x term determines the numerator. -/
theorem dyadic_dup_numerator_negative {b x : ℚ} (hb : b ≠ 0)
    (hvb : padicValRat 2 b = 0) (hx : x ≠ 0) (hvx : padicValRat 2 x < 0) :
    x ^ 2 - b ^ 2 ≠ 0 ∧
      padicValRat 2 (x ^ 2 - b ^ 2) = 2 * padicValRat 2 x := by
  have hlt : padicValRat 2 (x ^ 2) < padicValRat 2 (-(b ^ 2)) := by
    simp only [padicValRat.neg, padicValRat.pow, hvb, mul_zero, Nat.cast_ofNat]
    omega
  have hn := dyadic_add_ne_zero_of_val_ne (ne_of_lt hlt)
  have hv := padicValRat.add_eq_of_lt hn (pow_ne_zero 2 hx)
    (neg_ne_zero.mpr (pow_ne_zero 2 hb)) hlt
  exact ⟨by simpa only [sub_eq_add_neg] using hn,
    by simpa only [sub_eq_add_neg, padicValRat.pow, Nat.cast_ofNat] using hv⟩

/-- Valuation of the actual rational duplication expression. -/
theorem dyadic_duplication_val {b x y : ℚ} (hn : x ^ 2 - b ^ 2 ≠ 0)
    (hy : y ≠ 0) :
    ((x ^ 2 - b ^ 2) / (2 * y)) ^ 2 ≠ 0 ∧
    padicValRat 2 (((x ^ 2 - b ^ 2) / (2 * y)) ^ 2) =
      2 * padicValRat 2 (x ^ 2 - b ^ 2) - 2 - 2 * padicValRat 2 y := by
  have htwo : (2 : ℚ) ≠ 0 := by norm_num
  refine ⟨pow_ne_zero 2 (div_ne_zero hn (mul_ne_zero htwo hy)), ?_⟩
  rw [padicValRat.pow, padicValRat.div hn (mul_ne_zero htwo hy),
    padicValRat.mul htwo hy]
  have hv2 : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
  rw [hv2]
  norm_num
  ring

/-- Positive x-valuation gives the exact duplication valuation `-v₂(x)-2`.
The square equation forces v₂(x) even, so the new valuation is at most -4. -/
theorem dyadic_duplication_positive {a b x y : ℚ} (ha : 1 ≤ padicValRat 2 a)
    (hb : b ≠ 0) (hvb : padicValRat 2 b = 0) (hx : x ≠ 0)
    (heq : y ^ 2 = x ^ 3 + a * x ^ 2 + b ^ 2 * x)
    (hvx : 0 < padicValRat 2 x) :
    y ≠ 0 ∧ ((x ^ 2 - b ^ 2) / (2 * y)) ^ 2 ≠ 0 ∧
    padicValRat 2 (((x ^ 2 - b ^ 2) / (2 * y)) ^ 2) = -padicValRat 2 x - 2 ∧
    padicValRat 2 (((x ^ 2 - b ^ 2) / (2 * y)) ^ 2) ≤ -4 := by
  obtain ⟨hy, hxy⟩ := dyadic_curve_positive ha hb hvb hx heq hvx
  obtain ⟨hn, hvn⟩ := dyadic_dup_numerator_positive hb hvb hx hvx
  obtain ⟨hz, hvz⟩ := dyadic_duplication_val hn hy
  exact ⟨hy, hz, by omega, by omega⟩

/-- Negative x-valuation gives the exact duplication valuation `v₂(x)-2`.
The square equation forces v₂(x) even, so the new valuation is at most -4. -/
theorem dyadic_duplication_negative {a b x y : ℚ} (ha : 1 ≤ padicValRat 2 a)
    (hb : b ≠ 0) (hvb : padicValRat 2 b = 0) (hx : x ≠ 0)
    (heq : y ^ 2 = x ^ 3 + a * x ^ 2 + b ^ 2 * x)
    (hvx : padicValRat 2 x < 0) :
    y ≠ 0 ∧ ((x ^ 2 - b ^ 2) / (2 * y)) ^ 2 ≠ 0 ∧
    padicValRat 2 (((x ^ 2 - b ^ 2) / (2 * y)) ^ 2) = padicValRat 2 x - 2 ∧
    padicValRat 2 (((x ^ 2 - b ^ 2) / (2 * y)) ^ 2) ≤ -4 := by
  obtain ⟨hy, hxy⟩ := dyadic_curve_negative ha hb hvb hx heq hvx
  obtain ⟨hn, hvn⟩ := dyadic_dup_numerator_negative hb hvb hx hvx
  obtain ⟨hz, hvz⟩ := dyadic_duplication_val hn hy
  exact ⟨hy, hz, by omega, by omega⟩

/-- A nonzero finite x-valuation is necessarily even on the curve. -/
theorem dyadic_curve_val_even {a b x y : ℚ} (ha : 1 ≤ padicValRat 2 a)
    (hb : b ≠ 0) (hvb : padicValRat 2 b = 0) (hx : x ≠ 0)
    (heq : y ^ 2 = x ^ 3 + a * x ^ 2 + b ^ 2 * x)
    (hvx : padicValRat 2 x ≠ 0) : Even (padicValRat 2 x) := by
  rcases lt_or_gt_of_ne hvx with hn | hp
  · obtain ⟨_, hxy⟩ := dyadic_curve_negative ha hb hvb hx heq hn
    exact ⟨padicValRat 2 y - padicValRat 2 x, by omega⟩
  · obtain ⟨_, hxy⟩ := dyadic_curve_positive ha hb hvb hx heq hp
    exact ⟨padicValRat 2 y, by omega⟩

/-- Either sign of nonzero x-valuation puts the doubled abscissa at valuation
at most -4, using only the raw rational curve equation. -/
theorem dyadic_duplication_of_val_ne_zero {a b x y : ℚ}
    (ha : 1 ≤ padicValRat 2 a) (hb : b ≠ 0) (hvb : padicValRat 2 b = 0)
    (hx : x ≠ 0) (heq : y ^ 2 = x ^ 3 + a * x ^ 2 + b ^ 2 * x)
    (hvx : padicValRat 2 x ≠ 0) :
    y ≠ 0 ∧ ((x ^ 2 - b ^ 2) / (2 * y)) ^ 2 ≠ 0 ∧
    padicValRat 2 (((x ^ 2 - b ^ 2) / (2 * y)) ^ 2) ≤ -4 := by
  rcases lt_or_gt_of_ne hvx with hn | hp
  · obtain ⟨hy, hz, _, hvz⟩ := dyadic_duplication_negative ha hb hvb hx heq hn
    exact ⟨hy, hz, hvz⟩
  · obtain ⟨hy, hz, _, hvz⟩ := dyadic_duplication_positive ha hb hvb hx heq hp
    exact ⟨hy, hz, hvz⟩

#print axioms dyadic_curve_val_even
#print axioms dyadic_duplication_of_val_ne_zero
#print axioms dyadic_curve_positive
#print axioms dyadic_curve_negative
#print axioms dyadic_duplication_positive
#print axioms dyadic_duplication_negative

end FourCorner.UniformTorsion
