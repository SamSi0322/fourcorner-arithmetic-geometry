import UniformDyadicRat
import UniformDyadicVal

namespace FourCorner.UniformTorsion

lemma odd_int_dyadic_unit {z : ℤ} (hz : Odd z) :
    (z : ℚ) ≠ 0 ∧ padicValRat 2 (z : ℚ) = 0 := by
  have hz2 := Int.odd_iff.mp hz
  have hn : ¬ (2 : ℤ) ∣ z := by
    intro hd
    have h := Int.emod_eq_zero_of_dvd hd
    omega
  have hz0 : z ≠ 0 := by intro he; subst z; simp at hz2
  refine ⟨by exact_mod_cast hz0, ?_⟩
  have hv : padicValInt 2 z = 0 := padicValInt.eq_zero_iff.mpr (Or.inr (Or.inr hn))
  rw [padicValRat.of_int, hv]
  norm_num

/-- The actual odd-parameter coefficients have v2(alpha)=1 and v2(B)=0. -/
theorem family_dyadic_coefficients {mu nu : ℤ} (hmu : Odd mu) (hnu : Odd nu) :
    (B mu nu : ℚ) ≠ 0 ∧ padicValRat 2 (B mu nu : ℚ) = 0 ∧
      padicValRat 2 (alpha mu nu : ℚ) = 1 := by
  obtain ⟨hB, c, hc, he⟩ := dyadic_coefficients_odd hmu hnu
  obtain ⟨hB0, hvB⟩ := odd_int_dyadic_unit hB
  obtain ⟨hc0, hvc⟩ := odd_int_dyadic_unit hc
  refine ⟨hB0, hvB, ?_⟩
  rw [he]
  push_cast
  have htwo : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
  rw [padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) hc0, htwo, hvc, add_zero]

/-- At a nonzero square abscissa on the actual odd-parameter equation,
the duplication abscissa is nonzero and has dyadic valuation at most -4. -/
theorem family_square_x_duplication {mu nu : ℤ} (hmu : Odd mu) (hnu : Odd nu)
    {x y : ℚ} (hx : x ≠ 0) (hxsq : ∃ s : ℚ, x = s^2)
    (hxy : y^2 = x^3 + (alpha mu nu : ℚ)*x^2 + (B mu nu : ℚ)^2*x) :
    y ≠ 0 ∧ ((x^2 - (B mu nu : ℚ)^2)/(2*y))^2 ≠ 0 ∧
      padicValRat 2 (((x^2 - (B mu nu : ℚ)^2)/(2*y))^2) ≤ -4 := by
  obtain ⟨hB0, hvB, hva⟩ := family_dyadic_coefficients hmu hnu
  exact dyadic_duplication_of_val_ne_zero (by omega) hB0 hvB hx hxy
    (square_x_padicValRat_ne_zero hmu hnu hx hxsq hxy)

/-- Exhaustive scalar cases for a finite double: the visible point (0,0),
or a nonzero duplication abscissa of valuation at most -4. -/
theorem family_square_x_dyadic_cases {mu nu : ℤ} (hmu : Odd mu) (hnu : Odd nu)
    {x y : ℚ} (hxsq : ∃ s : ℚ, x = s^2)
    (hxy : y^2 = x^3 + (alpha mu nu : ℚ)*x^2 + (B mu nu : ℚ)^2*x) :
    (x = 0 ∧ y = 0) ∨
      (x ≠ 0 ∧ y ≠ 0 ∧ ((x^2 - (B mu nu : ℚ)^2)/(2*y))^2 ≠ 0 ∧
        padicValRat 2 (((x^2 - (B mu nu : ℚ)^2)/(2*y))^2) ≤ -4) := by
  by_cases hx : x = 0
  · left
    refine ⟨hx, ?_⟩
    have hy : y^2 = 0 := by simpa [hx] using hxy
    exact eq_zero_of_pow_eq_zero hy
  · right
    exact ⟨hx, family_square_x_duplication hmu hnu hx hxsq hxy⟩

/-- Exact valuation of the actual S-translation abscissa. -/
theorem family_translate_zero_x_val {mu nu : ℤ} (hmu : Odd mu) (hnu : Odd nu)
    {x : ℚ} (hx : x ≠ 0) :
    padicValRat 2 ((B mu nu : ℚ)^2 / x) = -padicValRat 2 x := by
  obtain ⟨hB0, hvB, _⟩ := family_dyadic_coefficients hmu hnu
  rw [padicValRat.div (pow_ne_zero 2 hB0) hx, padicValRat.pow, hvB]
  simp

/-- Positive abscissa valuation becomes negative after translation by S. -/
theorem family_translate_zero_x_negative {mu nu : ℤ} (hmu : Odd mu) (hnu : Odd nu)
    {x : ℚ} (hx : x ≠ 0) (hvx : 0 < padicValRat 2 x) :
    padicValRat 2 ((B mu nu : ℚ)^2 / x) < 0 := by
  rw [family_translate_zero_x_val hmu hnu hx]
  omega

/-- Negative abscissa valuation on the curve is at most -2, exactly the G1 threshold. -/
theorem family_negative_x_le_neg_two {mu nu : ℤ} (hmu : Odd mu) (hnu : Odd nu)
    {x y : ℚ} (hx : x ≠ 0)
    (hxy : y^2 = x^3 + (alpha mu nu : ℚ)*x^2 + (B mu nu : ℚ)^2*x)
    (hvx : padicValRat 2 x < 0) : padicValRat 2 x ≤ -2 := by
  obtain ⟨hB0, hvB, hva⟩ := family_dyadic_coefficients hmu hnu
  have hv := (dyadic_curve_negative (by omega) hB0 hvB hx hxy hvx).2
  omega

/-- The translated abscissa in the positive case is also at most -2. -/
theorem family_translate_zero_x_le_neg_two {mu nu : ℤ} (hmu : Odd mu) (hnu : Odd nu)
    {x y : ℚ} (hx : x ≠ 0)
    (hxy : y^2 = x^3 + (alpha mu nu : ℚ)*x^2 + (B mu nu : ℚ)^2*x)
    (hvx : 0 < padicValRat 2 x) : padicValRat 2 ((B mu nu : ℚ)^2 / x) ≤ -2 := by
  obtain ⟨hB0, hvB, hva⟩ := family_dyadic_coefficients hmu hnu
  have hv := (dyadic_curve_positive (by omega) hB0 hvB hx hxy hvx).2
  rw [family_translate_zero_x_val hmu hnu hx]
  omega

end FourCorner.UniformTorsion

#print axioms FourCorner.UniformTorsion.family_dyadic_coefficients
#print axioms FourCorner.UniformTorsion.family_square_x_duplication
#print axioms FourCorner.UniformTorsion.family_square_x_dyadic_cases

#print axioms FourCorner.UniformTorsion.family_translate_zero_x_val
#print axioms FourCorner.UniformTorsion.family_translate_zero_x_le_neg_two
#print axioms FourCorner.UniformTorsion.family_negative_x_le_neg_two
