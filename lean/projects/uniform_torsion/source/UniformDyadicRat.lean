import UniformCurve
import UniformDyadic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-! Rational denominator bridges for the dyadic obstruction on the pair curve.
The valuation at zero is treated separately wherever a unit is required. -/

namespace FourCorner.UniformTorsion

open WithZero

/-- Rational dyadic integrality is exactly oddness of the reduced denominator. -/
theorem padicValRat_two_nonneg_iff_odd_den (x : ℚ) :
    0 ≤ padicValRat 2 x ↔ Odd x.den := by
  have hi : Rat.padicValuation 2 x ≤ 1 ↔ 0 ≤ padicValRat 2 x := by
    by_cases hx : x = 0
    · simp [hx]
    · simp only [Rat.padicValuation, hx, ↓reduceIte, Valuation.coe_mk,
        MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
      rw [← exp_zero, exp_le_exp]
      omega
  rw [← hi, Rat.padicValuation_le_one_iff]
  simpa only [even_iff_two_dvd] using (Nat.not_even_iff_odd (n := x.den))

/-- A nonzero rational of dyadic valuation zero has odd reduced numerator and
denominator. The nonzero hypothesis is necessary for `padicValRat`. -/
theorem rat_unit_num_den_odd {s : ℚ} (hs : s ≠ 0) (hv : padicValRat 2 s = 0) :
    Odd s.num ∧ Odd s.den := by
  have hd : Odd s.den := (padicValRat_two_nonneg_iff_odd_den s).mp (by omega)
  have hdv : padicValNat 2 s.den = 0 :=
    padicValNat.eq_zero_of_not_dvd hd.not_two_dvd_nat
  have hnv : padicValInt 2 s.num = 0 := by
    rw [padicValRat_def, hdv, Nat.cast_zero, sub_zero] at hv
    exact_mod_cast hv
  have hn : ¬ (2 : ℤ) ∣ s.num := by
    simpa [padicValInt.eq_zero_iff, Rat.num_ne_zero.mpr hs] using hnv
  exact ⟨Int.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hn), hd⟩

/-- Clearing the square coordinate `x=s²` needs only the denominator of `s`.
If the resulting integer is a rational square, it is an integer square. -/
theorem rat_square_equation_clear_den {mu nu : ℤ} {s y : ℚ}
    (hxy : y ^ 2 = (s ^ 2) ^ 3 + (alpha mu nu : ℚ) * (s ^ 2) ^ 2 +
      (B mu nu : ℚ) ^ 2 * (s ^ 2)) :
    ∃ Y : ℤ, Y ^ 2 = s.num ^ 6 + alpha mu nu * s.num ^ 4 * (s.den : ℤ) ^ 2 +
      B mu nu ^ 2 * s.num ^ 2 * (s.den : ℤ) ^ 4 := by
  let N : ℤ := s.num ^ 6 + alpha mu nu * s.num ^ 4 * (s.den : ℤ) ^ 2 +
      B mu nu ^ 2 * s.num ^ 2 * (s.den : ℤ) ^ 4
  have hd : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_ne_zero
  have heq : (y * (s.den : ℚ) ^ 3) ^ 2 = (N : ℚ) := by
    dsimp [N]
    push_cast
    rw [← s.num_div_den] at hxy
    field_simp at hxy
    nlinarith only [hxy]
  have hsq : IsSquare (N : ℚ) := by
    exact (isSquare_iff_exists_sq (N : ℚ)).mpr ⟨y * (s.den : ℚ) ^ 3, heq.symm⟩
  obtain ⟨Y, hY⟩ := (isSquare_iff_exists_sq N).mp (Rat.isSquare_intCast_iff.mp hsq)
  exact ⟨Y, hY.symm⟩

/-- An odd-parameter curve cannot have an abscissa which is the square of a
nonzero rational dyadic unit. No denominator assumption on `y` is needed. -/
theorem rat_unit_square_not_on_curve {mu nu : ℤ} (hmu : Odd mu) (hnu : Odd nu)
    {s y : ℚ} (hs : s ≠ 0) (hv : padicValRat 2 s = 0) :
    y ^ 2 ≠ (s ^ 2) ^ 3 + (alpha mu nu : ℚ) * (s ^ 2) ^ 2 +
      (B mu nu : ℚ) ^ 2 * (s ^ 2) := by
  intro hxy
  obtain ⟨ha, hb⟩ := rat_unit_num_den_odd hs hv
  obtain ⟨Y, hY⟩ := rat_square_equation_clear_den hxy
  exact odd_parameter_square_rhs_not_square hmu hnu ha hb.natCast Y hY

/-- The coordinate form used for finite doubles: a nonzero rational square on
the curve cannot have dyadic valuation zero. -/
theorem square_x_padicValRat_ne_zero {mu nu : ℤ} (hmu : Odd mu) (hnu : Odd nu)
    {x y : ℚ} (hx : x ≠ 0) (hxsq : ∃ s : ℚ, x = s ^ 2)
    (hxy : y ^ 2 = x ^ 3 + (alpha mu nu : ℚ) * x ^ 2 + (B mu nu : ℚ) ^ 2 * x) :
    padicValRat 2 x ≠ 0 := by
  intro hv
  obtain ⟨s, rfl⟩ := hxsq
  have hs : s ≠ 0 := by
    intro hs
    simp [hs] at hx
  have hsv : padicValRat 2 s = 0 := by
    rw [padicValRat.pow] at hv
    omega
  exact rat_unit_square_not_on_curve hmu hnu hs hsv hxy

end FourCorner.UniformTorsion
