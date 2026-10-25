import FourCorner.RatIntegralAux
import FourCorner.NineThreeHPlusMod16
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! Denominator clearing for the positive quartic in the nine-three case. -/

set_option autoImplicit false

namespace FourCorner.NineThreeHPlus

/-- A rational number whose doubled square is integral is itself integral.
First `2q` is an integer; its square is even, so that integer is even. -/
theorem exists_int_of_two_mul_sq_eq_int {q : ℚ} {z : ℤ}
    (h : 2 * q ^ 2 = (z : ℚ)) : ∃ k : ℤ, q = (k : ℚ) := by
  have htwosq : (2 * q) ^ 2 = ((2 * z : ℤ) : ℚ) := by
    push_cast
    linear_combination 2 * h
  obtain ⟨t, ht⟩ := FourCorner.exists_int_of_sq_eq_int htwosq
  have htsq : t ^ 2 = 2 * z := by
    have htsqq : (t : ℚ) ^ 2 = ((2 * z : ℤ) : ℚ) := by
      rw [← ht]
      exact htwosq
    exact_mod_cast htsqq
  have hteven : Even t := (Int.even_pow.mp (show Even (t ^ 2) from
    ⟨z, by linarith [htsq]⟩)).1
  obtain ⟨k, hk⟩ := hteven
  refine ⟨k, ?_⟩
  have hkq : (t : ℚ) = (k : ℚ) + (k : ℚ) := by exact_mod_cast hk
  linarith [ht, hkq]

/-- A rational solution clears to the reduced numerator and denominator of
`a`, with an integral third coordinate and a primitive pair of coordinates. -/
theorem primitive_integral_model (a b : ℚ)
    (h : 8 * b ^ 2 = 3 + 2 * a ^ 2 - a ^ 4) :
    ∃ W : ℤ, 0 < (a.den : ℤ) ∧
      Nat.Coprime a.num.natAbs (a.den : ℤ).natAbs ∧
      2 * W ^ 2 = 3 * (a.den : ℤ) ^ 4 +
        2 * a.num ^ 2 * (a.den : ℤ) ^ 2 - a.num ^ 4 := by
  have hnum : (a.num : ℚ) = a * (a.den : ℚ) := (Rat.mul_den_eq_num a).symm
  have hclear : 2 * (2 * b * (a.den : ℚ) ^ 2) ^ 2 =
      ((3 * (a.den : ℤ) ^ 4 + 2 * a.num ^ 2 * (a.den : ℤ) ^ 2 -
        a.num ^ 4 : ℤ) : ℚ) := by
    push_cast
    rw [hnum]
    linear_combination (a.den : ℚ) ^ 4 * h
  obtain ⟨W, hW⟩ := exists_int_of_two_mul_sq_eq_int hclear
  refine ⟨W, by exact_mod_cast a.den_pos, ?_, ?_⟩
  · simpa only [Int.natAbs_natCast] using a.reduced
  · rw [hW] at hclear
    exact_mod_cast hclear

/-- The positive quartic has no rational affine point. Reduced numerator and
denominator clearing supplies the primitive guard for the dyadic obstruction. -/
theorem hplus_quartic_no_rational_point (a b : ℚ) :
    8 * b ^ 2 ≠ 3 + 2 * a ^ 2 - a ^ 4 := by
  intro h
  obtain ⟨W, _hden, hprim, hW⟩ := primitive_integral_model a b h
  exact primitive_quartic_impossible a.num (a.den : ℤ) W hprim hW

end FourCorner.NineThreeHPlus

#print axioms FourCorner.NineThreeHPlus.exists_int_of_two_mul_sq_eq_int
#print axioms FourCorner.NineThreeHPlus.primitive_integral_model
#print axioms FourCorner.NineThreeHPlus.hplus_quartic_no_rational_point
