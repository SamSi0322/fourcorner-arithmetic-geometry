import UniformCurve
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.IntervalCases

namespace FourCorner.UniformTorsion

lemma dyadic_square_mod_sixteen (z : ℤ) :
    z ^ 2 % 16 = 0 ∨ z ^ 2 % 16 = 1 ∨ z ^ 2 % 16 = 4 ∨ z ^ 2 % 16 = 9 := by
  have h0 := Int.emod_nonneg z (by norm_num : (16 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos z (by norm_num : (0 : ℤ) < 16)
  interval_cases h : z % 16 <;> norm_num [pow_two, Int.mul_emod, h]

lemma dyadic_odd_square_mod_sixteen {z : ℤ} (hz : Odd z) :
    z ^ 2 % 16 = 1 ∨ z ^ 2 % 16 = 9 := by
  have hz2 := Int.odd_iff.mp hz
  have h0 := Int.emod_nonneg z (by norm_num : (16 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos z (by norm_num : (0 : ℤ) < 16)
  interval_cases h : z % 16 <;> norm_num [pow_two, Int.mul_emod, h] <;> omega

/-- Exact coefficient residues for the odd-parameter family. -/
theorem dyadic_parameter_residues {mu nu : ℤ} (hmu : Odd mu) (hnu : Odd nu) :
    alpha mu nu % 16 = 14 ∧ B mu nu % 8 = 3 ∧ (B mu nu)^2 % 16 = 9 := by
  have hm := dyadic_odd_square_mod_sixteen hmu
  have hn := dyadic_odd_square_mod_sixteen hnu
  have hm8 : mu^2 % 8 = 1 := by omega
  have hn8 : nu^2 % 8 = 1 := by omega
  have hb8 : B mu nu % 8 = 3 := by
    norm_num [B, Int.sub_emod, Int.mul_emod, hm8, hn8]
  rcases hm with hm | hm <;> rcases hn with hn | hn
  all_goals
    refine ⟨?_, hb8, ?_⟩
    · norm_num [alpha, Int.mul_emod, Int.sub_emod, hm, hn]
    · rw [pow_two, Int.mul_emod]
      norm_num [B, Int.sub_emod, Int.mul_emod, hm, hn]

/-- The linear-square parameter is odd, and alpha is twice an odd integer. -/
theorem dyadic_coefficients_odd {mu nu : ℤ} (hmu : Odd mu) (hnu : Odd nu) :
    Odd (B mu nu) ∧ ∃ c : ℤ, Odd c ∧ alpha mu nu = 2 * c := by
  have hres := dyadic_parameter_residues hmu hnu
  refine ⟨Int.odd_iff.mpr (by omega), 3*mu^2-4*nu^2, ?_, rfl⟩
  have hm := Int.odd_iff.mp hmu
  apply Int.odd_iff.mpr
  norm_num [Int.sub_emod, Int.mul_emod, pow_two, hm]

/-- The denominator-cleared curve expression at an odd unit square is 8 modulo 16. -/
theorem odd_parameter_square_rhs_mod_sixteen {mu nu a b : ℤ}
    (hmu : Odd mu) (hnu : Odd nu) (ha : Odd a) (hb : Odd b) :
    (a^6 + alpha mu nu * a^4 * b^2 + (B mu nu)^2 * a^2 * b^4) % 16 = 8 := by
  obtain ⟨halpha, _, hB⟩ := dyadic_parameter_residues hmu hnu
  rcases dyadic_odd_square_mod_sixteen ha with ha2 | ha2 <;>
    rcases dyadic_odd_square_mod_sixteen hb with hb2 | hb2
  all_goals
    have ha4 : a^4 % 16 = 1 := by
      rw [show a^4 = a^2 * a^2 by ring, Int.mul_emod, ha2]
      norm_num
    have hb4 : b^4 % 16 = 1 := by
      rw [show b^4 = b^2 * b^2 by ring, Int.mul_emod, hb2]
      norm_num
    have ha6 : a^6 % 16 = a^2 % 16 := by
      rw [show a^6 = a^4 * a^2 by ring, Int.mul_emod, ha4]
      omega
    norm_num [Int.add_emod, Int.mul_emod, ha6, ha4, hb4, ha2, hb2, halpha, hB]

/-- Exact unbounded obstruction, with its finite residue computation proved in Lean. -/
theorem odd_parameter_square_rhs_not_square {mu nu a b : ℤ}
    (hmu : Odd mu) (hnu : Odd nu) (ha : Odd a) (hb : Odd b) (Y : ℤ) :
    Y^2 ≠ a^6 + alpha mu nu * a^4 * b^2 + (B mu nu)^2 * a^2 * b^4 := by
  intro he
  have h := congrArg (fun z : ℤ => z % 16) he
  rw [odd_parameter_square_rhs_mod_sixteen hmu hnu ha hb] at h
  have hs := dyadic_square_mod_sixteen Y
  omega

/-- All integral unit-abscissa points have x=3 modulo4 and y=2 modulo4. -/
theorem integer_unit_x_congruences {mu nu X Y : ℤ}
    (hmu : Odd mu) (hnu : Odd nu) (hX : Odd X)
    (hcurve : Y^2 = X^3 + alpha mu nu * X^2 + (B mu nu)^2 * X) :
    X % 4 = 3 ∧ Y % 4 = 2 := by
  obtain ⟨halpha, _, hB⟩ := dyadic_parameter_residues hmu hnu
  have he := congrArg (fun z : ℤ => z % 16) hcurve
  have he' : Y^2 % 16 = (X^3 + 14 * X^2 + 9 * X) % 16 := by
    simpa [Int.add_emod, Int.mul_emod, halpha, hB] using he
  have hx2 := Int.odd_iff.mp hX
  have hx0 := Int.emod_nonneg X (by norm_num : (16 : ℤ) ≠ 0)
  have hx1 := Int.emod_lt_of_pos X (by norm_num : (0 : ℤ) < 16)
  have hy0 := Int.emod_nonneg Y (by norm_num : (16 : ℤ) ≠ 0)
  have hy1 := Int.emod_lt_of_pos Y (by norm_num : (0 : ℤ) < 16)
  interval_cases hx : X % 16 <;> interval_cases hy : Y % 16 <;>
    norm_num [pow_succ, Int.mul_emod, Int.add_emod, hx, hy] at he' <;> omega

/-- Exact factorization controlling the unit-abscissa branch. -/
theorem dyadic_tangent_factorization (mu nu X Y : ℤ)
    (hcurve : Y^2 = X^3 + alpha mu nu * X^2 + (B mu nu)^2 * X) :
    (Y - 2*mu*X)*(Y + 2*mu*X) = X*(X-B mu nu)^2 := by
  have hid : alpha mu nu + 2*B mu nu = 4*mu^2 := by simp [alpha, B]; ring
  linear_combination hcurve + X^2*hid

end FourCorner.UniformTorsion

#print axioms FourCorner.UniformTorsion.odd_parameter_square_rhs_not_square
#print axioms FourCorner.UniformTorsion.integer_unit_x_congruences
#print axioms FourCorner.UniformTorsion.dyadic_tangent_factorization
