import UniformNonsingular
import UniformDyadicFamily

namespace FourCorner.UniformTorsion

/-- The odd factor in the quadratic discriminant is a dyadic unit. -/
theorem odd_norm_parameter {mu nu : ℤ} (hm : Odd mu) (hn : Odd nu) :
    Odd (mu^2-2*nu^2) := by
  apply Int.odd_iff.mpr
  have h := norm_parameter_mod_four hm hn
  omega

/-- Exact dyadic depth of the literal quadratic discriminant factor. -/
theorem quadratic_discriminant_padicValRat {mu nu : ℤ} (hm : Odd mu) (hn : Odd nu) :
    padicValRat 2 (((32*mu^2*(mu^2-2*nu^2) : ℤ) : ℚ)) = 5 := by
  obtain ⟨hm0, hmv⟩ := odd_int_dyadic_unit hm
  obtain ⟨hD0, hDv⟩ := odd_int_dyadic_unit (odd_norm_parameter hm hn)
  have htwo : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
  have h32 : padicValRat 2 (32 : ℚ) = 5 := by
    rw [show (32 : ℚ) = 2^5 by norm_num, padicValRat.pow, htwo]
    norm_num
  push_cast
  have hD0' : (mu : ℚ)^2-2*(nu : ℚ)^2 ≠ 0 := by exact_mod_cast hD0
  have hDv' : padicValRat 2 ((mu : ℚ)^2-2*(nu : ℚ)^2) = 0 := by
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_pow] using hDv
  rw [padicValRat.mul (mul_ne_zero (by norm_num) (pow_ne_zero 2 hm0)) hD0',
    padicValRat.mul (by norm_num : (32 : ℚ) ≠ 0) (pow_ne_zero 2 hm0),
    padicValRat.pow, h32, hmv, hDv']
  norm_num

/-- The same exact depth in the natural-valued integer valuation API. -/
theorem quadratic_discriminant_padicValInt {mu nu : ℤ} (hm : Odd mu) (hn : Odd nu) :
    padicValInt 2 (32*mu^2*(mu^2-2*nu^2)) = 5 := by
  have h := quadratic_discriminant_padicValRat hm hn
  rw [padicValRat.of_int] at h
  exact_mod_cast h

/-- Exact valuation five of alpha squared minus four B squared. -/
theorem alpha_discriminant_depth_five {mu nu : ℤ} (hm : Odd mu) (hn : Odd nu) :
    padicValInt 2 (alpha mu nu ^ 2 - 4 * B mu nu ^ 2) = 5 := by
  rw [alpha_disc_factor]
  exact quadratic_discriminant_padicValInt hm hn

#print axioms quadratic_discriminant_padicValRat
#print axioms quadratic_discriminant_padicValInt
#print axioms alpha_discriminant_depth_five
end FourCorner.UniformTorsion
