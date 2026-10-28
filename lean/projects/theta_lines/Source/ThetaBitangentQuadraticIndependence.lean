import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace FourCorner

/-- The three nontrivial products of the rational squareclasses of 2 and 51
are nonsquares. -/
theorem theta_rat_two_nonsquare : ¬ IsSquare (2 : ℚ) := by norm_num

theorem theta_rat_fiftyone_nonsquare : ¬ IsSquare (51 : ℚ) := by norm_num

theorem theta_rat_onehundredtwo_nonsquare : ¬ IsSquare (102 : ℚ) := by norm_num

theorem theta_rat_sq_ne_two (q : ℚ) : q ^ 2 ≠ 2 := by
  intro h
  exact theta_rat_two_nonsquare ⟨q, by simpa only [pow_two] using h.symm⟩

theorem theta_rat_sq_ne_fiftyone (q : ℚ) : q ^ 2 ≠ 51 := by
  intro h
  exact theta_rat_fiftyone_nonsquare ⟨q, by simpa only [pow_two] using h.symm⟩

theorem theta_rat_sq_ne_onehundredtwo (q : ℚ) : q ^ 2 ≠ 102 := by
  intro h
  exact theta_rat_onehundredtwo_nonsquare ⟨q, by simpa only [pow_two] using h.symm⟩

/-- A concrete copy of the quadratic field Q(sqrt(2)). -/
abbrev ThetaSqrtTwo := QuadraticAlgebra ℚ 2 0

instance theta_sqrtTwo_irreducible : Fact (∀ q : ℚ, q ^ 2 ≠ 2 + 0 * q) :=
  ⟨by intro q; simpa using theta_rat_sq_ne_two q⟩

/-- Adjoining sqrt(2) does not make 51 a square. Comparing coordinates reduces
this to the rational nonsquareness of 51 or 102. -/
theorem theta_sqrtTwo_sq_ne_fiftyone (z : ThetaSqrtTwo) : z ^ 2 ≠ 51 := by
  intro h
  have hre := congrArg QuadraticAlgebra.re h
  have him := congrArg QuadraticAlgebra.im h
  simp only [pow_two, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_ofNat] at hre
  simp only [pow_two, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_ofNat,
    zero_mul, add_zero] at him
  have hz : z.re * z.im = 0 := by linarith
  rcases mul_eq_zero.mp hz with hzero | hzero
  · have hsq : (2 * z.im) ^ 2 = 102 := by
      rw [hzero] at hre
      nlinarith [hre]
    exact theta_rat_sq_ne_onehundredtwo (2 * z.im) hsq
  · have hsq : z.re ^ 2 = 51 := by
      rw [hzero] at hre
      nlinarith [hre]
    exact theta_rat_sq_ne_fiftyone z.re hsq

theorem theta_sqrtTwo_fiftyone_nonsquare : ¬ IsSquare (51 : ThetaSqrtTwo) := by
  rintro ⟨z, hz⟩
  exact theta_sqrtTwo_sq_ne_fiftyone z (by simpa only [pow_two] using hz.symm)

/-- A concrete biquadratic field obtained by successively adjoining sqrt(2)
and sqrt(51). The two nonsquare facts supply both field instances. -/
abbrev ThetaBiquadratic := QuadraticAlgebra ThetaSqrtTwo 51 0

instance theta_biquadratic_irreducible :
    Fact (∀ z : ThetaSqrtTwo, z ^ 2 ≠ 51 + 0 * z) :=
  ⟨by intro z; simpa using theta_sqrtTwo_sq_ne_fiftyone z⟩

#synth Field ThetaSqrtTwo
#synth Field ThetaBiquadratic

#print axioms theta_rat_two_nonsquare
#print axioms theta_rat_fiftyone_nonsquare
#print axioms theta_rat_onehundredtwo_nonsquare
#print axioms theta_sqrtTwo_sq_ne_fiftyone
#print axioms theta_sqrtTwo_fiftyone_nonsquare

end FourCorner
