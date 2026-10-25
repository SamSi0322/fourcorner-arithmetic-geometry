import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Elementary rational integrality lemmas used in primitive normalization. -/

namespace FourCorner

/-- A rational number whose square is an integer has denominator one. -/
theorem den_eq_one_of_sq_eq_int {q : ℚ} {z : ℤ} (h : q ^ 2 = (z : ℚ)) :
    q.den = 1 := by
  have hd : q.den ^ 2 = 1 := by
    simpa only [Rat.den_pow, Rat.den_intCast] using congrArg Rat.den h
  exact (Nat.pow_eq_one.mp hd).resolve_right (by norm_num)

/-- A rational square root of an integer is itself an integer. -/
theorem exists_int_of_sq_eq_int {q : ℚ} {z : ℤ} (h : q ^ 2 = (z : ℚ)) :
    ∃ a : ℤ, q = (a : ℚ) :=
  ⟨q.num, (Rat.coe_int_num_of_den_eq_one (den_eq_one_of_sq_eq_int h)).symm⟩

/-- Denominator one is precisely integrality in the literal rational field. -/
theorem rat_den_eq_one_iff_exists_int (q : ℚ) :
    q.den = 1 ↔ ∃ a : ℤ, q = (a : ℚ) := by
  constructor
  · intro h
    exact ⟨q.num, (Rat.coe_int_num_of_den_eq_one h).symm⟩
  · rintro ⟨a, rfl⟩
    exact Rat.den_intCast a

/-- Multiplication by an integer clears a rational denominator exactly when
that denominator divides the absolute value of the integer. -/
theorem int_mul_rat_integral_iff (L : ℤ) (q : ℚ) :
    (∃ a : ℤ, (L : ℚ) * q = (a : ℚ)) ↔ q.den ∣ L.natAbs := by
  rw [← rat_den_eq_one_iff_exists_int]
  have heq : (L : ℚ) * q = ((L * q.num : ℤ) : ℚ) / ((q.den : ℤ) : ℚ) := by
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [mul_div_assoc, Rat.num_div_den]
  rw [heq, Rat.den_div_intCast_eq_one_iff _ _ (by exact_mod_cast q.den_nz)]
  rw [Int.natCast_dvd, Int.natAbs_mul]
  exact q.reduced.symm.dvd_mul_right

/-- Equivalent integer-valued denominator-clearing criterion. -/
theorem int_mul_rat_integral_iff_int_dvd (L : ℤ) (q : ℚ) :
    (∃ a : ℤ, (L : ℚ) * q = (a : ℚ)) ↔ (q.den : ℤ) ∣ L := by
  rw [int_mul_rat_integral_iff, Int.natCast_dvd]

/-- Natural-number denominator-clearing criterion. -/
theorem nat_mul_rat_integral_iff (N : ℕ) (q : ℚ) :
    (∃ a : ℤ, (N : ℚ) * q = (a : ℚ)) ↔ q.den ∣ N := by
  simpa only [Int.cast_natCast, Int.natAbs_natCast] using
    int_mul_rat_integral_iff (N : ℤ) q

/-- The least common denominator of two rationals divides precisely their
common integral scaling factors. -/
theorem pair_integral_iff_lcm_den_dvd (N : ℕ) (x y : ℚ) :
    (∃ X Y : ℤ, (N : ℚ) * x = (X : ℚ) ∧ (N : ℚ) * y = (Y : ℚ)) ↔
      Nat.lcm x.den y.den ∣ N := by
  constructor
  · rintro ⟨X, Y, hX, hY⟩
    exact Nat.lcm_dvd ((nat_mul_rat_integral_iff N x).mp ⟨X, hX⟩)
      ((nat_mul_rat_integral_iff N y).mp ⟨Y, hY⟩)
  · intro h
    obtain ⟨hx, hy⟩ := Nat.lcm_dvd_iff.mp h
    obtain ⟨X, hX⟩ := (nat_mul_rat_integral_iff N x).mpr hx
    obtain ⟨Y, hY⟩ := (nat_mul_rat_integral_iff N y).mpr hy
    exact ⟨X, Y, hX, hY⟩

/-- In particular, the least common denominator actually clears both
coordinates and is positive. -/
theorem lcm_den_positive_and_integral (x y : ℚ) :
    0 < Nat.lcm x.den y.den ∧
      ∃ X Y : ℤ, ((Nat.lcm x.den y.den : ℕ) : ℚ) * x = (X : ℚ) ∧
        ((Nat.lcm x.den y.den : ℕ) : ℚ) * y = (Y : ℚ) := by
  exact ⟨Nat.lcm_pos x.den_pos y.den_pos,
    (pair_integral_iff_lcm_den_dvd _ x y).mpr (dvd_refl _)⟩

end FourCorner

#print axioms FourCorner.den_eq_one_of_sq_eq_int
#print axioms FourCorner.exists_int_of_sq_eq_int
#print axioms FourCorner.int_mul_rat_integral_iff
#print axioms FourCorner.int_mul_rat_integral_iff_int_dvd

#print axioms FourCorner.rat_den_eq_one_iff_exists_int
#print axioms FourCorner.nat_mul_rat_integral_iff
#print axioms FourCorner.pair_integral_iff_lcm_den_dvd
#print axioms FourCorner.lcm_den_positive_and_integral
