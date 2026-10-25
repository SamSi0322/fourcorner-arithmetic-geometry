import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace FourCorner

/-- The least common denominator of two integer ratios, with their common
content explicitly retained. -/
theorem lcm_den_ratios (L X Y : ℤ) (hL : L ≠ 0) :
    Nat.lcm ((X : ℚ) / L).den ((Y : ℚ) / L).den =
      L.natAbs / Nat.gcd (Nat.gcd X.natAbs Y.natAbs) L.natAbs := by
  simp only [← Rat.divInt_eq_div, Rat.den_divInt, hL, if_false, Int.gcd]
  rw [Nat.div_lcm_eq_div_gcd (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)]
  congr 1
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · apply Nat.dvd_gcd
      · exact dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
      · exact dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
    · exact dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
  · apply Nat.dvd_gcd
    · exact Nat.dvd_gcd (Nat.gcd_dvd_right _ _)
        (dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _))
    · exact Nat.dvd_gcd (Nat.gcd_dvd_right _ _)
        (dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _))

/-- A primitive triple has precisely its displayed common denominator. -/
theorem primitive_lcm_den_ratios (L X Y : ℤ) (hL : L ≠ 0)
    (hprimitive : Nat.gcd (Nat.gcd X.natAbs Y.natAbs) L.natAbs = 1) :
    Nat.lcm ((X : ℚ) / L).den ((Y : ℚ) / L).den = L.natAbs := by
  rw [lcm_den_ratios L X Y hL, hprimitive, Nat.div_one]

/-- Clearing two rational coordinates by their least common denominator
produces a jointly primitive integral triple. -/
theorem primitive_of_lcm_den (x y : ℚ) (L : ℕ) (X Y : ℤ)
    (hL : L = Nat.lcm x.den y.den)
    (hX : (X : ℚ) = (L : ℚ) * x)
    (hY : (Y : ℚ) = (L : ℚ) * y) :
    Nat.gcd (Nat.gcd X.natAbs Y.natAbs) L = 1 := by
  have hL0 : L ≠ 0 := by
    rw [hL]
    exact Nat.lcm_ne_zero x.den_nz y.den_nz
  have hLQ : (L : ℚ) ≠ 0 := by exact_mod_cast hL0
  have hx : (X : ℚ) / (L : ℤ) = x := by
    simp only [Int.cast_natCast]
    rw [hX, mul_div_cancel_left₀ _ hLQ]
  have hy : (Y : ℚ) / (L : ℤ) = y := by
    simp only [Int.cast_natCast]
    rw [hY, mul_div_cancel_left₀ _ hLQ]
  have h := lcm_den_ratios (L : ℤ) X Y (by exact_mod_cast hL0)
  simp only [hx, hy, Int.natAbs_natCast] at h
  rw [← hL] at h
  exact (Nat.div_eq_self.mp h.symm).resolve_left hL0

#print axioms lcm_den_ratios
#print axioms primitive_lcm_den_ratios
#print axioms primitive_of_lcm_den

end FourCorner
