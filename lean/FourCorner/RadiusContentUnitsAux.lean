import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.NatPrime
import Mathlib.Tactic.Ring

namespace FourCorner

/-- Congruent integer squares have the same prime divisors at the given prime. -/
theorem prime_dvd_iff_of_dvd_square_sub {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (hab : (p : ℤ) ∣ b ^ 2 - a ^ 2) :
    ((p : ℤ) ∣ a ↔ (p : ℤ) ∣ b) := by
  constructor
  · intro ha
    have hb : (p : ℤ) ∣ b ^ 2 := by
      simpa only [sub_add_cancel] using Int.dvd_add hab (dvd_pow ha (by decide : 2 ≠ 0))
    exact Int.natCast_dvd.mpr (Int.Prime.dvd_natAbs_of_coe_dvd_sq hp b hb)
  · intro hb
    have ha : (p : ℤ) ∣ a ^ 2 := by
      simpa only [sub_sub_cancel] using Int.dvd_sub (dvd_pow hb (by decide : 2 ≠ 0)) hab
    exact Int.natCast_dvd.mpr (Int.Prime.dvd_natAbs_of_coe_dvd_sq hp a ha)

/-- Four primitive integers whose squares agree modulo a prime are all units
at that prime. -/
theorem primitive_four_equal_squares_not_dvd {p : ℕ} (hp : p.Prime)
    {a b c d : ℤ} (hprimitive : Nat.gcd (Int.gcd a b) (Int.gcd c d) = 1)
    (hb : (p : ℤ) ∣ b ^ 2 - a ^ 2)
    (hc : (p : ℤ) ∣ c ^ 2 - a ^ 2)
    (hd : (p : ℤ) ∣ d ^ 2 - a ^ 2) :
    ¬ (p : ℤ) ∣ a ∧ ¬ (p : ℤ) ∣ b ∧ ¬ (p : ℤ) ∣ c ∧ ¬ (p : ℤ) ∣ d := by
  have hab := prime_dvd_iff_of_dvd_square_sub hp hb
  have hac := prime_dvd_iff_of_dvd_square_sub hp hc
  have had := prime_dvd_iff_of_dvd_square_sub hp hd
  have ha : ¬ (p : ℤ) ∣ a := by
    intro ha
    have hg : p ∣ Nat.gcd (Int.gcd a b) (Int.gcd c d) :=
      Nat.dvd_gcd
        (Nat.dvd_gcd (Int.natCast_dvd.mp ha) (Int.natCast_dvd.mp (hab.mp ha)))
        (Nat.dvd_gcd (Int.natCast_dvd.mp (hac.mp ha)) (Int.natCast_dvd.mp (had.mp ha)))
    rw [hprimitive] at hg
    exact hp.not_dvd_one hg
  exact ⟨ha, fun hb => ha (hab.mpr hb), fun hc => ha (hac.mpr hc),
    fun hd => ha (had.mpr hd)⟩

/-- Dividing a square difference by a common square divisor preserves its
factorization, with exact integer quotients. -/
theorem div_square_sub_div_square {a b g L t : ℤ} (hg : g ≠ 0)
    (ha : g ∣ a) (hb : g ∣ b) (hL : g ^ 2 ∣ L)
    (heq : a ^ 2 - b ^ 2 = L * t) :
    (a / g) ^ 2 - (b / g) ^ 2 = (L / g ^ 2) * t := by
  apply mul_left_cancel₀ (pow_ne_zero 2 hg)
  calc
    g ^ 2 * ((a / g) ^ 2 - (b / g) ^ 2) =
        (g * (a / g)) ^ 2 - (g * (b / g)) ^ 2 := by ring
    _ = a ^ 2 - b ^ 2 := by rw [Int.mul_ediv_cancel' ha, Int.mul_ediv_cancel' hb]
    _ = L * t := heq
    _ = (g ^ 2 * (L / g ^ 2)) * t := by rw [Int.mul_ediv_cancel' hL]
    _ = g ^ 2 * ((L / g ^ 2) * t) := by ring

end FourCorner

#print axioms FourCorner.primitive_four_equal_squares_not_dvd
#print axioms FourCorner.div_square_sub_div_square
