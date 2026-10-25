import FourCorner.IntegralModel
import FourCorner.RadiusContentUnitsAux

namespace FourCorner

/-- Joint nonnegative integer content of four integers. -/
def gcd4 (a b c d : ℤ) : ℕ := Nat.gcd (Int.gcd a b) (Int.gcd c d)

theorem gcd4_dvd₀ (a b c d : ℤ) : (gcd4 a b c d : ℤ) ∣ a :=
  dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)) (Int.gcd_dvd_left a b)

theorem gcd4_dvd₁ (a b c d : ℤ) : (gcd4 a b c d : ℤ) ∣ b :=
  dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)) (Int.gcd_dvd_right a b)

theorem gcd4_dvd₂ (a b c d : ℤ) : (gcd4 a b c d : ℤ) ∣ c :=
  dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)) (Int.gcd_dvd_left c d)

theorem gcd4_dvd₃ (a b c d : ℤ) : (gcd4 a b c d : ℤ) ∣ d :=
  dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)) (Int.gcd_dvd_right c d)

theorem gcd4_pos (a b c d : ℤ) (ha : 0 < a) : 0 < gcd4 a b c d :=
  Nat.gcd_pos_of_pos_left _ (Int.gcd_pos_of_ne_zero_left b (ne_of_gt ha))

/-- Dividing all four integers by their joint content gives joint content one. -/
theorem gcd4_ediv_self (a b c d : ℤ) (h : gcd4 a b c d ≠ 0) :
    gcd4 (a / (gcd4 a b c d : ℤ)) (b / (gcd4 a b c d : ℤ))
      (c / (gcd4 a b c d : ℤ)) (d / (gcd4 a b c d : ℤ)) = 1 := by
  change Nat.gcd (Int.gcd (a / (gcd4 a b c d : ℤ)) (b / (gcd4 a b c d : ℤ)))
    (Int.gcd (c / (gcd4 a b c d : ℤ)) (d / (gcd4 a b c d : ℤ))) = 1
  rw [Int.gcd_ediv (gcd4_dvd₀ a b c d) (gcd4_dvd₁ a b c d),
    Int.gcd_ediv (gcd4_dvd₂ a b c d) (gcd4_dvd₃ a b c d), Int.natAbs_natCast]
  unfold gcd4
  rw [Nat.gcd_div (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)]
  exact Nat.div_self (Nat.pos_of_ne_zero h)

/-- Once the square of the joint radius content divides the side, every prime
of the reduced side is coprime to each of the four reduced radii. -/
theorem IntegralModel.reduced_radii_not_dvd (m : IntegralModel)
    (hL : (gcd4 m.A₀ m.A₁ m.A₂ m.A₃ : ℤ) ^ 2 ∣ m.L)
    {p : ℕ} (hp : p.Prime)
    (hpH : (p : ℤ) ∣ m.L / (gcd4 m.A₀ m.A₁ m.A₂ m.A₃ : ℤ) ^ 2) :
    ¬ (p : ℤ) ∣ m.A₀ / (gcd4 m.A₀ m.A₁ m.A₂ m.A₃ : ℤ) ∧
    ¬ (p : ℤ) ∣ m.A₁ / (gcd4 m.A₀ m.A₁ m.A₂ m.A₃ : ℤ) ∧
    ¬ (p : ℤ) ∣ m.A₂ / (gcd4 m.A₀ m.A₁ m.A₂ m.A₃ : ℤ) ∧
    ¬ (p : ℤ) ∣ m.A₃ / (gcd4 m.A₀ m.A₁ m.A₂ m.A₃ : ℤ) := by
  let G := gcd4 m.A₀ m.A₁ m.A₂ m.A₃
  have hg : G ≠ 0 := ne_of_gt (gcd4_pos _ _ _ _ m.A₀_pos)
  have hgZ : (G : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hg
  have h₀ := gcd4_dvd₀ m.A₀ m.A₁ m.A₂ m.A₃
  have h₁ := gcd4_dvd₁ m.A₀ m.A₁ m.A₂ m.A₃
  have h₂ := gcd4_dvd₂ m.A₀ m.A₁ m.A₂ m.A₃
  have h₃ := gcd4_dvd₃ m.A₀ m.A₁ m.A₂ m.A₃
  apply primitive_four_equal_squares_not_dvd hp
    (gcd4_ediv_self m.A₀ m.A₁ m.A₂ m.A₃ hg)
  · rw [div_square_sub_div_square hgZ h₁ h₀ hL
      (show m.A₁ ^ 2 - m.A₀ ^ 2 = m.L * (m.L - 2 * m.X) by
        rw [m.sq₁, m.sq₀]; ring)]
    exact dvd_mul_of_dvd_left hpH _
  · rw [div_square_sub_div_square hgZ h₂ h₀ hL
      (show m.A₂ ^ 2 - m.A₀ ^ 2 = m.L * (m.L - 2 * m.Y) by
        rw [m.sq₂, m.sq₀]; ring)]
    exact dvd_mul_of_dvd_left hpH _
  · rw [div_square_sub_div_square hgZ h₃ h₀ hL
      (show m.A₃ ^ 2 - m.A₀ ^ 2 = m.L * (2 * m.L - 2 * m.X - 2 * m.Y) by
        rw [m.sq₃, m.sq₀]; ring)]
    exact dvd_mul_of_dvd_left hpH _

end FourCorner
