import FourCorner.ThetaLocalHensel
import Mathlib.Tactic

namespace FourCorner

/-- The same three radicands, over the actual completed field. -/
def ThetaLocalSource (p : ℕ) [Fact p.Prime] (z : ℚ_[p]) : Prop :=
  ∃ P Q R : ℚ_[p], P^2=z^2+50 ∧ Q^2=z^2+14*z+51 ∧ R^2=z^2-14*z+51

/-- A small p-adic argument makes any integral polynomial with zero constant small. -/
theorem theta_small_quadratic_norm {p : ℕ} [Fact p.Prime]
    (a : ℚ_[p]) (ha : ‖a‖ < 1) (c d : ℤ) :
    ‖(c : ℚ_[p])*a + (d : ℚ_[p])*a^2‖ < 1 := by
  have hc := Padic.norm_int_le_one (p:=p) c
  have hd := Padic.norm_int_le_one (p:=p) d
  have ha0 := norm_nonneg a
  have ha2 : ‖a‖^2 < 1 := by nlinarith
  apply lt_of_le_of_lt (Padic.nonarchimedean _ _) (max_lt ?_ ?_)
  · rw [norm_mul]
    nlinarith [norm_nonneg (c : ℚ_[p])]
  · rw [norm_mul, norm_pow]
    nlinarith [norm_nonneg (d : ℚ_[p]), sq_nonneg ‖a‖]

/-- Actual roots of normalized units restore the original quadratic radicand. -/
theorem theta_quadratic_square_of_normalized {K : Type*} [Field K]
    (z c d : K) (hz : z ≠ 0)
    (hs : IsSquare (1 + c*z⁻¹ + d*(z⁻¹)^2)) :
    ∃ r : K, r^2=z^2+c*z+d := by
  obtain ⟨u, hu⟩ := hs
  refine ⟨z*u, ?_⟩
  have hu' : u^2=1+c*z⁻¹+d*(z⁻¹)^2 := by simpa [pow_two] using hu.symm
  rw [mul_pow, hu']
  field_simp

/-- Every odd prime admits all three roots at every negative-valuation coordinate. -/
theorem theta_odd_local_source {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (z : ℚ_[p]) (hz : 1 < ‖z‖) : ThetaLocalSource p z := by
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
  have hi : ‖z⁻¹‖ < 1 := by rw [norm_inv]; exact (inv_lt_one₀ (by positivity)).mpr hz
  have hp0 := padic_odd_isSquare_one_add hp
    ((0 : ℤ)*z⁻¹ + (50 : ℤ)*(z⁻¹)^2)
    (theta_small_quadratic_norm z⁻¹ hi 0 50)
  have hp1 := padic_odd_isSquare_one_add hp
    ((14 : ℤ)*z⁻¹ + (51 : ℤ)*(z⁻¹)^2)
    (theta_small_quadratic_norm z⁻¹ hi 14 51)
  have hp2 := padic_odd_isSquare_one_add hp
    ((-14 : ℤ)*z⁻¹ + (51 : ℤ)*(z⁻¹)^2)
    (theta_small_quadratic_norm z⁻¹ hi (-14) 51)
  obtain ⟨P, hP⟩ := theta_quadratic_square_of_normalized z 0 50 hz0 (by simpa [add_assoc] using hp0)
  obtain ⟨Q, hQ⟩ := theta_quadratic_square_of_normalized z 14 51 hz0 (by simpa [add_assoc] using hp1)
  obtain ⟨R, hR⟩ := theta_quadratic_square_of_normalized z (-14) 51 hz0 (by simpa [add_assoc] using hp2)
  exact ⟨P, Q, R, by simpa using hP, hQ, by simpa [sub_eq_add_neg] using hR⟩

#print axioms theta_odd_local_source
#print axioms theta_small_quadratic_norm
#print axioms theta_quadratic_square_of_normalized
end FourCorner
