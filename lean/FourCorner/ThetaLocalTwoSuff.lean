import FourCorner.ThetaLocalHensel
import FourCorner.ThetaLocalRootAssembly
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

set_option autoImplicit false

namespace FourCorner

/-- Every integral dyadic u has u(7+51u) in the maximal ideal. -/
theorem theta_two_even_polynomial (u : ℤ_[2]) :
    ‖u * (7 + 51 * u)‖ < 1 ∧ ‖u * (-7 + 51 * u)‖ < 1 := by
  have hpoly : ∀ v : ZMod 2, v * (7 + 51 * v) = 0 ∧ v * (-7 + 51 * v) = 0 := by
    intro v
    fin_cases v <;> decide
  have hplus : PadicInt.toZMod (u * (7 + 51 * u)) = 0 := by
    simpa only [map_mul, map_add, map_ofNat] using (hpoly (PadicInt.toZMod u)).1
  have hminus : PadicInt.toZMod (u * (-7 + 51 * u)) = 0 := by
    simpa only [map_mul, map_add, map_neg, map_ofNat] using (hpoly (PadicInt.toZMod u)).2
  have lift (x : ℤ_[2]) (hx : PadicInt.toZMod x = 0) : ‖x‖ < 1 := by
    have hm : x ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
      exact hx
    simpa only [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] using hm
  exact ⟨lift _ hplus, lift _ hminus⟩

/-- The inverse parameter is twice a dyadic integer, including valuation exactly one. -/
theorem theta_two_half_integral (a : ℚ_[2]) (ha : ‖a‖ < 1) : ‖a / 2‖ ≤ 1 := by
  have hb : ‖a‖ ≤ (1/2 : ℝ) := by
    have hh := (Padic.norm_lt_pow_iff_norm_le_pow_sub_one a 0).mp
      (by simpa using ha)
    norm_num at hh
    exact hh
  rw [norm_div]
  have htwo : ‖(2 : ℚ_[2])‖ = (1/2 : ℝ) := by simpa using (Padic.norm_p (p := 2))
  rw [htwo]
  linarith

/-- Exact dyadic cancellation at the first denominator depth makes all three
perturbations small enough for Hensel's square-root criterion. -/
theorem theta_two_perturbation_bounds (a : ℚ_[2]) (ha : ‖a‖ < 1) :
    ‖50*a^2‖ < (1/4 : ℝ) ∧
    ‖14*a+51*a^2‖ < (1/4 : ℝ) ∧
    ‖-14*a+51*a^2‖ < (1/4 : ℝ) := by
  let u : ℤ_[2] := ⟨a/2, theta_two_half_integral a ha⟩
  have hau : a = 2*(u : ℚ_[2]) := by dsimp [u]; field_simp
  have hu : ‖(u : ℚ_[2])‖ ≤ 1 := u.property
  have htwo : ‖(2 : ℚ_[2])‖ = (1/2 : ℝ) := by simpa using (Padic.norm_p (p := 2))
  have hfour : ‖(4 : ℚ_[2])‖ = (1/4 : ℝ) := by
    calc
      _ = ‖(2 : ℚ_[2])^2‖ := by norm_num
      _ = _ := by rw [norm_pow, htwo]; norm_num
  have height : ‖(8 : ℚ_[2])‖ = (1/8 : ℝ) := by
    calc
      _ = ‖(2 : ℚ_[2])^3‖ := by norm_num
      _ = _ := by rw [norm_pow, htwo]; norm_num
  have h25 : ‖(25 : ℚ_[2])‖ ≤ 1 := by
    exact le_of_eq ((Padic.norm_natCast_eq_one_iff (p := 2) (n := 25)).mpr (by decide))
  have h50 : ‖50*a^2‖ ≤ (1/8 : ℝ) := by
    rw [show (50:ℚ_[2])*a^2 = 8*(25*(u:ℚ_[2])^2) by rw [hau]; ring]
    rw [norm_mul, norm_mul, norm_pow, height]
    have huu : ‖(u : ℚ_[2])‖^2 ≤ 1 := by nlinarith [norm_nonneg (u : ℚ_[2])]
    have := mul_le_one₀ h25 (sq_nonneg _) huu
    nlinarith
  have he := theta_two_even_polynomial u
  have hp : ‖(u : ℚ_[2])*(7+51*(u : ℚ_[2]))‖ < 1 := by
    simpa only [PadicInt.norm_def, PadicInt.coe_mul, PadicInt.coe_add,
      show ((7:ℤ_[2]):ℚ_[2]) = 7 from rfl,
      show ((51:ℤ_[2]):ℚ_[2]) = 51 from rfl] using he.1
  have hm : ‖(u : ℚ_[2])*(-7+51*(u : ℚ_[2]))‖ < 1 := by
    simpa only [PadicInt.norm_def, PadicInt.coe_mul, PadicInt.coe_add,
      PadicInt.coe_neg, show ((7:ℤ_[2]):ℚ_[2]) = 7 from rfl,
      show ((51:ℤ_[2]):ℚ_[2]) = 51 from rfl] using he.2
  refine ⟨by linarith, ?_, ?_⟩
  · rw [show (14:ℚ_[2])*a+51*a^2 = 4*((u:ℚ_[2])*(7+51*(u:ℚ_[2]))) by
      rw [hau]; ring]
    rw [norm_mul, hfour]
    linarith
  · rw [show (-14:ℚ_[2])*a+51*a^2 = 4*((u:ℚ_[2])*(-7+51*(u:ℚ_[2]))) by
      rw [hau]; ring]
    rw [norm_mul, hfour]
    linarith

/-- Full dyadic sufficiency: every parameter of negative valuation admits
all three roots simultaneously in the actual field Q_2. -/
theorem theta_two_source_of_norm_gt_one (z : ℚ_[2]) (hz : 1 < ‖z‖) :
    ∃ P Q R : ℚ_[2], P^2 = z^2+50 ∧
      Q^2 = z^2+14*z+51 ∧ R^2 = z^2-14*z+51 := by
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
  have ha : ‖z⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz
  obtain ⟨hP, hQ, hR⟩ := theta_two_perturbation_bounds (z⁻¹) ha
  apply theta_roots_of_normalized_isSquare hz0
  · exact padic_two_isSquare_one_add _ hP
  · rw [show (1 + 14 * z⁻¹ + 51 * (z⁻¹)^2 : ℚ_[2]) =
        1 + (14 * z⁻¹ + 51 * (z⁻¹)^2) by ring]
    exact padic_two_isSquare_one_add _ hQ
  · rw [show (1 - 14 * z⁻¹ + 51 * (z⁻¹)^2 : ℚ_[2]) =
        1 + (-14 * z⁻¹ + 51 * (z⁻¹)^2) by ring]
    exact padic_two_isSquare_one_add _ hR

#print axioms theta_two_source_of_norm_gt_one
#print axioms theta_two_even_polynomial
#print axioms theta_two_half_integral
#print axioms theta_two_perturbation_bounds
end FourCorner
