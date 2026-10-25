import FourCorner.ThetaLocalHensel

set_option autoImplicit false

namespace FourCorner

/-- An integer congruent to one modulo eight is a square in the actual dyadic field. -/
theorem padic_two_isSquare_int_of_eight_dvd_sub_one (Δ : ℤ)
    (hΔ : (8 : ℤ) ∣ Δ - 1) : IsSquare (Δ : ℚ_[2]) := by
  have hbound : ‖((Δ - 1 : ℤ) : ℚ_[2])‖ ≤ (1 / 8 : ℝ) := by
    have hb := (Padic.norm_int_le_pow_iff_dvd (p := 2) (Δ - 1) 3).mpr
      (by simpa using hΔ)
    norm_num at hb ⊢
    exact hb
  have hsmall : ‖((Δ - 1 : ℤ) : ℚ_[2])‖ < (1 / 4 : ℝ) := by
    linarith
  simpa using padic_two_isSquare_one_add ((Δ - 1 : ℤ) : ℚ_[2]) hsmall

/-- Integer congruence form of the dyadic square criterion. -/
theorem padic_two_isSquare_int_of_modEq_one (Δ : ℤ) (hΔ : Int.ModEq 8 Δ 1) :
    IsSquare (Δ : ℚ_[2]) :=
  padic_two_isSquare_int_of_eight_dvd_sub_one Δ hΔ.symm.dvd

/-- Natural congruence form of the dyadic square criterion. -/
theorem padic_two_isSquare_nat_of_modEq_one (Δ : ℕ) (hΔ : Nat.ModEq 8 Δ 1) :
    IsSquare (Δ : ℚ_[2]) := by
  simpa using padic_two_isSquare_int_of_eight_dvd_sub_one (Δ : ℤ)
    (by simpa using hΔ.symm.dvd)

/-- Remainder form, convenient for finite modulo-eight calculations. -/
theorem padic_two_isSquare_nat_of_mod_eight_eq_one (Δ : ℕ) (hΔ : Δ % 8 = 1) :
    IsSquare (Δ : ℚ_[2]) :=
  padic_two_isSquare_nat_of_modEq_one Δ (by simpa [Nat.ModEq] using hΔ)

/-- The dyadic square property is unchanged upon multiplication by a rational square. -/
theorem padic_two_isSquare_rat_of_int_squareclass (d q : ℚ) (Δ : ℤ)
    (hd : d = (Δ : ℚ) * q ^ 2) (hΔ : (8 : ℤ) ∣ Δ - 1) :
    IsSquare (d : ℚ_[2]) := by
  rw [hd]
  push_cast
  exact (padic_two_isSquare_int_of_eight_dvd_sub_one Δ hΔ).mul (IsSquare.sq _)

/-- A natural squareclass representative congruent to one modulo eight gives a
genuine square root of the represented rational in the dyadic field. -/
theorem padic_two_isSquare_rat_of_nat_squareclass (d q : ℚ) (Δ : ℕ)
    (hd : d = (Δ : ℚ) * q ^ 2) (hΔ : Δ % 8 = 1) :
    IsSquare (d : ℚ_[2]) := by
  rw [hd]
  push_cast
  exact (padic_two_isSquare_nat_of_mod_eight_eq_one Δ hΔ).mul (IsSquare.sq _)

end FourCorner

#print axioms FourCorner.padic_two_isSquare_int_of_eight_dvd_sub_one
#print axioms FourCorner.padic_two_isSquare_rat_of_int_squareclass
#print axioms FourCorner.padic_two_isSquare_nat_of_modEq_one
#print axioms FourCorner.padic_two_isSquare_rat_of_nat_squareclass
