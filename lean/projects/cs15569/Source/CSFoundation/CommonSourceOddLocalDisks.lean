import CSFoundation.CommonSourceOddLocal

set_option autoImplicit false
namespace FourCorner
variable {p : ℕ} [Fact p.Prime]

/-- The norm of two at any odd prime. -/
theorem csOdd_norm_two (hp : p ≠ 2) : ‖(2 : ℚ_[p])‖ = 1 := by
  apply Padic.norm_natCast_eq_one_iff.mpr
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by
    intro h
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h))

private theorem csOdd_norm_add_dominant {x t : ℚ_[p]} (h : ‖t‖ < ‖x‖) :
    ‖x + t‖ = ‖x‖ := by
  rw [Padic.add_eq_max_of_ne (ne_of_gt h), max_eq_left h.le]

/-- Torsion translation formulas on the infinity disk. These strict norm
inequalities cover every finite depth of reduction to infinity. -/
theorem csOdd_torsion_disks_from_infinity (hp : p ≠ 2) {n u : ℚ_[p]}
    (hn : ‖n‖ = 1) (hu : 1 < ‖u‖) :
    ‖-n ^ 2 / u‖ < 1 ∧
    ‖(n + 2 * n ^ 2 / (u - n)) - n‖ < 1 ∧
    ‖(-n + 2 * n ^ 2 / (u + n)) + n‖ < 1 := by
  have hum : ‖u - n‖ = ‖u‖ := by
    simpa only [sub_eq_add_neg] using
      csOdd_norm_add_dominant (x := u) (t := -n) (by simpa [hn] using hu)
  have hup : ‖u + n‖ = ‖u‖ :=
    csOdd_norm_add_dominant (by simpa [hn] using hu)
  have hu0 : 0 < ‖u‖ := lt_trans zero_lt_one hu
  have hi : 1 / ‖u‖ < 1 := (div_lt_one hu0).mpr hu
  constructor
  · simpa only [norm_div, norm_neg, norm_pow, hn, one_pow] using hi
  constructor
  · have he : (n + 2 * n ^ 2 / (u - n)) - n = 2 * n ^ 2 / (u - n) := by ring
    rw [he, norm_div, norm_mul, norm_pow, csOdd_norm_two hp, hn, one_pow, mul_one, hum]
    exact hi
  · have he : (-n + 2 * n ^ 2 / (u + n)) + n = 2 * n ^ 2 / (u + n) := by ring
    rw [he, norm_div, norm_mul, norm_pow, csOdd_norm_two hp, hn, one_pow, mul_one, hup]
    exact hi

/-- Torsion translations by `T±` interchange the two nonzero torsion disks
when the original point reduces to `T₀`; exact `T₀` is included. -/
theorem csOdd_torsion_disks_from_zero (hp : p ≠ 2) {n u : ℚ_[p]}
    (hn : ‖n‖ = 1) (hu : ‖u‖ < 1) :
    ‖(n + 2 * n ^ 2 / (u - n)) + n‖ < 1 ∧
    ‖(-n + 2 * n ^ 2 / (u + n)) - n‖ < 1 := by
  have hum : ‖u - n‖ = 1 := by
    rw [sub_eq_add_neg, add_comm]
    exact (csOdd_norm_add_dominant (x := -n) (t := u) (by simpa [hn] using hu)).trans
      (by simpa using hn)
  have hup : ‖u + n‖ = 1 := by
    rw [add_comm]
    exact (csOdd_norm_add_dominant (by simpa [hn] using hu)).trans hn
  have hum0 : u - n ≠ 0 := by intro h; rw [h, norm_zero] at hum; norm_num at hum
  have hup0 : u + n ≠ 0 := by intro h; rw [h, norm_zero] at hup; norm_num at hup
  constructor
  · have he : (n + 2 * n ^ 2 / (u - n)) + n = 2 * n * u / (u - n) := by
      field_simp
      ring
    rw [he, norm_div, norm_mul, norm_mul, csOdd_norm_two hp, hn, hum]
    simpa using hu
  · have he : (-n + 2 * n ^ 2 / (u + n)) - n = -(2 * n * u) / (u + n) := by
      field_simp
      ring
    rw [he, norm_div, norm_neg, norm_mul, norm_mul, csOdd_norm_two hp, hn, hup]
    simpa using hu

/-- Translation by `T₀` takes every nonzero point of its own residue disk
to the infinity disk. The excluded zero abscissa is exactly the projective exception. -/
theorem csOdd_torsion_zero_to_infinity {n u : ℚ_[p]}
    (hn : ‖n‖ = 1) (hu : ‖u‖ < 1) (hu0 : u ≠ 0) : 1 < ‖-n ^ 2 / u‖ := by
  rw [norm_div, norm_neg, norm_pow, hn, one_pow]
  exact (one_lt_div (norm_pos_iff.mpr hu0)).mpr hu

end FourCorner

#print axioms FourCorner.csOdd_torsion_disks_from_infinity
#print axioms FourCorner.csOdd_torsion_disks_from_zero
#print axioms FourCorner.csOdd_torsion_zero_to_infinity
