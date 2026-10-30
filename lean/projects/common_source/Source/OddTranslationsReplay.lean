import CSFoundation.CommonSourceOddLocalResidue

set_option autoImplicit false

namespace FourCorner

/-- Integral addition to a quotient with unit denominator commutes with
reduction in the actual completed field. -/
theorem commonSource_add_ratio_integral_residue {p : ℕ} [Fact p.Prime]
    (s u v : ℤ_[p]) (hv : PadicInt.toZMod v ≠ 0) :
    ∃ h : ‖(s : ℚ_[p]) + (u : ℚ_[p]) / (v : ℚ_[p])‖ ≤ 1,
      padicResidue ((s : ℚ_[p]) + (u : ℚ_[p]) / (v : ℚ_[p])) h =
        PadicInt.toZMod s + PadicInt.toZMod u / PadicInt.toZMod v := by
  have hv0 : (v : ℚ_[p]) ≠ 0 := by
    intro hz
    have hvnorm := padicInt_norm_coe_eq_one_of_residue_ne_zero v hv
    rw [hz, norm_zero] at hvnorm
    norm_num at hvnorm
  have hquot : ((s * v + u : ℤ_[p]) : ℚ_[p]) / (v : ℚ_[p]) =
      (s : ℚ_[p]) + (u : ℚ_[p]) / (v : ℚ_[p]) := by
    push_cast
    field_simp
  have hred : PadicInt.toZMod (s * v + u) / PadicInt.toZMod v =
      PadicInt.toZMod s + PadicInt.toZMod u / PadicInt.toZMod v := by
    simp only [map_add, map_mul, add_div, mul_div_cancel_right₀ _ hv]
  have H := commonSource_ratio_integral_residue (s * v + u) v hv
  simpa only [hquot, hred] using H


theorem commonSource_sqrt_neg_one_ne_zero {K : Type*} [Field K]
    {i : K} (hi : i ^ 2 = -1) : i ≠ 0 := by
  intro h
  simp [h] at hi

theorem commonSource_sqrt_neg_one_sub_one_ne_zero {K : Type*} [Field K]
    (h20 : (2 : K) ≠ 0) {i : K} (hi : i ^ 2 = -1) : i - 1 ≠ 0 := by
  intro h
  have hi1 : i = 1 := by linear_combination h
  rw [hi1] at hi
  apply h20
  linear_combination hi

theorem commonSource_cyclic_denominator_ne_zero {K : Type*} [Field K]
    (h20 : (2 : K) ≠ 0) {n i : K} (hn0 : n ≠ 0) (hi : i ^ 2 = -1) :
    n * i ≠ 0 ∧ n * i - n ≠ 0 ∧ n * i + n ≠ 0 := by
  refine ⟨mul_ne_zero hn0 (commonSource_sqrt_neg_one_ne_zero hi), ?_, ?_⟩
  · simpa only [mul_sub, mul_one] using
      mul_ne_zero hn0 (commonSource_sqrt_neg_one_sub_one_ne_zero h20 hi)
  · simpa only [mul_add, mul_one] using
      mul_ne_zero hn0 (commonSource_sqrt_neg_one_add_one_ne_zero h20 hi)

theorem commonSource_cyclic_translation_zero_identity {K : Type*} [Field K]
    {n i : K} (hn0 : n ≠ 0) (hi : i ^ 2 = -1) :
    -n ^ 2 / (n * i) = n * i := by
  apply (div_eq_iff (mul_ne_zero hn0 (commonSource_sqrt_neg_one_ne_zero hi))).mpr
  linear_combination -n ^ 2 * hi

theorem commonSource_cyclic_translation_plus_identity {K : Type*} [Field K]
    (h20 : (2 : K) ≠ 0) {n i : K} (hn0 : n ≠ 0) (hi : i ^ 2 = -1) :
    n + 2 * n ^ 2 / (n * i - n) = -n * i := by
  have hd := (commonSource_cyclic_denominator_ne_zero h20 hn0 hi).2.1
  have hdiv : 2 * n ^ 2 / (n * i - n) = -n * i - n := by
    apply (div_eq_iff hd).mpr
    linear_combination n ^ 2 * hi
  rw [hdiv]
  ring

theorem commonSource_cyclic_translation_minus_identity {K : Type*} [Field K]
    (h20 : (2 : K) ≠ 0) {n i : K} (hn0 : n ≠ 0) (hi : i ^ 2 = -1) :
    -n + 2 * n ^ 2 / (n * i + n) = -n * i := by
  have hd := (commonSource_cyclic_denominator_ne_zero h20 hn0 hi).2.2
  have hdiv : 2 * n ^ 2 / (n * i + n) = -n * i + n := by
    apply (div_eq_iff hd).mpr
    linear_combination n ^ 2 * hi
  rw [hdiv]
  ring

/-- Translation by the zero two-torsion point fixes the cyclic abscissa
residue. This proves integrality of the actual translated field expression. -/
theorem commonSource_cyclic_translation_zero_residue {p : ℕ} [Fact p.Prime]
    (u n : ℤ_[p]) (i : ZMod p) (hn : PadicInt.toZMod n ≠ 0)
    (hi : i ^ 2 = -1) (hu : PadicInt.toZMod u = PadicInt.toZMod n * i) :
    ∃ h : ‖-(n : ℚ_[p]) ^ 2 / (u : ℚ_[p])‖ ≤ 1,
      padicResidue (-(n : ℚ_[p]) ^ 2 / (u : ℚ_[p])) h =
        PadicInt.toZMod n * i := by
  have hd : PadicInt.toZMod u ≠ 0 := by
    rw [hu]
    exact mul_ne_zero hn (commonSource_sqrt_neg_one_ne_zero hi)
  have H := commonSource_ratio_integral_residue (-n ^ 2) u hd
  have hres := commonSource_cyclic_translation_zero_identity hn hi
  push_cast at H
  simpa only [map_neg, map_pow, hu, hres] using H

/-- Translation by positive two-torsion reverses the cyclic abscissa
residue, at every p-adic depth. -/
theorem commonSource_cyclic_translation_plus_residue {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (u n : ℤ_[p]) (i : ZMod p) (hn : PadicInt.toZMod n ≠ 0)
    (hi : i ^ 2 = -1) (hu : PadicInt.toZMod u = PadicInt.toZMod n * i) :
    ∃ h : ‖(n : ℚ_[p]) + 2 * (n : ℚ_[p]) ^ 2 /
        ((u : ℚ_[p]) - (n : ℚ_[p]))‖ ≤ 1,
      padicResidue ((n : ℚ_[p]) + 2 * (n : ℚ_[p]) ^ 2 /
        ((u : ℚ_[p]) - (n : ℚ_[p]))) h = -(PadicInt.toZMod n * i) := by
  have h20 : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp)
  have hd : PadicInt.toZMod (u - n) ≠ 0 := by
    simpa only [map_sub, hu] using (commonSource_cyclic_denominator_ne_zero h20 hn hi).2.1
  have H := commonSource_add_ratio_integral_residue n (2 * n ^ 2) (u - n) hd
  have hcast : ((2 : ℤ_[p]) : ℚ_[p]) = 2 := by rfl
  have hres := commonSource_cyclic_translation_plus_identity h20 hn hi
  push_cast at H
  simpa only [map_sub, map_mul, map_ofNat, map_pow, hu, hres, neg_mul, hcast] using H

/-- Translation by negative two-torsion also reverses the cyclic abscissa
residue, with the actual rational translation expression remaining integral. -/
theorem commonSource_cyclic_translation_minus_residue {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (u n : ℤ_[p]) (i : ZMod p) (hn : PadicInt.toZMod n ≠ 0)
    (hi : i ^ 2 = -1) (hu : PadicInt.toZMod u = PadicInt.toZMod n * i) :
    ∃ h : ‖-(n : ℚ_[p]) + 2 * (n : ℚ_[p]) ^ 2 /
        ((u : ℚ_[p]) + (n : ℚ_[p]))‖ ≤ 1,
      padicResidue (-(n : ℚ_[p]) + 2 * (n : ℚ_[p]) ^ 2 /
        ((u : ℚ_[p]) + (n : ℚ_[p]))) h = -(PadicInt.toZMod n * i) := by
  have h20 : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp)
  have hd : PadicInt.toZMod (u + n) ≠ 0 := by
    simpa only [map_add, hu] using (commonSource_cyclic_denominator_ne_zero h20 hn hi).2.2
  have H := commonSource_add_ratio_integral_residue (-n) (2 * n ^ 2) (u + n) hd
  have hcast : ((2 : ℤ_[p]) : ℚ_[p]) = 2 := by rfl
  have hres := commonSource_cyclic_translation_minus_identity h20 hn hi
  push_cast at H
  simpa only [map_neg, map_add, map_mul, map_ofNat, map_pow, hu, hres, neg_mul, hcast] using H

end FourCorner

#print axioms FourCorner.commonSource_cyclic_translation_zero_residue
#print axioms FourCorner.commonSource_cyclic_translation_plus_residue
#print axioms FourCorner.commonSource_cyclic_translation_minus_residue
