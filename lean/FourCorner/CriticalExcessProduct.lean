import FourCorner.CriticalSeventeen

set_option autoImplicit false

namespace FourCorner.IntegralModel

/-- The content formula transports the literal rational opposite-product sum
into the actual completed field at any prime. -/
theorem oppositeProductSum_content_formula_padic (M : IntegralModel)
    {p : ℕ} [Fact p.Prime] :
    (M.oppositeProductSum : ℚ_[p]) = (M.criticalProductNumerator : ℚ_[p]) /
      (M.criticalProductDenominator : ℚ_[p]) ^ 2 := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[p])) M.oppositeProductSum_content_formula
  push_cast at h
  exact h

/-- A rational square among the four opposite-product expressions forces a
square residue of `Q` or `2Q` at every prime dividing the actual radius content.
The proof clears the common square denominator in `ℚ_[p]` and reduces an
integral `p`-adic square root. No critical-depth hypothesis is required. -/
theorem rational_product_square_residue (M : IntegralModel) {p : ℕ}
    (hp : p.Prime) (hG : p ∣ M.radiusContent)
    (hs : IsSquare M.oppositeProductSum ∨ IsSquare (2 * M.oppositeProductSum) ∨
      IsSquare (M.oppositeProductSum + 1) ∨ IsSquare (2 * (M.oppositeProductSum + 1))) :
    IsSquare (M.criticalProductNumerator : ZMod p) ∨
      IsSquare (2 * (M.criticalProductNumerator : ZMod p)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hD : M.criticalProductDenominator ≠ 0 :=
    ne_of_gt M.criticalProductDenominator_pos
  have hDp : (M.criticalProductDenominator : ℚ_[p]) ≠ 0 := by exact_mod_cast hD
  have hDmod : (M.criticalProductDenominator : ZMod p) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
    exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hG) _
  have hformula := M.oppositeProductSum_content_formula_padic (p := p)
  have hplus : (M.oppositeProductSum : ℚ_[p]) + 1 =
      ((M.criticalProductNumerator + M.criticalProductDenominator ^ 2 : ℤ) : ℚ_[p]) /
        (M.criticalProductDenominator : ℚ_[p]) ^ 2 := by
    rw [hformula]
    push_cast
    field_simp
  have hmap {q : ℚ} (hq : IsSquare q) : IsSquare (q : ℚ_[p]) := by
    obtain ⟨r, hr⟩ := hq
    refine ⟨(r : ℚ_[p]), ?_⟩
    exact_mod_cast hr
  have hclear (N : ℤ)
      (hN : IsSquare ((N : ℚ_[p]) / (M.criticalProductDenominator : ℚ_[p]) ^ 2)) :
      IsSquare (N : ZMod p) := by
    apply isSquare_zmod_of_isSquare_padic N
    have h := hN.mul (IsSquare.sq (M.criticalProductDenominator : ℚ_[p]))
    simpa only [div_mul_cancel₀ _ (pow_ne_zero 2 hDp)] using h
  rcases hs with hs | hs | hs | hs
  · left
    apply hclear M.criticalProductNumerator
    rw [← hformula]
    exact hmap hs
  · right
    have ht := hmap hs
    push_cast at ht
    rw [hformula] at ht
    have hc := hclear (2 * M.criticalProductNumerator) (by
      simpa only [Int.cast_mul, Int.cast_ofNat, mul_div_assoc] using ht)
    simpa only [Int.cast_mul, Int.cast_ofNat] using hc
  · left
    have ht := hmap hs
    push_cast at ht
    rw [hplus] at ht
    have hc := hclear (M.criticalProductNumerator + M.criticalProductDenominator ^ 2) ht
    simpa only [Int.cast_add, Int.cast_pow, hDmod,
      zero_pow (by decide : 2 ≠ 0), add_zero] using hc
  · right
    have ht := hmap hs
    push_cast at ht
    rw [hplus] at ht
    have hc := hclear (2 * (M.criticalProductNumerator + M.criticalProductDenominator ^ 2))
      (by simpa only [Int.cast_mul, Int.cast_ofNat, mul_div_assoc] using ht)
    simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_add, Int.cast_pow, hDmod,
      zero_pow (by decide : 2 ≠ 0), add_zero] using hc

end FourCorner.IntegralModel

#print axioms FourCorner.IntegralModel.rational_product_square_residue
