import FourCorner.KernelProduct
import FourCorner.RadiusContent
import Mathlib.Tactic.FieldSimp
import FourCorner.CriticalSeventeenActual
import FourCorner.CriticalSeventeenFinite
import FourCorner.CriticalSeventeenPadic
import FourCorner.CriticalSeventeenCenter
import FourCorner.NoncriticalSeventeenCenter

namespace FourCorner

/-- Multiplying by a square denominator preserves a non-square obstruction. -/
theorem nonsquare_div_square {F : Type*} [Field F] {Q D : F}
    (hQ : ¬ IsSquare Q) (hD : D ≠ 0) : ¬ IsSquare (Q / D^2) := by
  intro h
  apply hQ
  have hh := h.mul (show IsSquare (D^2) from ⟨D, by ring⟩)
  simpa only [div_mul_cancel₀ _ (pow_ne_zero 2 hD)] using hh

namespace IntegralModel

private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- Opposite product of the four integer radii after their common content
has been removed. -/
def criticalProductNumerator (M : IntegralModel) : ℤ :=
  (M.A₀ / (M.radiusContent : ℤ)) * (M.A₃ / (M.radiusContent : ℤ)) +
    (M.A₁ / (M.radiusContent : ℤ)) * (M.A₂ / (M.radiusContent : ℤ))

/-- The common reduced denominator GH of the normalized integer radii. -/
def criticalProductDenominator (M : IntegralModel) : ℤ :=
  (M.radiusContent : ℤ) * M.reducedSide

theorem criticalProductDenominator_pos (M : IntegralModel) :
    0 < M.criticalProductDenominator := by
  exact mul_pos (by exact_mod_cast M.radiusContent_pos) M.reducedSide_pos

/-- The literal opposite-product parameter has the denominator-square form
used in the critical-prime reduction. -/
theorem oppositeProductSum_content_formula (M : IntegralModel) :
    M.oppositeProductSum = (M.criticalProductNumerator : ℚ) /
      (M.criticalProductDenominator : ℚ)^2 := by
  obtain ⟨h0,h1,h2,h3⟩ := M.normalized_radii_ratios
  unfold oppositeProductSum
  rw [h0,h1,h2,h3]
  simp only [criticalProductNumerator, criticalProductDenominator, Int.cast_add, Int.cast_mul,
    Int.cast_natCast]
  rw [div_mul_div_comm, div_mul_div_comm, ← add_div, pow_two]

/-- The finite obstruction is attached to the actual critical content,
including both possible coordinate roots of minus one. -/
theorem critical_seventeen_residues (M : IntegralModel) (hG : 17 ∣ M.radiusContent)
    (hcrit : padicValInt 17 M.L = 2 * padicValNat 17 M.radiusContent) :
    ¬ IsSquare (M.criticalProductNumerator : ZMod 17) ∧
    ¬ IsSquare (2 * (M.criticalProductNumerator : ZMod 17)) ∧
    (17 : ℤ) ∣ (M.criticalReducedRadius 0)^2 + (M.criticalReducedRadius 3)^2 ∧
    (17 : ℤ) ∣ (M.criticalReducedRadius 1)^2 + (M.criticalReducedRadius 2)^2 := by
  obtain ⟨hi,hb,h1,h2,h3⟩ := M.critical_seventeen_square_pattern hG hcrit
  obtain ⟨_,_,_,_,hn,hn2,h03,h12,_⟩ := seventeen_square_pattern
    (M.criticalReducedRadius 0) (M.criticalReducedRadius 1)
    (M.criticalReducedRadius 2) (M.criticalReducedRadius 3)
    M.criticalIota17 M.criticalShift17 hi hb h1 h2 h3
  refine ⟨?_,?_,?_,?_⟩
  · simpa [criticalProductNumerator, criticalReducedRadius, pairRadius] using hn
  · simpa [criticalProductNumerator, criticalReducedRadius, pairRadius] using hn2
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 17).mp
    push_cast
    exact h03
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 17).mp
    push_cast
    exact h12

theorem oppositeProductSum_content_formula_padic17 (M : IntegralModel) :
    (M.oppositeProductSum : ℚ_[17]) = (M.criticalProductNumerator : ℚ_[17]) /
      (M.criticalProductDenominator : ℚ_[17])^2 := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[17])) M.oppositeProductSum_content_formula
  push_cast at h
  exact h

/-- The actual completed 17-adic field excludes all four product-square
conditions at a critical content prime. -/
theorem critical_seventeen_nonsquares (M : IntegralModel) (hG : 17 ∣ M.radiusContent)
    (hcrit : padicValInt 17 M.L = 2 * padicValNat 17 M.radiusContent) :
    ¬ IsSquare (M.oppositeProductSum : ℚ_[17]) ∧
    ¬ IsSquare (2 * (M.oppositeProductSum : ℚ_[17])) ∧
    ¬ IsSquare ((M.oppositeProductSum : ℚ_[17]) + 1) ∧
    ¬ IsSquare (2 * ((M.oppositeProductSum : ℚ_[17]) + 1)) := by
  obtain ⟨hn,hn2,_,_⟩ := M.critical_seventeen_residues hG hcrit
  have hD : M.criticalProductDenominator ≠ 0 := ne_of_gt M.criticalProductDenominator_pos
  have hD17 : (M.criticalProductDenominator : ZMod 17) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 17).mpr
    exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hG) _
  have hDp : (M.criticalProductDenominator : ℚ_[17]) ≠ 0 := by exact_mod_cast hD
  have hnplus : ¬ IsSquare
      ((M.criticalProductNumerator + M.criticalProductDenominator^2 : ℤ) : ZMod 17) := by
    simpa only [Int.cast_add, Int.cast_pow, hD17, zero_pow (by decide : 2 ≠ 0), add_zero] using hn
  have hn2plus : ¬ IsSquare
      ((2 * (M.criticalProductNumerator + M.criticalProductDenominator^2) : ℤ) : ZMod 17) := by
    simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_add, Int.cast_pow,
      hD17, zero_pow (by decide : 2 ≠ 0), add_zero] using hn2
  have htplus : (M.oppositeProductSum : ℚ_[17]) + 1 =
      ((M.criticalProductNumerator + M.criticalProductDenominator^2 : ℤ) : ℚ_[17]) /
        (M.criticalProductDenominator : ℚ_[17])^2 := by
    rw [M.oppositeProductSum_content_formula_padic17]
    push_cast
    field_simp
  refine ⟨?_,?_,?_,?_⟩
  · rw [M.oppositeProductSum_content_formula_padic17]
    exact genuineQ17_div_sq_nonsquare_of_residue _ _ hD hn
  · rw [M.oppositeProductSum_content_formula_padic17]
    have hn2' : ¬ IsSquare ((2 * M.criticalProductNumerator : ℤ) : ZMod 17) := by
      simpa using hn2
    have h := genuineQ17_div_sq_nonsquare_of_residue
      (2 * M.criticalProductNumerator) M.criticalProductDenominator hD hn2'
    simpa only [Int.cast_mul, Int.cast_ofNat, mul_div_assoc] using h
  · rw [htplus]
    exact genuineQ17_div_sq_nonsquare_of_residue _ _ hD hnplus
  · rw [htplus]
    have h := genuineQ17_div_sq_nonsquare_of_residue
      (2 * (M.criticalProductNumerator + M.criticalProductDenominator^2))
      M.criticalProductDenominator hD hn2plus
    simpa only [Int.cast_mul, Int.cast_ofNat, mul_div_assoc] using h

/-- A rational product square forces seventeen to occur beyond the
critical depth whenever seventeen divides the common radius content. -/
theorem rational_product_square_seventeen_noncritical (M : IntegralModel)
    (hs : IsSquare M.oppositeProductSum ∨ IsSquare (2 * M.oppositeProductSum) ∨
      IsSquare (M.oppositeProductSum + 1) ∨ IsSquare (2 * (M.oppositeProductSum + 1)))
    (hG : 17 ∣ M.radiusContent) : (17 : ℤ) ∣ M.reducedSide := by
  by_contra hH
  have hG0 : (M.radiusContent : ℤ) ≠ 0 := by exact_mod_cast M.radiusContent_pos.ne'
  have hH0 : M.reducedSide ≠ 0 := M.reducedSide_pos.ne'
  have hfac := congrArg (padicValInt 17) M.reducedSide_factorization
  rw [padicValInt.mul (pow_ne_zero 2 hG0) hH0,
    padicValInt.eq_zero_of_not_dvd hH, add_zero] at hfac
  have hv : padicValInt 17 M.L = 2 * padicValNat 17 M.radiusContent := by
    simpa only [padicValInt, Int.natAbs_pow, Int.natAbs_natCast, padicValNat.pow] using hfac.symm
  obtain ⟨hn0,hn1,hn2,hn3⟩ := M.critical_seventeen_nonsquares hG hv
  have hmap {q : ℚ} (h : IsSquare q) : IsSquare (q : ℚ_[17]) := by
    obtain ⟨r,hr⟩ := h
    refine ⟨(r : ℚ_[17]),?_⟩
    exact_mod_cast hr
  rcases hs with hs | hs | hs | hs
  · exact hn0 (hmap hs)
  · exact hn1 (by simpa using hmap hs)
  · exact hn2 (by simpa using hmap hs)
  · exact hn3 (by simpa using hmap hs)

/-- The complete critical-seventeen conclusion of Theorem thm:crit-17,
with the four exclusions in the actual completed field and the center depth. -/
theorem critical_seventeen (M : IntegralModel) (hG : 17 ∣ M.radiusContent)
    (hcrit : padicValInt 17 M.L = 2 * padicValNat 17 M.radiusContent) :
    (¬ IsSquare (M.oppositeProductSum : ℚ_[17]) ∧
      ¬ IsSquare (2 * (M.oppositeProductSum : ℚ_[17])) ∧
      ¬ IsSquare ((M.oppositeProductSum : ℚ_[17]) + 1) ∧
      ¬ IsSquare (2 * ((M.oppositeProductSum : ℚ_[17]) + 1))) ∧
    (17 : ℤ) ∣ (M.criticalReducedRadius 0)^2 + (M.criticalReducedRadius 3)^2 ∧
    (17 : ℤ) ∣ (M.criticalReducedRadius 1)^2 + (M.criticalReducedRadius 2)^2 ∧
    (17 : ℤ)^(2 * padicValNat 17 M.radiusContent + 1) ∣
      (2*M.X-M.L)^2 + (2*M.Y-M.L)^2 := by
  have hr := M.critical_seventeen_residues hG hcrit
  exact ⟨M.critical_seventeen_nonsquares hG hcrit, hr.2.2.1, hr.2.2.2,
    M.critical_seventeen_center_divisibility hG hcrit⟩

end IntegralModel
end FourCorner
#print axioms FourCorner.IntegralModel.oppositeProductSum_content_formula

#print axioms FourCorner.IntegralModel.critical_seventeen_residues
#print axioms FourCorner.IntegralModel.critical_seventeen_nonsquares

#print axioms FourCorner.IntegralModel.rational_product_square_seventeen_noncritical

#print axioms FourCorner.IntegralModel.critical_seventeen
