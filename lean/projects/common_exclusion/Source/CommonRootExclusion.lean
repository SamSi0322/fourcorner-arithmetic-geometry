import FourCorner.CommonRootMatrix
import FourCorner.CommonRoot37
import CommonRoot37Discriminant

set_option autoImplicit false

namespace FourCorner

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- Once the discriminant kernel is a local square, the two global classes
left by the matrix rank test are both incompatible with a square common
coordinate whenever two is a local nonsquare. -/
theorem commonRoot_two_classes_square_contradiction {K : Type*} [Field K]
    {ell Δ q : K} (hΔ0 : Δ ≠ 0) (hq : q ≠ 0)
    (hΔ : IsSquare Δ) (hell : IsSquare ell) (h2 : ¬ IsSquare (2 : K))
    (hc : ell = 2 * q ^ 2 ∨ ell = 2 * Δ * q ^ 2) : False := by
  have hs := hell.div (IsSquare.sq q)
  rcases hc with hc | hc
  · rw [hc, mul_div_cancel_right₀ _ (pow_ne_zero 2 hq)] at hs
    exact h2 hs
  · rw [hc, mul_div_cancel_right₀ _ (pow_ne_zero 2 hq)] at hs
    have htwo := hs.div hΔ
    rw [mul_div_cancel_right₀ _ hΔ0] at htwo
    exact h2 htwo

/-- The full matrix and 37-adic obstruction excludes every actual ordered
rational source on the affine four-root curve. This theorem makes no claim
about points added by a projective compactification. -/
theorem common_root_exclusion {t : ℚ} (ht : 1 < t) {r : ℕ}
    (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hpmod : ∀ i, p i % 8 = 1 ∨ p i % 8 = 7)
    (hDelta_gt : 1 < ∏ i, p i) (hDelta : (∏ i, p i) % 8 = 1) {qD : ℚ}
    (hd : t ^ 2 - 1 = ((∏ i, p i : ℕ) : ℚ) * qD ^ 2)
    (hrank : (primeLegendreMatrix p hp).rank = r - 1)
    (htint : ‖(t : ℚ_[37])‖ ≤ 1)
    (htres : padicResidue (t : ℚ_[37]) htint = 14 ∨
      padicResidue (t : ℚ_[37]) htint = -14 ∨
      padicResidue (t : ℚ_[37]) htint = 16 ∨
      padicResidue (t : ℚ_[37]) htint = -16) :
    IsEmpty (CommonRootSource ℚ t) := by
  refine ⟨fun S => ?_⟩
  have hqD : qD ≠ 0 := by
    intro hz
    rw [hz] at hd
    norm_num at hd
    nlinarith
  have hqDP : (qD : ℚ_[37]) ≠ 0 := by exact_mod_cast hqD
  have hΔ0 : (∏ i, p i) ≠ 0 := by omega
  have hΔP0 : ((∏ i, p i : ℕ) : ℚ_[37]) ≠ 0 := by exact_mod_cast hΔ0
  have hdP : (t : ℚ_[37]) ^ 2 - 1 =
      ((∏ i, p i : ℕ) : ℚ_[37]) * (qD : ℚ_[37]) ^ 2 := by exact_mod_cast hd
  have hds : IsSquare ((t : ℚ_[37]) ^ 2 - 1) :=
    commonRoot37_discriminant_isSquare htint htres
  have hΔs := hds.div (IsSquare.sq (qD : ℚ_[37]))
  rw [hdP, mul_div_cancel_right₀ _ (pow_ne_zero 2 hqDP)] at hΔs
  have hell := (S.toPadic 37).ell_isSquare_37_field htint htres
  obtain ⟨q, hq, hc⟩ :=
    (S.residue_matrix_proposition ht p hp hinj hpmod hDelta_gt hDelta hd).2 hrank
  have hqP : (q : ℚ_[37]) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  apply commonRoot_two_classes_square_contradiction hΔP0 hqP hΔs hell
    commonRoot37_two_not_isSquare
  change (S.ell : ℚ_[37]) = _ ∨ (S.ell : ℚ_[37]) = _
  rcases hc with hc | hc
  · left
    exact_mod_cast hc
  · right
    exact_mod_cast hc

end FourCorner

#print axioms FourCorner.commonRoot_two_classes_square_contradiction
#print axioms FourCorner.common_root_exclusion
