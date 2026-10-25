import FourCorner.CommonRootPadicVal
import FourCorner.CommonRootSource
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace FourCorner

private instance prime2 : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Every rational dyadic t of valuation at least two has nonsquare t²−1.
The residue proof takes place in Z2/8, after exhibiting t as four times a
2-adic integer and proving that a hypothetical square root is integral. -/
theorem commonRoot_dyadic_d_nonsquare_of_val_ge_two (t : ℚ_[2])
    (ht : 2 ≤ t.valuation) : ¬ IsSquare (t ^ 2 - 1) := by
  have ht0 : t ≠ 0 := by intro h; simp [h] at ht
  have hfour : (4 : ℚ_[2]).valuation = 2 := by
    have h := Padic.valuation_pow (2 : ℚ_[2]) 2
    norm_num [Padic.valuation_p] at h ⊢
    exact h
  have hfour0 : (4 : ℚ_[2]) ≠ 0 := by norm_num
  have hu : ‖t / 4‖ ≤ 1 := by
    rw [Padic.norm_le_one_iff_val_nonneg,
      commonRoot_val_div ht0 hfour0, hfour]
    omega
  let u : ℤ_[2] := ⟨t / 4, hu⟩
  have htu : (4 : ℚ_[2]) * (u : ℚ_[2]) = t := by
    change 4 * (t / 4) = t
    field_simp
  intro hs
  obtain ⟨r, hr⟩ := hs
  let d : ℤ_[2] := (4 * u) ^ 2 - 1
  have hd : (d : ℚ_[2]) = t ^ 2 - 1 := by
    change ((4 : ℚ_[2]) * (u : ℚ_[2])) ^ 2 - 1 = t ^ 2 - 1
    rw [htu]
  have hrnorm : ‖r‖ ≤ 1 := by
    have hsq : ‖r‖ * ‖r‖ ≤ 1 := by
      rw [← norm_mul, ← hr, ← hd]
      exact d.2
    nlinarith [norm_nonneg r]
  let ri : ℤ_[2] := ⟨r, hrnorm⟩
  have he : (4 * u) ^ 2 - 1 = ri ^ 2 := by
    apply PadicInt.ext
    change ((4 : ℚ_[2]) * (u : ℚ_[2])) ^ 2 - 1 = r ^ 2
    rw [htu]
    simpa only [pow_two] using hr
  have he8 := congrArg (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) he
  simp only [map_sub, map_pow, map_mul, map_ofNat, map_one] at he8
  change (4 * (PadicInt.toZModPow 3 u : ZMod 8)) ^ 2 - 1 =
    (PadicInt.toZModPow 3 ri : ZMod 8) ^ 2 at he8
  rw [mul_pow] at he8
  have hzero : (4 : ZMod 8) ^ 2 = 0 := by decide
  rw [hzero, zero_mul] at he8
  have hnosq : ∀ v : ZMod 8, (0 : ZMod 8) - 1 ≠ v ^ 2 := by decide
  exact hnosq _ he8

end FourCorner

namespace FourCorner.CommonRootSource

private instance prime2 : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- An actual dyadic source with negative odd valuation of t must have the
same valuation at ell. Both alternative orders contradict a literal square
coordinate: P when ell has larger valuation, and B when it has smaller. -/
theorem dyadic_ell_val_eq_of_negative_odd {t : ℚ_[2]}
    (S : CommonRootSource ℚ_[2] t) (ht : t.valuation < 0)
    (hodd : Odd t.valuation) : S.ell.valuation = t.valuation := by
  have htv : t.valuation ≠ (1 : ℚ_[2]).valuation := by
    rw [Padic.valuation_one]
    omega
  have hT : (t + 1).valuation = t.valuation := by
    rw [commonRoot_val_add_of_ne S.t_ne_zero one_ne_zero htv,
      Padic.valuation_one, min_eq_left (le_of_lt ht)]
  have hs : (t - 1).valuation = t.valuation := by
    rw [commonRoot_val_sub_of_ne S.t_ne_zero one_ne_zero htv,
      Padic.valuation_one, min_eq_left (le_of_lt ht)]
  have hP : 2 * S.P.valuation = (S.ell + (t + 1)).valuation := by
    simpa only [Padic.valuation_pow, Nat.cast_ofNat] using congrArg Padic.valuation S.sqP
  have hB : 2 * S.B.valuation =
      (t + 1).valuation + (S.ell + (t - 1)).valuation - S.ell.valuation := by
    have h := congrArg Padic.valuation S.sqB
    rw [Padic.valuation_pow,
      commonRoot_val_div (mul_ne_zero S.T_ne_zero S.ell_add_s_ne_zero) S.ell_ne_zero,
      Padic.valuation_mul S.T_ne_zero S.ell_add_s_ne_zero] at h
    exact h
  obtain ⟨k, hk⟩ := hodd
  rcases lt_trichotomy S.ell.valuation t.valuation with hlt | heq | hgt
  · have hls := commonRoot_val_add_of_ne S.ell_ne_zero S.s_ne_zero
      (show S.ell.valuation ≠ (t - 1).valuation by rw [hs]; omega)
    rw [hs, min_eq_left (le_of_lt hlt)] at hls
    rw [hT, hls] at hB
    omega
  · exact heq
  · have hlT := commonRoot_val_add_of_ne S.ell_ne_zero S.T_ne_zero
      (show S.ell.valuation ≠ (t + 1).valuation by rw [hT]; omega)
    rw [hT, min_eq_right (le_of_lt hgt)] at hlT
    rw [hlT] at hP
    omega

end FourCorner.CommonRootSource

#print axioms FourCorner.commonRoot_dyadic_d_nonsquare_of_val_ge_two
#print axioms FourCorner.CommonRootSource.dyadic_ell_val_eq_of_negative_odd
