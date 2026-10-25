import CSFoundation.CommonSourceOddLocal
import CSFoundation.CommonSourceOddLocalResidue
import CSFoundation.CommonSourceOddLocalDisks

set_option autoImplicit false
namespace FourCorner
variable {p : ℕ} [Fact p.Prime]

/-- Equal reductions are exactly the open unit neighborhood of the difference. -/
theorem csOdd_residue_eq_of_norm_sub_lt_one (a n : ℤ_[p])
    (h : ‖((a : ℚ_[p]) - (n : ℚ_[p]))‖ < 1) :
    PadicInt.toZMod a = PadicInt.toZMod n := by
  have hz : PadicInt.toZMod (a - n) = 0 :=
    (padicInt_norm_lt_one_iff_residue_zero (a - n)).mp h
  simpa only [map_sub, sub_eq_zero] using hz

/-- Two actual field abscissae in the positive two-torsion residue disk
force a nonsquare return, including arbitrarily deep or exact reductions. -/
theorem csOdd_not_isSquare_return_plus_plus (hp : p % 8 = 5)
    {n a c : ℚ_[p]} (hn : ‖n‖ = 1)
    (ha : ‖a - n‖ < 1) (hc : ‖c - n‖ < 1) :
    ¬ IsSquare (csOddReturn n a c) := by
  have han : ‖a‖ = 1 := (Padic.norm_eq_of_norm_sub_lt_right (by simpa [hn] using ha)).trans hn
  have hcn : ‖c‖ = 1 := (Padic.norm_eq_of_norm_sub_lt_right (by simpa [hn] using hc)).trans hn
  let ai : ℤ_[p] := padicIntegral a han.le
  let ci : ℤ_[p] := padicIntegral c hcn.le
  let ni : ℤ_[p] := padicIntegral n hn.le
  exact commonSource_both_plus_nonsquare_mod_eight hp ai ci ni
    (csOdd_residue_eq_of_norm_sub_lt_one ai ni ha)
    (csOdd_residue_eq_of_norm_sub_lt_one ci ni hc)
    ((padicInt_norm_eq_one_iff_residue_ne_zero ni).mp hn)

/-- Two actual abscissae in the negative two-torsion residue disk have
nonsquare return, using the exact rescaling identity and the actual cubic. -/
theorem csOdd_not_isSquare_return_minus_minus (hp : p % 8 = 5)
    {n a c e : ℚ_[p]} (hn : ‖n‖ = 1) (hns : IsSquare n)
    (ha : ‖a + n‖ < 1) (hc : ‖c + n‖ < 1) (he : e ≠ 0)
    (hcurve : e ^ 2 = c * (c - n) * (c + n)) :
    ¬ IsSquare (csOddReturn n a c) := by
  have hnn : ‖-n‖ = 1 := by simpa using hn
  have han : ‖a‖ = 1 :=
    (Padic.norm_eq_of_norm_sub_lt_right (by simpa [hnn] using ha)).trans hnn
  have hcn : ‖c‖ = 1 :=
    (Padic.norm_eq_of_norm_sub_lt_right (by simpa [hnn] using hc)).trans hnn
  let ai : ℤ_[p] := padicIntegral a han.le
  let ci : ℤ_[p] := padicIntegral c hcn.le
  let ni : ℤ_[p] := padicIntegral n hn.le
  apply commonSource_both_minus_nonsquare_mod_eight hp ai ci ni e he hcurve
  · simpa only [map_neg] using csOdd_residue_eq_of_norm_sub_lt_one ai (-ni) (by simpa [ai, ni] using ha)
  · simpa only [map_neg] using csOdd_residue_eq_of_norm_sub_lt_one ci (-ni) (by simpa [ci, ni] using hc)
  · exact (padicInt_norm_eq_one_iff_residue_ne_zero ni).mp hn
  · exact padicInt_isSquare_toZMod_of_isSquare_coe ni hns

/-- All four possible mismatched even-label coordinate disks are obstructed.
This theorem concerns the actual affine curve coordinates and the actual return value;
no character-row conclusion is included among its hypotheses. -/
theorem csOdd_not_isSquare_return_mismatched_disks (hp : p % 8 = 5)
    {n a b c e : ℚ_[p]} (hn : ‖n‖ = 1) (hns : IsSquare n) (he : e ≠ 0)
    (hQ : b ^ 2 = a * (a - n) * (a + n))
    (hR : e ^ 2 = c * (c - n) * (c + n))
    (hdisks : (‖a - n‖ < 1 ∧ ‖c - n‖ < 1) ∨
      (‖a + n‖ < 1 ∧ ‖c + n‖ < 1) ∨
      (1 < ‖a‖ ∧ ‖c‖ < 1) ∨ (‖a‖ < 1 ∧ 1 < ‖c‖)) :
    ¬ IsSquare (csOddReturn n a c) := by
  rcases hdisks with ⟨ha, hc⟩ | ⟨ha, hc⟩ | ⟨ha, hc⟩ | ⟨ha, hc⟩
  · exact csOdd_not_isSquare_return_plus_plus hp hn ha hc
  · exact csOdd_not_isSquare_return_minus_minus hp hn hns ha hc he hR
  · exact csOdd_not_isSquare_return_infinity_zero hp hn hns ha hc hQ
  · exact csOdd_not_isSquare_return_zero_infinity hp hn ha hc hR

end FourCorner

#print axioms FourCorner.csOdd_not_isSquare_return_plus_plus
#print axioms FourCorner.csOdd_not_isSquare_return_minus_minus

#print axioms FourCorner.csOdd_not_isSquare_return_mismatched_disks
