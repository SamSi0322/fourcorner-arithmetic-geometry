import HasseDyadicAlgebra

namespace FourCorner.HasseDyadicDepthFive
open HasseLocalUnits HasseDyadicSymbol HasseDyadicNonunit

noncomputable section
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem normalizedUnit_eq_of_valuation_zero (x : ℚ_[2]) (hx : x ≠ 0) (hv : x.valuation=0)
    (X : ℤ_[2]) (hX : (X : ℚ_[2])=x) : (normalizedUnit x hx : ℤ_[2])=X := by
  apply Subtype.ext
  simp only [coe_normalizedUnit,unitPart,hv,neg_zero,zpow_zero,mul_one]
  exact hX.symm

theorem residue8_eq_integral (x : ℚ_[2]) (hx : x ≠ 0) (hv : x.valuation=0)
    (X : ℤ_[2]) (hX : (X : ℚ_[2])=x) : residue8 x hx=PadicInt.toZModPow 3 X := by
  unfold residue8
  rw [normalizedUnit_eq_of_valuation_zero x hx hv X hX]

theorem integral_residue8_zero_of_val_ge_three (X : ℤ_[2]) (hX : (X : ℚ_[2]) ≠ 0)
    (hv : 3 ≤ (X : ℚ_[2]).valuation) : PadicInt.toZModPow 3 X=0 := by
  apply (dyadic_residue_zero_iff_norm_le X 3).mpr
  change ‖(X : ℚ_[2])‖ ≤ _
  rw [Padic.norm_eq_zpow_neg_valuation hX]
  exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ)<2)).mpr (by omega)

theorem integral_residue8_four_of_val_two (X : ℤ_[2]) (hX : (X : ℚ_[2]) ≠ 0)
    (hv : (X : ℚ_[2]).valuation=2) : PadicInt.toZModPow 3 X=4 := by
  have hfour : (4 : ℚ_[2]).valuation=2 := by
    rw [show (4 : ℚ_[2])=2^2 by norm_num,Padic.valuation_pow]
    norm_num [show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p]
  have hdiv : ((X : ℚ_[2])/4).valuation=0 := by
    rw [div_eq_mul_inv,Padic.valuation_mul hX (inv_ne_zero (by norm_num)),Padic.valuation_inv,hv,hfour]
    norm_num
  let U : ℤ_[2] := ⟨(X : ℚ_[2])/4,(Padic.norm_le_one_iff_val_nonneg _).mpr hdiv.ge⟩
  have hU : (U : ℚ_[2]) ≠ 0 := div_ne_zero hX (by norm_num)
  have huodd : HilbertDyadicFormulaHigh11.OddUnit (PadicInt.toZModPow 3 U) := by
    rw [← residue8_eq_integral _ hU hdiv U rfl]
    exact residue8_odd _ hU
  have he : X=4*U := by
    apply Subtype.ext
    change (X : ℚ_[2])=4*((X : ℚ_[2])/4)
    field_simp
  rw [he,map_mul,map_ofNat]
  have hf : ∀ u : ZMod 8, HilbertDyadicFormulaHigh11.OddUnit u → 4*u=4 := by decide
  exact hf _ huodd

/-- The exact principal correction at all depths d≥2. The exceptional sign
occurs precisely at d=2; no upper valuation cutoff is imposed. -/
theorem principal_correction_sign (C : ℚ_[2]) (hC : C ≠ 0) (hv : 2 ≤ C.valuation) :
    ∃ hunit : 1-C ≠ 0,
      dyadicSign (-2) (1-C) (by norm_num) hunit=(if C.valuation=2 then -1 else 1) ∧
      dyadicSign 2 (1-C) (by norm_num) hunit=(if C.valuation=2 then -1 else 1) := by
  have hne : (1 : ℚ_[2]).valuation ≠ C.valuation := by rw [Padic.valuation_one]; omega
  have hunit : 1-C ≠ 0 := by
    intro h
    have hh : C=1 := (sub_eq_zero.mp h).symm
    rw [hh,Padic.valuation_one] at hv
    omega
  have hval : (1-C).valuation=0 := by
    rw [commonRoot_val_sub_of_ne one_ne_zero hC hne,Padic.valuation_one,min_eq_left (by omega)]
  let Ci : ℤ_[2] := ⟨C,(Padic.norm_le_one_iff_val_nonneg _).mpr (by omega)⟩
  have hres : residue8 (1-C) hunit=1-PadicInt.toZModPow 3 Ci := by
    rw [residue8_eq_integral (1-C) hunit hval (1-Ci) (by change (1 : ℚ_[2])-C=1-C; rfl),map_sub,map_one]
  have h2 : residue8 (2 : ℚ_[2]) (by norm_num)=1 := by simpa using residue8_qpow 1
  have hnv : (-2 : ℚ_[2]).valuation=1 := by
    rw [show (-2 : ℚ_[2])= -(2 : ℚ_[2]) by ring,commonRoot_val_neg]
    exact Padic.valuation_p
  refine ⟨hunit,?_,?_⟩
  · by_cases hh : C.valuation=2
    · have hr := integral_residue8_four_of_val_two Ci hC hh
      rw [dyadicSign,hnv,residue8_negTwo,hval,hres,hr,if_pos hh]
      decide
    · have hr := integral_residue8_zero_of_val_ge_three Ci hC (show 3 ≤ C.valuation by omega)
      rw [dyadicSign,hnv,residue8_negTwo,hval,hres,hr,if_neg hh]
      decide
  · by_cases hh : C.valuation=2
    · have hr := integral_residue8_four_of_val_two Ci hC hh
      rw [dyadicSign,show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p,h2,hval,hres,hr,if_pos hh]
      decide
    · have hr := integral_residue8_zero_of_val_ge_three Ci hC (show 3 ≤ C.valuation by omega)
      rw [dyadicSign,show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p,h2,hval,hres,hr,if_neg hh]
      decide

/-- Rewriting d=(h−1)/2 gives exactly the manuscript's depth-five indicator. -/
theorem depth_five_correction_sign (C : ℚ_[2]) (hC : C ≠ 0) (h : ℤ)
    (hh : Odd h) (hge : 5 ≤ h) (hdepth : C.valuation=(h-1)/2) :
    ∃ hunit : 1-C ≠ 0,
      dyadicSign (-2) (1-C) (by norm_num) hunit=(-1 : ℤ)^(if h=5 then 1 else 0) ∧
      dyadicSign 2 (1-C) (by norm_num) hunit=(-1 : ℤ)^(if h=5 then 1 else 0) := by
  obtain ⟨k,hk⟩ := hh
  obtain ⟨hu,hminus,hplus⟩ := principal_correction_sign C hC (by omega)
  have he : (if C.valuation=2 then (-1 : ℤ) else 1)=(-1 : ℤ)^(if h=5 then 1 else 0) := by
    by_cases hh5 : h=5
    · have hd : C.valuation=2 := by omega
      simp [hh5,hd]
    · have hd : C.valuation ≠ 2 := by omega
      simp [hh5,hd]
  exact ⟨hu,hminus.trans he,hplus.trans he⟩

#print axioms normalizedUnit_eq_of_valuation_zero
#print axioms residue8_eq_integral
#print axioms integral_residue8_zero_of_val_ge_three
#print axioms integral_residue8_four_of_val_two
#print axioms principal_correction_sign
#print axioms depth_five_correction_sign
end
end FourCorner.HasseDyadicDepthFive
