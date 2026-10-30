import HasseDyadicUnitOneResidue

namespace FourCorner.HasseDyadicIntegralSign
open HasseLocalUnits HasseDyadicSymbol HasseDyadicDepthFive HasseDyadicUnitOneResidue
noncomputable section
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem valuation_one_of_residue16 (H S : ℤ_[2])
    (hres : PadicInt.toZModPow 4 H=2+8*PadicInt.toZModPow 4 S) :
    (H : ℚ_[2]) ≠ 0 ∧ (H : ℚ_[2]).valuation=1 := by
  have hf : ∀ s : ZMod 16,
      2+8*s ≠ 0 ∧ (ZMod.cast (2+8*s) : ZMod 2)=0 ∧
      (ZMod.cast (2+8*s) : ZMod 4) ≠ 0 := by decide
  have hfin := hf (PadicInt.toZModPow 4 S)
  have hH : (H : ℚ_[2]) ≠ 0 := by
    intro h
    have hz : H=0 := Subtype.ext h
    rw [hz,map_zero] at hres
    exact hfin.1 hres.symm
  have hz2 : PadicInt.toZModPow 1 H=0 := by
    have hc := PadicInt.cast_toZModPow (p:=2) 1 4 (by decide) H
    rw [hres] at hc
    exact hc.symm.trans hfin.2.1
  have hn4 : PadicInt.toZModPow 2 H ≠ 0 := by
    have hc := PadicInt.cast_toZModPow (p:=2) 2 4 (by decide) H
    rw [hres] at hc
    exact hc.symm.trans_ne hfin.2.2
  have hn2 := (dyadic_residue_zero_iff_norm_le H 1).mp hz2
  have hn4' : ¬ ‖H‖ ≤ (2 : ℝ)^(-(2 : ℤ)) := by
    intro h
    exact hn4 ((dyadic_residue_zero_iff_norm_le H 2).mpr h)
  have hvlo : 1 ≤ (H : ℚ_[2]).valuation := by
    change ‖(H : ℚ_[2])‖ ≤ _ at hn2
    rw [Padic.norm_eq_zpow_neg_valuation hH] at hn2
    have h := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ)<2)).mp hn2
    omega
  have hvhi : (H : ℚ_[2]).valuation < 2 := by
    by_contra h
    apply hn4'
    change ‖(H : ℚ_[2])‖ ≤ _
    rw [Padic.norm_eq_zpow_neg_valuation hH]
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ)<2)).mpr (by omega)
  exact ⟨hH,by omega⟩

/-- The actual Q₂ dyadic sign of the original numerator, read directly
from its mod-sixteen residue. -/
theorem negative_numerator_sign (H S : ℤ_[2])
    (hres : PadicInt.toZModPow 4 H=2+8*PadicInt.toZModPow 4 S) :
    ∃ hH : -(H : ℚ_[2]) ≠ 0,
      dyadicSign (-2) (-(H : ℚ_[2])) (by norm_num) hH=
        if PadicInt.toZModPow 1 S=0 then -1 else 1 := by
  obtain ⟨hH,hval⟩ := valuation_one_of_residue16 H S hres
  let U : ℤ_[2] := normalizedUnit (H : ℚ_[2]) hH
  have he : H=2*U := by
    apply Subtype.ext
    change (H : ℚ_[2])=2*unitPart (H : ℚ_[2])
    rw [unitPart,hval]
    norm_num
    ring
  have her := congrArg (PadicInt.toZModPow 4) he
  rw [hres,map_mul,map_ofNat] at her
  have hu : residue8 (H : ℚ_[2]) hH=PadicInt.toZModPow 3 U := rfl
  have hminusone : residue8 (-1 : ℚ_[2]) (by norm_num)= -1 := by
    simpa only [Int.cast_neg,Int.cast_one] using residue8_intCast (-1) (by decide)
  have hminus : residue8 (-(H : ℚ_[2])) (neg_ne_zero.mpr hH)= -PadicInt.toZModPow 3 U := by
    have hh := residue8_mul (-1 : ℚ_[2]) (H : ℚ_[2]) (by norm_num) hH
    simpa only [neg_one_mul,hminusone,hu] using hh
  have huc := PadicInt.cast_toZModPow (p:=2) 3 4 (by decide) U
  have hsc := PadicInt.cast_toZModPow (p:=2) 1 4 (by decide) S
  have hnv : (-2 : ℚ_[2]).valuation=1 := by
    rw [show (-2 : ℚ_[2])= -(2 : ℚ_[2]) by ring,commonRoot_val_neg]
    exact Padic.valuation_p
  have hformula : ∀ u s : ZMod 16, 2+8*s=2*u →
      HilbertDyadicFormulaHigh11.formula 1 (-1) 1 (-(ZMod.cast u : ZMod 8))=
        if (ZMod.cast s : ZMod 2)=0 then -1 else 1 := by decide
  refine ⟨neg_ne_zero.mpr hH,?_⟩
  rw [dyadicSign,hnv,residue8_negTwo,commonRoot_val_neg,hval,hminus]
  rw [← huc,← hsc]
  exact hformula _ _ her

#print axioms valuation_one_of_residue16
#print axioms negative_numerator_sign
end
end FourCorner.HasseDyadicIntegralSign
