import HasseDyadicUnitFifteenFinite

namespace FourCorner.HasseDyadicIntegralTwo
open HasseLocalUnits HasseDyadicSymbol HasseDyadicUnitFifteenFinite
noncomputable section
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem valuation_one_of_residue4 (H : ℤ_[2]) (hres : PadicInt.toZModPow 2 H=2) :
    (H : ℚ_[2]) ≠ 0 ∧ (H : ℚ_[2]).valuation=1 := by
  have hH : (H : ℚ_[2]) ≠ 0 := by
    intro h
    have hz : H=0 := Subtype.ext h
    rw [hz,map_zero] at hres
    exact (by decide : (0 : ZMod 4) ≠ 2) hres
  have hz2 : PadicInt.toZModPow 1 H=0 := by
    have hc := PadicInt.cast_toZModPow (p:=2) 1 2 (by decide) H
    rw [hres] at hc
    exact hc.symm.trans (by decide : (ZMod.cast (2 : ZMod 4) : ZMod 2)=0)
  have hn4 : PadicInt.toZModPow 2 H ≠ 0 := by rw [hres]; decide
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

/-- Exact actual Q₂ sign from the residue classes 2,6,10,14 modulo 16. -/
theorem sign_two_of_residue16 (H : ℤ_[2])
    (hres : PadicInt.toZModPow 4 H=2 ∨ PadicInt.toZModPow 4 H=6 ∨
      PadicInt.toZModPow 4 H=10 ∨ PadicInt.toZModPow 4 H=14) :
    ∃ hH : (H : ℚ_[2]) ≠ 0,
      dyadicSign 2 (H : ℚ_[2]) (by norm_num) hH=
        if PadicInt.toZModPow 4 H=6 ∨ PadicInt.toZModPow 4 H=10 then -1 else 1 := by
  have h4 : PadicInt.toZModPow 2 H=2 := by
    have hc := PadicInt.cast_toZModPow (p:=2) 2 4 (by decide) H
    have hf : ∀ h : ZMod 16, h=2 ∨ h=6 ∨ h=10 ∨ h=14 → (ZMod.cast h : ZMod 4)=2 := by decide
    exact hc.symm.trans (hf _ hres)
  obtain ⟨hH,hval⟩ := valuation_one_of_residue4 H h4
  let U : ℤ_[2] := normalizedUnit (H : ℚ_[2]) hH
  have he : H=2*U := by
    apply Subtype.ext
    change (H : ℚ_[2])=2*unitPart (H : ℚ_[2])
    rw [unitPart,hval]
    norm_num
    ring
  have her := congrArg (PadicInt.toZModPow 4) he
  simp only [map_mul,map_ofNat] at her
  have hu : residue8 (H : ℚ_[2]) hH=PadicInt.toZModPow 3 U := rfl
  have huc := PadicInt.cast_toZModPow (p:=2) 3 4 (by decide) U
  have h2 : residue8 (2 : ℚ_[2]) (by norm_num)=1 := by simpa using residue8_qpow 1
  have hf : ∀ h u : ZMod 16,
      (h=2 ∨ h=6 ∨ h=10 ∨ h=14) → h=2*u →
      HilbertDyadicFormulaHigh11.formula 1 1 1 (ZMod.cast u : ZMod 8)=
        if h=6 ∨ h=10 then -1 else 1 := by decide
  refine ⟨hH,?_⟩
  rw [dyadicSign,show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p,h2,hval,hu,← huc]
  exact hf _ _ hres her

#print axioms valuation_one_of_residue4
#print axioms sign_two_of_residue16
end
end FourCorner.HasseDyadicIntegralTwo
