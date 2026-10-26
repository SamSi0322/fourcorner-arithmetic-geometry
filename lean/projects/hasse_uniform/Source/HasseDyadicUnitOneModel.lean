import HasseDyadicUnitOneFlip

namespace FourCorner.HasseDyadicUnitOneModel
open HasseLocalUnits HasseDyadicSymbol HasseDyadicNonunit HasseDyadicUnitOneNormalization
open HasseDyadicUnitOneResidue HasseDyadicIntegralSign HasseDyadicUnitOneFlip
noncomputable section
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem model_sign (s x y t : ℚ_[2]) (hs : s ≠ 0) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (ht0 : t ≠ 0)
    (hsv : 2 ≤ s.valuation) (hxv : x.valuation=0) (hyv : y.valuation=0) (htv : t.valuation=0)
    (hx : x^2=(1+2*s^2)*(2*t^2-(1+s^2)))
    (hy : y^2=(1+s^2)*(2*t^2-1))
    (hL : y*(1+s^2+t)+(1+s^2)*s*(2*t+1) ≠ 0) :
    ∃ hH : -numerator (1+2*s^2) s x y t ≠ 0,
      dyadicSign (-2) (-numerator (1+2*s^2) s x y t) (by norm_num) hH=
        if s.valuation=2 then 1 else -1 := by
  have hfour : (4 : ℚ_[2]).valuation=2 := by
    rw [show (4 : ℚ_[2])=2^2 by norm_num,Padic.valuation_pow,
      show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p]
    norm_num
  have hSval : (s/4).valuation=s.valuation-2 := by
    rw [div_eq_mul_inv,Padic.valuation_mul hs (inv_ne_zero (by norm_num)),Padic.valuation_inv,hfour]
    ring
  let S : ℤ_[2] := ⟨s/4,(Padic.norm_le_one_iff_val_nonneg _).mpr (by rw [hSval]; omega)⟩
  let X : ℤ_[2] := ⟨x,(Padic.norm_le_one_iff_val_nonneg _).mpr hxv.ge⟩
  let Y : ℤ_[2] := ⟨y,(Padic.norm_le_one_iff_val_nonneg _).mpr hyv.ge⟩
  let T : ℤ_[2] := ⟨t,(Padic.norm_le_one_iff_val_nonneg _).mpr htv.ge⟩
  have hsS : 4*(S : ℚ_[2])=s := by change 4*(s/4)=s; field_simp
  have hXi : X^2=(1+2*(4*S)^2)*(2*T^2-(1+(4*S)^2)) := by
    apply Subtype.ext
    change x^2=(1+2*(4*(S : ℚ_[2]))^2)*(2*t^2-(1+(4*(S : ℚ_[2]))^2))
    rwa [hsS]
  have hYi : Y^2=(1+(4*S)^2)*(2*T^2-1) := by
    apply Subtype.ext
    change y^2=(1+(4*(S : ℚ_[2]))^2)*(2*t^2-1)
    rwa [hsS]
  have hTnorm : ‖T‖=1 := by
    change ‖t‖=1
    rw [Padic.norm_eq_zpow_neg_valuation ht0,htv]
    simp
  have hXnorm : ‖X‖=1 := by
    change ‖x‖=1
    rw [Padic.norm_eq_zpow_neg_valuation hx0,hxv]
    simp
  have hYnorm : ‖Y‖=1 := by
    change ‖y‖=1
    rw [Padic.norm_eq_zpow_neg_valuation hy0,hyv]
    simp
  have hSout : (if PadicInt.toZModPow 1 S=0 then (-1 : ℤ) else 1)=
      if s.valuation=2 then 1 else -1 := by
    by_cases hv2 : s.valuation=2
    · have hvS : (S : ℚ_[2]).valuation=0 := by change (s/4).valuation=0; omega
      have hnS : ‖S‖=1 := by
        change ‖s/4‖=1
        rw [Padic.norm_eq_zpow_neg_valuation (div_ne_zero hs (by norm_num)),hvS]
        simp
      have hrS := (dyadic_norm_one_iff_residue_ne_zero S).mp hnS
      simp only [hrS,if_false,hv2,if_true]
    · have hrS : PadicInt.toZModPow 1 S=0 := by
        apply (dyadic_residue_zero_iff_norm_le S 1).mpr
        change ‖s/4‖ ≤ _
        rw [Padic.norm_eq_zpow_neg_valuation (div_ne_zero hs (by norm_num)),hSval]
        exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ)<2)).mpr (by omega)
      simp only [hrS,if_true,hv2,if_false]
  have horient : PadicInt.toZModPow 2 (X*Y)=1 ∨ PadicInt.toZModPow 2 (X*Y)= -1 := by
    have hnorm : ‖X*Y‖=1 := by rw [norm_mul,hXnorm,hYnorm,mul_one]
    have hn := (dyadic_norm_one_iff_residue_ne_zero (X*Y)).mp hnorm
    have hc := PadicInt.cast_toZModPow (p:=2) 1 2 (by decide) (X*Y)
    have hf : ∀ u : ZMod 4, (ZMod.cast u : ZMod 2) ≠ 0 → u=1 ∨ u= -1 := by decide
    exact hf _ (hc.trans_ne hn)
  have hN : (modelNumerator S X Y T : ℚ_[2])=numerator (1+2*s^2) s x y t := by
    change x*y+(4*(S : ℚ_[2]))*(2*t+1)*(x+y)+
      2*(1+2*(4*(S : ℚ_[2]))^2)*t^2+2*(4*(S : ℚ_[2]))^2*t-(1+(4*(S : ℚ_[2]))^2)=_
    rw [hsS]
    dsimp [numerator]
    ring
  rcases horient with hpos|hneg
  · obtain ⟨hH,he⟩ := negative_numerator_sign (modelNumerator S X Y T) S
      (source_model_residue S X Y T hTnorm hXi hYi hpos)
    simp only [hN] at hH he
    exact ⟨hH,he.trans hSout⟩
  · have hXi' : (-X)^2=(1+2*(4*S)^2)*(2*T^2-(1+(4*S)^2)) := by simpa only [neg_sq] using hXi
    have hpos : PadicInt.toZModPow 2 ((-X)*Y)=1 := by
      rw [neg_mul,map_neg,hneg,neg_neg]
    obtain ⟨hM,he⟩ := negative_numerator_sign (modelNumerator S (-X) Y T) S
      (source_model_residue S (-X) Y T hTnorm hXi' hYi hpos)
    have hMnum : (modelNumerator S (-X) Y T : ℚ_[2])=numerator (1+2*s^2) s (-x) y t := by
      change (-x)*y+(4*(S : ℚ_[2]))*(2*t+1)*((-x)+y)+
        2*(1+2*(4*(S : ℚ_[2]))^2)*t^2+2*(4*(S : ℚ_[2]))^2*t-(1+(4*(S : ℚ_[2]))^2)=_
      rw [hsS]
      dsimp [numerator]
      ring
    simp only [hMnum] at hM he
    obtain ⟨hH,hM',hflip⟩ := numerator_flip_sign s x y t hs hsv hx hy hL
    exact ⟨hH,hflip.trans (he.trans hSout)⟩

#print axioms model_sign
end
end FourCorner.HasseDyadicUnitOneModel
