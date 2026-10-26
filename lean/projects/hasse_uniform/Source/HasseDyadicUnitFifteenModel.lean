import HasseDyadicIntegralTwo

namespace FourCorner.HasseDyadicUnitFifteenModel
open HasseLocalUnits HasseDyadicSymbol HasseDyadicDepthFive HasseDyadicIntegralTwo
open HasseDyadicUnitFifteenFinite
noncomputable section
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def numerator (s x y z : ℚ_[2]) : ℚ_[2] := x+y+2*z+s*((x+2*z)*(x+y)+2)

theorem oriented_numerator_sign (s x y z : ℚ_[2])
    (hs : s ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hsv : 2 ≤ s.valuation) (hxv : x.valuation=0) (hyv : y.valuation=0) (hzv : z.valuation=0)
    (heqx : (1-s^2)*x^2=(1-2*s^2)*(2*z^2-1))
    (heqy : (1-s^2)*y^2=1-2*s^2*z^2)
    (ho : PadicInt.toZModPow 2 ((normalizedUnit x hx : ℤ_[2])+(normalizedUnit y hy : ℤ_[2]))=0) :
    ∃ hN : numerator s x y z ≠ 0,
      dyadicSign 2 (numerator s x y z) (by norm_num) hN=
        if s.valuation=2 then -1 else 1 := by
  let S : ℤ_[2] := ⟨s,(Padic.norm_le_one_iff_val_nonneg _).mpr (by omega)⟩
  let X : ℤ_[2] := normalizedUnit x hx
  let Y : ℤ_[2] := normalizedUnit y hy
  let Z : ℤ_[2] := normalizedUnit z hz
  have hX : (X : ℚ_[2])=x := by simp only [X,coe_normalizedUnit,unitPart,hxv,neg_zero,zpow_zero,mul_one]
  have hY : (Y : ℚ_[2])=y := by simp only [Y,coe_normalizedUnit,unitPart,hyv,neg_zero,zpow_zero,mul_one]
  have hZ : (Z : ℚ_[2])=z := by simp only [Z,coe_normalizedUnit,unitPart,hzv,neg_zero,zpow_zero,mul_one]
  have hS : (S : ℚ_[2])=s := rfl
  have hTwo : ((2 : ℤ_[2]) : ℚ_[2])=(2 : ℚ_[2]) := rfl
  have hXi : (1-S^2)*X^2=(1-2*S^2)*(2*Z^2-1) := by
    apply Subtype.ext
    simpa only [PadicInt.coe_mul,PadicInt.coe_sub,PadicInt.coe_pow,PadicInt.coe_one,
      hTwo,hX,hZ,hS] using heqx
  have hYi : (1-S^2)*Y^2=1-2*S^2*Z^2 := by
    apply Subtype.ext
    simpa only [PadicInt.coe_mul,PadicInt.coe_sub,PadicInt.coe_pow,PadicInt.coe_one,
      hTwo,hY,hZ,hS] using heqy
  let r := PadicInt.toZModPow 5 (p:=2)
  have odd_of_unit (U : ℤ_[2]) (hU : ‖U‖=1) : (r U).val%2=1 := by
    have hn := (dyadic_norm_one_iff_residue_ne_zero U).mp hU
    have hc := PadicInt.cast_toZModPow (p:=2) 1 5 (by decide) U
    have hf : ∀ u : ZMod 32, (ZMod.cast u : ZMod 2) ≠ 0 → u.val%2=1 := by decide
    exact hf _ (hc.trans_ne hn)
  have hxodd : (r X).val%2=1 := by
    apply odd_of_unit
    change ‖unitPart x‖=1
    exact unitPart_norm x hx
  have hyodd : (r Y).val%2=1 := by
    apply odd_of_unit
    change ‖unitPart y‖=1
    exact unitPart_norm y hy
  have hzodd : (r Z).val%2=1 := by
    apply odd_of_unit
    change ‖unitPart z‖=1
    exact unitPart_norm z hz
  have hS4 : PadicInt.toZModPow 2 S=0 := by
    apply (dyadic_residue_zero_iff_norm_le S 2).mpr
    change ‖s‖ ≤ _
    rw [Padic.norm_eq_zpow_neg_valuation hs]
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ)<2)).mpr (by omega)
  have hsmod : r4 (r S)=0 := by
    have hc := PadicInt.cast_toZModPow (p:=2) 2 5 (by decide) S
    simpa only [r4,ZMod.castHom_apply,hS4] using hc
  have hxmod := congrArg r hXi
  have hymod := congrArg r hYi
  simp only [map_sub,map_mul,map_pow,map_one,map_ofNat] at hxmod hymod
  have homod : r4 (r X+r Y)=0 := by
    have hc := PadicInt.cast_toZModPow (p:=2) 2 5 (by decide) (X+Y)
    change PadicInt.toZModPow 2 (X+Y)=0 at ho
    rw [ho] at hc
    change (ZMod.cast (r X+r Y) : ZMod 4)=0
    simpa only [r,map_add] using hc
  have hfinite := numerator_residue (r S) (r X) (r Y) (r Z) hsmod hxodd hyodd hzodd hxmod hymod homod
  let N : ℤ_[2] := X+Y+2*Z+S*((X+2*Z)*(X+Y)+2)
  have hNr : PadicInt.toZModPow 4 N=r16 (n (r S) (r X) (r Y) (r Z)) := by
    have hc := PadicInt.cast_toZModPow (p:=2) 4 5 (by decide) N
    have hh : r N=n (r S) (r X) (r Y) (r Z) := by
      simp only [N,n,map_add,map_mul,map_ofNat]
    change PadicInt.toZModPow 4 N=(ZMod.cast (n (r S) (r X) (r Y) (r Z)) : ZMod 16)
    rw [← hh]
    exact hc.symm
  have hpar : ((r S).val/4)%2=0 ↔ s.valuation ≠ 2 := by
    by_cases hv2 : s.valuation=2
    · have hr8 := integral_residue8_four_of_val_two S hs (by simpa only [hS] using hv2)
      have hc := PadicInt.cast_toZModPow (p:=2) 3 5 (by decide) S
      rw [hr8] at hc
      have hf : ∀ u : ZMod 32, (ZMod.cast u : ZMod 8)=4 → ¬u.val/4%2=0 := by decide
      have hn := hf (r S) hc
      constructor
      · intro h; exact False.elim (hn h)
      · intro h; exact False.elim (h hv2)
    · have hr8 := integral_residue8_zero_of_val_ge_three S hs (show 3 ≤ s.valuation by omega)
      have hc := PadicInt.cast_toZModPow (p:=2) 3 5 (by decide) S
      rw [hr8] at hc
      have hf : ∀ u : ZMod 32, (ZMod.cast u : ZMod 8)=0 → u.val/4%2=0 := by decide
      have hh := hf (r S) hc
      exact ⟨fun _ => hv2,fun _ => hh⟩
  have hclass : if s.valuation=2 then (PadicInt.toZModPow 4 N=6 ∨ PadicInt.toZModPow 4 N=10)
      else (PadicInt.toZModPow 4 N=2 ∨ PadicInt.toZModPow 4 N=14) := by
    unfold signResidue at hfinite
    rw [← hNr] at hfinite
    by_cases hv2 : s.valuation=2
    · have hn : ¬((r S).val/4)%2=0 := by simpa only [hpar,hv2,ne_self_iff_false,not_false_eq_true]
      simpa only [hv2,if_true,hn,if_false] using hfinite
    · have hh : ((r S).val/4)%2=0 := hpar.mpr hv2
      simpa only [hv2,if_false,hh,if_true] using hfinite
  have hmembership : PadicInt.toZModPow 4 N=2 ∨ PadicInt.toZModPow 4 N=6 ∨
      PadicInt.toZModPow 4 N=10 ∨ PadicInt.toZModPow 4 N=14 := by
    by_cases hv2 : s.valuation=2
    · simp only [hv2,if_true] at hclass
      rcases hclass with h|h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · simp only [hv2,if_false] at hclass
      rcases hclass with h|h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
  obtain ⟨hN,hSign⟩ := sign_two_of_residue16 N hmembership
  have hbit : (if PadicInt.toZModPow 4 N=6 ∨ PadicInt.toZModPow 4 N=10 then (-1 : ℤ) else 1)=
      if s.valuation=2 then -1 else 1 := by
    by_cases hv2 : s.valuation=2
    · simp only [hv2,if_true] at hclass ⊢
      simp only [hclass,if_true]
    · simp only [hv2,if_false] at hclass ⊢
      have hf : ∀ n : ZMod 16, (n=2 ∨ n=14) → ¬(n=6 ∨ n=10) := by decide
      simp only [hf _ hclass,if_false]
  have hNfield : (N : ℚ_[2])=numerator s x y z := by
    dsimp [N,numerator]
    simp only [PadicInt.coe_add,PadicInt.coe_mul,hTwo,hX,hY,hZ,hS]
  simp only [hNfield] at hN hSign
  exact ⟨hN,hSign.trans hbit⟩

#print axioms oriented_numerator_sign
end
end FourCorner.HasseDyadicUnitFifteenModel

namespace FourCorner.HasseDyadicUnitFifteenModel
open HasseLocalUnits HasseDyadicSymbol
noncomputable section
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Every pair of actual dyadic units admits one of the two literal U signs
with x+y=0 mod4. This is only a proved sign choice on coordinates. -/
theorem oriented_sign_exists (x y : ℚ_[2]) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxv : x.valuation=0) :
    ∃ x' : ℚ_[2], (x'=x ∨ x'= -x) ∧ ∃ hx' : x' ≠ 0,
      x'.valuation=0 ∧ PadicInt.toZModPow 2
        ((normalizedUnit x' hx' : ℤ_[2])+(normalizedUnit y hy : ℤ_[2]))=0 := by
  let X : ℤ_[2] := normalizedUnit x hx
  let Y : ℤ_[2] := normalizedUnit y hy
  have unit_residue (U : ℤ_[2]) (hU : ‖U‖=1) :
      (ZMod.cast (PadicInt.toZModPow 2 U) : ZMod 2) ≠ 0 := by
    have hc := PadicInt.cast_toZModPow (p:=2) 1 2 (by decide) U
    exact hc.trans_ne ((dyadic_norm_one_iff_residue_ne_zero U).mp hU)
  have hX : (ZMod.cast (PadicInt.toZModPow 2 X) : ZMod 2) ≠ 0 :=
    unit_residue X (unitPart_norm x hx)
  have hY : (ZMod.cast (PadicInt.toZModPow 2 Y) : ZMod 2) ≠ 0 :=
    unit_residue Y (unitPart_norm y hy)
  have hf : ∀ u v : ZMod 4, (ZMod.cast u : ZMod 2) ≠ 0 →
      (ZMod.cast v : ZMod 2) ≠ 0 → u+v=0 ∨ -u+v=0 := by decide
  have ho : PadicInt.toZModPow 2 (X+Y)=0 ∨ PadicInt.toZModPow 2 (-X+Y)=0 := by
    simpa only [map_add,map_neg] using hf _ _ hX hY
  rcases ho with hp|hn
  · exact ⟨x,Or.inl rfl,hx,hxv,hp⟩
  · have hx' : -x ≠ 0 := neg_ne_zero.mpr hx
    have hneg : (normalizedUnit (-x) hx' : ℤ_[2])= -X := by
      apply Subtype.ext
      simp only [X,coe_normalizedUnit,PadicInt.coe_neg,unitPart,commonRoot_val_neg,neg_mul]
    refine ⟨-x,Or.inr rfl,hx',by simpa only [commonRoot_val_neg] using hxv,?_⟩
    rw [hneg]
    exact hn

#print axioms oriented_sign_exists
end
end FourCorner.HasseDyadicUnitFifteenModel

namespace FourCorner.HasseDyadicUnitFifteenModel
open HasseLocalUnits HasseDyadicSymbol
noncomputable section
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem dyadicSign_two_y (s y z : ℚ_[2]) (hs : s ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hsv : 2 ≤ s.valuation) (hyv : y.valuation=0) (hzv : z.valuation=0)
    (heq : (1-s^2)*y^2=1-2*s^2*z^2) : dyadicSign 2 y (by norm_num) hy=1 := by
  let S : ℤ_[2] := ⟨s,(Padic.norm_le_one_iff_val_nonneg _).mpr (by omega)⟩
  let Y : ℤ_[2] := normalizedUnit y hy
  let Z : ℤ_[2] := ⟨z,(Padic.norm_le_one_iff_val_nonneg _).mpr hzv.ge⟩
  have hY : (Y : ℚ_[2])=y := by simp only [Y,coe_normalizedUnit,unitPart,hyv,neg_zero,zpow_zero,mul_one]
  have hTwo : ((2 : ℤ_[2]) : ℚ_[2])=(2 : ℚ_[2]) := rfl
  have hei : (1-S^2)*Y^2=1-2*S^2*Z^2 := by
    apply Subtype.ext
    simpa only [PadicInt.coe_mul,PadicInt.coe_sub,PadicInt.coe_pow,PadicInt.coe_one,hTwo,hY]
      using heq
  have hsres : PadicInt.toZModPow 4 (S^2)=0 := by
    apply (dyadic_residue_zero_iff_norm_le (S^2) 4).mpr
    change ‖s^2‖ ≤ _
    rw [Padic.norm_eq_zpow_neg_valuation (pow_ne_zero _ hs),Padic.valuation_pow]
    change (2 : ℝ)^(-(2*s.valuation)) ≤ (2 : ℝ)^(-4 : ℤ)
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ)<2)).mpr (by omega)
  have hr := congrArg (PadicInt.toZModPow 4) hei
  simp only [map_mul,map_sub,map_pow,map_one,map_ofNat] at hr hsres
  rw [hsres] at hr
  norm_num only [sub_zero,mul_zero,zero_mul,one_mul] at hr
  have hc := PadicInt.cast_toZModPow (p:=2) 3 4 (by decide) Y
  have hu : residue8 y hy=PadicInt.toZModPow 3 Y := rfl
  have h2 : residue8 (2 : ℚ_[2]) (by norm_num)=1 := by simpa using residue8_qpow 1
  have hf : ∀ u : ZMod 16, u^2=1 →
      HilbertDyadicFormulaHigh11.formula 1 1 0 (ZMod.cast u : ZMod 8)=1 := by decide
  rw [dyadicSign,show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p,h2,hyv,hu,← hc]
  exact hf _ hr

#print axioms dyadicSign_two_y
end
end FourCorner.HasseDyadicUnitFifteenModel
