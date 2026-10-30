import HasseDyadicUnitOneNormalization
import HasseConstantDyadic

namespace FourCorner.HasseUnitFifteenNormalization

open HasseDyadicSymbol HasseDyadicDepthFive HasseRationalSource HasseAnchorChoice HasseTangentGlobal

noncomputable section
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem one_sub_unit (C : ℚ_[2]) (hC : C ≠ 0) (hv : 0<C.valuation) :
    1-C ≠ 0 ∧ (1-C).valuation=0 := by
  have hne : (1 : ℚ_[2]).valuation ≠ C.valuation := by rw [Padic.valuation_one];omega
  have hn : 1-C ≠ 0 := commonRoot_sub_ne_zero_of_val_ne hne
  exact ⟨hn,by rw [commonRoot_val_sub_of_ne one_ne_zero hC hne,Padic.valuation_one,min_eq_left (by omega)]⟩

/-- The exact unit-fifteen conic forces normalized U and T to be units,
without any assumed chart, chosen source orientation or bounded depth. -/
theorem conic_units (s x z : ℚ_[2]) (hs : s ≠ 0) (hx : x ≠ 0) (hz : z ≠ 0)
    (hsv : 2≤s.valuation)
    (heq : (1-s^2)*x^2=(1-2*s^2)*(2*z^2-1)) : x.valuation=0 ∧ z.valuation=0 := by
  have hs2 : s^2 ≠ 0 := pow_ne_zero _ hs
  have hsv2 : (s^2).valuation=2*s.valuation := by rw [Padic.valuation_pow];norm_num
  have h2sv : (2*s^2).valuation=1+2*s.valuation := by
    rw [Padic.valuation_mul (by norm_num) hs2,Padic.valuation_pow,
      show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p]
    norm_num
  obtain ⟨hA,hAval⟩ := one_sub_unit (s^2) hs2 (by omega)
  obtain ⟨hB,hBval⟩ := one_sub_unit (2*s^2) (mul_ne_zero (by norm_num) hs2) (by omega)
  have hz2 : 2*z^2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hz)
  have hz2v : (2*z^2).valuation=1+2*z.valuation := by
    rw [Padic.valuation_mul (by norm_num) (pow_ne_zero _ hz),Padic.valuation_pow,
      show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p]
    norm_num
  have hzi : 0≤z.valuation := by
    by_contra hn
    have hne : (2*z^2).valuation ≠ (1 : ℚ_[2]).valuation := by rw [hz2v,Padic.valuation_one];omega
    have hN : 2*z^2-1 ≠ 0 := commonRoot_sub_ne_zero_of_val_ne hne
    have hNv : (2*z^2-1).valuation=1+2*z.valuation := by
      rw [commonRoot_val_sub_of_ne hz2 one_ne_zero hne,hz2v,Padic.valuation_one,min_eq_left (by omega)]
    have hv := congrArg Padic.valuation heq
    rw [Padic.valuation_mul hA (pow_ne_zero _ hx),Padic.valuation_pow,hAval,
      Padic.valuation_mul hB hN,hBval,hNv] at hv
    norm_num at hv
    omega
  have hne : (2*z^2).valuation ≠ (1 : ℚ_[2]).valuation := by rw [hz2v,Padic.valuation_one];omega
  have hN : 2*z^2-1 ≠ 0 := commonRoot_sub_ne_zero_of_val_ne hne
  have hNv : (2*z^2-1).valuation=0 := by
    rw [commonRoot_val_sub_of_ne hz2 one_ne_zero hne,hz2v,Padic.valuation_one,min_eq_right (by omega)]
  have hxv : x.valuation=0 := by
    have hv := congrArg Padic.valuation heq
    rw [Padic.valuation_mul hA (pow_ne_zero _ hx),Padic.valuation_pow,hAval,
      Padic.valuation_mul hB hN,hBval,hNv] at hv
    norm_num at hv
    omega
  let S : ℤ_[2] := ⟨s,(Padic.norm_le_one_iff_val_nonneg s).mpr (by omega)⟩
  let X : ℤ_[2] := ⟨x,(Padic.norm_le_one_iff_val_nonneg x).mpr hxv.ge⟩
  let Z : ℤ_[2] := ⟨z,(Padic.norm_le_one_iff_val_nonneg z).mpr hzi⟩
  have hsres : PadicInt.toZModPow 3 (S^2)=0 :=
    integral_residue8_zero_of_val_ge_three (S^2) hs2 (by change 3≤(s^2).valuation;omega)
  have hxres : (PadicInt.toZModPow 3 X)^2=1 := by
    have hh := residue8_sq x hx
    have hv : (x^2).valuation=0 := by rw [Padic.valuation_pow,hxv];simp
    rw [residue8_eq_integral _ (pow_ne_zero _ hx) hv (X^2) rfl,map_pow] at hh
    exact hh
  have heqi : (1-S^2)*X^2=(1-2*S^2)*(2*Z^2-1) := by apply Subtype.ext;exact heq
  have her := congrArg (PadicInt.toZModPow 3) heqi
  simp only [map_sub,map_mul,map_pow,map_one,map_ofNat] at her hsres
  rw [hsres] at her
  norm_num only [mul_zero,sub_zero,one_mul,hxres] at her
  have hf : ∀ z : ZMod 8, 1=2*z^2-1 → HilbertDyadicFormulaHigh11.OddUnit z := by decide
  have hzodd := hf _ her
  have hzres : PadicInt.toZModPow 1 Z ≠ 0 := by
    have hc := PadicInt.cast_toZModPow (p:=2) 1 3 (by decide) Z
    have hn : ∀ z : ZMod 8,HilbertDyadicFormulaHigh11.OddUnit z → (ZMod.cast z : ZMod 2) ≠ 0 := by decide
    rw [← hc]
    exact hn _ hzodd
  have hznorm : ‖Z‖=1 := (dyadic_norm_one_iff_residue_ne_zero Z).mpr hzres
  exact ⟨hxv,(commonDyadic_unit_val hznorm).2⟩

def numerator (s x y z : ℚ_[2]) : ℚ_[2] := x+y+2*z+s*((x+2*z)*(x+y)+2)

/-- The same original source gives the complete unit-fifteen normal form. -/
theorem source_normal_form (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p) (D : TangentData p P)
    (hroot : IsSquare (((p : ℚ_[2])+1)/2)) (hdepth : 5≤((p : ℚ_[2])+1).valuation) :
    ∃ s x y z : ℚ_[2], s ≠ 0 ∧ x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧
      2≤s.valuation ∧ x.valuation=0 ∧ y.valuation=0 ∧ z.valuation=0 ∧
      (p : ℚ_[2])= -1+2*s^2 ∧
      (1-s^2)*x^2=(1-2*s^2)*(2*z^2-1) ∧
      (1-s^2)*y^2=1-2*s^2*z^2 ∧
      (P.U : ℚ_[2])=s*x*(P.Z : ℚ_[2]) ∧
      (D.w : ℚ_[2])=2*s*y*(P.Z : ℚ_[2]) ∧
      (P.T : ℚ_[2])=2*s*z*(P.Z : ℚ_[2]) := by
  obtain ⟨s,hs⟩ := hroot
  have hs2 : s^2=((p : ℚ_[2])+1)/2 := by simpa only [pow_two] using hs.symm
  have hb0 : (p : ℚ_[2])+1 ≠ 0 := by exact_mod_cast (show p+1 ≠ 0 by linarith)
  have hs0 : s ≠ 0 := by intro h;apply hb0;rw [h] at hs2;linear_combination -2*hs2
  have hpeq : (p : ℚ_[2])= -1+2*s^2 := by linear_combination -2*hs2
  have hbs : (p : ℚ_[2])+1=2*s^2 := by linear_combination hpeq
  have hsv : 2≤s.valuation := by
    have hv := congrArg Padic.valuation hbs
    rw [Padic.valuation_mul (by norm_num) (pow_ne_zero _ hs0),Padic.valuation_pow,
      show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p] at hv
    norm_num at hv
    omega
  obtain ⟨hz,hu,hv,hw,ht⟩ := coordinates_ne_zero p hp P
  have hz2 : (P.Z : ℚ_[2]) ≠ 0 := by exact_mod_cast hz
  have hu2 : (P.U : ℚ_[2]) ≠ 0 := by exact_mod_cast hu
  have ht2 : (P.T : ℚ_[2]) ≠ 0 := by exact_mod_cast ht
  have hdw : D.w ≠ 0 := by rcases D.sign with h | h <;> rw [h] <;> simpa using hw
  have hw2 : (D.w : ℚ_[2]) ≠ 0 := by exact_mod_cast hdw
  let x : ℚ_[2] := (P.U : ℚ_[2])/(s*(P.Z : ℚ_[2]))
  let y : ℚ_[2] := (D.w : ℚ_[2])/(2*s*(P.Z : ℚ_[2]))
  let z : ℚ_[2] := (P.T : ℚ_[2])/(2*s*(P.Z : ℚ_[2]))
  have hx0 : x ≠ 0 := div_ne_zero hu2 (mul_ne_zero hs0 hz2)
  have hy0 : y ≠ 0 := div_ne_zero hw2 (mul_ne_zero (mul_ne_zero (by norm_num) hs0) hz2)
  have hz0 : z ≠ 0 := div_ne_zero ht2 (mul_ne_zero (mul_ne_zero (by norm_num) hs0) hz2)
  have hconic : ((p : ℚ_[2])-1)*(P.U : ℚ_[2])^2-
      (p : ℚ_[2])*(P.T : ℚ_[2])^2+(p : ℚ_[2])*((p : ℚ_[2])+1)*(P.Z : ℚ_[2])^2=0 := by
    have hc : (p-1)*P.U^2-p*P.T^2+p*(p+1)*P.Z^2=0 := by linear_combination -P.equations.2.2
    exact_mod_cast hc
  have hxeq : (1-s^2)*x^2=(1-2*s^2)*(2*z^2-1) := by
    dsimp [x,z]
    field_simp
    rw [hpeq] at hconic
    linear_combination -hconic
  have hyeq : (1-s^2)*y^2=1-2*s^2*z^2 := by
    have hh : ((p : ℚ_[2])-1)*(D.w : ℚ_[2])^2=
        2*((p : ℚ_[2])+1)*((P.T : ℚ_[2])^2-2*(P.Z : ℚ_[2])^2) := by exact_mod_cast D.omission.2
    rw [hpeq] at hh
    dsimp [y,z]
    field_simp
    linear_combination (-1/2 : ℚ_[2])*hh
  obtain ⟨hxv,hzv⟩ := conic_units s x z hs0 hx0 hz0 hsv hxeq
  have hyv : y.valuation=0 := by
    have hs2v : (s^2).valuation=2*s.valuation := by rw [Padic.valuation_pow];norm_num
    obtain ⟨hA,hAv⟩ := one_sub_unit (s^2) (pow_ne_zero _ hs0) (by omega)
    have hn : 2*s^2*z^2 ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hs0)) (pow_ne_zero _ hz0)
    have hnv : 0<(2*s^2*z^2).valuation := by
      rw [Padic.valuation_mul (mul_ne_zero (by norm_num) (pow_ne_zero _ hs0)) (pow_ne_zero _ hz0),
        Padic.valuation_mul (by norm_num) (pow_ne_zero _ hs0),Padic.valuation_pow,Padic.valuation_pow,
        hzv,show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p]
      norm_num
      omega
    obtain ⟨hB,hBv⟩ := one_sub_unit (2*s^2*z^2) hn hnv
    have hv := congrArg Padic.valuation hyeq
    rw [Padic.valuation_mul hA (pow_ne_zero _ hy0),Padic.valuation_pow,hAv,hBv] at hv
    norm_num at hv
    omega
  refine ⟨s,x,y,z,hs0,hx0,hy0,hz0,hsv,hxv,hyv,hzv,hpeq,hxeq,hyeq,?_,?_,?_⟩
  · dsimp [x];field_simp
  · dsimp [y];field_simp
  · dsimp [z];field_simp

#print axioms conic_units
#print axioms source_normal_form

end
end FourCorner.HasseUnitFifteenNormalization
