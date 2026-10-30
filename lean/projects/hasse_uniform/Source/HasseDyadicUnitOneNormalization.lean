import HasseDyadicDepthFive

namespace FourCorner.HasseDyadicUnitOneNormalization
open HasseDyadicSymbol HasseDyadicDepthFive
noncomputable section
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The original source conic, in the exact unit-one square gauge, forces
its rescaled U and T coordinates to be genuine dyadic units. -/
theorem conic_units (s x t : ℚ_[2]) (hs : s ≠ 0) (hx : x ≠ 0) (ht : t ≠ 0)
    (hsv : 2 ≤ s.valuation)
    (heq : x^2=(1+2*s^2)*(2*t^2-(1+s^2))) :
    x.valuation=0 ∧ t.valuation=0 := by
  have h2 : (2 : ℚ_[2]) ≠ 0 := by norm_num
  have hs2 : s^2 ≠ 0 := pow_ne_zero _ hs
  have hsv2 : (s^2).valuation=2*s.valuation := by rw [Padic.valuation_pow]; norm_num
  have hs2val : 0<(s^2).valuation := by omega
  have hAsum : (1 : ℚ_[2]).valuation ≠ (s^2).valuation := by rw [Padic.valuation_one]; omega
  have hA0 : 1+s^2 ≠ 0 := by
    intro h
    have hh : s^2= -1 := by linear_combination h
    have hv : (s^2).valuation=0 := by rw [hh,commonRoot_val_neg,Padic.valuation_one]
    omega
  have hAval : (1+s^2).valuation=0 := by
    rw [commonRoot_val_add_of_ne one_ne_zero hs2 hAsum,Padic.valuation_one,min_eq_left (by omega)]
  have h2s : 2*s^2 ≠ 0 := mul_ne_zero h2 hs2
  have h2sv : (2*s^2).valuation=1+2*s.valuation := by
    rw [Padic.valuation_mul h2 hs2,show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p,hsv2]
  have hpsum : (1 : ℚ_[2]).valuation ≠ (2*s^2).valuation := by rw [Padic.valuation_one]; omega
  have hpval : (1+2*s^2).valuation=0 := by
    rw [commonRoot_val_add_of_ne one_ne_zero h2s hpsum,Padic.valuation_one,min_eq_left (by omega)]
  have hp0 : 1+2*s^2 ≠ 0 := by
    intro h
    have hh : 2*s^2= -1 := by linear_combination h
    have hv : (2*s^2).valuation=0 := by rw [hh,commonRoot_val_neg,Padic.valuation_one]
    omega
  have ht2 : 2*t^2 ≠ 0 := mul_ne_zero h2 (pow_ne_zero _ ht)
  have htv : (2*t^2).valuation=1+2*t.valuation := by
    rw [Padic.valuation_mul h2 (pow_ne_zero _ ht),show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p,
      Padic.valuation_pow]
    norm_num
  have htval : 0 ≤ t.valuation := by
    by_contra hh
    have hne : (2*t^2).valuation ≠ (1+s^2).valuation := by rw [htv,hAval]; omega
    have hd : 2*t^2-(1+s^2) ≠ 0 := by
      intro hz
      exact hne (congrArg Padic.valuation (sub_eq_zero.mp hz))
    have hsub : (2*t^2-(1+s^2)).valuation=1+2*t.valuation := by
      rw [commonRoot_val_sub_of_ne ht2 hA0 hne,htv,hAval,min_eq_left (by omega)]
    have h := congrArg Padic.valuation heq
    rw [Padic.valuation_pow,Padic.valuation_mul hp0 hd,hpval,hsub] at h
    norm_num at h
    omega
  have hne : (2*t^2).valuation ≠ (1+s^2).valuation := by rw [htv,hAval]; omega
  have hd : 2*t^2-(1+s^2) ≠ 0 := by
    intro hz
    exact hne (congrArg Padic.valuation (sub_eq_zero.mp hz))
  have hsub : (2*t^2-(1+s^2)).valuation=0 := by
    rw [commonRoot_val_sub_of_ne ht2 hA0 hne,htv,hAval,min_eq_right (by omega)]
  have hxval : x.valuation=0 := by
    have h := congrArg Padic.valuation heq
    rw [Padic.valuation_pow,Padic.valuation_mul hp0 hd,hpval,hsub] at h
    norm_num at h
    omega
  let S : ℤ_[2] := ⟨s,(Padic.norm_le_one_iff_val_nonneg s).mpr (by omega)⟩
  let X : ℤ_[2] := ⟨x,(Padic.norm_le_one_iff_val_nonneg x).mpr hxval.ge⟩
  let T : ℤ_[2] := ⟨t,(Padic.norm_le_one_iff_val_nonneg t).mpr htval⟩
  have hsres : PadicInt.toZModPow 3 (S^2)=0 := by
    apply integral_residue8_zero_of_val_ge_three (S^2)
    · change s^2 ≠ 0; exact hs2
    · change 3 ≤ (s^2).valuation; omega
  have hxres : (PadicInt.toZModPow 3 X)^2=1 := by
    have hh := residue8_sq x hx
    have hxsq : (x^2).valuation=0 := by rw [Padic.valuation_pow,hxval]; simp
    rw [residue8_eq_integral _ (pow_ne_zero _ hx) hxsq (X^2) rfl,map_pow] at hh
    exact hh
  have heqi : X^2=(1+2*S^2)*(2*T^2-(1+S^2)) := by
    apply Subtype.ext
    exact heq
  have her := congrArg (PadicInt.toZModPow 3) heqi
  simp only [map_pow,map_mul,map_add,map_sub,map_one,map_ofNat] at her hsres
  rw [hsres] at her
  norm_num only [mul_zero,add_zero,one_mul,hxres] at her
  have hf : ∀ t : ZMod 8, 1=2*t^2-1 → HilbertDyadicFormulaHigh11.OddUnit t := by decide
  have htodd := hf _ her
  have htmod2 : PadicInt.toZModPow 1 T ≠ 0 := by
    have hh := PadicInt.cast_toZModPow (p:=2) 1 3 (by decide) T
    have hn : ∀ t : ZMod 8, HilbertDyadicFormulaHigh11.OddUnit t →
      (ZMod.cast t : ZMod 2) ≠ 0 := by decide
    rw [← hh]
    exact hn _ htodd
  have htnorm : ‖T‖=1 := (dyadic_norm_one_iff_residue_ne_zero T).mpr htmod2
  have htzero := (commonDyadic_unit_val htnorm).2
  exact ⟨hxval,htzero⟩

#print axioms conic_units
end
end FourCorner.HasseDyadicUnitOneNormalization

namespace FourCorner.HasseDyadicUnitOneNormalization
open HasseDyadicSymbol HasseDyadicDepthFive HasseRationalSource HasseAnchorChoice HasseTangentGlobal
noncomputable section
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The literal normalized numerator of the original-source polar. -/
def numerator (p s x y t : ℚ_[2]) : ℚ_[2] :=
  x*y+s*(2*t+1)*(x+y)+2*p*t^2+2*s^2*t-(p+1)/2

/-- The unit-one normal form is constructed from the same source and the
same original tangent coefficient. No evaluation transfer is used. -/
theorem source_normal_form (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p) (D : TangentData p P)
    (hroot : IsSquare (((p : ℚ_[2])-1)/2)) (hdepth : 5 ≤ ((p : ℚ_[2])-1).valuation) :
    ∃ s x y t : ℚ_[2], s ≠ 0 ∧ x ≠ 0 ∧ y ≠ 0 ∧ t ≠ 0 ∧
      2 ≤ s.valuation ∧ x.valuation=0 ∧ y.valuation=0 ∧ t.valuation=0 ∧
      (p : ℚ_[2])=1+2*s^2 ∧
      x^2=(1+2*s^2)*(2*t^2-(1+s^2)) ∧
      y^2=(1+s^2)*(2*t^2-1) ∧
      y*(1+s^2+t)+(1+s^2)*s*(2*t+1) ≠ 0 ∧
      (secondCoefficient p P D : ℚ_[2])=
        -4*(p : ℚ_[2])^2*((p : ℚ_[2])+1)*(P.Z : ℚ_[2])^2*numerator p s x y t := by
  obtain ⟨s,hs⟩ := hroot
  have hs2 : s^2=((p : ℚ_[2])-1)/2 := by simpa only [pow_two] using hs.symm
  have ha0 : (p : ℚ_[2])-1 ≠ 0 := by exact_mod_cast (show p-1 ≠ 0 by linarith)
  have hs0 : s ≠ 0 := by intro h; apply ha0; rw [h] at hs2; linear_combination -2*hs2
  have hpeq : (p : ℚ_[2])=1+2*s^2 := by linear_combination -2*hs2
  have has : (p : ℚ_[2])-1=2*s^2 := by linear_combination hpeq
  have hsv : 2 ≤ s.valuation := by
    have hv := congrArg Padic.valuation has
    rw [Padic.valuation_mul (by norm_num) (pow_ne_zero _ hs0),Padic.valuation_pow,
      show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p] at hv
    norm_num at hv
    omega
  obtain ⟨hz,hu,hv,hw,ht⟩ := coordinates_ne_zero p hp P
  have hz2 : (P.Z : ℚ_[2]) ≠ 0 := by exact_mod_cast hz
  have hu2 : (P.U : ℚ_[2]) ≠ 0 := by exact_mod_cast hu
  have ht2 : (P.T : ℚ_[2]) ≠ 0 := by exact_mod_cast ht
  have hdw : D.w ≠ 0 := by
    rcases D.sign with h|h
    · rw [h]; exact hw
    · rw [h]; exact neg_ne_zero.mpr hw
  have hw2 : (D.w : ℚ_[2]) ≠ 0 := by exact_mod_cast hdw
  let x : ℚ_[2] := s*((P.U : ℚ_[2])/(P.Z : ℚ_[2]))
  let y : ℚ_[2] := s*((D.w : ℚ_[2])/(P.Z : ℚ_[2]))/2
  let t : ℚ_[2] := ((P.T : ℚ_[2])/(P.Z : ℚ_[2]))/2
  have hx0 : x ≠ 0 := mul_ne_zero hs0 (div_ne_zero hu2 hz2)
  have hy0 : y ≠ 0 := div_ne_zero (mul_ne_zero hs0 (div_ne_zero hw2 hz2)) (by norm_num)
  have ht0 : t ≠ 0 := div_ne_zero (div_ne_zero ht2 hz2) (by norm_num)
  have hconic : ((p : ℚ_[2])-1)*(P.U : ℚ_[2])^2-
      (p : ℚ_[2])*(P.T : ℚ_[2])^2+(p : ℚ_[2])*((p : ℚ_[2])+1)*(P.Z : ℚ_[2])^2=0 := by
    have hh := P.equations.2.2
    have hc : (p-1)*P.U^2-p*P.T^2+p*(p+1)*P.Z^2=0 := by linear_combination -hh
    exact_mod_cast hc
  have hxeq : x^2=(1+2*s^2)*(2*t^2-(1+s^2)) := by
    dsimp [x,t]
    field_simp
    rw [hpeq] at hconic
    linear_combination hconic
  have hyeq : y^2=(1+s^2)*(2*t^2-1) := by
    have hh : ((p : ℚ_[2])-1)*(D.w : ℚ_[2])^2=
        2*((p : ℚ_[2])+1)*((P.T : ℚ_[2])^2-2*(P.Z : ℚ_[2])^2) := by
      exact_mod_cast D.omission.2
    rw [has,hpeq] at hh
    dsimp [y,t]
    field_simp
    linear_combination (1/2 : ℚ_[2])*hh
  obtain ⟨hxval,htval⟩ := conic_units s x t hs0 hx0 ht0 hsv hxeq
  have hyv : y.valuation=0 := by
    have hs2 : (s^2).valuation=2*s.valuation := by rw [Padic.valuation_pow]; norm_num
    have hA0 : 1+s^2 ≠ 0 := by
      intro h
      have hh : s^2= -1 := by linear_combination h
      have hv : (s^2).valuation=0 := by rw [hh,commonRoot_val_neg,Padic.valuation_one]
      omega
    have hAval : (1+s^2).valuation=0 := by
      rw [commonRoot_val_add_of_ne one_ne_zero (pow_ne_zero _ hs0)
        (show (1 : ℚ_[2]).valuation ≠ (s^2).valuation by rw [Padic.valuation_one]; omega),
        Padic.valuation_one,min_eq_left (by omega)]
    have htv : (2*t^2).valuation=1 := by
      rw [Padic.valuation_mul (by norm_num) (pow_ne_zero _ ht0),Padic.valuation_pow,htval,
        show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p]
      norm_num
    have hB0 : 2*t^2-1 ≠ 0 := by
      intro h
      have hv := congrArg Padic.valuation (sub_eq_zero.mp h)
      rw [htv,Padic.valuation_one] at hv
      omega
    have hBval : (2*t^2-1).valuation=0 := by
      rw [commonRoot_val_sub_of_ne (mul_ne_zero (by norm_num) (pow_ne_zero _ ht0)) one_ne_zero
        (by rw [htv,Padic.valuation_one]; omega),htv,Padic.valuation_one]
      norm_num
    have h := congrArg Padic.valuation hyeq
    rw [Padic.valuation_pow,Padic.valuation_mul hA0 hB0,hAval,hBval] at h
    norm_num at h
    omega
  have hsep : y*(1+s^2+t)+(1+s^2)*s*(2*t+1) ≠ 0 := by
    intro hzL
    have hd : (separation p P.Z D.w P.T : ℚ_[2]) ≠ 0 := by exact_mod_cast D.separated
    apply hd
    have he : (separation p P.Z D.w P.T : ℚ_[2])=
        8*s*(P.Z : ℚ_[2])^2*(y*(1+s^2+t)+(1+s^2)*s*(2*t+1)) := by
      dsimp [separation,anchorZ,anchorT,y,t]
      push_cast
      field_simp
      rw [hpeq]
      ring
    rw [he,hzL,mul_zero]
  refine ⟨s,x,y,t,hs0,hx0,hy0,ht0,hsv,hxval,hyv,htval,hpeq,hxeq,hyeq,hsep,?_⟩
  dsimp [secondCoefficient,secondPolar,anchorU,anchorT,anchorZ,numerator,x,y,t]
  push_cast
  field_simp
  rw [hpeq]
  ring

#print axioms source_normal_form
end
end FourCorner.HasseDyadicUnitOneNormalization
