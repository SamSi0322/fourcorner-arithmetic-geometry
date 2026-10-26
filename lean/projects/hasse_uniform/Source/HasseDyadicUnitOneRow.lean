import HasseDyadicUnitOneModel

namespace FourCorner.HasseDyadicUnitOneRow
open HasseDyadicSymbol HasseDyadicAlgebra HasseDyadicNonunit HasseDyadicUnitOneNormalization
open HasseDyadicUnitOneModel HasseObstructionArithmetic HasseRationalSource HasseAnchorChoice HasseTangentGlobal
noncomputable section
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem unitOne_square_depth (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p) (h : UnitOne p) :
    IsSquare (((p : ℚ_[2])-1)/2) ∧ 5 ≤ ((p : ℚ_[2])-1).valuation := by
  obtain ⟨u,hu,hr⟩ := h
  have hpv : (p : ℚ_[2]).valuation=0 := by
    rw [← hu]
    exact HasseDyadicBranches.val_zero_of_residue_one_or_fifteen u (Or.inl hr)
  rcases HasseNorms.dyadic_conclusion p hp hL with hpos|hneg|h1|h15
  · rw [hpv] at hpos; omega
  · rw [hpv] at hneg; omega
  · exact ⟨h1.choose_spec.2.2.1,h1.choose_spec.2.2.2.2⟩
  · obtain ⟨v,hv,hrv,_⟩ := h15
    exact False.elim (unit_branches_disjoint p ⟨⟨u,hu,hr⟩,⟨v,hv,hrv⟩⟩)

/-- The full unit-one dyadic table row on the SAME original rational tangent
coefficient, at every permitted odd depth, with exactly the depth-five bit. -/
theorem tangentSign_unitOne (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p)
    (P : HomogeneousPoint p) (D : TangentData p P) (h : UnitOne p) :
    tangentSign p hp P D 2=(-1 : ℤ)^(1+(if padicValRat 2 (p-1)=5 then 1 else 0)) := by
  obtain ⟨hroot,hdepth⟩ := unitOne_square_depth p hp hL h
  obtain ⟨s,x,y,t,hs,hx0,hy0,ht0,hsv,hxv,hyv,htv,hpeq,hx,hy,hsep,hF⟩ :=
    source_normal_form p hp P D hroot hdepth
  obtain ⟨hH,hmodel⟩ := model_sign s x y t hs hx0 hy0 ht0 hsv hxv hyv htv hx hy hsep
  let H := numerator (1+2*s^2) s x y t
  let F := (secondCoefficient p P D : ℚ_[2])
  have hF0 : F ≠ 0 := by
    change (secondCoefficient p P D : ℚ_[2]) ≠ 0
    exact_mod_cast (ne_of_lt D.coefficient_negative)
  have hc : (firstCoefficient p : ℚ_[2])= (-2)*s^2 := by
    simp only [firstCoefficient,Rat.cast_neg,Rat.cast_sub,Rat.cast_one]
    rw [hpeq]
    ring
  have hC0 : (firstCoefficient p : ℚ_[2]) ≠ 0 := by
    exact_mod_cast (ne_of_lt (firstCoefficient_negative p hp))
  have hA : IsSquare (1+s^2) := square_one_add_of_val_ge_three (s^2) (pow_ne_zero _ hs)
    (by rw [Padic.valuation_pow]; norm_num; omega)
  obtain ⟨r,hr⟩ := hA
  have hr2 : 1+s^2=r^2 := by simpa only [pow_two] using hr
  have hr0 : r ≠ 0 := by
    intro hz
    have ha : 1+s^2=0 := by simp [hr2,hz]
    have ha' : s^2= -1 := by linear_combination ha
    have hv : (s^2).valuation=0 := by rw [ha',commonRoot_val_neg,Padic.valuation_one]
    rw [Padic.valuation_pow] at hv
    norm_num at hv
    omega
  have hp0 : (p : ℚ_[2]) ≠ 0 := by exact_mod_cast (show p ≠ 0 by linarith)
  have hz0 : (P.Z : ℚ_[2]) ≠ 0 := by exact_mod_cast (coordinates_ne_zero p hp P).1
  have hscale : 2*(p : ℚ_[2])*(P.Z : ℚ_[2])*r ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hp0) hz0) hr0
  have hHm : H ≠ 0 := neg_ne_zero.mp hH
  have hminus2H : (-2)*H ≠ 0 := mul_ne_zero (by norm_num) hHm
  have hfact : F=((-2)*H)*(2*(p : ℚ_[2])*(P.Z : ℚ_[2])*r)^2 := by
    dsimp [F,H]
    rw [hF,hpeq]
    linear_combination -8*(1+2*s^2)^2*(P.Z : ℚ_[2])^2*
      (numerator (1+2*s^2) s x y t)*hr2
  have hbase : dyadicSign (-2 : ℚ_[2]) 2 (by norm_num) (by norm_num)=1 := by
    have hnv : (-2 : ℚ_[2]).valuation=1 := by
      rw [show (-2 : ℚ_[2])= -(2 : ℚ_[2]) by ring,commonRoot_val_neg]
      exact Padic.valuation_p
    have h2 : residue8 (2 : ℚ_[2]) (by norm_num)=1 := by simpa using residue8_qpow 1
    rw [dyadicSign,hnv,residue8_negTwo,show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p,h2]
    decide
  have hleft : dyadicSign (firstCoefficient p : ℚ_[2]) F hC0 hF0=
      dyadicSign (-2) F (by norm_num) hF0 := by
    have hh := dyadicSign_mul_sq_left (-2 : ℚ_[2]) F s (by norm_num) hF0 hs
    simpa only [← hc] using hh
  have hright : dyadicSign (-2) F (by norm_num) hF0=
      dyadicSign (-2) (-H) (by norm_num) hH := by
    have hh := dyadicSign_mul_sq_right (-2 : ℚ_[2]) ((-2)*H)
      (2*(p : ℚ_[2])*(P.Z : ℚ_[2])*r) (by norm_num) hminus2H hscale
    have hsame : dyadicSign (-2) F (by norm_num) hF0=
        dyadicSign (-2) ((-2)*H) (by norm_num) hminus2H := by
      simpa only [← hfact] using hh
    rw [hsame]
    have hm := dyadicSign_mul_right (-2 : ℚ_[2]) 2 (-H) (by norm_num) (by norm_num) hH
    rw [hbase,one_mul] at hm
    simpa only [mul_neg,neg_mul] using hm
  have hval : padicValRat 2 (p-1)=1+2*s.valuation := by
    have he : ((p-1 : ℚ) : ℚ_[2])=2*s^2 := by push_cast; rw [hpeq]; ring
    rw [← Padic.valuation_ratCast,he,Padic.valuation_mul (by norm_num) (pow_ne_zero _ hs),
      Padic.valuation_pow,show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p]
    norm_num
  have hsign : (if s.valuation=2 then (1 : ℤ) else -1)=
      (-1 : ℤ)^(1+(if padicValRat 2 (p-1)=5 then 1 else 0)) := by
    by_cases hv2 : s.valuation=2
    · have hv5 : padicValRat 2 (p-1)=5 := by omega
      simp [hv2,hv5]
    · have hv5 : padicValRat 2 (p-1) ≠ 5 := by omega
      simp [hv2,hv5]
  rw [tangentSign_eq_dyadicSign]
  exact hleft.trans (hright.trans (hmodel.trans hsign))

#print axioms unitOne_square_depth
#print axioms tangentSign_unitOne
end
end FourCorner.HasseDyadicUnitOneRow
