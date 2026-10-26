import HasseDyadicSymbol

namespace FourCorner.HasseDyadicNonunit
open HasseDyadicSymbol HasseTangentGlobal HasseRationalSource HasseAnchorChoice

noncomputable section
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem square_one_add_of_val_ge_three (x : ℚ_[2]) (hx : x ≠ 0)
    (hv : 3 ≤ x.valuation) : IsSquare (1+x) := by
  apply padic_two_isSquare_one_add
  rw [Padic.norm_eq_zpow_neg_valuation hx]
  calc
    (2 : ℝ)^(-x.valuation) ≤ (2 : ℝ)^(-3 : ℤ) :=
      (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ)<2)).mpr (by omega)
    _ < 1/4 := by norm_num

/-- The rational source is embedded into the actual completed field, with
all original four-square equations and nonzero conditions retained. -/
def localPointTwo (p : ℚ) (S : HasseNorms.LocalPoint ℚ p) :
    HasseNorms.LocalPoint ℚ_[2] (p : ℚ_[2]) where
  rho := (S.rho : ℚ_[2])
  u := (S.u : ℚ_[2])
  v := (S.v : ℚ_[2])
  w := (S.w : ℚ_[2])
  t := (S.t : ℚ_[2])
  rho_ne_zero := by exact_mod_cast S.rho_ne_zero
  rho_ne_one := by exact_mod_cast S.rho_ne_one
  rho_ne_neg_one := by exact_mod_cast S.rho_ne_neg_one
  u_ne_zero := by exact_mod_cast S.u_ne_zero
  v_ne_zero := by exact_mod_cast S.v_ne_zero
  w_ne_zero := by exact_mod_cast S.w_ne_zero
  t_ne_zero := by exact_mod_cast S.t_ne_zero
  sqU := by exact_mod_cast S.sqU
  sqV := by exact_mod_cast S.sqV
  sqW := by exact_mod_cast S.sqW
  sqT := by exact_mod_cast S.sqT

/-- At every positive nonunit depth allowed by Loc, c=1-p is a literal
square in Q₂. The stronger hypothesis depth≥3 suffices. -/
theorem firstCoefficient_square_positive (p : ℚ) (hp0 : p ≠ 0)
    (hv : 3 ≤ (p : ℚ_[2]).valuation) :
    IsSquare (firstCoefficient p : ℚ_[2]) := by
  have hsmall := square_one_add_of_val_ge_three (-(p : ℚ_[2]))
    (neg_ne_zero.mpr (by exact_mod_cast hp0)) (by simpa only [commonRoot_val_neg] using hv)
  simpa only [firstCoefficient,Rat.cast_neg,Rat.cast_sub,Rat.cast_one,sub_eq_add_neg,
    neg_add_rev,neg_neg,Rat.cast_add] using hsmall

/-- A negative-depth actual source forces rho+1 to depth at least three.
This is the source calculation excluding the spurious squareclass +1 of p. -/
theorem rho_add_one_val_ge_three (p : ℚ_[2]) (S : HasseNorms.LocalPoint ℚ_[2] p)
    (hp0 : p ≠ 0) (ha0 : p-1 ≠ 0) (hb0 : p+1 ≠ 0) (hv : p.valuation ≤ -4) :
    3 ≤ (S.rho+1).valuation := by
  have hc0 : S.rho-1 ≠ 0 := sub_ne_zero.mpr S.rho_ne_one
  have hd0 : S.rho+1 ≠ 0 := by intro h; apply S.rho_ne_neg_one; linear_combination h
  have h0 : IsSquare (p*S.rho) := ⟨S.u,by simpa only [pow_two] using S.sqU.symm⟩
  have h1 : IsSquare (2*(p-1)*(S.rho-1)) := ⟨S.v,by simpa only [pow_two] using S.sqV.symm⟩
  have h2 : IsSquare (2*(p+1)*(S.rho+1)) := ⟨S.w,by simpa only [pow_two] using S.sqW.symm⟩
  have h3 : IsSquare ((p-1)*S.rho+p+1) := ⟨S.t,by simpa only [pow_two] using S.sqT.symm⟩
  have hd := HasseDyadicSource.valuation_dichotomy p S.rho hp0 S.rho_ne_zero ha0 hb0 hc0 hd0
    h0 h1 h2 h3
  have hrval : S.rho.valuation=0 := by
    rcases hd with h|h
    · omega
    · exact h.1
  have heven : Even p.valuation := by
    rcases hd with h|h
    · omega
    · exact h.2.2
  have hmin := commonRoot_dyadic_unit_pair_min S.rho_ne_zero one_ne_zero hrval Padic.valuation_one hd0 hc0
  have hnb := (HasseDyadicSource.neighbor_vals hp0 (by omega)).2
  have hodd : Odd (S.rho+1).valuation := by
    obtain ⟨j,hj⟩ := commonRoot_even_val_of_isSquare h2
    rw [Padic.valuation_mul (mul_ne_zero (by norm_num) hb0) hd0,
      Padic.valuation_mul (by norm_num) hb0,
      show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p,hnb,min_eq_left (by omega)] at hj
    obtain ⟨k,hk⟩ := heven
    exact ⟨j-k-1,by omega⟩
  have hnot : (S.rho+1).valuation ≠ 1 := by
    intro hsum
    have hleft : (p*(S.rho+1)).valuation=p.valuation+1 := by
      rw [Padic.valuation_mul hp0 hd0,hsum]
    have hright : (1-S.rho).valuation=(S.rho-1).valuation := by
      rw [show 1-S.rho= -(S.rho-1) by ring,commonRoot_val_neg]
    have hdiff : (1-S.rho) ≠ 0 := sub_ne_zero.mpr (Ne.symm S.rho_ne_one)
    have hne : (p*(S.rho+1)).valuation ≠ (1-S.rho).valuation := by
      rw [hleft,hright]
      omega
    have hlast : ((p-1)*S.rho+p+1).valuation=p.valuation+1 := by
      rw [show (p-1)*S.rho+p+1=p*(S.rho+1)+(1-S.rho) by ring,
        commonRoot_val_add_of_ne (mul_ne_zero hp0 hd0) hdiff hne,hleft,hright,
        min_eq_left (by omega)]
    have helast := commonRoot_even_val_of_isSquare h3
    rw [hlast] at helast
    obtain ⟨j,hj⟩ := helast
    obtain ⟨k,hk⟩ := heven
    omega
  obtain ⟨j,hj⟩ := hodd
  omega

/-- At every negative nonunit depth≤−4, the actual source forces c=1-p
to be square. The proof never transfers an evaluation to a selected point. -/
theorem firstCoefficient_square_negative (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p)
    (hv : (p : ℚ_[2]).valuation ≤ -4) :
    IsSquare (firstCoefficient p : ℚ_[2]) := by
  let S := localPointTwo p (toLocalPoint p hp P)
  have hp0 : (p : ℚ_[2]) ≠ 0 := by exact_mod_cast (show p ≠ 0 by linarith)
  have ha0 : (p : ℚ_[2])-1 ≠ 0 := by exact_mod_cast (show p-1 ≠ 0 by linarith)
  have hb0 : (p : ℚ_[2])+1 ≠ 0 := by exact_mod_cast (show p+1 ≠ 0 by linarith)
  have hrval := rho_add_one_val_ge_three (p : ℚ_[2]) S hp0 ha0 hb0 hv
  have hradd : S.rho+1 ≠ 0 := by intro h; apply S.rho_ne_neg_one; linear_combination h
  have hmr : IsSquare (-S.rho) := by
    have h := square_one_add_of_val_ge_three (-(S.rho+1)) (neg_ne_zero.mpr hradd)
      (by simpa only [commonRoot_val_neg] using hrval)
    convert h using 1 <;> ring
  have hpr : IsSquare ((p : ℚ_[2])*S.rho) := ⟨S.u,by simpa only [pow_two] using S.sqU.symm⟩
  have hmp : IsSquare (-(p : ℚ_[2])) := by
    have h := hpr.div hmr
    have he : ((p : ℚ_[2])*S.rho)/(-S.rho)= -(p : ℚ_[2]) := by field_simp [S.rho_ne_zero]
    rwa [he] at h
  have hip : IsSquare (1-(p : ℚ_[2])⁻¹) := by
    have h := square_one_add_of_val_ge_three (-(p : ℚ_[2])⁻¹)
      (neg_ne_zero.mpr (inv_ne_zero hp0)) (by rw [commonRoot_val_neg,Padic.valuation_inv]; omega)
    simpa only [sub_eq_add_neg] using h
  have h := hmp.mul hip
  have he : -(p : ℚ_[2])*(1-(p : ℚ_[2])⁻¹)=(firstCoefficient p : ℚ_[2]) := by
    simp only [firstCoefficient,Rat.cast_neg,Rat.cast_sub,Rat.cast_one]
    field_simp
  rwa [he] at h

theorem tangentSign_positive_nonunit (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p)
    (D : TangentData p P) (hv : 4 ≤ (p : ℚ_[2]).valuation) : tangentSign p hp P D 2=1 := by
  rw [tangentSign_eq_dyadicSign]
  apply dyadicSign_one_of_left_square
  exact firstCoefficient_square_positive p (by linarith) (by omega)

theorem tangentSign_negative_nonunit (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p)
    (D : TangentData p P) (hv : (p : ℚ_[2]).valuation ≤ -4) : tangentSign p hp P D 2=1 := by
  rw [tangentSign_eq_dyadicSign]
  apply dyadicSign_one_of_left_square
  exact firstCoefficient_square_negative p hp P hv

#print axioms square_one_add_of_val_ge_three
#print axioms localPointTwo
#print axioms rho_add_one_val_ge_three
#print axioms firstCoefficient_square_positive
#print axioms firstCoefficient_square_negative
#print axioms tangentSign_positive_nonunit
#print axioms tangentSign_negative_nonunit
end
end FourCorner.HasseDyadicNonunit
