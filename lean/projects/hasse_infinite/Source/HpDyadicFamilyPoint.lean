import HpDomainArithmetic

namespace FourCorner.HpDyadicFamilyPoint

open HasseNorms HasseObstructionArithmetic
noncomputable section
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem principal_square_root (F : ℚ_[2]) (hv : 3≤(F-1).valuation) :
    ∃ e : ℚ_[2],e ≠ 0 ∧ e^2=F := by
  have hsq : IsSquare F := by
    have hh := HasseUnitBranches.square_one_add_of_val_ge_three (F-1) hv
    simpa only [add_sub_cancel] using hh
  have hF : F ≠ 0 := by
    intro hz
    simp only [hz,zero_sub,commonRoot_val_neg,Padic.valuation_one] at hv
    omega
  obtain ⟨e,he⟩ := hsq
  refine ⟨e,?_,?_⟩
  · intro hz
    apply hF
    simp [hz] at he
    exact he
  · simpa only [pow_two] using he.symm

/-- A depth-five b and an actual square root of 2b give all four nonzero
dyadic squares by the literal rho-minus witness, at arbitrary larger depths. -/
theorem local_point_at_two (p : ℚ) (hp : 1<p) (r : ℚ)
    (hr : r^2=2*(p+1)) (hr0 : r ≠ 0) (hbdepth : 5≤((p : ℚ_[2])+1).valuation) :
    Nonempty (LocalPoint ℚ_[2] (p : ℚ_[2])) := by
  let P : ℚ_[2] := p
  let b : ℚ_[2] := P+1
  let d : ℚ_[2] := 3*P+1
  have hp0 : P ≠ 0 := by dsimp [P];exact_mod_cast (show p ≠ 0 by linarith)
  have hb0 : b ≠ 0 := by dsimp [b,P];exact_mod_cast (show p+1 ≠ 0 by linarith)
  have hd0 : d ≠ 0 := by dsimp [d,P];exact_mod_cast (show 3*p+1 ≠ 0 by linarith)
  have hd00 : 3*P+1 ≠ 0 := hd0
  have hdNorm : 1+P*3 ≠ 0 := by convert hd00 using 1 <;> ring
  have hdenInv : (3*P+1)*(3*P+1)⁻¹=1 := mul_inv_cancel₀ hd00
  have ha0 : P-1 ≠ 0 := by dsimp [P];exact_mod_cast (show p-1 ≠ 0 by linarith)
  have h2p1 : 2*P+1 ≠ 0 := by dsimp [P];exact_mod_cast (show 2*p+1 ≠ 0 by linarith)
  have hr2 : (r : ℚ_[2]) ≠ 0 := by exact_mod_cast hr0
  have hrEq : (r : ℚ_[2])^2=2*b := by dsimp [b,P];exact_mod_cast hr
  have hbv : 5≤b.valuation := hbdepth
  have h3 : (3 : ℚ_[2]).valuation=0 := by
    rw [Padic.valuation_ofNat,padicValNat.eq_zero_of_not_dvd (by decide : ¬2∣3)]
    rfl
  have hdv : d.valuation=1 := by
    have he : d=3*b-2 := by dsimp [d,b];ring
    have hv3b : (3*b).valuation=b.valuation := by
      rw [Padic.valuation_mul (by norm_num) hb0,h3,zero_add]
    rw [he,commonRoot_val_sub_of_ne (mul_ne_zero (by norm_num) hb0) (by norm_num)
      (by rw [hv3b,show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p];omega),
      hv3b,show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p,min_eq_right (by omega)]
  let F1 : ℚ_[2] := 2*P/d
  let F2 : ℚ_[2] := -P*(P-1)/d
  let F3 : ℚ_[2] := 2*(2*P+1)/d
  have hF1 : F1-1= -b/d := by
    dsimp [F1]
    apply (eq_div_iff hd0).mpr
    rw [sub_mul,div_mul_cancel₀ _ hd0,one_mul]
    dsimp [b,d]
    ring
  have hF2 : F2-1= -(b^2)/d := by
    dsimp [F2]
    apply (eq_div_iff hd0).mpr
    rw [sub_mul,div_mul_cancel₀ _ hd0,one_mul]
    dsimp [b,d]
    ring
  have hF3 : F3-1=b/d := by
    dsimp [F3]
    apply (eq_div_iff hd0).mpr
    rw [sub_mul,div_mul_cancel₀ _ hd0,one_mul]
    dsimp [b,d]
    ring
  obtain ⟨e1,he1,h1⟩ := principal_square_root F1 (by
    rw [hF1,commonRoot_val_div (neg_ne_zero.mpr hb0) hd0,commonRoot_val_neg,hdv];omega)
  obtain ⟨e2,he2,h2⟩ := principal_square_root F2 (by
    rw [hF2,commonRoot_val_div (neg_ne_zero.mpr (pow_ne_zero _ hb0)) hd0,
      commonRoot_val_neg,Padic.valuation_pow,hdv]
    norm_num
    omega)
  obtain ⟨e3,he3,h3e⟩ := principal_square_root F3 (by
    rw [hF3,commonRoot_val_div hb0 hd0,hdv];omega)
  let rho := b/d
  let u := (r : ℚ_[2])/2*e1
  let v := 2*e2
  let w := (r : ℚ_[2])*e3
  let t := 2*u
  have hrho0 : rho ≠ 0 := div_ne_zero hb0 hd0
  have hrho1 : rho ≠ 1 := by
    intro hh
    have hh' : b=d := (div_eq_one_iff_eq hd0).mp hh
    apply hp0
    dsimp [b,d] at hh'
    linear_combination (-1/2 : ℚ_[2])*hh'
  have hrhom : rho ≠ -1 := by
    intro hh
    have hh' : b= -d := (div_eq_iff hd0).mp hh |>.trans (by ring)
    apply h2p1
    dsimp [b,d] at hh'
    linear_combination (1/2 : ℚ_[2])*hh'
  have hu0 : u ≠ 0 := mul_ne_zero (div_ne_zero hr2 (by norm_num)) he1
  have hv0 : v ≠ 0 := mul_ne_zero (by norm_num) he2
  have hw0 : w ≠ 0 := mul_ne_zero hr2 he3
  have ht0 : t ≠ 0 := mul_ne_zero (by norm_num) hu0
  refine ⟨⟨rho,u,v,w,t,hrho0,hrho1,hrhom,hu0,hv0,hw0,ht0,?_,?_,?_,?_⟩⟩
  · change u^2=P*rho
    dsimp [u,rho]
    rw [mul_pow,h1,div_pow]
    dsimp [F1]
    rw [hrEq]
    field_simp [hd00,hdNorm]
  · change v^2=2*(P-1)*(rho-1)
    dsimp [v,rho]
    rw [mul_pow,h2]
    dsimp [F2,b,d]
    linear_combination -2*(P-1)*hdenInv
  · change w^2=2*(P+1)*(rho+1)
    dsimp [w,rho]
    rw [mul_pow,h3e,hrEq]
    dsimp [F3,b,d]
    linear_combination 2*(P+1)*hdenInv
  · change t^2=(P-1)*rho+P+1
    dsimp [t,u,rho]
    rw [mul_pow,mul_pow,h1,div_pow,hrEq]
    dsimp [F1,b,d]
    linear_combination (P+1)*hdenInv

#print axioms local_point_at_two

end
end FourCorner.HpDyadicFamilyPoint
