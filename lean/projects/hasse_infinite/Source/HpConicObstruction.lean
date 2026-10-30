import HpFamilyDyadicValuation

namespace FourCorner.HpConicObstruction

open HasseObstructionArithmetic HpDomainArithmetic

noncomputable section
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem unitFifteen_of_b_depth (p : ℚ) (hp : 1<p) (hv : 4≤((p : ℚ_[2])+1).valuation) : UnitFifteen p := by
  have hb0 : (p : ℚ_[2])+1 ≠ 0 := by exact_mod_cast (show p+1 ≠ 0 by linarith)
  let b : ℤ_[2] := ⟨(p : ℚ_[2])+1,(Padic.norm_le_one_iff_val_nonneg _).mpr (by omega)⟩
  have hb : PadicInt.toZModPow 4 b=0 := by
    apply (dyadic_residue_zero_iff_norm_le b 4).mpr
    change ‖(p : ℚ_[2])+1‖≤ _
    rw [Padic.norm_eq_zpow_neg_valuation hb0]
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ)<2)).mpr (by omega)
  refine ⟨b-1,?_,?_⟩
  · change (p : ℚ_[2])+1-1=(p : ℚ_[2])
    ring
  · rw [map_sub,map_one,hb]
    decide

theorem pab_square_at_two (p : ℚ) (hp : 1<p) (r : ℚ) (hr : r^2=2*(p+1))
    (hv : 5≤((p : ℚ_[2])+1).valuation) : IsSquare ((p*(p^2-1) : ℚ) : ℚ_[2]) := by
  have hb0 : (p : ℚ_[2])+1 ≠ 0 := by exact_mod_cast (show p+1 ≠ 0 by linarith)
  have h1 : IsSquare (-(p : ℚ_[2])) := by
    have hh := HasseUnitBranches.square_one_add_of_val_ge_three (-((p : ℚ_[2])+1))
      (by rw [commonRoot_val_neg];omega)
    convert hh using 1 <;> ring
  have h2 : IsSquare (-((p : ℚ_[2])-1)/2) := by
    have hd : 3≤(-(((p : ℚ_[2])+1)/2)).valuation := by
      rw [commonRoot_val_neg,commonRoot_val_div hb0 (by norm_num),
        show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p]
      omega
    have hh := HasseUnitBranches.square_one_add_of_val_ge_three (-(((p : ℚ_[2])+1)/2)) hd
    convert hh using 1 <;> ring
  have hh := (h1.mul h2).mul (IsSquare.sq (r : ℚ_[2]))
  have hrq : (r : ℚ_[2])^2=2*((p : ℚ_[2])+1) := by exact_mod_cast hr
  have he : (-(p : ℚ_[2]))*(-((p : ℚ_[2])-1)/2)*(r : ℚ_[2])^2=
      ((p*(p^2-1) : ℚ) : ℚ_[2]) := by
    rw [hrq]
    push_cast
    ring
  rwa [he] at hh

theorem domain_of_conic_depth (p : ℚ) (hp : 1<p) (r : ℚ) (hr : r^2=2*(p+1))
    (hv : 5≤((p : ℚ_[2])+1).valuation) : HasseNorms.Domain p := by
  apply domain_of_even_dyadic p hp
  have hh := commonRoot_even_val_of_isSquare (pab_square_at_two p hp r hr hv)
  simpa only [Padic.valuation_ratCast] using hh

theorem A_zero_of_conic (p s : ℚ) (hp : 1<p) (hs : s^2=3-p) (hs0 : s ≠ 0) : A p=0 := by
  classical
  unfold A halfInertSum
  apply Finset.sum_eq_zero
  intro q hq
  obtain ⟨hmem,hq2,hns,hva⟩ := Finset.mem_filter.mp hq
  have hprime := HasseInertParity.prime_of_rationalSupport (p-1) q hmem
  letI : Fact q.Prime := ⟨hprime⟩
  let Q : HilbertArithmeticHigh11.OddPrime := ⟨q,hprime,hq2⟩
  have h2 : ¬IsSquare (2 : ℚ_[q]) := SqrtTwoGlobalNorm.nonsquare_two_completion hns
  have hsQ : (s : ℚ_[q]) ≠ 0 := by exact_mod_cast hs0
  have haQ : ((p-1 : ℚ) : ℚ_[q]) ≠ 0 := by exact_mod_cast (show p-1 ≠ 0 by linarith)
  have hsEq : (s : ℚ_[q])^2=2-((p-1 : ℚ) : ℚ_[q]) := by
    have he : s^2=2-(p-1) := by linear_combination hs
    exact_mod_cast he
  have haV : 0<(((p-1 : ℚ) : ℚ_[q])).valuation := by rwa [Padic.valuation_ratCast]
  have hsVal : ((s : ℚ_[q])^2).valuation=0 := by
    rw [hsEq,commonRoot_val_sub_of_ne (by norm_num) haQ
      (by rw [commonRoot_val_two hq2];omega),commonRoot_val_two hq2,min_eq_left (by omega)]
  have hd : (2 : ℚ_[q])-(s : ℚ_[q])^2=((p-1 : ℚ) : ℚ_[q]) := by linear_combination -hsEq
  have hsq2 := HasseOddSymbol.square_of_positive_perturbation Q ((s : ℚ_[q])^2) 2
    (pow_ne_zero _ hsQ) hsVal (IsSquare.sq _) (by rwa [hd]) (by rwa [hd])
  exact False.elim (h2 hsq2)

theorem pole_even_of_conic (p s : ℚ) (hp : 1<p) (hs : s^2=3-p) (hs0 : s ≠ 0)
    (q : ℕ) [Fact q.Prime] (hv : padicValRat q p<0) : Even (padicValRat q p) := by
  have hv3 : 0≤padicValRat q (3 : ℚ) := by
    simpa only [Nat.cast_ofNat] using (zero_le_padicValRat_of_nat (p:=q) 3)
  have he : -p+3=s^2 := by linear_combination -hs
  have hh := padicValRat.add_eq_of_lt (p:=q) (q:=-p) (r:=3)
    (by rw [he];exact pow_ne_zero _ hs0) (neg_ne_zero.mpr (by linarith)) (by norm_num)
    (by rw [padicValRat.neg];omega)
  rw [he,padicValRat.pow,padicValRat.neg] at hh
  norm_num only [Nat.cast_ofNat] at hh
  exact ⟨padicValRat q s,by omega⟩

theorem P_zero_of_conic (p s : ℚ) (hp : 1<p) (hs : s^2=3-p) (hs0 : s ≠ 0) : P p=0 := by
  classical
  unfold P
  apply Finset.sum_eq_zero
  intro q hq
  obtain ⟨hmem,hq2,hv,hodd⟩ := Finset.mem_filter.mp hq
  have hprime := HasseInertParity.prime_of_rationalSupport p q hmem
  letI : Fact q.Prime := ⟨hprime⟩
  have heven := pole_even_of_conic p s hp hs hs0 q hv
  exact False.elim ((Int.not_even_iff_odd.mpr hodd) heven)

/-- Complete literal thin obstruction bit for the displayed progression,
without assuming any local solubility or the desired no-point conclusion. -/
theorem family_T_one (j : ℕ) : T (HpInfiniteArithmetic.p j)=1 := by
  let p := HpInfiniteArithmetic.p j
  let s := HpInfiniteArithmetic.s j
  have hp : 1<p := HpInfiniteArithmetic.p_gt_one j
  have hs : s^2=3-p := by dsimp [s,p,HpInfiniteArithmetic.p];ring
  have hs0 : s ≠ 0 := ne_of_lt (HpInfiniteArithmetic.s_negative j)
  have hb : padicValRat 2 (p+1)=5 := HpFamilyDyadicValuation.b_valuation j
  have hbq : ((p : ℚ_[2])+1).valuation=5 := by
    have he : (p : ℚ_[2])+1=((p+1 : ℚ) : ℚ_[2]) := by simp
    rw [he,Padic.valuation_ratCast]
    exact hb
  have hunit := unitFifteen_of_b_depth p hp (by omega)
  have hpv := HasseConstantDyadic.unitFifteen_val_zero p hunit
  rw [Padic.valuation_ratCast] at hpv
  rw [T_unit_fifteen p hpv hunit,hb,A_zero_of_conic p s hp hs hs0,P_zero_of_conic p s hp hs hs0]
  simp

theorem family_domain (j : ℕ) : HasseNorms.Domain (HpInfiniteArithmetic.p j) := by
  apply domain_of_conic_depth (HpInfiniteArithmetic.p j) (HpInfiniteArithmetic.p_gt_one j)
    (HpInfiniteArithmetic.r j) (HpInfiniteArithmetic.r_square j)
  have he : ((HpInfiniteArithmetic.p j : ℚ_[2])+1)=((HpInfiniteArithmetic.p j+1 : ℚ) : ℚ_[2]) := by simp
  rw [he,Padic.valuation_ratCast,HpFamilyDyadicValuation.b_valuation]

#print axioms domain_of_conic_depth
#print axioms A_zero_of_conic
#print axioms P_zero_of_conic
#print axioms family_T_one
#print axioms family_domain

end
end FourCorner.HpConicObstruction
