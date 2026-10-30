import HpConicObstruction
import HpDyadicFamilyPoint

namespace FourCorner.HpOddBadLocal

open HasseNorms HasseNormsInterface HilbertArithmeticHigh11

theorem rho_p_point {K : Type*} [Field K] [CharZero K] (p : ℚ) (hp : 1<p)
    (h2 : IsSquare (2 : K)) (ht : IsSquare ((p : K)^2+1)) (ht0 : (p : K)^2+1 ≠ 0) :
    Nonempty (LocalPoint K (p : K)) := by
  apply (localPoint_iff_localSquares (p : K)).mpr
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast (show p ≠ 0 by linarith)
  have ha0 : (p : K)-1 ≠ 0 := by exact_mod_cast (show p-1 ≠ 0 by linarith)
  have hb0 : (p : K)+1 ≠ 0 := by exact_mod_cast (show p+1 ≠ 0 by linarith)
  refine ⟨(p : K),hp0,by exact_mod_cast (show p ≠ 1 by linarith),
    by exact_mod_cast (show p ≠ -1 by linarith),?_,?_,?_,?_⟩
  · exact ⟨IsSquare.mul_self _,mul_ne_zero hp0 hp0⟩
  · have hh : IsSquare (2*((p : K)-1)*((p : K)-1)) := by
      have he : 2*((p : K)-1)*((p : K)-1)=2*(((p : K)-1)^2) := by ring
      rw [he]
      exact h2.mul (IsSquare.sq _)
    exact ⟨hh,mul_ne_zero (mul_ne_zero (by norm_num) ha0) ha0⟩
  · have hh : IsSquare (2*((p : K)+1)*((p : K)+1)) := by
      have he : 2*((p : K)+1)*((p : K)+1)=2*(((p : K)+1)^2) := by ring
      rw [he]
      exact h2.mul (IsSquare.sq _)
    exact ⟨hh,mul_ne_zero (mul_ne_zero (by norm_num) hb0) hb0⟩
  · have he : ((p : K)-1)*(p : K)+(p : K)+1=(p : K)^2+1 := by ring
    rw [he]
    exact ⟨ht,ht0⟩

theorem square_unit_perturbation (Q : OddPrime) (x y : ℚ_[Q.val])
    (hx : x ≠ 0) (hvx : x.valuation=0) (hsq : IsSquare x)
    (hd : y-x ≠ 0) (hvd : 0<(y-x).valuation) : IsSquare y ∧ y ≠ 0 := by
  refine ⟨HasseOddSymbol.square_of_positive_perturbation Q x y hx hvx hsq hd hvd,?_⟩
  intro hy
  rw [hy,zero_sub,commonRoot_val_neg,hvx] at hvd
  omega

theorem positive_p (Q : OddPrime) (p r : ℚ) (hp : 1<p) (hr : r^2=2*(p+1))
    (hv : 0<padicValRat Q.val p) : Nonempty (LocalPoint ℚ_[Q.val] (p : ℚ_[Q.val])) := by
  have hp0 : (p : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast (show p ≠ 0 by linarith)
  have hb0 : (p : ℚ_[Q.val])+1 ≠ 0 := by exact_mod_cast (show p+1 ≠ 0 by linarith)
  have hpv : 0<(p : ℚ_[Q.val]).valuation := by rwa [Padic.valuation_ratCast]
  have hdiffB : ((p : ℚ_[Q.val])+1)-1=(p : ℚ_[Q.val]) := by ring
  obtain ⟨hbSq,_⟩ := square_unit_perturbation Q 1 ((p : ℚ_[Q.val])+1) one_ne_zero Padic.valuation_one
    IsSquare.one (by rwa [hdiffB]) (by rwa [hdiffB])
  have hrQ : (r : ℚ_[Q.val])^2=2*((p : ℚ_[Q.val])+1) := by exact_mod_cast hr
  have hs2 : IsSquare (2 : ℚ_[Q.val]) := by
    have hh := (IsSquare.sq (r : ℚ_[Q.val])).div hbSq
    have he : (r : ℚ_[Q.val])^2/((p : ℚ_[Q.val])+1)=2 := by rw [hrQ];field_simp
    rwa [he] at hh
  have hdiffT : ((p : ℚ_[Q.val])^2+1)-1=(p : ℚ_[Q.val])^2 := by ring
  obtain ⟨hTSq,hT0⟩ := square_unit_perturbation Q 1 ((p : ℚ_[Q.val])^2+1) one_ne_zero Padic.valuation_one
    IsSquare.one (by rw [hdiffT];exact pow_ne_zero _ hp0) (by rw [hdiffT,Padic.valuation_pow];norm_num;omega)
  exact rho_p_point p hp hs2 hTSq hT0

theorem positive_a (Q : OddPrime) (p s : ℚ) (hp : 1<p) (hs : s^2=3-p) (hs0 : s ≠ 0)
    (hv : 0<padicValRat Q.val (p-1)) : Nonempty (LocalPoint ℚ_[Q.val] (p : ℚ_[Q.val])) := by
  have ha0 : (p : ℚ_[Q.val])-1 ≠ 0 := by exact_mod_cast (show p-1 ≠ 0 by linarith)
  have hb0 : (p : ℚ_[Q.val])+1 ≠ 0 := by exact_mod_cast (show p+1 ≠ 0 by linarith)
  have hsQ0 : (s : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast hs0
  have hav : 0<((p : ℚ_[Q.val])-1).valuation := by
    have he : (p : ℚ_[Q.val])-1=((p-1 : ℚ) : ℚ_[Q.val]) := by simp
    rwa [he,Padic.valuation_ratCast]
  have hbv : ((p : ℚ_[Q.val])+1).valuation=0 := by
    have he : (p : ℚ_[Q.val])+1=((p+1 : ℚ) : ℚ_[Q.val]) := by simp
    rw [he,Padic.valuation_ratCast]
    exact HasseInertParity.positive_a_b_zero Q p hp hv
  have hsEq : (s : ℚ_[Q.val])^2=2-((p : ℚ_[Q.val])-1) := by
    have he : s^2=2-(p-1) := by linear_combination hs
    exact_mod_cast he
  have hsval : ((s : ℚ_[Q.val])^2).valuation=0 := by
    rw [hsEq,commonRoot_val_sub_of_ne (by norm_num) ha0
      (by rw [commonRoot_val_two Q.property.2];omega),commonRoot_val_two Q.property.2,min_eq_left (by omega)]
  have hd2 : (2 : ℚ_[Q.val])-(s : ℚ_[Q.val])^2=(p : ℚ_[Q.val])-1 := by linear_combination -hsEq
  have hs2 := HasseOddSymbol.square_of_positive_perturbation Q ((s : ℚ_[Q.val])^2) 2
    (pow_ne_zero _ hsQ0) hsval (IsSquare.sq _) (by rwa [hd2]) (by rwa [hd2])
  have hdiffT : ((p : ℚ_[Q.val])^2+1)-2=((p : ℚ_[Q.val])-1)*((p : ℚ_[Q.val])+1) := by ring
  obtain ⟨hTSq,hT0⟩ := square_unit_perturbation Q 2 ((p : ℚ_[Q.val])^2+1)
    (by norm_num) (commonRoot_val_two Q.property.2) hs2
    (by rw [hdiffT];exact mul_ne_zero ha0 hb0)
    (by rw [hdiffT,Padic.valuation_mul ha0 hb0,hbv];omega)
  exact rho_p_point p hp hs2 hTSq hT0

#print axioms positive_p
#print axioms positive_a

end FourCorner.HpOddBadLocal
