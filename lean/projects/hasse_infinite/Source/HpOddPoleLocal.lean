import HpOddMoreLocal

namespace FourCorner.HpOddPoleLocal
open HasseNorms HasseNormsInterface HilbertArithmeticHigh11
noncomputable section

theorem principal (Q : OddPrime) (x : ℚ_[Q.val]) (hx : x ≠ 0) (hv : 0<x.valuation) :
    IsSquare (1+x) ∧ 1+x ≠ 0 := by
  exact HpOddBadLocal.square_unit_perturbation Q 1 (1+x) one_ne_zero
    Padic.valuation_one IsSquare.one (by simpa) (by simpa)

/-- A genuine pole witness rho=-(p+1)/(p+3), using the paper's conic
s²=3-p and odd-adic principal-unit square roots. -/
theorem pole (Q : OddPrime) (p s : ℚ) (hp : 1<p)
    (hs : s^2=3-p) (hv : padicValRat Q.val p<0) :
    Nonempty (LocalPoint ℚ_[Q.val] (p : ℚ_[Q.val])) := by
  let P : ℚ_[Q.val] := p
  let h : ℚ_[Q.val] := P⁻¹
  have hP : P ≠ 0 := by dsimp [P];exact_mod_cast (show p ≠ 0 by linarith)
  have ha : P-1 ≠ 0 := by dsimp [P];exact_mod_cast (show p-1 ≠ 0 by linarith)
  have hb : P+1 ≠ 0 := by dsimp [P];exact_mod_cast (show p+1 ≠ 0 by linarith)
  have hd : P+3 ≠ 0 := by dsimp [P];exact_mod_cast (show p+3 ≠ 0 by linarith)
  have hp2 : P+2 ≠ 0 := by dsimp [P];exact_mod_cast (show p+2 ≠ 0 by linarith)
  have hh : h ≠ 0 := inv_ne_zero hP
  have hhv : 0<h.valuation := by dsimp [h,P];rw [Padic.valuation_inv,Padic.valuation_ratCast];omega
  have h3v : 0≤(3 : ℚ_[Q.val]).valuation := by
    rw [Padic.valuation_ofNat]
    exact_mod_cast (Nat.zero_le (padicValNat Q.val 3))
  obtain ⟨hp1,hp10⟩ := principal Q h hh hhv
  obtain ⟨hm1,hm10⟩ := principal Q (-h) (neg_ne_zero.mpr hh) (by rwa [commonRoot_val_neg])
  obtain ⟨hp2s,hp20⟩ := principal Q (2*h) (mul_ne_zero (by norm_num) hh)
    (by rw [Padic.valuation_mul (by norm_num) hh,commonRoot_val_two Q.property.2];omega)
  obtain ⟨hp3,hp30⟩ := principal Q (3*h) (mul_ne_zero (by norm_num) hh)
    (by rw [Padic.valuation_mul (by norm_num) hh];omega)
  obtain ⟨hm3,hm30⟩ := principal Q (-(3*h)) (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hh))
    (by rw [commonRoot_val_neg,Padic.valuation_mul (by norm_num) hh];omega)
  have hmP : IsSquare (-P) := by
    have hsq := (IsSquare.sq (s : ℚ_[Q.val])).div hm3
    have hs' : (s : ℚ_[Q.val])^2=3-P := by dsimp [P];exact_mod_cast hs
    have he : (s : ℚ_[Q.val])^2/(1+ -(3*h))= -P := by
      rw [hs']
      apply (div_eq_iff hm30).mpr
      dsimp [h]
      field_simp [hP]
      <;> ring
    rwa [he] at hsq
  let rho : ℚ_[Q.val] := -(P+1)/(P+3)
  have heU : P*rho=(-P)*((1+h)/(1+3*h)) := by
    dsimp [rho,h]
    field_simp [hP,hd]
    <;> ring
  have heV : 2*(P-1)*(rho-1)=4*(-P)*(1+ -h)*(1+2*h)/(1+3*h) := by
    dsimp [rho,h]
    field_simp [hP,hd]
    <;> ring
  have heW : 2*(P+1)*(rho+1)=4*(1+h)/(1+3*h) := by
    dsimp [rho,h]
    field_simp [hP,hd]
    <;> ring
  have heT : (P-1)*rho+P+1=4*(1+h)/(1+3*h) := by
    dsimp [rho,h]
    field_simp [hP,hd]
    <;> ring
  apply (localPoint_iff_localSquares P).mpr
  refine ⟨rho,div_ne_zero (neg_ne_zero.mpr hb) hd,?_,?_,?_,?_,?_,?_⟩
  · intro he
    have hh' : -(P+1)=P+3 := (div_eq_one_iff_eq hd).mp he
    apply hp2
    linear_combination (-1/2 : ℚ_[Q.val])*hh'
  · intro he
    have hh' : -(P+1)= -(P+3) := (div_eq_iff hd).mp he |>.trans (by ring)
    have : (2 : ℚ_[Q.val])=0 := by linear_combination hh'
    norm_num at this
  · rw [heU]
    exact ⟨hmP.mul (hp1.div hp3),mul_ne_zero (neg_ne_zero.mpr hP) (div_ne_zero hp10 hp30)⟩
  · rw [heV]
    exact ⟨(((by exact ⟨2,by norm_num⟩ : IsSquare (4 : ℚ_[Q.val])).mul hmP).mul hm1).mul hp2s |>.div hp3,
      div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (neg_ne_zero.mpr hP)) hm10) hp20) hp30⟩
  · rw [heW]
    exact ⟨((by exact ⟨2,by norm_num⟩ : IsSquare (4 : ℚ_[Q.val])).mul hp1).div hp3,
      div_ne_zero (mul_ne_zero (by norm_num) hp10) hp30⟩
  · rw [heT]
    exact ⟨((by exact ⟨2,by norm_num⟩ : IsSquare (4 : ℚ_[Q.val])).mul hp1).div hp3,
      div_ne_zero (mul_ne_zero (by norm_num) hp10) hp30⟩

#print axioms pole
end
end FourCorner.HpOddPoleLocal
