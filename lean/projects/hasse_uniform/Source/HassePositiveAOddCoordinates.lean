import HasseOddPole
namespace FourCorner.HassePositiveAOddCoordinates
open HilbertArithmeticHigh11 HasseRationalSource HasseAnchorChoice HasseTangentGlobal
open HassePositiveBInert HasseRationalNormalization HasseOddPoleResidues

/-- At a positive odd depth of a, the full original V equation forces U/Z
unit and its square congruent to p. No point at V=0 is substituted. -/
theorem normalized_U_valuation (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (hZ : P.Z=1)
    (hv : 0<padicValRat Q.val (p-1)) (hodd : Odd (padicValRat Q.val (p-1))) :
    padicValRat Q.val P.U=0 ∧ 0<padicValRat Q.val (P.U^2-p) := by
  have hp0 : p ≠ 0 := by linarith
  have ha0 : p-1 ≠ 0 := by linarith
  obtain ⟨hZZ,hU,hV,hW,hT⟩ := coordinates_ne_zero p hp P
  let pp : ℚ_[Q.val] := p
  let a : ℚ_[Q.val] := ((p-1 : ℚ) : ℚ_[Q.val])
  let u : ℚ_[Q.val] := P.U
  let v : ℚ_[Q.val] := P.V
  have hpq : pp ≠ 0 := by dsimp [pp]; exact_mod_cast hp0
  have haq : a ≠ 0 := by dsimp [a]; exact_mod_cast ha0
  have huq : u ≠ 0 := by dsimp [u]; exact_mod_cast hU
  have hvq : v ≠ 0 := by dsimp [v]; exact_mod_cast hV
  have htwo : (2 : ℚ_[Q.val]) ≠ 0 := by norm_num
  have hav : 0<a.valuation := by dsimp [a]; rwa [Padic.valuation_ratCast]
  have hpval : pp.valuation=0 := by
    apply commonRoot_val_eq_zero_of_sub_one_pos
    have he : pp-1=a := by simp [pp,a]
    rwa [he]
  have he : pp*v^2=2*a*(u^2-pp) := by
    have hr := P.equations.1
    rw [hZ] at hr
    norm_num only [one_pow,mul_one] at hr
    dsimp [pp,v,a,u]
    exact_mod_cast hr
  have hd : u^2-pp ≠ 0 := by
    intro hd
    rw [hd,mul_zero] at he
    exact (mul_ne_zero hpq (pow_ne_zero 2 hvq)) he
  have heval := congrArg Padic.valuation he
  rw [Padic.valuation_mul hpq (pow_ne_zero _ hvq),hpval,Padic.valuation_pow,
    Padic.valuation_mul (mul_ne_zero htwo haq) hd,
    Padic.valuation_mul htwo haq,commonRoot_val_two Q.property.2] at heval
  have haodd : Odd a.valuation := by dsimp [a]; rwa [Padic.valuation_ratCast]
  have huval : u.valuation=0 := by
    by_contra hne
    have hvdiff : (u^2-pp).valuation=2*min u.valuation 0 := by
      rw [commonRoot_val_sub_of_ne (pow_ne_zero _ huq) hpq
        (by rw [Padic.valuation_pow,hpval]; norm_num only [Nat.cast_ofNat]; omega),Padic.valuation_pow,hpval]
      norm_num only [Nat.cast_ofNat]
      omega
    rw [hvdiff] at heval
    rw [Int.odd_iff] at haodd
    norm_num only [Nat.cast_ofNat] at heval
    omega
  have hdnonneg : 0≤(u^2-pp).valuation := by
    have hh := Padic.le_valuation_add (x:=u^2) (y:= -pp) (by simpa only [← sub_eq_add_neg] using hd)
    rw [← sub_eq_add_neg,Padic.valuation_pow,huval,commonRoot_val_neg,hpval] at hh
    norm_num at hh
    simpa only [one_mul] using hh
  have hdpos : 0<(u^2-pp).valuation := by
    rw [Int.odd_iff] at haodd
    norm_num only [Nat.cast_ofNat] at heval
    omega
  refine ⟨?_,?_⟩
  · dsimp [u] at huval
    rwa [Padic.valuation_ratCast] at huval
  · have heq : u^2-pp=((P.U^2-p : ℚ) : ℚ_[Q.val]) := by simp [u,pp]
    rwa [heq,Padic.valuation_ratCast] at hdpos

/-- Literal completed residue coordinates of the original normalized source
at positive odd depth of a. -/
theorem residue_coordinates (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P) (hZ : P.Z=1)
    (hv : 0<padicValRat Q.val (p-1)) (hodd : Odd (padicValRat Q.val (p-1))) :
    ∃ u t w : ℤ_[Q.val], (u : ℚ_[Q.val])=(P.U : ℚ_[Q.val]) ∧
      (t : ℚ_[Q.val])=(P.T : ℚ_[Q.val]) ∧ (w : ℚ_[Q.val])=(D.w : ℚ_[Q.val]) ∧
      (PadicInt.toZMod u)^2=1 ∧ (PadicInt.toZMod t)^2=2 ∧ (PadicInt.toZMod w)^2=8 := by
  have hp0 : p ≠ 0 := by linarith
  have ha0 : p-1 ≠ 0 := by linarith
  obtain ⟨hZZ,hU,hV,hW,hT⟩ := coordinates_ne_zero p hp P
  have hw : D.w ≠ 0 := by rcases D.sign with h | h <;> rw [h] <;> simpa using hW
  have hc := normalized_U_valuation Q p hp P hZ hv hodd
  let pp : ℚ_[Q.val] := p
  let uu : ℚ_[Q.val] := P.U
  let tt : ℚ_[Q.val] := P.T
  let ww : ℚ_[Q.val] := D.w
  have hpq : pp ≠ 0 := by dsimp [pp]; exact_mod_cast hp0
  have htq : tt ≠ 0 := by dsimp [tt]; exact_mod_cast hT
  have hwq : ww ≠ 0 := by dsimp [ww]; exact_mod_cast hw
  have hpdelta : 0<(pp-1).valuation := by
    have he : pp-1=((p-1 : ℚ) : ℚ_[Q.val]) := by simp [pp]
    rw [he,Padic.valuation_ratCast]
    exact hv
  have hpval : pp.valuation=0 := commonRoot_val_eq_zero_of_sub_one_pos hpdelta
  have huval : uu.valuation=0 := by dsimp [uu]; rw [Padic.valuation_ratCast]; exact hc.1
  let pi := integralOfVal pp (by omega : 0≤pp.valuation)
  let ui := integralOfVal uu (by omega : 0≤uu.valuation)
  have hpi : PadicInt.toZMod pi=1 := integral_residue_one_of_sub_one_positive pp hpval hpdelta
  have hpi0 : PadicInt.toZMod pi ≠ 0 := by rw [hpi]; exact one_ne_zero
  have hudelta : 0<(uu^2-pp).valuation := by
    have he : uu^2-pp=((P.U^2-p : ℚ) : ℚ_[Q.val]) := by simp [uu,pp]
    rw [he,Padic.valuation_ratCast]
    exact hc.2
  have hui : (PadicInt.toZMod ui)^2=1 := by
    have he : ui^2-pi=integralOfVal (uu^2-pp) (by omega : 0≤(uu^2-pp).valuation) := rfl
    have hh := integral_residue_zero_of_positive (uu^2-pp) hudelta
    rw [← he,map_sub,map_pow,hpi] at hh
    linear_combination hh
  let yt : ℤ_[Q.val] := (pi-1)*ui^2+pi*(pi+1)
  let yw : ℤ_[Q.val] := 2*(pi+1)*(ui^2+pi)
  have hTfield : pp*tt^2=(yt : ℚ_[Q.val]) := by
    change pp*tt^2=(pp-1)*uu^2+pp*(pp+1)
    have hr := P.equations.2.2
    rw [hZ] at hr
    norm_num only [one_pow,mul_one] at hr
    dsimp [pp,tt,uu]
    exact_mod_cast hr
  have hWfield : pp*ww^2=(yw : ℚ_[Q.val]) := by
    change pp*ww^2=2*(pp+1)*(uu^2+pp)
    have hr := P.equations.2.1
    have hwsq : D.w^2=P.W^2 := by rcases D.sign with h | h <;> simp only [h,neg_sq]
    rw [hZ,← hwsq] at hr
    norm_num only [one_pow,mul_one] at hr
    dsimp [pp,ww,uu]
    exact_mod_cast hr
  have htval : 0≤tt.valuation := integral_of_unit_times_square pi tt yt hpi0 htq hTfield
  have hwval : 0≤ww.valuation := integral_of_unit_times_square pi ww yw hpi0 hwq hWfield
  let ti := integralOfVal tt htval
  let wi := integralOfVal ww hwval
  have hTI : pi*ti^2=yt := Subtype.ext hTfield
  have hWI : pi*wi^2=yw := Subtype.ext hWfield
  refine ⟨ui,ti,wi,rfl,rfl,rfl,hui,?_,?_⟩
  · have hh := congrArg PadicInt.toZMod hTI
    dsimp [yt] at hh
    norm_num only [map_mul,map_pow,map_sub,map_add,map_one,hpi,hui] at hh
    simpa only [one_mul] using hh
  · have hh := congrArg PadicInt.toZMod hWI
    dsimp [yw] at hh
    norm_num only [map_mul,map_pow,map_sub,map_add,map_one,map_ofNat,hpi,hui] at hh
    simpa only [one_mul] using hh

#print axioms normalized_U_valuation
#print axioms residue_coordinates
end FourCorner.HassePositiveAOddCoordinates
