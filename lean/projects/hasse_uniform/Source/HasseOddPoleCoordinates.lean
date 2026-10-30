import HassePoleParameters
namespace FourCorner.HasseOddPoleCoordinates
open HilbertArithmeticHigh11 HasseRationalSource HasseAnchorChoice HasseTangentGlobal
open HassePoleParameters HassePositiveBInert HasseRationalNormalization

/-- The first source equation forces the exact strict z-depth at every
odd-depth pole after the actual normalization T=1. -/
theorem z_depth_at_odd_pole (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P) (hT : P.T=1)
    (hv : padicValRat Q.val p<0) (hodd : Odd (padicValRat Q.val p)) :
    0<padicValRat Q.val p+2*padicValRat Q.val P.Z := by
  have hp0 : p ≠ 0 := by linarith
  obtain ⟨hZ,hU,hV,hW,hTT⟩ := coordinates_ne_zero p hp P
  let pp : ℚ_[Q.val] := p
  let z : ℚ_[Q.val] := P.Z
  let v : ℚ_[Q.val] := P.V
  have hpq : pp ≠ 0 := by dsimp [pp]; exact_mod_cast hp0
  have hzq : z ≠ 0 := by dsimp [z]; exact_mod_cast hZ
  have hvq : v ≠ 0 := by dsimp [v]; exact_mod_cast hV
  have h4 : (4 : ℚ_[Q.val]) ≠ 0 := by norm_num
  have h2 : (2 : ℚ_[Q.val]) ≠ 0 := by norm_num
  have h4v : (4 : ℚ_[Q.val]).valuation=0 := by
    have he : (4 : ℚ_[Q.val])=2^2 := by norm_num
    rw [he,Padic.valuation_pow,commonRoot_val_two Q.property.2]
    simp
  have he : v^2=2-4*pp*z^2 := by
    have hr := D.omission.1
    rw [hT] at hr
    dsimp [v,pp,z]
    exact_mod_cast hr
  have hcoeff : (4*pp*z^2).valuation=padicValRat Q.val p+2*padicValRat Q.val P.Z := by
    rw [Padic.valuation_mul (mul_ne_zero h4 hpq) (pow_ne_zero _ hzq),
      Padic.valuation_mul h4 hpq,h4v,Padic.valuation_pow]
    dsimp [pp,z]
    rw [Padic.valuation_ratCast,Padic.valuation_ratCast]
    ring
  have hzero : padicValRat Q.val p+2*padicValRat Q.val P.Z ≠ 0 := by
    intro heq
    rw [Int.odd_iff] at hodd
    omega
  by_contra hn
  have hneg : padicValRat Q.val p+2*padicValRat Q.val P.Z<0 := by omega
  have hval := congrArg Padic.valuation he
  rw [Padic.valuation_pow,commonRoot_val_sub_of_ne h2 (mul_ne_zero (mul_ne_zero h4 hpq) (pow_ne_zero _ hzq))
    (by rw [commonRoot_val_two Q.property.2,hcoeff]; omega),commonRoot_val_two Q.property.2,hcoeff,
    min_eq_right (by omega : padicValRat Q.val p+2*padicValRat Q.val P.Z≤0)] at hval
  rw [Int.odd_iff] at hodd
  norm_num only [Nat.cast_ofNat] at hval
  omega

/-- Every normalized original source at an odd pole has unit U and W,
and Z has strictly positive valuation. -/
theorem unit_coordinates_at_odd_pole (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P) (hT : P.T=1)
    (hv : padicValRat Q.val p<0) (hodd : Odd (padicValRat Q.val p)) :
    0<padicValRat Q.val P.Z ∧ padicValRat Q.val P.U=0 ∧ padicValRat Q.val D.w=0 := by
  have hp0 : p ≠ 0 := by linarith
  have ha0 : p-1 ≠ 0 := by linarith
  have hb0 : p+1 ≠ 0 := by linarith
  obtain ⟨hZ,hU,hV,hW,hTT⟩ := coordinates_ne_zero p hp P
  have hw : D.w ≠ 0 := by rcases D.sign with h | h <;> rw [h] <;> simpa using hW
  have hdepth := z_depth_at_odd_pole Q p hp P D hT hv hodd
  have hzpos : 0<padicValRat Q.val P.Z := by omega
  refine ⟨hzpos,?_,?_⟩
  all_goals
    let pp : ℚ_[Q.val] := p
    let a : ℚ_[Q.val] := ((p-1 : ℚ) : ℚ_[Q.val])
    let b : ℚ_[Q.val] := ((p+1 : ℚ) : ℚ_[Q.val])
    let z : ℚ_[Q.val] := P.Z
    have hpq : pp ≠ 0 := by dsimp [pp]; exact_mod_cast hp0
    have haq : a ≠ 0 := by dsimp [a]; exact_mod_cast ha0
    have hbq : b ≠ 0 := by dsimp [b]; exact_mod_cast hb0
    have hzq : z ≠ 0 := by dsimp [z]; exact_mod_cast hZ
    have hav : a.valuation=pp.valuation := pole_a_valuation Q p hp hv
    have hbv : b.valuation=pp.valuation := pole_b_valuation Q p hp hv
    have hzv : 0<z.valuation := by dsimp [z]; rwa [Padic.valuation_ratCast]
    have htwo : (2 : ℚ_[Q.val]) ≠ 0 := by norm_num
  · let u : ℚ_[Q.val] := P.U
    have huq : u ≠ 0 := by dsimp [u]; exact_mod_cast hU
    have hbx : (b*z^2).valuation>0 := by
      rw [Padic.valuation_mul hbq (pow_ne_zero _ hzq),hbv,Padic.valuation_pow]
      dsimp [pp,z]
      rw [Padic.valuation_ratCast,Padic.valuation_ratCast]
      norm_num only [Nat.cast_ofNat]
      exact hdepth
    have h1 : (1-b*z^2).valuation=0 := by
      rw [commonRoot_val_sub_of_ne one_ne_zero (mul_ne_zero hbq (pow_ne_zero _ hzq))
        (by rw [Padic.valuation_one]; omega),Padic.valuation_one,min_eq_left (by omega)]
    have hn : 1-b*z^2 ≠ 0 := commonRoot_sub_ne_zero_of_val_ne
      (by rw [Padic.valuation_one]; omega)
    have he : a*u^2=pp*(1-b*z^2) := by
      have hr := P.equations.2.2
      rw [hT] at hr
      have hrat : (p-1)*P.U^2=p*(1-(p+1)*P.Z^2) := by linear_combination -hr
      dsimp [a,u,pp,b,z]
      exact_mod_cast hrat
    have heval := congrArg Padic.valuation he
    rw [Padic.valuation_mul haq (pow_ne_zero _ huq),Padic.valuation_pow,
      Padic.valuation_mul hpq hn,h1,hav] at heval
    have huval : u.valuation=0 := by norm_num only [Nat.cast_ofNat] at heval; omega
    dsimp [u] at huval
    rwa [Padic.valuation_ratCast] at huval
  · let w : ℚ_[Q.val] := D.w
    have hwq : w ≠ 0 := by dsimp [w]; exact_mod_cast hw
    have hzx : (2*z^2).valuation>0 := by
      rw [Padic.valuation_mul htwo (pow_ne_zero _ hzq),commonRoot_val_two Q.property.2,Padic.valuation_pow]
      omega
    have h1 : (1-2*z^2).valuation=0 := by
      rw [commonRoot_val_sub_of_ne one_ne_zero (mul_ne_zero htwo (pow_ne_zero _ hzq))
        (by rw [Padic.valuation_one]; omega),Padic.valuation_one,min_eq_left (by omega)]
    have hn : 1-2*z^2 ≠ 0 := commonRoot_sub_ne_zero_of_val_ne
      (by rw [Padic.valuation_one]; omega)
    have he : a*w^2=2*b*(1-2*z^2) := by
      have hr := D.omission.2
      rw [hT] at hr
      dsimp [a,w,b,z]
      exact_mod_cast hr
    have heval := congrArg Padic.valuation he
    rw [Padic.valuation_mul haq (pow_ne_zero _ hwq),Padic.valuation_pow,
      Padic.valuation_mul (mul_ne_zero htwo hbq) hn,
      Padic.valuation_mul htwo hbq,commonRoot_val_two Q.property.2,h1,hav,hbv] at heval
    have hwval : w.valuation=0 := by norm_num only [Nat.cast_ofNat] at heval; omega
    dsimp [w] at hwval
    rwa [Padic.valuation_ratCast] at hwval

#print axioms unit_coordinates_at_odd_pole

#print axioms z_depth_at_odd_pole
end FourCorner.HasseOddPoleCoordinates
