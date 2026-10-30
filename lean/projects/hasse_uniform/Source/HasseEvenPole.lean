import HasseEvenPoleModel
namespace FourCorner.HasseEvenPole
open HilbertArithmeticHigh11 HasseRationalSource HasseAnchorChoice HasseTangentGlobal
open HasseRationalNormalization HasseConicTangentParity HasseOddBadModels
open HassePositiveBInert HasseHilbertArithmetic HasseOddSymbol HasseEvenPoleModel

/-- Complete original-source even-pole row, including both split and inert
primes, arbitrary negative depth, denominators and every tangent contact. -/
theorem tangentSign_even_pole_depth (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (h : ℕ) (hh : 0<h) (hvp : padicValRat Q.val p= -2*h) :
    tangentSign p hp P D Q.val=1 := by
  have hp0 : p ≠ 0 := by linarith
  have ha0 : p-1 ≠ 0 := by linarith
  have hb0 : p+1 ≠ 0 := by linarith
  obtain ⟨hZ,hU,hV,hW,hT⟩ := coordinates_ne_zero p hp P
  have hw : D.w ≠ 0 := by rcases D.sign with h | h <;> rw [h] <;> simpa using hW
  let r : ℚ := (Q.val : ℚ)^h
  have hr : r ≠ 0 := pow_ne_zero h (by exact_mod_cast Q.property.1.ne_zero)
  have hrv : padicValRat Q.val r=h := by
    dsimp [r]
    rw [padicValRat.pow,padicValRat.self Q.property.1.one_lt]
    simp
  obtain ⟨s,hs,hvu,hvt,hvz,hprim⟩ := exists_primitive_rational_scale (q:=Q.val)
    P.U P.T (P.Z/r) hU hT (div_ne_zero hZ hr)
  let pp : ℚ_[Q.val] := (r^2*p : ℚ)
  let rr : ℚ_[Q.val] := r
  let u : ℚ_[Q.val] := (s*P.U : ℚ)
  let t : ℚ_[Q.val] := (s*P.T : ℚ)
  let z : ℚ_[Q.val] := (s*(P.Z/r) : ℚ)
  let w : ℚ_[Q.val] := (s*D.w : ℚ)
  have hpq : pp ≠ 0 := by dsimp [pp]; exact_mod_cast mul_ne_zero (pow_ne_zero _ hr) hp0
  have huq : u ≠ 0 := by dsimp [u]; exact_mod_cast mul_ne_zero hs hU
  have htq : t ≠ 0 := by dsimp [t]; exact_mod_cast mul_ne_zero hs hT
  have hzq : z ≠ 0 := by dsimp [z]; exact_mod_cast mul_ne_zero hs (div_ne_zero hZ hr)
  have hwq : w ≠ 0 := by dsimp [w]; exact_mod_cast mul_ne_zero hs hw
  have hrval : rr.valuation=h := by dsimp [rr]; rwa [Padic.valuation_ratCast]
  have hpval : pp.valuation=0 := by
    dsimp [pp]
    rw [Padic.valuation_ratCast,padicValRat.mul (pow_ne_zero _ hr) hp0,padicValRat.pow,hrv,hvp]
    norm_num
  have huval : 0≤u.valuation := by dsimp [u]; rwa [Padic.valuation_ratCast]
  have htval : 0≤t.valuation := by dsimp [t]; rwa [Padic.valuation_ratCast]
  have hzval : 0≤z.valuation := by dsimp [z]; rwa [Padic.valuation_ratCast]
  let pi := integralOfVal pp (by omega : 0≤pp.valuation)
  let ri := integralOfVal rr (by omega : 0≤rr.valuation)
  let ui := integralOfVal u huval
  let ti := integralOfVal t htval
  let zi := integralOfVal z hzval
  have hpI : PadicInt.toZMod pi ≠ 0 := integralOfVal_residue_ne_zero pp hpq hpval
  have hrI : PadicInt.toZMod ri=0 := integral_residue_zero_of_positive _ (by omega)
  have haI : PadicInt.toZMod (pi-ri^2) ≠ 0 := by
    simpa only [map_sub,map_pow,hrI,zero_pow (by decide : 2 ≠ 0),sub_zero] using hpI
  have hDU : (pp-rr^2)*w^2=2*(pp+rr^2)*(t^2-2*rr^2*z^2) := by
    have he : (r^2*p-r^2)*(s*D.w)^2=2*(r^2*p+r^2)*((s*P.T)^2-2*r^2*(s*(P.Z/r))^2) := by
      field_simp
      linear_combination D.omission.2
    dsimp [pp,rr,w,t,z]
    exact_mod_cast he
  let yi : ℤ_[Q.val] := 2*(pi+ri^2)*(ti^2-2*ri^2*zi^2)
  have hwval : 0≤w.valuation := integral_of_unit_times_square (pi-ri^2) w yi haI hwq hDU
  let wi := integralOfVal w hwval
  have hCI : (pi-ri^2)*ui^2-pi*ti^2+pi*(pi+ri^2)*zi^2=0 := by
    apply Subtype.ext
    change (pp-rr^2)*u^2-pp*t^2+pp*(pp+rr^2)*z^2=0
    have he : (r^2*p-r^2)*(s*P.U)^2-r^2*p*(s*P.T)^2+r^2*p*(r^2*p+r^2)*(s*(P.Z/r))^2=0 := by
      field_simp
      linear_combination -r^2*s^2*P.equations.2.2
    dsimp [pp,rr,u,t,z]
    exact_mod_cast he
  have hDUI : (pi-ri^2)*wi^2=2*(pi+ri^2)*(ti^2-2*ri^2*zi^2) := Subtype.ext hDU
  have hprimI : PadicInt.toZMod ui ≠ 0 ∨ PadicInt.toZMod ti ≠ 0 ∨ PadicInt.toZMod zi ≠ 0 := by
    rcases hprim with hu | ht | hz
    · exact Or.inl (integralOfVal_residue_ne_zero u huq (by dsimp [u]; rwa [Padic.valuation_ratCast]))
    · exact Or.inr (Or.inl (integralOfVal_residue_ne_zero t htq (by dsimp [t]; rwa [Padic.valuation_ratCast])))
    · exact Or.inr (Or.inr (integralOfVal_residue_ne_zero z hzq (by dsimp [z]; rwa [Padic.valuation_ratCast])))
  by_cases htI : PadicInt.toZMod ti ≠ 0
  · let L := secondPolar p P.Z P.U P.T P.Z D.w P.T
    have hL : L ≠ 0 := by
      intro he
      have hn := D.coefficient_negative
      change -p*L<0 at hn
      rw [he,mul_zero] at hn
      exact lt_irrefl _ hn
    let li := (pi-ri^2)*ui*(pi*(pi+ri^2)*(wi+2*ti+2*ri*zi))-
      pi*ti*(-(pi+ri^2)*((pi-ri^2)*wi+2*pi*ti+2*ri*(pi-ri^2)*zi))+
      pi*(pi+ri^2)*zi*(ri*(pi-ri^2)*wi-2*ri^2*(pi+ri^2)*zi)
    have hscale : (li : ℚ_[Q.val])=((s^2*r^6*L : ℚ) : ℚ_[Q.val]) := by
      change (pp-rr^2)*u*(pp*(pp+rr^2)*(w+2*t+2*rr*z))-
        pp*t*(-(pp+rr^2)*((pp-rr^2)*w+2*pp*t+2*rr*(pp-rr^2)*z))+
        pp*(pp+rr^2)*z*(rr*(pp-rr^2)*w-2*rr^2*(pp+rr^2)*z)=_
      dsimp [pp,rr,u,w,t,z,L,secondPolar,anchorU,anchorT,anchorZ]
      push_cast
      field_simp
      <;> ring
    have hli : li ≠ 0 := by
      intro he
      have hn : ((s^2*r^6*L : ℚ) : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast mul_ne_zero (mul_ne_zero (pow_ne_zero _ hs) (pow_ne_zero _ hr)) hL
      apply hn
      rw [← hscale,he]
      rfl
    have heven := even_pole_model_tangent_even Q pi ri ui ti zi wi hpI hrI htI hCI hDUI hli
    change Even (li : ℚ_[Q.val]).valuation at heven
    rw [hscale,Padic.valuation_ratCast,padicValRat.mul (mul_ne_zero (pow_ne_zero _ hs) (pow_ne_zero _ hr)) hL,
      padicValRat.mul (pow_ne_zero _ hs) (pow_ne_zero _ hr),padicValRat.pow,padicValRat.pow,hrv] at heven
    have haVal : padicValRat Q.val (p-1)=padicValRat Q.val p := by
      have he := commonRoot_val_sub_of_ne (show (p : ℚ_[Q.val]) ≠ 0 by exact_mod_cast hp0)
        (one_ne_zero : (1 : ℚ_[Q.val]) ≠ 0)
        (by rw [Padic.valuation_ratCast,Padic.valuation_one,hvp]; omega)
      have heq : (p : ℚ_[Q.val])-1=((p-1 : ℚ) : ℚ_[Q.val]) := by simp
      rw [heq,Padic.valuation_ratCast,Padic.valuation_ratCast,Padic.valuation_one,hvp,min_eq_left (by omega : -2*(h : ℤ)≤0)] at he
      rwa [hvp]
    rw [tangentSign]
    apply rationalSign_one_of_even_valuations Q
    · change Even (padicValRat Q.val (-(p-1)))
      rw [padicValRat.neg,haVal,hvp]
      exact ⟨-(h : ℤ),by ring⟩
    · change Even (padicValRat Q.val (-p*L))
      rw [padicValRat.mul (neg_ne_zero.mpr hp0) hL,padicValRat.neg,hvp]
      rw [Int.even_iff] at heven ⊢
      norm_num only [Nat.cast_ofNat] at heven
      omega
  · have hsquare := even_pole_model_square_of_t_nonunit Q pi ri ui ti zi hpI hrI (not_ne_iff.mp htI) hCI hprimI
    have hrq : rr ≠ 0 := by dsimp [rr]; exact_mod_cast hr
    have heq : ((-(pi-ri^2) : ℤ_[Q.val]) : ℚ_[Q.val])/(rr^2)=
        (firstCoefficient p : ℚ_[Q.val]) := by
      change -(pp-rr^2)/rr^2=_
      dsimp [pp,rr,firstCoefficient]
      push_cast
      field_simp
      <;> ring
    have hfirst := hsquare.div (IsSquare.sq rr)
    rw [heq] at hfirst
    rw [tangentSign,rationalSign_eq_oddSign]
    exact oddSign_one_of_left_square Q _ _ _ _ hfirst

theorem tangentSign_even_pole (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (hv : padicValRat Q.val p<0) (he : Even (padicValRat Q.val p)) :
    tangentSign p hp P D Q.val=1 := by
  obtain ⟨k,hk⟩ := he
  have hkneg : k<0 := by omega
  have hkn : ((-k).toNat : ℤ)= -k := Int.toNat_of_nonneg (by omega)
  exact tangentSign_even_pole_depth Q p hp P D (-k).toNat (by omega) (by omega)

#print axioms tangentSign_even_pole_depth
#print axioms tangentSign_even_pole
end FourCorner.HasseEvenPole
