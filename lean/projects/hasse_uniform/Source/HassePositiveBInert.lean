import HasseOddBadModels

namespace FourCorner.HassePositiveBInert

open HilbertArithmeticHigh11 HasseRationalSource HasseAnchorChoice HasseTangentGlobal
open HasseRationalNormalization HasseConicTangentParity HasseOddBadModels
open HasseOddSymbol HasseLocalUnits

variable {q : ℕ} [Fact q.Prime]

theorem integral_residue_zero_of_positive (x : ℚ_[q]) (hv : 0<x.valuation) :
    PadicInt.toZMod (integralOfVal x (by omega))=0 := by
  by_contra hn
  have hh := valuation_zero_of_residue_ne_zero (integralOfVal x (by omega)) hn
  change x.valuation=0 at hh
  omega

theorem integral_of_unit_times_square (a : ℤ_[q]) (x : ℚ_[q]) (y : ℤ_[q])
    (ha : PadicInt.toZMod a ≠ 0) (hx : x ≠ 0)
    (he : (a : ℚ_[q])*x^2=(y : ℚ_[q])) : 0≤x.valuation := by
  have ha0 : (a : ℚ_[q]) ≠ 0 := by
    intro hh
    have hh' := PadicInt.coe_eq_zero.mp hh
    exact ha (by simp [hh'])
  have hh := congrArg Padic.valuation he
  rw [Padic.valuation_mul ha0 (pow_ne_zero _ hx),
    valuation_zero_of_residue_ne_zero a ha,Padic.valuation_pow] at hh
  have hy := y.valuation_coe_nonneg
  norm_num only [Nat.cast_ofNat] at hh
  omega

/-- Exact valuation parity of the original rational second coefficient,
for the entire positive-b inert branch, at every half-depth and contact depth. -/
theorem secondCoefficient_positive_b_parity (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (h2 : ¬ IsSquare (2 : ZMod Q.val))
    (h : ℕ) (hh : 0<h) (hvb : padicValRat Q.val (p+1)=2*h) :
    ((padicValRat Q.val (secondCoefficient p P D) : ℤ) : ZMod 2)=(h : ZMod 2) := by
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
  let B : ℚ := (p+1)/r^2
  have hB : B ≠ 0 := div_ne_zero hb0 (pow_ne_zero _ hr)
  have hBv : padicValRat Q.val B=0 := by
    dsimp [B]
    rw [padicValRat.div hb0 (pow_ne_zero _ hr),padicValRat.pow,hrv,hvb]
    norm_num
  obtain ⟨s,hs,hvu,hvt,hvz,hprim⟩ := exists_primitive_rational_scale (q:=Q.val)
    (P.U/r) (P.T/r) P.Z (div_ne_zero hU hr) (div_ne_zero hT hr) hZ
  let pp : ℚ_[Q.val] := p
  let rr : ℚ_[Q.val] := r
  let BB : ℚ_[Q.val] := B
  let u : ℚ_[Q.val] := (s*(P.U/r) : ℚ)
  let t : ℚ_[Q.val] := (s*(P.T/r) : ℚ)
  let z : ℚ_[Q.val] := (s*P.Z : ℚ)
  let w : ℚ_[Q.val] := (s*(D.w/r) : ℚ)
  have hpq : pp ≠ 0 := by dsimp [pp]; exact_mod_cast hp0
  have hrq : rr ≠ 0 := by dsimp [rr]; exact_mod_cast hr
  have hBq : BB ≠ 0 := by dsimp [BB]; exact_mod_cast hB
  have huq : u ≠ 0 := by dsimp [u]; exact_mod_cast mul_ne_zero hs (div_ne_zero hU hr)
  have htq : t ≠ 0 := by dsimp [t]; exact_mod_cast mul_ne_zero hs (div_ne_zero hT hr)
  have hzq : z ≠ 0 := by dsimp [z]; exact_mod_cast mul_ne_zero hs hZ
  have hwq : w ≠ 0 := by dsimp [w]; exact_mod_cast mul_ne_zero hs (div_ne_zero hw hr)
  have hrval : rr.valuation=h := by dsimp [rr]; rwa [Padic.valuation_ratCast]
  have hBval : BB.valuation=0 := by dsimp [BB]; rwa [Padic.valuation_ratCast]
  have hbq : pp+1=rr^2*BB := by
    dsimp [pp,rr,BB,B]
    push_cast
    field_simp
  have hbval : (pp+1).valuation=2*h := by
    have he : pp+1=((p+1 : ℚ) : ℚ_[Q.val]) := by simp [pp]
    rw [he,Padic.valuation_ratCast,hvb]
  have hbb0 : pp+1 ≠ 0 := by dsimp [pp]; exact_mod_cast hb0
  have hpval : pp.valuation=0 := by
    have he := commonRoot_val_sub_of_ne hbb0 (show (1 : ℚ_[Q.val]) ≠ 0 by exact one_ne_zero)
      (show (pp+1).valuation ≠ (1 : ℚ_[Q.val]).valuation by rw [hbval,Padic.valuation_one]; omega)
    simpa only [add_sub_cancel_right,Padic.valuation_one,hbval,min_eq_right (show (0 : ℤ)≤2*h by omega)] using he
  have huval : 0≤u.valuation := by dsimp [u]; rwa [Padic.valuation_ratCast]
  have htval : 0≤t.valuation := by dsimp [t]; rwa [Padic.valuation_ratCast]
  have hzval : 0≤z.valuation := by dsimp [z]; rwa [Padic.valuation_ratCast]
  let pi := integralOfVal pp (by omega : 0≤pp.valuation)
  let ri := integralOfVal rr (by omega : 0≤rr.valuation)
  let Bi := integralOfVal BB (by omega : 0≤BB.valuation)
  let ui := integralOfVal u huval
  let ti := integralOfVal t htval
  let zi := integralOfVal z hzval
  have hpI : PadicInt.toZMod pi= -1 := by
    have hbI : PadicInt.toZMod (pi+1)=0 := by
      have he : (pi+1 : ℤ_[Q.val])=integralOfVal (pp+1) (by omega : 0≤(pp+1).valuation) := rfl
      rw [he]
      exact integral_residue_zero_of_positive _ (by omega)
    rw [map_add,map_one] at hbI
    linear_combination hbI
  have hrI : PadicInt.toZMod ri=0 := integral_residue_zero_of_positive _ (by omega)
  have hBI : PadicInt.toZMod Bi ≠ 0 := integralOfVal_residue_ne_zero BB hBq hBval
  have htwo : (2 : ZMod Q.val) ≠ 0 := by
    intro he
    apply h2
    rw [he]
    exact IsSquare.zero
  have haI : PadicInt.toZMod (pi-1) ≠ 0 := by
    simpa only [map_sub,map_one,hpI,show (-1 : ZMod Q.val)-1= -2 by ring,neg_ne_zero] using htwo
  have hDU : (pp-1)*w^2=2*BB*(rr^2*t^2-2*z^2) := by
    have he : (p-1)*(s*(D.w/r))^2=2*B*(r^2*(s*(P.T/r))^2-2*(s*P.Z)^2) := by
      dsimp [B]
      field_simp
      linear_combination D.omission.2
    dsimp [pp,w,BB,rr,t,z]
    exact_mod_cast he
  let yi : ℤ_[Q.val] := 2*Bi*(ri^2*ti^2-2*zi^2)
  have hwval : 0≤w.valuation := integral_of_unit_times_square (pi-1) w yi haI hwq hDU
  let wi := integralOfVal w hwval
  have hbI : pi+1=ri^2*Bi := Subtype.ext hbq
  have hCI : (pi-1)*ui^2-pi*ti^2+pi*Bi*zi^2=0 := by
    apply Subtype.ext
    change (pp-1)*u^2-pp*t^2+pp*BB*z^2=0
    have he : (p-1)*(s*(P.U/r))^2-p*(s*(P.T/r))^2+p*B*(s*P.Z)^2=0 := by
      dsimp [B]
      field_simp
      linear_combination -s^2*P.equations.2.2
    dsimp [pp,u,t,BB,z]
    exact_mod_cast he
  have hDUI : (pi-1)*wi^2=2*Bi*(ri^2*ti^2-2*zi^2) := Subtype.ext hDU
  have hprimI : PadicInt.toZMod ui ≠ 0 ∨ PadicInt.toZMod ti ≠ 0 ∨ PadicInt.toZMod zi ≠ 0 := by
    rcases hprim with hu | ht | hz
    · exact Or.inl (integralOfVal_residue_ne_zero u huq (by dsimp [u]; rwa [Padic.valuation_ratCast]))
    · exact Or.inr (Or.inl (integralOfVal_residue_ne_zero t htq (by dsimp [t]; rwa [Padic.valuation_ratCast])))
    · exact Or.inr (Or.inr (integralOfVal_residue_ne_zero z hzq (by dsimp [z]; rwa [Padic.valuation_ratCast])))
  let L := secondPolar p P.Z P.U P.T P.Z D.w P.T
  have hL : L ≠ 0 := by
    intro he
    have hn := D.coefficient_negative
    change -p*L<0 at hn
    rw [he,mul_zero] at hn
    exact lt_irrefl _ hn
  let li := (pi-1)*ui*(pi*Bi*(ri*wi+2*ri*ti+2*zi))-
    pi*ti*(-Bi*((pi-1)*ri*wi+2*pi*ri*ti+2*(pi-1)*zi))+
    pi*Bi*zi*((pi-1)*wi-2*ri*Bi*zi)
  have hscale : (li : ℚ_[Q.val])=((s^2/r^3*L : ℚ) : ℚ_[Q.val]) := by
    change (pp-1)*u*(pp*BB*(rr*w+2*rr*t+2*z))-
      pp*t*(-BB*((pp-1)*rr*w+2*pp*rr*t+2*(pp-1)*z))+
      pp*BB*z*((pp-1)*w-2*rr*BB*z)=_
    dsimp [pp,u,BB,rr,w,t,z,L,B,secondPolar,anchorU,anchorT,anchorZ]
    push_cast
    field_simp
    <;> ring
  have hli : li ≠ 0 := by
    intro he
    have hn : ((s^2/r^3*L : ℚ) : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast mul_ne_zero (div_ne_zero (pow_ne_zero _ hs) (pow_ne_zero _ hr)) hL
    apply hn
    rw [← hscale,he]
    rfl
  have heven := positive_b_model_tangent_even Q pi ri Bi ui ti zi wi h2 hpI hrI hBI hbI hCI hDUI hprimI hli
  change Even (li : ℚ_[Q.val]).valuation at heven
  rw [hscale,Padic.valuation_ratCast,padicValRat.mul (div_ne_zero (pow_ne_zero _ hs) (pow_ne_zero _ hr)) hL,
    padicValRat.div (pow_ne_zero _ hs) (pow_ne_zero _ hr),padicValRat.pow,padicValRat.pow,hrv] at heven
  have hvp : padicValRat Q.val p=0 := by rwa [Padic.valuation_ratCast] at hpval
  have hemod : ((padicValRat Q.val L : ℤ) : ZMod 2)=(h : ZMod 2) := by
    rw [Int.even_iff] at heven
    have he : (padicValRat Q.val L)%2=(h : ℤ)%2 := by norm_num only [Nat.cast_ofNat] at heven; omega
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr he
  change ((padicValRat Q.val (-p*L) : ℤ) : ZMod 2)=_
  rw [padicValRat.mul (neg_ne_zero.mpr hp0) hL,padicValRat.neg,hvp,zero_add]
  exact hemod

theorem residue_eq_integral_residue (x : ℚ_[q]) (hx : x ≠ 0) (hv : x.valuation=0) :
    residue x hx=PadicInt.toZMod (integralOfVal x (by omega)) := by
  have he : (normalizedUnit x hx : ℤ_[q])=integralOfVal x (by omega) := by
    apply Subtype.ext
    simp only [coe_normalizedUnit,unitPart,hv,neg_zero,zpow_zero,mul_one,coe_integralOfVal]
  change PadicInt.toZMod (normalizedUnit x hx : ℤ_[q])=_
  rw [he]

/-- The full inert positive-b evaluation for the very same original-source
rational coefficient and exact half-valuation; no partner value is substituted. -/
theorem tangentSign_positive_b_inert (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (h2 : ¬ IsSquare (2 : ZMod Q.val))
    (h : ℕ) (hh : 0<h) (hvb : padicValRat Q.val (p+1)=2*h) :
    tangentSign p hp P D Q.val=(-1 : ℤ)^(h : ZMod 2).val := by
  have hp0 : p ≠ 0 := by linarith
  have ha0 : firstCoefficient p ≠ 0 := ne_of_lt (firstCoefficient_negative p hp)
  have hb0 : secondCoefficient p P D ≠ 0 := ne_of_lt D.coefficient_negative
  have hx : (firstCoefficient p : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast ha0
  have hy : (secondCoefficient p P D : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast hb0
  let x : ℚ_[Q.val] := firstCoefficient p
  have hc : x-2= -((p+1 : ℚ) : ℚ_[Q.val]) := by
    dsimp [x,firstCoefficient]
    push_cast
    ring
  have hB0 : p+1 ≠ 0 := by linarith
  have hdelta : x-2 ≠ 0 := by rw [hc]; exact neg_ne_zero.mpr (by exact_mod_cast hB0)
  have hvdelta : (x-2).valuation=2*h := by rw [hc,commonRoot_val_neg,Padic.valuation_ratCast,hvb]
  have htwo : (2 : ℚ_[Q.val]) ≠ 0 := by norm_num
  have hxval : x.valuation=0 := by
    have he := commonRoot_val_add_of_ne hdelta htwo
      (show (x-2).valuation ≠ (2 : ℚ_[Q.val]).valuation by rw [hvdelta,commonRoot_val_two Q.property.2]; omega)
    have heq : (x-2)+2=x := by ring
    rw [heq,hvdelta,commonRoot_val_two Q.property.2,min_eq_right (by omega : (0 : ℤ)≤2*h)] at he
    exact he
  let xi := integralOfVal x (by omega : 0≤x.valuation)
  have hres : PadicInt.toZMod xi=2 := by
    have hdI : xi-2=integralOfVal (x-2) (by omega : 0≤(x-2).valuation) := rfl
    have hd := integral_residue_zero_of_positive (x-2) (by omega)
    rw [← hdI,map_sub,map_ofNat] at hd
    linear_combination hd
  have hchar : quadraticChar (ZMod Q.val) (residue x hx)= -1 := by
    rw [residue_eq_integral_residue x hx hxval,hres]
    have ht : (2 : ZMod Q.val) ≠ 0 := by intro he; apply h2; rw [he]; exact IsSquare.zero
    norm_num [quadraticChar_apply,quadraticCharFun,ht,h2]
  have hyv : (((secondCoefficient p P D : ℚ_[Q.val]).valuation : ℤ) : ZMod 2)=(h : ZMod 2) := by
    rw [Padic.valuation_ratCast]
    exact secondCoefficient_positive_b_parity Q p hp P D h2 h hh hvb
  rw [tangentSign,rationalSign_eq_oddSign]
  change oddSign Q x _ hx hy=_
  simp only [oddSign,hxval,Int.cast_zero,ZMod.val_zero,zero_mul,mul_zero,pow_zero,one_mul,mul_one,hchar,hyv]

/-- Literal table row using the paper's half-valuation, with the original
Loc hypothesis supplying its integrality. -/
theorem tangentSign_positive_b_inert_half (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (hL : HasseNorms.Loc p) (P : HomogeneousPoint p) (D : TangentData p P)
    (h2 : ¬ IsSquare (2 : ZMod Q.val)) (hv : 0<padicValRat Q.val (p+1)) :
    tangentSign p hp P D Q.val=
      (-1 : ℤ)^(((padicValRat Q.val (p+1)/2 : ℤ) : ZMod 2).val) := by
  have he := (HasseNorms.local_inert_parities p hp hL Q.val Q.property.2
    (SqrtTwoGlobalNorm.nonsquare_two_completion h2)).2.2
  obtain ⟨k,hk⟩ := he
  have hkpos : 0<k := by omega
  have hkn : (k.toNat : ℤ)=k := Int.toNat_of_nonneg (by omega)
  have hkh : 0<k.toNat := by omega
  have hvb : padicValRat Q.val (p+1)=2*k.toNat := by omega
  have hr := tangentSign_positive_b_inert Q p hp P D h2 k.toNat hkh hvb
  have hex : (padicValRat Q.val (p+1)/2 : ℤ)=k.toNat := by omega
  rwa [hex]

#print axioms tangentSign_positive_b_inert_half

#print axioms residue_eq_integral_residue
#print axioms tangentSign_positive_b_inert

#print axioms integral_residue_zero_of_positive
#print axioms integral_of_unit_times_square
#print axioms secondCoefficient_positive_b_parity

end FourCorner.HassePositiveBInert
